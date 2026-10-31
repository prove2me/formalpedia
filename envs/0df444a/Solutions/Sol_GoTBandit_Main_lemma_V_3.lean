-- Prove2me | solution 1 for GoTBandit.Main.lemma_V_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:18:50.417492+00:00
-- url     : https://prove2.me/submissions/143157b9-e746-4e93-ae5a-10feb044fcfb

import Mathlib
import Definitions.Def_GoTBandit_Main_Algorithm

open Finset MeasureTheory ProbabilityTheory

namespace GoTV3
open GoTBandit.Main

noncomputable section
open Classical

def isExp : Phase → Bool
  | Phase.explore => true
  | _ => false

variable {N M : ℕ}

lemma preState_V (p : GoTParams) (t : ℕ) (st : PlayerState M) (seed : Fin 4 → ℝ) :
    (preState p t st seed).V = st.V ∧ (preState p t st seed).s = st.s := by
  unfold preState; split <;> exact ⟨rfl, rfl⟩

lemma act_explore (p : GoTParams) (t k : ℕ) (hph : phaseOf p t = (k, Phase.explore))
    (hM : 0 < M) (st : PlayerState M) (seed : Fin 4 → ℝ) :
    act p t st seed = unifArm hM (seed 0) := by
  simp only [act, hph]

lemma update_explore (p : GoTParams) (t k : ℕ) (hph : phaseOf p t = (k, Phase.explore))
    (st : PlayerState M) (seed : Fin 4 → ℝ) (a : Fin M) (obs : ℝ) :
    update p t st seed a obs = (if obs ≠ 0 then
        { st with V := Function.update st.V a (st.V a + 1),
                  s := Function.update st.s a (st.s a + obs) }
      else st) := by
  simp only [update, preState, hph]

lemma update_nonexplore (p : GoTParams) (t : ℕ) (hph : isExp (phaseOf p t).2 = false)
    (st : PlayerState M) (seed : Fin 4 → ℝ) (a : Fin M) (obs : ℝ) :
    (update p t st seed a obs).V = st.V ∧ (update p t st seed a obs).s = st.s := by
  rcases h : phaseOf p t with ⟨k, ph⟩
  rw [h] at hph
  cases ph with
  | explore => simp [isExp] at hph
  | got o =>
      have := preState_V p t st seed
      simp only [update, h]; exact this
  | exploit =>
      have := preState_V p t st seed
      simp only [update, h]; exact this

def prof (hM : 0 < M) (x : RandIdx N M → ℝ) (t : ℕ) : Fin N → Fin M :=
  fun m => unifArm hM (x (Sum.inr (m, t, 0)))

def cond (p : GoTParams) (hM : 0 < M) (x : RandIdx N M → ℝ) (n : Fin N) (i : Fin M)
    (t : ℕ) : Prop :=
  isExp (phaseOf p t).2 = true ∧ prof hM x t n = i ∧ noColl (prof hM x t) i = 1

def cntR (p : GoTParams) (hM : 0 < M) (x : RandIdx N M → ℝ) (n : Fin N) (i : Fin M)
    (T : ℕ) : ℝ :=
  ∑ t ∈ range T, if cond p hM x n i t then (1 : ℝ) else 0

def smR (p : GoTParams) (hM : 0 < M) (x : RandIdx N M → ℝ) (n : Fin N) (i : Fin M)
    (T : ℕ) : ℝ :=
  ∑ t ∈ range T, if cond p hM x n i t then x (Sum.inl (n, i, t)) else 0

variable {Ω : Type*}

def xv (r : Fin N → Fin M → ℕ → Ω → ℝ) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (ω : Ω) :
    RandIdx N M → ℝ := fun x =>
  match x with
  | Sum.inl (n, i, t) => r n i t ω
  | Sum.inr (n, t, j) => ξ n t j ω

lemma noColl_eq (a : Fin N → Fin M) (i : Fin M) : noColl a i = 0 ∨ noColl a i = 1 := by
  unfold noColl; split_ifs <;> simp

theorem traj_eq (p : GoTParams) (hNM : N ≤ M) (hM : 0 < M) (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (ω : Ω) (h0 : ∀ n i t, r n i t ω ≠ 0) :
    ∀ t n i, ((traj p hNM r ξ t ω n).V i : ℝ) = cntR p hM (xv r ξ ω) n i t ∧
      (traj p hNM r ξ t ω n).s i = smR p hM (xv r ξ ω) n i t := by
  intro t
  induction t with
  | zero => intro n i; simp [traj, initState, cntR, smR]
  | succ t ih =>
    intro n i
    simp only [cntR, smR, Finset.sum_range_succ]
    rw [← cntR, ← smR]
    obtain ⟨ihV, ihs⟩ := ih n i
    rcases hph : phaseOf p t with ⟨k, ph⟩
    cases ph with
    | explore =>
      have hprof : (fun m => act p t (traj p hNM r ξ t ω m) (seedsAt ξ m t ω)) =
          prof hM (xv r ξ ω) t := by
        funext m; rw [act_explore p t k hph hM]; rfl
      have hact : act p t (traj p hNM r ξ t ω n) (seedsAt ξ n t ω) = prof hM (xv r ξ ω) t n :=
        congrFun hprof n
      simp only [traj]
      rw [hprof, hact, update_explore p t k hph]
      have hr := h0 n (prof hM (xv r ξ ω) t n) t
      by_cases hc : noColl (prof hM (xv r ξ ω) t) (prof hM (xv r ξ ω) t n) = 1
      · rw [hc, mul_one, if_pos hr]
        simp only
        by_cases hi : prof hM (xv r ξ ω) t n = i
        · subst hi
          have hcd : cond p hM (xv r ξ ω) n (prof hM (xv r ξ ω) t n) t :=
            ⟨by rw [hph]; rfl, rfl, hc⟩
          simp only [Function.update_self, if_pos hcd]
          refine ⟨by push_cast; rw [ihV], by rw [ihs]; rfl⟩
        · have hcd : ¬ cond p hM (xv r ξ ω) n i t := fun h => hi h.2.1
          simp only [Function.update_of_ne (Ne.symm hi), if_neg hcd, add_zero]
          exact ⟨ihV, ihs⟩
      · have hc0 : noColl (prof hM (xv r ξ ω) t) (prof hM (xv r ξ ω) t n) = 0 :=
          (noColl_eq _ _).resolve_right hc
        rw [hc0, mul_zero, if_neg (by simp)]
        have hcd : ¬ cond p hM (xv r ξ ω) n i t := by
          rintro ⟨-, h1, h2⟩; rw [← h1] at h2; exact hc h2
        simp only [if_neg hcd, add_zero]
        exact ⟨ihV, ihs⟩
    | got o =>
      have hcd : ¬ cond p hM (xv r ξ ω) n i t := by
        rintro ⟨h1, -, -⟩; rw [hph] at h1; simp [isExp] at h1
      have hne : isExp (phaseOf p t).2 = false := by rw [hph]; rfl
      simp only [if_neg hcd, add_zero, traj]
      rw [(update_nonexplore p t hne _ _ _ _).1, (update_nonexplore p t hne _ _ _ _).2]
      exact ⟨ihV, ihs⟩
    | exploit =>
      have hcd : ¬ cond p hM (xv r ξ ω) n i t := by
        rintro ⟨h1, -, -⟩; rw [hph] at h1; simp [isExp] at h1
      have hne : isExp (phaseOf p t).2 = false := by rw [hph]; rfl
      simp only [if_neg hcd, add_zero, traj]
      rw [(update_nonexplore p t hne _ _ _ _).1, (update_nonexplore p t hne _ _ _ _).2]
      exact ⟨ihV, ihs⟩
theorem indep_null {ι : Type*} [Countable ι] [DecidableEq ι] {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P]
    (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (j : ι)
    (hat : ∀ y : ℝ, P (X j ⁻¹' {y}) = 0)
    (h : (ι → ℝ) → ℝ) (hh : Measurable h)
    (hinv : ∀ x : ι → ℝ, h (Function.update x j 0) = h x) :
    P {ω | X j ω = h (fun i => X i ω)} = 0 := by
  set V : Ω' → (ι → ℝ) := fun ω => Function.update (fun i => X i ω) j 0 with hVdef
  have hcoord : ∀ i, (fun ω => V ω i) = if i = j then (fun _ => (0:ℝ)) else X i := by
    intro i
    by_cases hij : i = j
    · subst hij; funext ω; simp [V]
    · funext ω; simp [V, Function.update_of_ne hij, hij]
  have hVm : Measurable V := measurable_pi_iff.2 fun i => by
    rw [hcoord i]; split_ifs
    · exact measurable_const
    · exact hX i
  have hind2 : Indep (⨆ i ∈ ({j} : Set ι), MeasurableSpace.comap (X i) inferInstance)
      (⨆ i ∈ ({j}ᶜ : Set ι), MeasurableSpace.comap (X i) inferInstance) P :=
    indep_iSup_of_disjoint (fun i => (hX i).comap_le)
      ((iIndepFun_iff_iIndep _ _ _).1 hind) disjoint_compl_right
  have hXV : IndepFun (X j) V P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hind2 ?_) ?_
    · apply Measurable.comap_le
      refine @measurable_pi_lambda Ω' ι (fun _ => ℝ)
        (⨆ i ∈ ({j}ᶜ : Set ι), MeasurableSpace.comap (X i) inferInstance)
        (fun _ => inferInstance) V (fun i => ?_)
      rw [hcoord i]
      split_ifs with hij
      · exact measurable_const
      · exact Measurable.mono (comap_measurable (X i))
          (le_iSup₂ (f := fun i (_ : i ∈ ({j}ᶜ : Set ι)) =>
            MeasurableSpace.comap (X i) inferInstance) i hij) le_rfl
    · exact le_iSup₂ (f := fun i (_ : i ∈ ({j} : Set ι)) =>
        MeasurableSpace.comap (X i) inferInstance) j rfl
  have hset : {ω | X j ω = h (fun i => X i ω)} =
      (fun ω => (X j ω, V ω)) ⁻¹' {q : ℝ × (ι → ℝ) | q.1 = h q.2} := by
    ext ω; simp [V, hinv]
  have hA : MeasurableSet {q : ℝ × (ι → ℝ) | q.1 = h q.2} :=
    measurableSet_eq_fun measurable_fst (hh.comp measurable_snd)
  rw [hset, ← Measure.map_apply ((hX j).prodMk hVm) hA,
    (indepFun_iff_map_prod_eq_prod_map_map (hX j).aemeasurable hVm.aemeasurable).1 hXV,
    Measure.prod_apply_symm hA]
  have hz : ∀ y : ι → ℝ, (Measure.map (X j) P)
      ((fun x => (x, y)) ⁻¹' {q : ℝ × (ι → ℝ) | q.1 = h q.2}) = 0 := by
    intro y
    have e : (fun x => (x, y)) ⁻¹' {q : ℝ × (ι → ℝ) | q.1 = h q.2} = {h y} := by ext; simp
    rw [e, Measure.map_apply (hX j) (measurableSet_singleton _)]; exact hat _
  simp_rw [hz]
  exact lintegral_zero

lemma noColl_nonneg (a : Fin N → Fin M) (i : Fin M) : 0 ≤ noColl a i := by
  unfold noColl; split_ifs <;> norm_num

lemma noColl_eq_one_iff (a : Fin N → Fin M) (i : Fin M) :
    noColl a i = 1 ↔ (univ.filter (fun m => a m = i)).card ≤ 1 := by
  unfold noColl
  split_ifs with h
  · constructor
    · intro hh; norm_num at hh
    · intro hh; omega
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem optimal_noColl (hNM : N ≤ M) (U : Fin N → Fin M → ℝ) (hpos : ∀ n i, 0 < U n i)
    (a : Fin N → Fin M) (ha : IsOptimal U a) : ∀ n, noColl a (a n) = 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨n1, hn1⟩ := hc
  have hn1' : 1 < (univ.filter (fun m => a m = a n1)).card := by
    rw [Ne, noColl_eq_one_iff] at hn1; omega
  obtain ⟨m1, hm1, m2, hm2, hm12⟩ := Finset.one_lt_card.1 hn1'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm1 hm2
  have hnotinj : ¬ Set.InjOn a (univ : Finset (Fin N)) := by
    intro hinj
    exact hm12 (hinj (by simp) (by simp) (hm1.trans hm2.symm))
  have hlt : (univ.image a).card < (univ : Finset (Fin M)).card := by
    have h1 : (univ.image a).card < (univ : Finset (Fin N)).card :=
      lt_of_le_of_ne Finset.card_image_le (fun h => hnotinj (Finset.card_image_iff.1 h))
    simp only [Finset.card_univ, Fintype.card_fin] at h1 ⊢
    omega
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hf' : ∀ m, a m ≠ f := fun m h => hf (Finset.mem_image.2 ⟨m, Finset.mem_univ _, h⟩)
  set a2 := Function.update a n1 f with ha2
  have key := ha a2
  apply absurd key
  push Not
  unfold obj
  apply Finset.sum_lt_sum
  · intro n _
    by_cases hn : n = n1
    · subst hn
      have h0 : noColl a (a n) = 0 := (noColl_eq _ _).resolve_right hn1
      simp only [gUtil, h0, mul_zero]
      exact mul_nonneg (le_of_lt (hpos _ _)) (noColl_nonneg _ _)
    · have e : a2 n = a n := Function.update_of_ne hn _ _
      simp only [gUtil, e]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (hpos _ _))
      rcases noColl_eq a (a n) with h | h
      · rw [h]; exact noColl_nonneg _ _
      · rw [h]
        rw [noColl_eq_one_iff] at h
        refine le_of_eq ((noColl_eq_one_iff _ _).2 (le_trans (Finset.card_le_card ?_) h)).symm
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        by_cases hmn : m = n1
        · subst hmn; simp [a2] at hm; exact absurd hm.symm (hf' n)
        · rwa [show a2 m = a m from Function.update_of_ne hmn _ _] at hm
  · refine ⟨n1, Finset.mem_univ _, ?_⟩
    have h0 : noColl a (a n1) = 0 := (noColl_eq _ _).resolve_right hn1
    have e : a2 n1 = f := Function.update_self _ _ _
    have h1 : noColl a2 f = 1 := by
      rw [noColl_eq_one_iff]
      refine le_trans (Finset.card_le_card (t := {n1}) ?_) (by simp)
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      by_contra hmn
      simp only [Finset.mem_singleton] at hmn
      rw [show a2 m = a m from Function.update_of_ne hmn _ _] at hm
      exact hf' m hm
    simp only [gUtil, h0, e, h1, mul_zero, mul_one]
    exact hpos _ _

lemma unifArm_meas (hM : 0 < M) : Measurable (unifArm hM : ℝ → Fin M) := by
  have : (unifArm hM : ℝ → Fin M) =
      (fun k : ℕ => (⟨min k (M - 1), by omega⟩ : Fin M)) ∘ (fun x : ℝ => ⌊(M : ℝ) * x⌋₊) := rfl
  rw [this]
  exact measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

lemma prof_meas (hM : 0 < M) (t : ℕ) :
    Measurable (fun x : RandIdx N M → ℝ => prof hM x t) :=
  measurable_pi_lambda _ fun m => (unifArm_meas hM).comp (measurable_pi_apply _)

lemma cond_meas (p : GoTParams) (hM : 0 < M) (n : Fin N) (i : Fin M) (t : ℕ) :
    MeasurableSet {x : RandIdx N M → ℝ | cond p hM x n i t} := by
  by_cases he : isExp (phaseOf p t).2 = true
  · have : {x : RandIdx N M → ℝ | cond p hM x n i t} =
        (fun x => prof hM x t) ⁻¹' {a | a n = i ∧ noColl a i = 1} := by
      ext x; simp [cond, he]
    rw [this]
    exact prof_meas hM t (Set.toFinite _).measurableSet
  · have : {x : RandIdx N M → ℝ | cond p hM x n i t} = ∅ := by
      ext x; simp [cond, he]
    rw [this]; exact MeasurableSet.empty

lemma cntR_meas (p : GoTParams) (hM : 0 < M) (n : Fin N) (i : Fin M) (T : ℕ) :
    Measurable (fun x : RandIdx N M → ℝ => cntR p hM x n i T) :=
  Finset.measurable_sum _ fun t _ =>
    Measurable.ite (cond_meas p hM n i t) measurable_const measurable_const

lemma smR_meas (p : GoTParams) (hM : 0 < M) (n : Fin N) (i : Fin M) (T : ℕ) :
    Measurable (fun x : RandIdx N M → ℝ => smR p hM x n i T) :=
  Finset.measurable_sum _ fun t _ =>
    Measurable.ite (cond_meas p hM n i t) (measurable_pi_apply _) measurable_const

def Ef (p : GoTParams) (hM : 0 < M) (T : ℕ) (x : RandIdx N M → ℝ) (n : Fin N) (i : Fin M) : ℝ :=
  smR p hM x n i T / cntR p hM x n i T

def hfun (p : GoTParams) (hM : 0 < M) (T : ℕ) (a a' : Fin N → Fin M) (n0 : Fin N) (t0 : ℕ)
    (x : RandIdx N M → ℝ) : ℝ :=
  cntR p hM x n0 (a n0) T *
      (∑ n, Ef p hM T x n (a' n) - ∑ n ∈ univ.erase n0, Ef p hM T x n (a n)) -
    ∑ t ∈ (range T).erase t0, (if cond p hM x n0 (a n0) t then x (Sum.inl (n0, a n0, t)) else 0)

lemma hfun_meas (p : GoTParams) (hM : 0 < M) (T : ℕ) (a a' : Fin N → Fin M) (n0 : Fin N)
    (t0 : ℕ) : Measurable (hfun p hM T a a' n0 t0) := by
  have hE : ∀ n i, Measurable (fun x : RandIdx N M → ℝ => Ef p hM T x n i) := fun n i =>
    (smR_meas p hM n i T).div (cntR_meas p hM n i T)
  unfold hfun
  refine Measurable.sub (Measurable.mul (cntR_meas p hM _ _ T) (Measurable.sub ?_ ?_)) ?_
  · exact Finset.measurable_sum _ fun n _ => hE n _
  · exact Finset.measurable_sum _ fun n _ => hE n _
  · exact Finset.measurable_sum _ fun t _ =>
      Measurable.ite (cond_meas p hM _ _ t) (measurable_pi_apply _) measurable_const

lemma cond_update (p : GoTParams) (hM : 0 < M) (x : RandIdx N M → ℝ) (q : Fin N × Fin M × ℕ)
    (v : ℝ) : cond p hM (Function.update x (Sum.inl q) v) = cond p hM x := by
  have : ∀ t, prof hM (Function.update x (Sum.inl q) v) t = prof hM x t := by
    intro t; funext m; simp [prof]
  funext n i t; simp only [cond, this]

lemma cntR_update (p : GoTParams) (hM : 0 < M) (x : RandIdx N M → ℝ) (q : Fin N × Fin M × ℕ)
    (v : ℝ) (n : Fin N) (i : Fin M) (T : ℕ) :
    cntR p hM (Function.update x (Sum.inl q) v) n i T = cntR p hM x n i T := by
  simp only [cntR, cond_update]

lemma smR_update (p : GoTParams) (hM : 0 < M) (x : RandIdx N M → ℝ) (n0 : Fin N) (i0 : Fin M)
    (t0 : ℕ) (v : ℝ) (n : Fin N) (i : Fin M) (hni : (n, i) ≠ (n0, i0)) (T : ℕ) :
    smR p hM (Function.update x (Sum.inl (n0, i0, t0)) v) n i T = smR p hM x n i T := by
  simp only [smR, cond_update]
  refine Finset.sum_congr rfl fun t _ => ?_
  have : (Sum.inl (n, i, t) : RandIdx N M) ≠ Sum.inl (n0, i0, t0) := by
    intro h; apply hni; simp only [Sum.inl.injEq, Prod.mk.injEq] at h; rw [h.1, h.2.1]
  rw [Function.update_of_ne this]

lemma hfun_update (p : GoTParams) (hM : 0 < M) (T : ℕ) (a a' : Fin N → Fin M) (n0 : Fin N)
    (t0 : ℕ) (hne : a n0 ≠ a' n0) (x : RandIdx N M → ℝ) :
    hfun p hM T a a' n0 t0 (Function.update x (Sum.inl (n0, a n0, t0)) 0) =
      hfun p hM T a a' n0 t0 x := by
  have e1 : ∀ n, Ef p hM T (Function.update x (Sum.inl (n0, a n0, t0)) 0) n (a' n) =
      Ef p hM T x n (a' n) := by
    intro n; unfold Ef
    rw [cntR_update, smR_update]
    intro h; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2⟩ := h; subst h1; exact hne h2.symm
  have e2 : ∀ n ∈ univ.erase n0, Ef p hM T (Function.update x (Sum.inl (n0, a n0, t0)) 0) n
      (a n) = Ef p hM T x n (a n) := by
    intro n hn; unfold Ef
    rw [cntR_update, smR_update]
    intro h; simp only [Prod.mk.injEq] at h
    exact (Finset.mem_erase.1 hn).1 h.1
  have e3 : ∑ t ∈ (range T).erase t0,
      (if cond p hM (Function.update x (Sum.inl (n0, a n0, t0)) 0) n0 (a n0) t then
        (Function.update x (Sum.inl (n0, a n0, t0)) 0) (Sum.inl (n0, a n0, t)) else 0) =
      ∑ t ∈ (range T).erase t0, (if cond p hM x n0 (a n0) t then x (Sum.inl (n0, a n0, t))
        else 0) := by
    rw [cond_update]
    refine Finset.sum_congr rfl fun t ht => ?_
    have : (Sum.inl (n0, a n0, t) : RandIdx N M) ≠ Sum.inl (n0, a n0, t0) := by
      intro h; simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact (Finset.mem_erase.1 ht).1 h.2.2
    rw [Function.update_of_ne this]
  unfold hfun
  rw [cntR_update, Finset.sum_congr rfl (fun n _ => e1 n), Finset.sum_congr rfl e2, e3]

end
end GoTV3

open GoTBandit.Main GoTV3

theorem solution {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (k : ℕ) (hk : 1 ≤ k) :
    P {ω | (∀ n i, 1 ≤ visitCount p hNM r ξ k n i ω ∧ 0 < est p hNM r ξ k n i ω) ∧
        ¬ ∃! a, IsOptimal (fun n i => est p hNM r ξ k n i ω) a} = 0 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    apply measure_mono_null _ measure_empty
    intro ω hω
    exact hω.2 ⟨fun i => i.elim0, fun a' => le_of_eq (by rw [Subsingleton.elim a' (fun i => i.elim0)]),
      fun b _ => Subsingleton.elim _ _⟩
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  set T := p.epochStart k + expLen p.c1 p.δ k with hT
  let X : RandIdx N M → Ω → ℝ := fun (x : RandIdx N M) (ω : Ω) =>
    match x with
    | Sum.inl (n, i, t) => r n i t ω
    | Sum.inr (n, t, j) => ξ n t j ω
  have hXm : ∀ i, Measurable (X i) := by
    rintro (⟨n, i, t⟩ | ⟨n, t, j⟩)
    · exact hr.meas n i t
    · exact hξ.meas n t j
  have hxv : ∀ ω, xv r ξ ω = fun i => X i ω := by
    intro ω; funext i; rcases i with (⟨n, i, t⟩ | ⟨n, t, j⟩) <;> rfl
  have hr0 : ∀ n i t (y : ℝ), P (r n i t ⁻¹' {y}) = 0 := by
    intro n i t y
    rw [(hr.ident n i t).measure_mem_eq (measurableSet_singleton y)]
    exact hr.continuous n i y
  -- the bad sets
  let B : Set Ω := (⋃ n, ⋃ i, ⋃ t, {ω | r n i t ω = 0}) ∪
    ⋃ a : Fin N → Fin M, ⋃ a' : Fin N → Fin M, ⋃ n0 : Fin N, ⋃ t0 : ℕ,
      {ω | a n0 ≠ a' n0 ∧ r n0 (a n0) t0 ω = hfun p hM T a a' n0 t0 (xv r ξ ω)}
  have hB : P B = 0 := by
    apply measure_union_null
    · refine measure_iUnion_null fun n => measure_iUnion_null fun i =>
        measure_iUnion_null fun t => hr0 n i t 0
    · refine measure_iUnion_null fun a => measure_iUnion_null fun a' =>
        measure_iUnion_null fun n0 => measure_iUnion_null fun t0 => ?_
      by_cases hne : a n0 = a' n0
      · apply measure_mono_null _ measure_empty
        intro ω hω; exact hω.1 hne
      · apply measure_mono_null _ (indep_null P X hXm hξ.indep (Sum.inl (n0, a n0, t0))
          (fun y => hr0 n0 (a n0) t0 y) (hfun p hM T a a' n0 t0) (hfun_meas p hM T a a' n0 t0)
          (hfun_update p hM T a a' n0 t0 hne))
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [hxv] at hω
        exact hω.2
  apply measure_mono_null _ hB
  intro ω ⟨hgood, hnu⟩
  by_contra hωB
  have h0 : ∀ n i t, r n i t ω ≠ 0 := by
    intro n i t h; exact hωB (Or.inl (by simp only [Set.mem_iUnion, Set.mem_ofPred_eq]; exact ⟨n, i, t, h⟩))
  have htr := traj_eq p hNM hM r ξ ω h0 T
  set μh : Fin N → Fin M → ℝ := fun n i => est p hNM r ξ k n i ω with hμh
  have hest : ∀ n i, μh n i = Ef p hM T (xv r ξ ω) n i := by
    intro n i
    simp only [hμh, est, PlayerState.estimate, Ef]
    rw [(htr n i).1, (htr n i).2]
  have hpos : ∀ n i, 0 < μh n i := fun n i => (hgood n i).2
  haveI : Nonempty (Fin N → Fin M) := ⟨fun _ => ⟨0, hM⟩⟩
  obtain ⟨a1, ha1⟩ := Finite.exists_max (obj μh)
  have hopt1 : IsOptimal μh a1 := ha1
  obtain ⟨a2, hopt2, hne12⟩ : ∃ a2, IsOptimal μh a2 ∧ a2 ≠ a1 := by
    by_contra hcon
    push Not at hcon
    exact hnu ⟨a1, hopt1, fun b hb => hcon b hb⟩
  have hsum : ∀ a, IsOptimal μh a → obj μh a = ∑ n, μh n (a n) := by
    intro a ha
    unfold obj gUtil
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [optimal_noColl hNM μh hpos a ha n, mul_one]
  have heq : ∑ n, μh n (a1 n) = ∑ n, μh n (a2 n) := by
    rw [← hsum a1 hopt1, ← hsum a2 hopt2]
    exact le_antisymm (hopt2 a1) (hopt1 a2)
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 hne12
  -- isolate the estimate of (n0, a1 n0)
  have hiso : μh n0 (a1 n0) = ∑ n, μh n (a2 n) - ∑ n ∈ univ.erase n0, μh n (a1 n) := by
    rw [← heq, ← Finset.add_sum_erase _ _ (Finset.mem_univ n0)]; ring
  set x := xv r ξ ω with hx
  have hcnt : (1 : ℝ) ≤ cntR p hM x n0 (a1 n0) T := by
    rw [← (htr n0 (a1 n0)).1]
    exact_mod_cast (hgood n0 (a1 n0)).1
  obtain ⟨t0, ht0, hc0⟩ : ∃ t0 ∈ range T, cond p hM x n0 (a1 n0) t0 := by
    by_contra hcon
    push Not at hcon
    have : cntR p hM x n0 (a1 n0) T = 0 := by
      unfold cntR
      exact Finset.sum_eq_zero fun t ht => if_neg (hcon t ht)
    linarith
  have hsm : smR p hM x n0 (a1 n0) T = r n0 (a1 n0) t0 ω +
      ∑ t ∈ (range T).erase t0, (if cond p hM x n0 (a1 n0) t then x (Sum.inl (n0, a1 n0, t))
        else 0) := by
    unfold smR
    rw [← Finset.add_sum_erase _ _ ht0, if_pos hc0]
    rfl
  have hEf : smR p hM x n0 (a1 n0) T = cntR p hM x n0 (a1 n0) T * μh n0 (a1 n0) := by
    rw [hest, Ef]; field_simp
  apply hωB
  refine Or.inr ?_
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨a1, a2, n0, t0, fun h => hn0 (h.symm ▸ rfl), ?_⟩
  unfold hfun
  rw [← hx]
  have hL : ∑ n, Ef p hM T x n (a2 n) - ∑ n ∈ univ.erase n0, Ef p hM T x n (a1 n) =
      μh n0 (a1 n0) := by
    rw [hiso]; simp only [hest, hx]
  rw [hL, ← hEf, hsm]
  ring

