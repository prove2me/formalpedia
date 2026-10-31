-- Prove2me | solution 1 for GoTBandit.Main.lemma_IV_3_eq20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:40:47.118993+00:00
-- url     : https://prove2.me/submissions/cd1c1f39-54c1-4169-844b-5e35a0d00862

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




open Finset MeasureTheory ProbabilityTheory

namespace GoT20

lemma exp_le_aux (x : ℝ) : Real.exp x ≤ 1 + x + (Real.exp |x| - 1 - |x|) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith
  · rw [abs_of_neg hx]
    have h := Real.sinh_le_self_iff.2 hx.le
    rw [Real.sinh_eq] at h
    linarith

lemma hasSum_exp_sub (z : ℝ) :
    HasSum (fun k : ℕ => z ^ (k + 2) / ((k + 2).factorial : ℝ)) (Real.exp z - 1 - z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rw [← congrFun Real.exp_eq_exp_ℝ z] at h
  have := (hasSum_nat_add_iff' 2).2 h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one] at this
  rw [sub_sub]; exact this

/-- Bernstein's moment-generating-function bound. -/
theorem bern_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hYm : Measurable Y) (hYi : Integrable Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (s2 b : ℝ) (hs2 : 0 ≤ s2) (hb : 0 < b)
    (hmom : ∀ k : ℕ, 2 ≤ k → Integrable (fun ω => |Y ω| ^ k) P ∧
      ∫ ω, |Y ω| ^ k ∂P ≤ (k.factorial : ℝ) / 2 * s2 * b ^ (k - 2))
    (l : ℝ) (hl : 0 ≤ l) (hlb : l * b < 1) :
    Integrable (fun ω => Real.exp (l * Y ω)) P ∧
      mgf Y P l ≤ Real.exp (l ^ 2 * s2 / (2 * (1 - l * b))) := by
  set g : Ω → ℝ := fun ω => Real.exp (l * |Y ω|) - 1 - l * |Y ω| with hg
  have hgnn : ∀ ω, 0 ≤ g ω := by
    intro ω; simp only [hg]; linarith [Real.add_one_le_exp (l * |Y ω|)]
  set term : ℕ → Ω → ℝ := fun k ω => (l * |Y ω|) ^ (k + 2) / ((k + 2).factorial : ℝ) with hterm
  have htermnn : ∀ k ω, 0 ≤ term k ω := fun k ω => by
    simp only [hterm]; have := abs_nonneg (Y ω); positivity
  have hgsum : ∀ ω, HasSum (fun k => term k ω) (g ω) := fun ω => hasSum_exp_sub (l * |Y ω|)
  have hterm_int : ∀ k, Integrable (term k) P := by
    intro k
    have := (hmom (k + 2) (by omega)).1
    simp only [hterm, mul_pow]
    exact (this.const_mul (l ^ (k + 2))).div_const _
  have hterm_eq : ∀ k, ∫ ω, term k ω ∂P =
      l ^ (k + 2) * (∫ ω, |Y ω| ^ (k + 2) ∂P) / ((k + 2).factorial : ℝ) := by
    intro k
    simp only [hterm, mul_pow]
    rw [integral_div, integral_const_mul]
  set B := l ^ 2 * s2 / (2 * (1 - l * b)) with hB
  have hgeo : HasSum (fun k : ℕ => l ^ 2 * s2 / 2 * (l * b) ^ k) B := by
    have := (hasSum_geometric_of_lt_one (by positivity) hlb).mul_left (l ^ 2 * s2 / 2)
    have e : B = l ^ 2 * s2 / 2 * (1 - l * b)⁻¹ := by
      rw [hB]; field_simp
    rw [e]; exact this
  have hbound : ∀ k, ∫ ω, term k ω ∂P ≤ l ^ 2 * s2 / 2 * (l * b) ^ k := by
    intro k
    rw [hterm_eq]
    have hm := (hmom (k + 2) (by omega)).2
    simp only [Nat.add_sub_cancel] at hm
    have hf : (0 : ℝ) < ((k + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_iff₀ hf]
    calc l ^ (k + 2) * ∫ ω, |Y ω| ^ (k + 2) ∂P
        ≤ l ^ (k + 2) * (((k + 2).factorial : ℝ) / 2 * s2 * b ^ k) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = l ^ 2 * s2 / 2 * (l * b) ^ k * ((k + 2).factorial : ℝ) := by ring
  -- lintegral of g
  have hlin : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≤ ENNReal.ofReal B := by
    have e1 : ∀ ω, ENNReal.ofReal (g ω) = ∑' k, ENNReal.ofReal (term k ω) := by
      intro ω
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => htermnn k ω) (hgsum ω).summable,
        (hgsum ω).tsum_eq]
    simp_rw [e1]
    rw [lintegral_tsum (fun k => (hterm_int k).aemeasurable.ennreal_ofReal)]
    have e2 : ∀ k, ∫⁻ ω, ENNReal.ofReal (term k ω) ∂P = ENNReal.ofReal (∫ ω, term k ω ∂P) :=
      fun k => (ofReal_integral_eq_lintegral_ofReal (hterm_int k)
        (Filter.Eventually.of_forall (htermnn k))).symm
    simp_rw [e2]
    rw [← hgeo.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeo.summable]
    exact ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hbound k)
  have hgmeas : Measurable g := by
    simp only [hg]
    exact ((measurable_const.mul hYm.abs).exp.sub measurable_const).sub
      (measurable_const.mul hYm.abs)
  have hgint : Integrable g P := by
    refine ⟨hgmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hgnn)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hgle : ∫ ω, g ω ∂P ≤ B := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgnn)
      hgmeas.aestronglyMeasurable]
    have hB0 : 0 ≤ B := by
      rw [hB]; apply div_nonneg (by positivity); linarith
    exact ENNReal.toReal_le_of_le_ofReal hB0 hlin
  have hpt : ∀ ω, Real.exp (l * Y ω) ≤ 1 + l * Y ω + g ω := by
    intro ω
    have := exp_le_aux (l * Y ω)
    rw [abs_mul, abs_of_nonneg hl] at this
    simpa [hg] using this
  have hdom : Integrable (fun ω => 1 + l * Y ω + g ω) P :=
    ((integrable_const 1).add (hYi.const_mul l)).add hgint
  have hint : Integrable (fun ω => Real.exp (l * Y ω)) P := by
    refine hdom.mono' (measurable_const.mul hYm).exp.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt ω
  refine ⟨hint, ?_⟩
  have h1 : mgf Y P l ≤ 1 + B := by
    unfold mgf
    calc ∫ ω, Real.exp (l * Y ω) ∂P ≤ ∫ ω, (1 + l * Y ω + g ω) ∂P :=
          integral_mono hint hdom hpt
      _ = 1 + l * ∫ ω, Y ω ∂P + ∫ ω, g ω ∂P := by
          rw [integral_add (f := fun ω => 1 + l * Y ω) (g := g)
              ((integrable_const 1).add (hYi.const_mul l)) hgint,
            integral_add (f := fun _ => (1:ℝ)) (g := fun ω => l * Y ω) (integrable_const 1)
              (hYi.const_mul l), integral_const_mul]
          simp
      _ ≤ 1 + B := by rw [hY0]; linarith
  linarith [Real.add_one_le_exp B]

/-- Bernstein's inequality (upper tail) for independent centred variables. -/
theorem bern_tail {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hind : iIndepFun Y P)
    (hm : ∀ i, Measurable (Y i)) (S0 : Finset ι) (s2 b : ℝ) (hs2 : 0 < s2) (hb : 0 < b)
    (hYi : ∀ i, Integrable (Y i) P) (hY0 : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hmom : ∀ i, ∀ k : ℕ, 2 ≤ k → Integrable (fun ω => |Y i ω| ^ k) P ∧
      ∫ ω, |Y i ω| ^ k ∂P ≤ (k.factorial : ℝ) / 2 * s2 * b ^ (k - 2))
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (S0.card : ℝ) * ε ≤ ∑ i ∈ S0, Y i ω} ≤
      Real.exp (-(S0.card : ℝ) * ε ^ 2 / (2 * (s2 + b * ε))) := by
  have hd : 0 < s2 + b * ε := by positivity
  set l := ε / (s2 + b * ε) with hl
  have hl0 : 0 ≤ l := by positivity
  have hlb : l * b < 1 := by
    rw [hl, div_mul_eq_mul_div, div_lt_one hd]; nlinarith
  have hbm := fun i => bern_mgf (Y i) (hm i) (hYi i) (hY0 i) s2 b hs2.le hb (hmom i) l hl0 hlb
  have hint : Integrable (fun ω => Real.exp (l * (∑ i ∈ S0, Y i) ω)) P :=
    hind.integrable_exp_mul_sum hm (fun i _ => (hbm i).1)
  have hset : {ω | (S0.card : ℝ) * ε ≤ ∑ i ∈ S0, Y i ω} =
      {ω | (S0.card : ℝ) * ε ≤ (∑ i ∈ S0, Y i) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine le_trans (measure_ge_le_exp_mul_mgf _ hl0 hint) ?_
  rw [hind.mgf_sum hm S0]
  set B := l ^ 2 * s2 / (2 * (1 - l * b)) with hB
  have hprod : ∏ i ∈ S0, mgf (Y i) P l ≤ ∏ _i ∈ S0, Real.exp B :=
    Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hbm i).2)
  rw [Finset.prod_const, ← Real.exp_nat_mul] at hprod
  calc Real.exp (-l * ((S0.card : ℝ) * ε)) * ∏ i ∈ S0, mgf (Y i) P l
      ≤ Real.exp (-l * ((S0.card : ℝ) * ε)) * Real.exp ((S0.card : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-(S0.card : ℝ) * ε ^ 2 / (2 * (s2 + b * ε))) := by
        rw [← Real.exp_add]
        congr 1
        have h1 : 1 - l * b = s2 / (s2 + b * ε) := by
          rw [hl]; field_simp; ring
        rw [hB, h1, hl]
        field_simp
        ring

/-- Two-sided Bernstein inequality. -/
theorem bern_two {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hind : iIndepFun Y P)
    (hm : ∀ i, Measurable (Y i)) (S0 : Finset ι) (s2 b : ℝ) (hs2 : 0 < s2) (hb : 0 < b)
    (hYi : ∀ i, Integrable (Y i) P) (hY0 : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hmom : ∀ i, ∀ k : ℕ, 2 ≤ k → Integrable (fun ω => |Y i ω| ^ k) P ∧
      ∫ ω, |Y i ω| ^ k ∂P ≤ (k.factorial : ℝ) / 2 * s2 * b ^ (k - 2))
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (S0.card : ℝ) * ε ≤ |∑ i ∈ S0, Y i ω|} ≤
      2 * Real.exp (-(S0.card : ℝ) * ε ^ 2 / (2 * (s2 + b * ε))) := by
  have h1 := bern_tail Y hind hm S0 s2 b hs2 hb hYi hY0 hmom ε hε
  have hind' : iIndepFun (fun i ω => -Y i ω) P :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have h2 := bern_tail (fun i ω => -Y i ω) hind' (fun i => (hm i).neg) S0 s2 b hs2 hb
    (fun i => (hYi i).neg) (fun i => by rw [integral_neg, hY0 i, neg_zero])
    (fun i k hk => by simpa only [abs_neg] using hmom i k hk) ε hε
  have hsub : {ω | (S0.card : ℝ) * ε ≤ |∑ i ∈ S0, Y i ω|} ⊆
      {ω | (S0.card : ℝ) * ε ≤ ∑ i ∈ S0, Y i ω} ∪
        {ω | (S0.card : ℝ) * ε ≤ ∑ i ∈ S0, (fun i ω => -Y i ω) i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; exact h
  calc P.real {ω | (S0.card : ℝ) * ε ≤ |∑ i ∈ S0, Y i ω|}
      ≤ P.real ({ω | (S0.card : ℝ) * ε ≤ ∑ i ∈ S0, Y i ω} ∪
        {ω | (S0.card : ℝ) * ε ≤ ∑ i ∈ S0, (fun i ω => -Y i ω) i ω}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end GoT20



open Finset MeasureTheory ProbabilityTheory

namespace GoT20
open GoTBandit.Main GoTV3

lemma expLen_pos (p : GoTParams) (hc1 : 0 < p.c1) {j : ℕ} (hj : 1 ≤ j) :
    1 ≤ expLen p.c1 p.δ j := by
  unfold expLen
  have : (0 : ℝ) < (p.c1 : ℝ) * (j : ℝ) ^ p.δ := by
    have hc : (0 : ℝ) < p.c1 := by exact_mod_cast hc1
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    positivity
  exact Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)

lemma epochLen_pos (p : GoTParams) (hc1 : 0 < p.c1) {j : ℕ} (hj : 1 ≤ j) :
    1 ≤ p.epochLen j := by
  unfold GoTParams.epochLen; have := expLen_pos p hc1 hj; omega

lemma epochStart_succ (p : GoTParams) {j : ℕ} (hj : 1 ≤ j) :
    p.epochStart (j + 1) = p.epochStart j + p.epochLen j := by
  unfold GoTParams.epochStart
  rw [Finset.sum_Ico_succ_top hj]

lemma epochStart_mono (p : GoTParams) {i j : ℕ} (hij : i ≤ j) :
    p.epochStart i ≤ p.epochStart j := by
  unfold GoTParams.epochStart
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hij)

lemma epochStart_ge (p : GoTParams) (hc1 : 0 < p.c1) (i : ℕ) : i - 1 ≤ p.epochStart i := by
  unfold GoTParams.epochStart
  calc i - 1 = ∑ j ∈ Finset.Ico 1 i, 1 := by simp
    _ ≤ ∑ j ∈ Finset.Ico 1 i, p.epochLen j :=
        Finset.sum_le_sum fun j hj => epochLen_pos p hc1 (Finset.mem_Ico.1 hj).1

lemma epochOf_eq (p : GoTParams) (hc1 : 0 < p.c1) {i t : ℕ} (hi : 1 ≤ i)
    (h1 : p.epochStart i ≤ t) (h2 : t < p.epochStart (i + 1)) : p.epochOf t = i := by
  unfold GoTParams.epochOf
  have hmem : i ∈ (Finset.range (t + 2)).filter (fun k => 1 ≤ k ∧ p.epochStart k ≤ t) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hi, h1⟩
    have := epochStart_ge p hc1 i; omega
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    show k ≤ i
    by_contra hki
    push Not at hki
    have := epochStart_mono p (show i + 1 ≤ k by omega)
    omega
  · exact Finset.le_sup (f := id) hmem

lemma phase_explore (p : GoTParams) (hc1 : 0 < p.c1) {i o : ℕ} (hi : 1 ≤ i)
    (ho : o < expLen p.c1 p.δ i) :
    phaseOf p (p.epochStart i + o) = (i, Phase.explore) := by
  have hlt : p.epochStart i + o < p.epochStart (i + 1) := by
    rw [epochStart_succ p hi]; unfold GoTParams.epochLen; omega
  have he := epochOf_eq p hc1 hi (Nat.le_add_right _ _) hlt
  unfold phaseOf
  simp only [he, Nat.add_sub_cancel_left, if_pos ho]

/-- The number of exploration turns before the end of the exploration phase of epoch `k`. -/
lemma count_explore (p : GoTParams) (hc1 : 0 < p.c1) (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.Icc 1 k, expLen p.c1 p.δ i ≤
      ((Finset.range (p.epochStart k + expLen p.c1 p.δ k)).filter
        (fun t => isExp (phaseOf p t).2 = true)).card := by
  set T := p.epochStart k + expLen p.c1 p.δ k
  set piece : ℕ → Finset ℕ := fun i =>
    (Finset.range (expLen p.c1 p.δ i)).image (fun o => p.epochStart i + o) with hpiece
  have hcard : ∀ i, (piece i).card = expLen p.c1 p.δ i := by
    intro i; simp only [hpiece]
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
  have hdisj : (↑(Finset.Icc 1 k) : Set ℕ).PairwiseDisjoint piece := by
    intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [hpiece, Finset.mem_image, Finset.mem_range] at hxi hxj
    obtain ⟨o1, ho1, rfl⟩ := hxi
    obtain ⟨o2, ho2, h⟩ := hxj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have a1 := epochStart_succ p hi.1
      have a2 := epochStart_mono p (show i + 1 ≤ j by omega)
      unfold GoTParams.epochLen at a1
      omega
    · have a1 := epochStart_succ p hj.1
      have a2 := epochStart_mono p (show j + 1 ≤ i by omega)
      unfold GoTParams.epochLen at a1
      omega
  have hsub : (Finset.Icc 1 k).biUnion piece ⊆
      (Finset.range T).filter (fun t => isExp (phaseOf p t).2 = true) := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_Icc, hpiece, Finset.mem_image,
      Finset.mem_range] at hx
    obtain ⟨i, ⟨hi1, hik⟩, o, ho, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, by rw [phase_explore p hc1 hi1 ho]; rfl⟩
    rcases lt_or_eq_of_le hik with hlt | heq
    · have a1 := epochStart_succ p hi1
      have a2 := epochStart_mono p (show i + 1 ≤ k by omega)
      unfold GoTParams.epochLen at a1
      simp only [T]; omega
    · subst heq; simp only [T]; omega
  calc ∑ i ∈ Finset.Icc 1 k, expLen p.c1 p.δ i = ∑ i ∈ Finset.Icc 1 k, (piece i).card := by
        simp only [hcard]
    _ = ((Finset.Icc 1 k).biUnion piece).card := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma sum_expLen_ge (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (k : ℕ) (hk : 1 ≤ k) :
    (p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ * k / 2 ≤ ∑ i ∈ Finset.Icc 1 k, (expLen p.c1 p.δ i : ℝ) := by
  have hc : (0 : ℝ) ≤ p.c1 := by positivity
  have hsub : Finset.Icc (k - k / 2) k ⊆ Finset.Icc 1 k := by
    intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  have hcard : ((Finset.Icc (k - k / 2) k).card : ℝ) = (k / 2 : ℕ) + 1 := by
    rw [Nat.card_Icc]; push_cast [show k + 1 - (k - k / 2) = k / 2 + 1 by omega]; ring
  have hk2 : (k : ℝ) / 2 ≤ ((k / 2 : ℕ) : ℝ) + 1 := by
    have := Nat.lt_div_mul_add (show 0 < 2 by norm_num) (a := k)
    have h' : (k : ℝ) < ((k / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
    linarith
  calc (p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ * k / 2
      = ((k : ℝ) / 2) * ((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ) := by ring
    _ ≤ ((Finset.Icc (k - k / 2) k).card : ℝ) * ((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ) := by
        rw [hcard]; apply mul_le_mul_of_nonneg_right hk2; positivity
    _ = ∑ i ∈ Finset.Icc (k - k / 2) k, (p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.Icc (k - k / 2) k, (expLen p.c1 p.δ i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_Icc] at hi
        have hik : (k : ℝ) / 2 ≤ i := by
          have : k ≤ 2 * i := by omega
          have : (k : ℝ) ≤ 2 * i := by exact_mod_cast this
          linarith
        calc (p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ ≤ (p.c1 : ℝ) * (i : ℝ) ^ p.δ := by
              apply mul_le_mul_of_nonneg_left _ hc
              exact Real.rpow_le_rpow (by positivity) hik hδ.le
          _ ≤ (expLen p.c1 p.δ i : ℝ) := Nat.le_ceil _
    _ ≤ ∑ i ∈ Finset.Icc 1 k, (expLen p.c1 p.δ i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)

end GoT20



open Finset MeasureTheory ProbabilityTheory

namespace GoT20
open GoTBandit.Main GoTV3

noncomputable section
open Classical

lemma unifArm_set (M : ℕ) (hM : 0 < M) (i : Fin M) :
    unifArm hM ⁻¹' {i} ∩ Set.Icc (0 : ℝ) 1 =
      if i.val < M - 1 then Set.Ico ((i : ℝ) / M) (((i : ℝ) + 1) / M)
      else Set.Icc (((M : ℝ) - 1) / M) 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Icc]
  have hU : unifArm hM x = i ↔ min ⌊(M : ℝ) * x⌋₊ (M - 1) = i.val := by
    rw [Fin.ext_iff]; rfl
  rw [hU]
  split_ifs with hi
  · simp only [Set.mem_Ico]
    constructor
    · rintro ⟨hm, hx0, hx1⟩
      have hfl : ⌊(M : ℝ) * x⌋₊ = i.val := by
        rcases le_total ⌊(M : ℝ) * x⌋₊ (M - 1) with h | h
        · rwa [min_eq_left h] at hm
        · rw [min_eq_right h] at hm; omega
      rw [Nat.floor_eq_iff (by positivity)] at hfl
      constructor
      · rw [div_le_iff₀ hMr]; linarith [hfl.1]
      · rw [lt_div_iff₀ hMr]; linarith [hfl.2]
    · rintro ⟨h1, h2⟩
      rw [div_le_iff₀ hMr] at h1
      rw [lt_div_iff₀ hMr] at h2
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      have hiM : (i.val : ℝ) + 1 ≤ M - 1 := by
        have : i.val + 1 ≤ M - 1 := by omega
        have : ((i.val + 1 : ℕ) : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast [Nat.cast_sub (show 1 ≤ M by omega)] at this; linarith
      have hx0 : 0 ≤ x := by nlinarith
      have hfl : ⌊(M : ℝ) * x⌋₊ = i.val := by
        rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
      refine ⟨by rw [hfl]; exact min_eq_left (by omega), hx0, ?_⟩
      nlinarith
  · have hiv : i.val = M - 1 := by have := i.isLt; omega
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ M by omega)]; simp
    constructor
    · rintro ⟨hm, hx0, hx1⟩
      have : M - 1 ≤ ⌊(M : ℝ) * x⌋₊ := by
        by_contra hc; push Not at hc
        rw [min_eq_left hc.le] at hm; omega
      rw [Nat.le_floor_iff (by positivity), hM1] at this
      refine ⟨?_, hx1⟩
      rw [div_le_iff₀ hMr]; linarith
    · rintro ⟨h1, h2⟩
      rw [div_le_iff₀ hMr] at h1
      have hx0 : 0 ≤ x := by
        have : (0 : ℝ) ≤ (M : ℝ) - 1 := by
          have : (1 : ℝ) ≤ M := by exact_mod_cast hM
          linarith
        nlinarith
      refine ⟨?_, hx0, h2⟩
      have : M - 1 ≤ ⌊(M : ℝ) * x⌋₊ := by
        rw [Nat.le_floor_iff (by positivity), hM1]; linarith
      rw [min_eq_right this, hiv]

lemma unifArm_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : ℕ) (hM : 0 < M)
    (Y : Ω → ℝ) (hY : Measurable Y) (hU : P.map Y = volume.restrict (Set.Icc (0 : ℝ) 1))
    (i : Fin M) : P (Y ⁻¹' (unifArm hM ⁻¹' {i})) = ENNReal.ofReal (1 / M) := by
  have hs : MeasurableSet (unifArm hM ⁻¹' {i}) :=
    unifArm_meas hM (measurableSet_singleton i)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [← Measure.map_apply hY hs, hU, Measure.restrict_apply hs, unifArm_set M hM i]
  split_ifs
  · rw [Real.volume_Ico]; congr 1; field_simp; ring
  · rw [Real.volume_Icc]; congr 1; field_simp; ring

lemma cond_iff (p : GoTParams) {N M : ℕ} (hM : 0 < M) (x : RandIdx N M → ℝ) (n : Fin N)
    (i : Fin M) (t : ℕ) (he : isExp (phaseOf p t).2 = true) :
    GoTV3.cond p hM x n i t ↔ ∀ m, (m = n → prof hM x t m = i) ∧ (m ≠ n → prof hM x t m ≠ i) := by
  unfold GoTV3.cond
  rw [noColl_eq_one_iff]
  constructor
  · rintro ⟨-, hn, hc⟩ m
    refine ⟨fun h => h ▸ hn, fun hmn hm => ?_⟩
    have : ({m, n} : Finset (Fin N)) ⊆ univ.filter (fun m' => prof hM x t m' = i) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with rfl | rfl
      · exact hm
      · exact hn
    have := Finset.card_le_card this
    rw [Finset.card_pair hmn] at this
    omega
  · intro h
    refine ⟨he, (h n).1 rfl, ?_⟩
    refine le_trans (Finset.card_le_card (t := {n}) ?_) (by simp)
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_contra hyn
    exact (h y).2 (by simpa using hyn) hy

lemma cond_prob {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ) (hM : 0 < M) (p : GoTParams)
    (n : Fin N) (i : Fin M) (t : ℕ) (he : isExp (phaseOf p t).2 = true) :
    P.real {ω | GoTV3.cond p hM (xv r ξ ω) n i t} = (1 / M) * (1 - 1 / M) ^ (N - 1) := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set S : Set ℝ := unifArm hM ⁻¹' {i} with hS
  have hSm : MeasurableSet S := unifArm_meas hM (measurableSet_singleton i)
  set A : Fin N → Set Ω := fun m => (fun ω => ξ m t 0 ω) ⁻¹' (if m = n then S else Sᶜ) with hA
  have hset : {ω | GoTV3.cond p hM (xv r ξ ω) n i t} = ⋂ m, A m := by
    ext ω
    rw [Set.mem_ofPred_eq, cond_iff p hM _ n i t he, Set.mem_iInter]
    apply forall_congr'
    intro m
    have hpm : prof hM (xv r ξ ω) t m = unifArm hM (ξ m t 0 ω) := rfl
    rw [hpm]
    by_cases hmn : m = n
    · simp [A, hmn, S]
    · simp [A, hmn, S]
  have hind : iIndepFun (fun m : Fin N => fun ω => ξ m t 0 ω) P := by
    have := hξ.indep.precomp (g := fun m : Fin N => (Sum.inr (m, t, 0) : RandIdx N M))
      (by intro a b h; simpa using h)
    exact this
  have hmeas : P (⋂ m, A m) = ∏ m, P (A m) := by
    apply hind.meas_iInter
    intro m
    refine ⟨if m = n then S else Sᶜ, ?_, rfl⟩
    split_ifs
    · exact hSm
    · exact hSm.compl
  have hp1 : P ((fun ω => ξ n t 0 ω) ⁻¹' S) = ENNReal.ofReal (1 / M) :=
    unifArm_prob P M hM _ (hξ.meas n t 0) (hξ.uniform n t 0) i
  have hpA : ∀ m, P (A m) = if m = n then ENNReal.ofReal (1 / M)
      else 1 - ENNReal.ofReal (1 / M) := by
    intro m
    by_cases hmn : m = n
    · simp only [A, hmn, if_true]; exact hp1
    · simp only [A, hmn, if_false]
      rw [Set.preimage_compl, prob_compl_eq_one_sub ((hξ.meas m t 0) hSm),
        unifArm_prob P M hM _ (hξ.meas m t 0) (hξ.uniform m t 0) i]
  rw [hset, measureReal_def, hmeas, ENNReal.toReal_prod]
  simp_rw [hpA]
  rw [Fintype.prod_eq_mul_prod_compl n]
  simp only [if_true]
  rw [Finset.prod_congr rfl (fun m hm => by
    rw [if_neg (by simpa using hm)])]
  rw [Finset.prod_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have h1M : 1 / (M : ℝ) ≤ 1 := by
    rw [div_le_one hMr]; exact_mod_cast hM
  rw [ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_sub_of_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1M)
      ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp

theorem meas_of_dep {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (S : Set ι) {β : Type*} [MeasurableSpace β]
    (h : (ι → ℝ) → β) (hh : Measurable h)
    (hdep : ∀ x y : ι → ℝ, (∀ i ∈ S, x i = y i) → h x = h y) :
    Measurable[⨆ i ∈ S, MeasurableSpace.comap (X i) inferInstance]
      (fun ω => h (fun i => X i ω)) := by
  classical
  set V : Ω → (ι → ℝ) := fun ω i => if i ∈ S then X i ω else 0 with hVdef
  have hV : Measurable[⨆ i ∈ S, MeasurableSpace.comap (X i) inferInstance] V := by
    refine @measurable_pi_lambda Ω ι (fun _ => ℝ)
      (⨆ i ∈ S, MeasurableSpace.comap (X i) inferInstance) (fun _ => inferInstance) V
      (fun i => ?_)
    by_cases hi : i ∈ S
    · simp only [V, if_pos hi]
      exact Measurable.mono (comap_measurable (X i))
        (le_iSup₂ (f := fun i (_ : i ∈ S) => MeasurableSpace.comap (X i) inferInstance) i hi)
        le_rfl
    · simp only [V, if_neg hi]; exact measurable_const
  have heq : (fun ω => h (fun i => X i ω)) = h ∘ V := by
    funext ω
    simp only [Function.comp]
    apply hdep
    intro i hi
    simp [V, hi]
  rw [heq]
  exact hh.comp hV

/-- The reward/seed family of the model, as in `Seeds.indep`. -/
def Xf {N M : ℕ} {Ω : Type*} (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) : RandIdx N M → Ω → ℝ :=
  fun (x : RandIdx N M) (ω : Ω) =>
    match x with
    | Sum.inl (n, i, t) => r n i t ω
    | Sum.inr (n, t, j) => ξ n t j ω

lemma xv_eq {N M : ℕ} {Ω : Type*} (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (ω : Ω) : xv r ξ ω = fun i => Xf r ξ i ω := by
  funext i; rcases i with (⟨n, i, t⟩ | ⟨n, t, j⟩) <;> rfl

lemma Xf_meas {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {r : Fin N → Fin M → ℕ → Ω → ℝ} {μ σ2 b : Fin N → Fin M → ℝ}
    (hr : IIDRewards P r μ σ2 b) {ξ : Fin N → ℕ → Fin 4 → Ω → ℝ} (hξ : Seeds P r ξ) :
    ∀ i, Measurable (Xf r ξ i) := by
  rintro (⟨n, i, t⟩ | ⟨n, t, j⟩)
  · exact hr.meas n i t
  · exact hξ.meas n t j

/-- seed block of turn `t`. -/
def Bt {N M : ℕ} (t : ℕ) : Set (RandIdx N M) := {x | ∃ m j, x = Sum.inr (m, t, j)}

def BF {N M : ℕ} (F : Finset ℕ) : Set (RandIdx N M) :=
  {x | ∃ m t j, t ∈ F ∧ x = Sum.inr (m, t, j)}

lemma prof_dep {N M : ℕ} (hM : 0 < M) (t : ℕ) (x y : RandIdx N M → ℝ)
    (h : ∀ m, x (Sum.inr (m, t, 0)) = y (Sum.inr (m, t, 0))) : prof hM x t = prof hM y t := by
  funext m; simp only [prof, h m]

def Zf (p : GoTParams) {N M : ℕ} (hM : 0 < M) (n : Fin N) (i : Fin M) (t : ℕ)
    (x : RandIdx N M → ℝ) : ℝ :=
  if GoTV3.cond p hM x n i t then 1 else 0

lemma Zf_meas (p : GoTParams) {N M : ℕ} (hM : 0 < M) (n : Fin N) (i : Fin M) (t : ℕ) :
    Measurable (Zf p hM n i t) :=
  Measurable.ite (cond_meas p hM n i t) measurable_const measurable_const

lemma Zf_dep (p : GoTParams) {N M : ℕ} (hM : 0 < M) (n : Fin N) (i : Fin M) (t : ℕ)
    (x y : RandIdx N M → ℝ) (h : ∀ m, x (Sum.inr (m, t, 0)) = y (Sum.inr (m, t, 0))) :
    Zf p hM n i t x = Zf p hM n i t y := by
  unfold Zf GoTV3.cond
  rw [prof_dep hM t x y h]

/-- Hoeffding's inequality for the number of collision-free exploration visits. -/
theorem hoeff_count {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (hM : 0 < M) (p : GoTParams) (n : Fin N) (i : Fin M) (E : Finset ℕ)
    (hE : ∀ t ∈ E, isExp (phaseOf p t).2 = true) (u : ℝ) (hu : 0 ≤ u) :
    P.real {ω | u ≤ ∑ t ∈ E, ((1 / M) * (1 - 1 / M) ^ (N - 1) -
        Zf p hM n i t (xv r ξ ω))} ≤ Real.exp (-u ^ 2 / (2 * ((E.card : ℝ) / 4))) := by
  classical
  set q : ℝ := (1 / M) * (1 - 1 / M) ^ (N - 1) with hq
  have hXm := Xf_meas hr hξ
  set c0 : NNReal := (‖q - (q - 1)‖₊ / 2) ^ 2 with hc0
  have hc0v : (c0 : ℝ) = 1 / 4 := by
    simp only [hc0, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, sub_sub_cancel, norm_one]
    norm_num
  have hZm : ∀ t, Measurable (fun ω => Zf p hM n i t (xv r ξ ω)) := by
    intro t
    have : (fun ω => Zf p hM n i t (xv r ξ ω)) = fun ω => Zf p hM n i t (fun j => Xf r ξ j ω) := by
      funext ω; rw [xv_eq]
    rw [this]
    exact (Zf_meas p hM n i t).comp (measurable_pi_lambda _ fun j => hXm j)
  have hsub1 : ∀ t ∈ E, HasSubgaussianMGF (fun ω => q - Zf p hM n i t (xv r ξ ω)) c0 P := by
    intro t ht
    have hs : MeasurableSet {ω | GoTV3.cond p hM (xv r ξ ω) n i t} := by
      have : {ω | GoTV3.cond p hM (xv r ξ ω) n i t} =
          (fun ω => fun j => Xf r ξ j ω) ⁻¹' {x | GoTV3.cond p hM x n i t} := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_preimage, xv_eq]
      rw [this]
      exact (measurable_pi_lambda _ fun j => hXm j) (cond_meas p hM n i t)
    have hZ : (fun ω => Zf p hM n i t (xv r ξ ω)) =
        Set.indicator {ω | GoTV3.cond p hM (xv r ξ ω) n i t} 1 := by
      funext ω; simp only [Zf, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    have hZi : Integrable (fun ω => Zf p hM n i t (xv r ξ ω)) P := by
      rw [hZ]; exact (integrable_const (1:ℝ)).indicator hs
    have hZint : ∫ ω, Zf p hM n i t (xv r ξ ω) ∂P = q := by
      rw [hZ, integral_indicator_one hs, cond_prob P r ξ hξ hM p n i t (hE t ht)]
    have hint0 : ∫ ω, (q - Zf p hM n i t (xv r ξ ω)) ∂P = 0 := by
      rw [integral_sub (integrable_const q) hZi, hZint, integral_const]; simp
    have hW : ∀ ω, (q - Zf p hM n i t (xv r ξ ω)) ∈ Set.Icc (q - 1) q := by
      intro ω
      simp only [Set.mem_Icc, Zf]
      split_ifs <;> constructor <;> linarith
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (measurable_const.sub (hZm t)).aemeasurable (Filter.Eventually.of_forall hW) hint0
  -- independence of one turn from a set of other turns
  have hindep : ∀ a (F : Finset ℕ), a ∉ F →
      IndepFun (fun ω => q - Zf p hM n i a (xv r ξ ω))
        (fun ω => ∑ t ∈ F, (q - Zf p hM n i t (xv r ξ ω))) P := by
    intro a F haF
    have hdisj : Disjoint (Bt a : Set (RandIdx N M)) (BF F) := by
      rw [Set.disjoint_left]
      rintro x ⟨m, j, rfl⟩ ⟨m', t', j', ht', h⟩
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact haF (h.2.1 ▸ ht')
    have hI := indep_iSup_of_disjoint (fun j => (hXm j).comap_le)
      ((iIndepFun_iff_iIndep _ _ _).1 hξ.indep) hdisj
    have m1 : Measurable[⨆ j ∈ (Bt a : Set (RandIdx N M)),
        MeasurableSpace.comap (Xf r ξ j) inferInstance]
        (fun ω => q - Zf p hM n i a (xv r ξ ω)) := by
      have := meas_of_dep (Xf r ξ) hXm (Bt a) (fun x => q - Zf p hM n i a x)
        (measurable_const.sub (Zf_meas p hM n i a))
        (fun x y hxy => by
          rw [Zf_dep p hM n i a x y (fun m => hxy _ ⟨m, 0, rfl⟩)])
      simpa only [xv_eq] using this
    have m2 : Measurable[⨆ j ∈ (BF F : Set (RandIdx N M)),
        MeasurableSpace.comap (Xf r ξ j) inferInstance]
        (fun ω => ∑ t ∈ F, (q - Zf p hM n i t (xv r ξ ω))) := by
      have := meas_of_dep (Xf r ξ) hXm (BF F) (fun x => ∑ t ∈ F, (q - Zf p hM n i t x))
        (Finset.measurable_sum _ fun t _ => measurable_const.sub (Zf_meas p hM n i t))
        (fun x y hxy => by
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [Zf_dep p hM n i t x y (fun m => hxy _ ⟨m, t, 0, ht, rfl⟩)])
      simpa only [xv_eq] using this
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hI m2.comap_le) m1.comap_le
  have hsum : ∀ F : Finset ℕ, F ⊆ E →
      HasSubgaussianMGF (fun ω => ∑ t ∈ F, (q - Zf p hM n i t (xv r ξ ω)))
        (∑ _t ∈ F, c0) P := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; simpa using (HasSubgaussianMGF.fun_zero (μ := P))
    | insert a F haF ih =>
      intro hF
      have h1 := hsub1 a (hF (Finset.mem_insert_self _ _))
      have h2 := ih (fun x hx => hF (Finset.mem_insert_of_mem hx))
      have := h1.add_of_indepFun h2 (hindep a F haF)
      simp only [Finset.sum_insert haF]
      exact this
  have := (hsum E le_rfl).measure_ge_le hu
  refine le_trans this (le_of_eq ?_)
  congr 2
  simp only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, hc0v]
  ring

/-- σ-algebra of all seeds. -/
def mSeed {N M : ℕ} {Ω : Type*} (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨆ j ∈ Set.range (fun q : Fin N × ℕ × Fin 4 => (Sum.inr q : RandIdx N M)),
    MeasurableSpace.comap (Xf r ξ j) inferInstance

/-- σ-algebra of all rewards. -/
def mRew {N M : ℕ} {Ω : Type*} (r : Fin N → Fin M → ℕ → Ω → ℝ)
    (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨆ j ∈ Set.range (fun q : Fin N × Fin M × ℕ => (Sum.inl q : RandIdx N M)),
    MeasurableSpace.comap (Xf r ξ j) inferInstance

lemma sigma2_pos {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {r : Fin N → Fin M → ℕ → Ω → ℝ} {μ σ2 b : Fin N → Fin M → ℝ}
    (hr : IIDRewards P r μ σ2 b) (n : Fin N) (i : Fin M) : 0 < σ2 n i := by
  rcases lt_or_eq_of_le (show 0 ≤ σ2 n i from hr.var n i ▸ variance_nonneg _ _) with h | h
  · exact h
  exfalso
  have hae := ae_eq_integral_of_variance_eq_zero (hr.memLp n i) ((hr.var n i).trans h.symm)
  have h1 : P {ω | r n i 0 ω ≠ ∫ ω', r n i 0 ω' ∂P} = 0 := by
    rw [ae_iff] at hae; exact hae
  have h2 := hr.continuous n i (∫ ω', r n i 0 ω' ∂P)
  have : (Set.univ : Set Ω) ⊆ {ω | r n i 0 ω ≠ ∫ ω', r n i 0 ω' ∂P} ∪
      r n i 0 ⁻¹' {∫ ω', r n i 0 ω' ∂P} := by
    intro ω _
    by_cases hω : r n i 0 ω = ∫ ω', r n i 0 ω' ∂P
    · right; exact hω
    · left; exact hω
  have := measure_mono_null this (measure_union_null h1 h2)
  simp at this

/-- The centred rewards `r n i t - μ n i` satisfy the hypotheses of Bernstein's inequality. -/
lemma reward_moments {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {r : Fin N → Fin M → ℕ → Ω → ℝ} {μ σ2 b : Fin N → Fin M → ℝ}
    (hr : IIDRewards P r μ σ2 b) (n : Fin N) (i : Fin M) (t : ℕ) :
    Integrable (fun ω => r n i t ω - μ n i) P ∧ ∫ ω, (r n i t ω - μ n i) ∂P = 0 ∧
    ∀ k : ℕ, 2 ≤ k → Integrable (fun ω => |r n i t ω - μ n i| ^ k) P ∧
      ∫ ω, |r n i t ω - μ n i| ^ k ∂P ≤ (k.factorial : ℝ) / 2 * σ2 n i * b n i ^ (k - 2) := by
  have hid := hr.ident n i t
  have hint0 : Integrable (r n i 0) P := (hr.memLp n i).integrable one_le_two
  have hint : Integrable (r n i t) P := hid.integrable_iff.2 hint0
  refine ⟨hint.sub (integrable_const _), ?_, ?_⟩
  · rw [integral_sub hint (integrable_const _), hid.integral_eq, ← hr.mean n i]; simp
  · intro k hk
    have hf : Measurable (fun x : ℝ => |x - μ n i| ^ k) :=
      ((measurable_id.sub measurable_const).abs).pow_const k
    have hid2 := hid.comp hf
    have e1 : Integrable (fun ω => |r n i t ω - μ n i| ^ k) P ↔
        Integrable (fun ω => |r n i 0 ω - μ n i| ^ k) P := hid2.integrable_iff
    have e2 : ∫ ω, |r n i t ω - μ n i| ^ k ∂P = ∫ ω, |r n i 0 ω - μ n i| ^ k ∂P :=
      hid2.integral_eq
    rw [e1, e2]
    rcases lt_or_eq_of_le hk with hk3 | hk2
    · exact hr.bernstein n i k hk3
    · subst hk2
      have hsq : (fun ω => |r n i 0 ω - μ n i| ^ 2) = fun ω => (r n i 0 ω - μ n i) ^ 2 := by
        funext ω; exact sq_abs _
      rw [hsq]
      refine ⟨((hr.memLp n i).sub (memLp_const (μ n i))).integrable_sq, ?_⟩
      have hv := variance_eq_integral (hr.meas n i 0).aemeasurable (μ := P)
      rw [hr.var n i, ← hr.mean n i] at hv
      rw [← hv]; simp

/-- Bernstein's inequality for the estimate of one arm, given enough visits; the visit set is
determined by the seeds, which are independent of the rewards. -/
theorem bern_cond {N M : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (hM : 0 < M) (p : GoTParams) (n : Fin N) (i : Fin M) (T : ℕ) (thr ε : ℝ) (hε : 0 < ε) :
    P.real {ω | thr ≤ cntR p hM (xv r ξ ω) n i T ∧
        cntR p hM (xv r ξ ω) n i T * ε ≤
          |smR p hM (xv r ξ ω) n i T - cntR p hM (xv r ξ ω) n i T * μ n i|} ≤
      2 * Real.exp (-thr * ε ^ 2 / (2 * (σ2 n i + b n i * ε))) := by
  have hXm := Xf_meas hr hξ
  set Sx : (RandIdx N M → ℝ) → Finset ℕ :=
    fun x => (range T).filter (fun t => GoTV3.cond p hM x n i t) with hSx
  have hcnt : ∀ x, cntR p hM x n i T = ((Sx x).card : ℝ) := by
    intro x; simp only [cntR, hSx]; rw [Finset.sum_boole]
  have hsm : ∀ x, smR p hM x n i T - cntR p hM x n i T * μ n i =
      ∑ t ∈ Sx x, (x (Sum.inl (n, i, t)) - μ n i) := by
    intro x
    rw [hcnt, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [smR, hSx]
    rw [Finset.sum_filter]
  set c := ε ^ 2 / (2 * (σ2 n i + b n i * ε)) with hc
  have hc0 : 0 ≤ c := by
    have := sigma2_pos hr n i; have := hr.b_pos n i; positivity
  set F := ((range T).powerset).filter (fun S0 => thr ≤ (S0.card : ℝ)) with hF
  set A : Finset ℕ → Set Ω := fun S0 => {ω | Sx (xv r ξ ω) = S0} with hA
  set B : Finset ℕ → Set Ω := fun S0 =>
    {ω | (S0.card : ℝ) * ε ≤ |∑ t ∈ S0, (r n i t ω - μ n i)|} with hB
  have hsub : {ω | thr ≤ cntR p hM (xv r ξ ω) n i T ∧
        cntR p hM (xv r ξ ω) n i T * ε ≤
          |smR p hM (xv r ξ ω) n i T - cntR p hM (xv r ξ ω) n i T * μ n i|} ⊆
      ⋃ S0 ∈ F, (A S0 ∩ B S0) := by
    intro ω ⟨h1, h2⟩
    rw [hsm] at h2
    rw [hcnt] at h1 h2
    simp only [Set.mem_iUnion, Set.mem_inter_iff, hA, hB, Set.mem_ofPred_eq, exists_prop, hF,
      Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Sx (xv r ξ ω), ⟨Finset.filter_subset _ _, h1⟩, rfl, ?_⟩
    exact h2
  -- σ-algebras
  have hdisj : Disjoint (Set.range (fun q : Fin N × ℕ × Fin 4 => (Sum.inr q : RandIdx N M)))
      (Set.range (fun q : Fin N × Fin M × ℕ => (Sum.inl q : RandIdx N M))) := by
    rw [Set.disjoint_left]
    rintro x ⟨q, rfl⟩ ⟨q', h⟩
    exact Sum.inl_ne_inr h
  have hI : Indep (mSeed r ξ) (mRew r ξ) P := indep_iSup_of_disjoint (fun j => (hXm j).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 hξ.indep) hdisj
  have hcond_dep : ∀ x y : RandIdx N M → ℝ,
      (∀ j ∈ Set.range (fun q : Fin N × ℕ × Fin 4 => (Sum.inr q : RandIdx N M)), x j = y j) →
      Sx x = Sx y := by
    intro x y hxy
    have : ∀ t, prof hM x t = prof hM y t := fun t =>
      prof_dep hM t x y (fun m => hxy _ ⟨(m, t, 0), rfl⟩)
    simp only [hSx]
    congr 1
    funext t
    simp only [GoTV3.cond, this]
  have hAm : ∀ S0, MeasurableSet[mSeed r ξ] (A S0) := by
    intro S0
    have hmeasP : Measurable (fun x : RandIdx N M → ℝ => Sx x = S0) := by
      rw [← measurableSet_setOfPred]
      have : {x : RandIdx N M → ℝ | Sx x = S0} =
          ⋂ t : ℕ, {x | (t < T ∧ GoTV3.cond p hM x n i t) ↔ t ∈ S0} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, hSx, Finset.ext_iff, Finset.mem_filter,
          Finset.mem_range]
      rw [this]
      refine MeasurableSet.iInter fun t => ?_
      refine MeasurableSet.iff ?_ (MeasurableSet.const _)
      exact (MeasurableSet.const _).inter (cond_meas p hM n i t)
    have := meas_of_dep (Xf r ξ) hXm _ (fun x => Sx x = S0) hmeasP
      (fun x y hxy => by rw [hcond_dep x y hxy])
    have h2 : MeasurableSet[mSeed r ξ]
        ((fun ω => Sx (fun j => Xf r ξ j ω) = S0) ⁻¹' {True}) :=
      this (MeasurableSpace.measurableSet_top)
    convert h2 using 1
    ext ω
    simp [hA, xv_eq]
  have hBm : ∀ S0, MeasurableSet[mRew r ξ] (B S0) := by
    intro S0
    have hg := meas_of_dep (Xf r ξ) hXm
      (Set.range (fun q : Fin N × Fin M × ℕ => (Sum.inl q : RandIdx N M)))
      (fun x => |∑ t ∈ S0, (x (Sum.inl (n, i, t)) - μ n i)|)
      (Measurable.abs (Finset.measurable_sum _ fun t _ =>
        (measurable_pi_apply _).sub measurable_const))
      (fun x y hxy => by
        congr 1
        exact Finset.sum_congr rfl fun t _ => by rw [hxy _ ⟨(n, i, t), rfl⟩])
    have := hg (measurableSet_Ici : MeasurableSet (Set.Ici ((S0.card : ℝ) * ε)))
    exact this
  have hprod : ∀ S0, P.real (A S0 ∩ B S0) = P.real (A S0) * P.real (B S0) := by
    intro S0
    simp only [measureReal_def]
    rw [(Indep_iff _ _ _).1 hI _ _ (hAm S0) (hBm S0), ENNReal.toReal_mul]
  -- Bernstein for fixed visit set
  have hind : iIndepFun (fun t : ℕ => fun ω => r n i t ω - μ n i) P := by
    have h1 := hξ.indep.precomp (g := fun t : ℕ => (Sum.inl (n, i, t) : RandIdx N M))
      (by intro a b h; simpa using h)
    exact h1.comp (fun _ x => x - μ n i) (fun _ => measurable_id.sub measurable_const)
  have hBb : ∀ S0, P.real (B S0) ≤ 2 * Real.exp (-(S0.card : ℝ) * c) := by
    intro S0
    have := bern_two (fun t : ℕ => fun ω => r n i t ω - μ n i) hind
      (fun t => (hr.meas n i t).sub measurable_const) S0 (σ2 n i) (b n i) (sigma2_pos hr n i)
      (hr.b_pos n i) (fun t => (reward_moments hr n i t).1)
      (fun t => (reward_moments hr n i t).2.1) (fun t => (reward_moments hr n i t).2.2) ε hε
    simp only [hB]
    refine le_trans this (le_of_eq ?_)
    rw [hc]; ring_nf
  have hdisjA : (↑F : Set (Finset ℕ)).PairwiseDisjoint A := by
    intro S0 _ S1 _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h0 h1
    simp only [hA, Set.mem_ofPred_eq] at h0 h1
    exact hne (h0.symm.trans h1)
  have hsumA : ∑ S0 ∈ F, P.real (A S0) ≤ 1 := by
    rw [← measureReal_biUnion_finset hdisjA (fun S0 _ =>
      (iSup₂_le fun j _ => (hXm j).comap_le : mSeed r ξ ≤ _) _ (hAm S0))
      (fun _ _ => measure_ne_top _ _)]
    exact measureReal_le_one
  calc P.real {ω | thr ≤ cntR p hM (xv r ξ ω) n i T ∧
        cntR p hM (xv r ξ ω) n i T * ε ≤
          |smR p hM (xv r ξ ω) n i T - cntR p hM (xv r ξ ω) n i T * μ n i|}
      ≤ P.real (⋃ S0 ∈ F, (A S0 ∩ B S0)) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ S0 ∈ F, P.real (A S0 ∩ B S0) := measureReal_biUnion_finset_le _ _
    _ = ∑ S0 ∈ F, P.real (A S0) * P.real (B S0) := Finset.sum_congr rfl fun S0 _ => hprod S0
    _ ≤ ∑ S0 ∈ F, P.real (A S0) * (2 * Real.exp (-thr * c)) := by
        apply Finset.sum_le_sum
        intro S0 hS0
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        refine le_trans (hBb S0) ?_
        have hth : thr ≤ (S0.card : ℝ) := (Finset.mem_filter.1 hS0).2
        gcongr
    _ = (∑ S0 ∈ F, P.real (A S0)) * (2 * Real.exp (-thr * c)) := by rw [Finset.sum_mul]
    _ ≤ 1 * (2 * Real.exp (-thr * c)) := by
        apply mul_le_mul_of_nonneg_right hsumA; positivity
    _ = 2 * Real.exp (-thr * ε ^ 2 / (2 * (σ2 n i + b n i * ε))) := by rw [hc]; ring_nf

lemma pow_ge_exp_neg (M N : ℕ) (hM : 0 < M) (hNM : N ≤ M) :
    Real.exp (-1) ≤ (1 - 1 / (M : ℝ)) ^ (N - 1) := by
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have : N - 1 = 0 := by omega
    rw [this, pow_zero, Real.exp_le_one_iff]; norm_num
  · set m := M - 1 with hm
    have hm1 : 1 ≤ m := by omega
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hMm : (M : ℝ) = m + 1 := by rw [hm]; push_cast [Nat.cast_sub (by omega : 1 ≤ M)]; ring
    have hbase : 1 - 1 / (M : ℝ) = m / (m + 1) := by rw [hMm]; field_simp; ring
    have hb0 : 0 ≤ 1 - 1 / (M : ℝ) := by rw [hbase]; positivity
    have hb1 : 1 - 1 / (M : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (M : ℝ) := by positivity
      linarith
    calc Real.exp (-1) ≤ (1 - 1 / (M : ℝ)) ^ m := by
          rw [hbase]
          have h1 : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
            calc (1 + 1 / (m : ℝ)) ^ m ≤ (Real.exp (1 / m)) ^ m := by
                  apply pow_le_pow_left₀ (by positivity)
                  have := Real.add_one_le_exp (1 / (m : ℝ)); linarith
              _ = Real.exp 1 := by
                  rw [← Real.exp_nat_mul]; congr 1; field_simp
          have h2 : ((m : ℝ) / (m + 1)) ^ m * (1 + 1 / (m : ℝ)) ^ m = 1 := by
            rw [← mul_pow]
            have : (m : ℝ) / (m + 1) * (1 + 1 / m) = 1 := by field_simp
            rw [this, one_pow]
          have hpos : 0 < (1 + 1 / (m : ℝ)) ^ m := by positivity
          rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
          calc (1 : ℝ) = ((m : ℝ) / (m + 1)) ^ m * (1 + 1 / (m : ℝ)) ^ m := h2.symm
            _ ≤ ((m : ℝ) / (m + 1)) ^ m * Real.exp 1 :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (1 - 1 / (M : ℝ)) ^ (N - 1) := pow_le_pow_of_le_one hb0 hb1 (by omega)

theorem pair_bound {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (k : ℕ) (hk : 1 ≤ k)
    (hM : 0 < M) (hΔ : 0 < Δmin μ) (n : Fin N) (i : Fin M) :
    P.real {ω | Δmin μ / 4 < |est p hNM r ξ k n i ω - μ n i|} ≤
      2 * Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i)) *
          ((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ * k)) +
        Real.exp (-((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ * k) / (36 * (M : ℝ) ^ 2)) := by
  classical
  set σmax := ⨆ n, ⨆ i, Real.sqrt (σ2 n i) with hσmax
  set bmax := ⨆ n, ⨆ i, b n i with hbmax
  set Δ := Δmin μ with hΔdef
  set a := (p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ * k with ha
  set T := p.epochStart k + expLen p.c1 p.δ k with hT
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc1r : (0 : ℝ) < p.c1 := by exact_mod_cast hc1
  have hapos : 0 < a := by
    have : 0 < ((k : ℝ) / 2) ^ p.δ := Real.rpow_pos_of_pos (by linarith) _
    rw [ha]; positivity
  set thr := a / (10 * M) with hthr
  have hthr0 : 0 < thr := by positivity
  set ε := Δ / 4 with hε
  have hε0 : 0 < ε := by positivity
  -- the three bad events
  set G : Set Ω := ⋃ n', ⋃ i', ⋃ t, {ω | r n' i' t ω = 0} with hG
  set E1 : Set Ω := {ω | cntR p hM (xv r ξ ω) n i T < thr} with hE1
  set E2 : Set Ω := {ω | thr ≤ cntR p hM (xv r ξ ω) n i T ∧
        cntR p hM (xv r ξ ω) n i T * ε ≤
          |smR p hM (xv r ξ ω) n i T - cntR p hM (xv r ξ ω) n i T * μ n i|} with hE2
  have hsub : {ω | Δ / 4 < |est p hNM r ξ k n i ω - μ n i|} ⊆ G ∪ E1 ∪ E2 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hg : ω ∈ G
    · left; left; exact hg
    have h0 : ∀ n' i' t, r n' i' t ω ≠ 0 := by
      intro n' i' t h; apply hg
      simp only [hG, Set.mem_iUnion, Set.mem_ofPred_eq]; exact ⟨n', i', t, h⟩
    have htr := traj_eq p hNM hM r ξ ω h0 T n i
    have hest : est p hNM r ξ k n i ω =
        smR p hM (xv r ξ ω) n i T / cntR p hM (xv r ξ ω) n i T := by
      simp only [est, PlayerState.estimate]; rw [htr.1, htr.2]
    by_cases h1 : cntR p hM (xv r ξ ω) n i T < thr
    · left; right; exact h1
    · right
      push Not at h1
      refine ⟨h1, ?_⟩
      have hc : 0 < cntR p hM (xv r ξ ω) n i T := lt_of_lt_of_le hthr0 h1
      rw [hest] at hω
      have : |smR p hM (xv r ξ ω) n i T / cntR p hM (xv r ξ ω) n i T - μ n i| *
          cntR p hM (xv r ξ ω) n i T =
          |smR p hM (xv r ξ ω) n i T - cntR p hM (xv r ξ ω) n i T * μ n i| := by
        rw [← abs_of_pos hc, ← abs_mul, abs_of_pos hc]
        congr 1; field_simp
      rw [← this, mul_comm (cntR _ _ _ _ _ _) ε]
      exact mul_le_mul_of_nonneg_right hω.le hc.le
  have hG0 : P.real G = 0 := by
    rw [measureReal_def]
    have : P G = 0 := by
      refine measure_iUnion_null fun n' => measure_iUnion_null fun i' =>
        measure_iUnion_null fun t => ?_
      have := (hr.ident n' i' t).measure_mem_eq (measurableSet_singleton (0 : ℝ))
      rw [show {ω | r n' i' t ω = 0} = r n' i' t ⁻¹' {0} from rfl, this]
      exact hr.continuous n' i' 0
    rw [this]; rfl
  -- Hoeffding part
  have hE1 : P.real E1 ≤ Real.exp (-a / (36 * (M : ℝ) ^ 2)) := by
    set Ex := (Finset.range T).filter (fun t => isExp (phaseOf p t).2 = true) with hEx
    have hExp : ∀ t ∈ Ex, isExp (phaseOf p t).2 = true := fun t ht => (Finset.mem_filter.1 ht).2
    set L := (Ex.card : ℝ) with hL
    have hLa : a / 2 ≤ L := by
      have h1 := count_explore p hc1 k hk
      have h2 := sum_expLen_ge p hc1 hδ k hk
      have h3 : (∑ i ∈ Finset.Icc 1 k, (expLen p.c1 p.δ i : ℝ)) ≤ L := by
        rw [hL]; exact_mod_cast h1
      rw [ha]; linarith
    have hL0 : 0 < L := by linarith
    set q : ℝ := (1 / M) * (1 - 1 / M) ^ (N - 1) with hq
    have hqM : Real.exp (-1) / M ≤ q := by
      rw [hq, div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_ge_exp_neg M N hM hNM) (by positivity)
    have he : (11 : ℝ) / 30 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9; nlinarith
    set u := q * L - thr with hu
    have hu6 : L / (6 * M) ≤ u := by
      rw [hu, hthr]
      have h1 : (11 / 30 : ℝ) / M ≤ q := le_trans (div_le_div_of_nonneg_right he hMr.le) hqM
      have h2 : a / (10 * M) ≤ L / (5 * M) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have h3 : (11 / 30 : ℝ) / M * L ≤ q * L := mul_le_mul_of_nonneg_right h1 hL0.le
      have h4 : L / (6 * M) = (11 / 30 : ℝ) / M * L - L / (5 * M) := by field_simp; ring
      linarith
    have hu0 : 0 ≤ u := le_trans (by positivity) hu6
    have hsubE : E1 ⊆ {ω | u ≤ ∑ t ∈ Ex, (q - Zf p hM n i t (xv r ξ ω))} := by
      intro ω hω
      simp only [hE1, Set.mem_ofPred_eq] at hω ⊢
      have hcnt : cntR p hM (xv r ξ ω) n i T = ∑ t ∈ Ex, Zf p hM n i t (xv r ξ ω) := by
        simp only [cntR, hEx, Zf]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases ht : isExp (phaseOf p t).2 = true
        · rw [if_pos ht]
        · rw [if_neg ht, if_neg (fun h => ht h.1)]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hcnt]
      rw [hu, hL, mul_comm]; linarith
    have hh := hoeff_count P r μ σ2 b hr ξ hξ hM p n i Ex hExp u hu0
    refine le_trans (measureReal_mono hsubE) (le_trans hh ?_)
    apply Real.exp_le_exp.2
    rw [← hL]
    have hu2 : (L / (6 * M)) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu6 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (L / (6 * M)) ^ 2 * (36 * (M : ℝ) ^ 2) = L ^ 2 := by field_simp; ring
    nlinarith
  -- Bernstein part
  have hE2 : P.real E2 ≤ 2 * Real.exp (-(wConst μ σmax bmax) * a) := by
    have hb := bern_cond P r μ σ2 b hr ξ hξ hM p n i T thr ε hε0
    refine le_trans hb ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    have hs2 : σ2 n i ≤ σmax ^ 2 := by
      have h1 : Real.sqrt (σ2 n i) ≤ σmax := by
        have e1 : Real.sqrt (σ2 n i) ≤ ⨆ i', Real.sqrt (σ2 n i') :=
          le_ciSup (f := fun i' => Real.sqrt (σ2 n i')) (Finite.bddAbove_range _) i
        have e2 : (⨆ i', Real.sqrt (σ2 n i')) ≤ σmax :=
          le_ciSup (f := fun n => ⨆ i', Real.sqrt (σ2 n i')) (Finite.bddAbove_range _) n
        linarith
      have h0 : 0 ≤ σ2 n i := (sigma2_pos hr n i).le
      calc σ2 n i = Real.sqrt (σ2 n i) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ σmax ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    have hbb : b n i ≤ bmax := by
      have e1 : b n i ≤ ⨆ i', b n i' :=
        le_ciSup (f := fun i' => b n i') (Finite.bddAbove_range _) i
      have e2 : (⨆ i', b n i') ≤ bmax :=
        le_ciSup (f := fun n => ⨆ i', b n i') (Finite.bddAbove_range _) n
      linarith
    have hσ0 := sigma2_pos hr n i
    have hb0 := hr.b_pos n i
    have hden : 0 < 4 * σ2 n i + b n i * Δ := by positivity
    have hden2 : 4 * σ2 n i + b n i * Δ ≤ 4 * σmax ^ 2 + bmax * Δ := by nlinarith
    -- thr * ε² / (2(σ2 + bε)) = a Δ² / (80 M (4σ2 + bΔ))
    have key : thr * ε ^ 2 / (2 * (σ2 n i + b n i * ε)) =
        a * Δ ^ 2 / (80 * M * (4 * σ2 n i + b n i * Δ)) := by
      rw [hthr, hε]; field_simp; ring
    have key2 : wConst μ σmax bmax * a = a * Δ ^ 2 / (80 * M * (4 * σmax ^ 2 + bmax * Δ)) := by
      unfold wConst; rw [← hΔdef]; field_simp
    have : a * Δ ^ 2 / (80 * M * (4 * σmax ^ 2 + bmax * Δ)) ≤
        a * Δ ^ 2 / (80 * M * (4 * σ2 n i + b n i * Δ)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hden2 (by positivity)
    have e3 : -thr * ε ^ 2 / (2 * (σ2 n i + b n i * ε)) =
        -(thr * ε ^ 2 / (2 * (σ2 n i + b n i * ε))) := by ring
    rw [e3, key, neg_mul, key2]
    linarith
  calc P.real {ω | Δ / 4 < |est p hNM r ξ k n i ω - μ n i|}
      ≤ P.real (G ∪ E1 ∪ E2) := measureReal_mono hsub
    _ ≤ P.real (G ∪ E1) + P.real E2 := measureReal_union_le _ _
    _ ≤ P.real G + P.real E1 + P.real E2 := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ _ := by rw [hG0]; linarith

end
end GoT20



open Finset MeasureTheory ProbabilityTheory

open GoTBandit.Main GoTV3 GoT20

theorem solution {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (k : ℕ) (hk : 1 ≤ k) :
    P.real {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ k n i ω - μ n i|} ≤
      2 * N * M * Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i)) *
          p.c1 * ((k : ℝ) / 2) ^ p.δ * k) +
        N * M * Real.exp (-((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2)) * k) := by
  set w := wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i) with hw
  have hRHS : 0 ≤ 2 * N * M * Real.exp (-w * p.c1 * ((k : ℝ) / 2) ^ p.δ * k) +
      N * M * Real.exp (-((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2)) * k) := by
    positivity
  have hΔ0 : 0 ≤ Δmin μ := by
    unfold Δmin
    apply Real.sInf_nonneg
    rintro d ⟨n, a₁, a₂, -, rfl⟩
    exact abs_nonneg _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : {ω | Δmin μ / 4 < ⨆ n : Fin 0, ⨆ i, |est p hNM r ξ k n i ω - μ n i|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [Real.iSup_of_isEmpty]; linarith
    rw [this, measureReal_empty]; exact hRHS
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rcases lt_or_eq_of_le hΔ0 with hΔ | hΔ
  · haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have hsub : {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ k n i ω - μ n i|} ⊆
        ⋃ n, ⋃ i, {ω | Δmin μ / 4 < |est p hNM r ξ k n i ω - μ n i|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hω ⊢
      obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hω
      obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hn
      exact ⟨n, i, hi⟩
    set a := (p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ * k with ha
    have hpb := fun n i => pair_bound hNM P r μ σ2 b hr ξ hξ p hc1 hδ k hk hM hΔ n i
    calc P.real {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ k n i ω - μ n i|}
        ≤ P.real (⋃ n, ⋃ i, {ω | Δmin μ / 4 < |est p hNM r ξ k n i ω - μ n i|}) :=
          measureReal_mono hsub
      _ ≤ ∑ n, P.real (⋃ i, {ω | Δmin μ / 4 < |est p hNM r ξ k n i ω - μ n i|}) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ n : Fin N, ∑ i : Fin M,
            P.real {ω | Δmin μ / 4 < |est p hNM r ξ k n i ω - μ n i|} :=
          Finset.sum_le_sum fun n _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ n : Fin N, ∑ i : Fin M,
            (2 * Real.exp (-w * a) + Real.exp (-a / (36 * (M : ℝ) ^ 2))) :=
          Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun i _ => hpb n i
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have e1 : -w * a = -w * p.c1 * ((k : ℝ) / 2) ^ p.δ * k := by rw [ha]; ring
          have e2 : -a / (36 * (M : ℝ) ^ 2) =
              -((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2)) * k := by
            rw [ha]; ring
          rw [e1, e2]; ring
  · -- Δmin = 0: the bound is at least 2NM ≥ 1
    have hw0 : w = 0 := by rw [hw]; unfold wConst; rw [← hΔ]; simp
    have h1 : P.real {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ k n i ω - μ n i|} ≤ 1 :=
      measureReal_le_one
    have h2 : (1 : ℝ) ≤ 2 * N * M * Real.exp (-w * p.c1 * ((k : ℝ) / 2) ^ p.δ * k) := by
      rw [hw0]; simp; nlinarith
    have h3 : 0 ≤ (N : ℝ) * M *
        Real.exp (-((p.c1 : ℝ) * ((k : ℝ) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2)) * k) := by
      positivity
    linarith

