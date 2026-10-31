-- Prove2me | solution 1 for MeanRiskBellman.Recursion.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:55:53.12501+00:00
-- url     : https://prove2.me/submissions/3bff08f5-a9b6-433b-9ca3-e0888c1d04e6

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace MRBThm51Aux

open MeanRiskBellman.Recursion

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]

lemma ae_eq_to_eq (M : Market Ω) (hM : M.Assumptions) {f g : Ω → ℝ}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (h : f =ᵐ[M.P] g) : f = g := by
  funext ω
  by_contra hne
  have hs : MeasurableSet {ω | ¬ f ω = g ω} :=
    (measurableSet_eq_fun hf.measurable hg.measurable).compl
  have hpos := hM.space.pos _ hs ⟨ω, hne⟩
  rw [Filter.EventuallyEq, ae_iff] at h
  exact (ne_of_gt hpos) h

lemma ae_le_to_le (M : Market Ω) (hM : M.Assumptions) {f g : Ω → ℝ}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (h : f ≤ᵐ[M.P] g) : f ≤ g := by
  intro ω
  by_contra hne
  have hs : MeasurableSet {ω | ¬ f ω ≤ g ω} := by
    simp only [not_le]
    exact measurableSet_lt hg.measurable hf.measurable
  have hpos := hM.space.pos _ hs ⟨ω, hne⟩
  rw [Filter.EventuallyLE, ae_iff] at h
  exact (ne_of_gt hpos) h

lemma memLp_of_sm (M : Market Ω) (hM : M.Assumptions) {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    MemLp f ⊤ M.P :=
  have := hM.space.isProb
  MemLp.of_bound hf.aestronglyMeasurable (∑ ω, ‖f ω‖)
    (ae_of_all _ fun ω => Finset.single_le_sum (f := fun ω => ‖f ω‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ ω))

lemma integrable_of_sm (M : Market Ω) (hM : M.Assumptions) {f : Ω → ℝ}
    (hf : StronglyMeasurable f) : Integrable f M.P := by
  have := hM.space.isProb
  exact (memLp_of_sm M hM hf).integrable le_top

lemma sm_of_le (M : Market Ω) {t : ℕ} {f : Ω → ℝ × ℝ} (hf : StronglyMeasurable[M.ℱ t] f) :
    StronglyMeasurable f := hf.mono (M.ℱ.le t)

lemma sm_fst {f : Ω → ℝ × ℝ} {m : MeasurableSpace Ω} (hf : StronglyMeasurable[m] f) :
    StronglyMeasurable[m] (fun ω => (f ω).1) := hf.fst

lemma sm_snd {f : Ω → ℝ × ℝ} {m : MeasurableSpace Ω} (hf : StronglyMeasurable[m] f) :
    StronglyMeasurable[m] (fun ω => (f ω).2) := hf.snd

lemma E_trans (M : Market Ω) (hM : M.Assumptions) {t : ℕ} {f r : Ω → ℝ}
    (hf : StronglyMeasurable f) (hr : StronglyMeasurable[M.ℱ t] r) :
    M.P[f + r | M.ℱ t] = M.P[f | M.ℱ t] + r := by
  have := hM.space.isProb
  have hri : Integrable r M.P := integrable_of_sm M hM (hr.mono (M.ℱ.le t))
  have hae := condExp_add (integrable_of_sm M hM hf) hri (M.ℱ t)
  rw [condExp_of_stronglyMeasurable (M.ℱ.le t) hr hri] at hae
  exact ae_eq_to_eq M hM (stronglyMeasurable_condExp.mono (M.ℱ.le t))
    ((stronglyMeasurable_condExp.mono (M.ℱ.le t)).add (hr.mono (M.ℱ.le t))) hae

lemma rho_trans (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {f r : Ω → ℝ}
    (hf : StronglyMeasurable f) (hr : StronglyMeasurable[M.ℱ t] r) :
    M.ρ t (f + r) = M.ρ t f - r := by
  have hR := hM.risk.risk t ht
  have hr' := hr.mono (M.ℱ.le t)
  have hae := hR.translation f r (memLp_of_sm M hM hf) (memLp_of_sm M hM hr') hr
  exact ae_eq_to_eq M hM ((hR.stronglyMeasurable _ (memLp_of_sm M hM (hf.add hr'))).mono (M.ℱ.le t))
    (((hR.stronglyMeasurable _ (memLp_of_sm M hM hf)).mono (M.ℱ.le t)).sub hr') hae

lemma Γ_sm (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {X : Ω → ℝ × ℝ}
    (hX : StronglyMeasurable X) : StronglyMeasurable[M.ℱ t] (Γ M t X) := by
  have hR := hM.risk.risk t ht
  exact (stronglyMeasurable_condExp.neg).prodMk
    (hR.stronglyMeasurable _ (memLp_of_sm M hM (sm_snd hX)))

lemma Γ_trans (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {X r : Ω → ℝ × ℝ}
    (hX : StronglyMeasurable X) (hr : StronglyMeasurable[M.ℱ t] r) :
    Γ M t (X + r) = Γ M t X - r := by
  have h1 := E_trans M hM (sm_fst hX) (sm_fst hr)
  have h2 := rho_trans M hM ht (sm_snd hX) (sm_snd hr)
  funext ω
  refine Prod.ext ?_ ?_
  · show -(M.P[(fun ω => (X ω).1) + (fun ω => (r ω).1) | M.ℱ t]) ω = _
    rw [h1]
    simp [Γ]
    ring
  · show M.ρ t ((fun ω => (X ω).2) + (fun ω => (r ω).2)) ω = _
    rw [h2]
    simp [Γ]

lemma Γ_mono (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {X Y : Ω → ℝ × ℝ}
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) (hXY : X ≤ Y) :
    Γ M t Y ≤ Γ M t X := by
  have := hM.space.isProb
  have hR := hM.risk.risk t ht
  have h1 : M.P[fun ω => (X ω).1 | M.ℱ t] ≤ M.P[fun ω => (Y ω).1 | M.ℱ t] :=
    ae_le_to_le M hM (stronglyMeasurable_condExp.mono (M.ℱ.le t))
      (stronglyMeasurable_condExp.mono (M.ℱ.le t))
      (condExp_mono (integrable_of_sm M hM (sm_fst hX)) (integrable_of_sm M hM (sm_fst hY))
        (ae_of_all _ fun ω => (Prod.le_def.1 (hXY ω)).1))
  have h2 : M.ρ t (fun ω => (Y ω).2) ≤ M.ρ t (fun ω => (X ω).2) :=
    ae_le_to_le M hM
      ((hR.stronglyMeasurable _ (memLp_of_sm M hM (sm_snd hY))).mono (M.ℱ.le t))
      ((hR.stronglyMeasurable _ (memLp_of_sm M hM (sm_snd hX))).mono (M.ℱ.le t))
      (hR.monotone _ _ (memLp_of_sm M hM (sm_snd hX)) (memLp_of_sm M hM (sm_snd hY))
        (ae_of_all _ fun ω => (Prod.le_def.1 (hXY ω)).2))
  intro ω
  exact Prod.le_def.2 ⟨neg_le_neg (h1 ω), h2 ω⟩

lemma Γ_lip (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {X Y : Ω → ℝ × ℝ}
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    dist (Γ M t X) (Γ M t Y) ≤ dist X Y := by
  have key : ∀ X Y : Ω → ℝ × ℝ, StronglyMeasurable X → StronglyMeasurable Y →
      ∀ ω, (Γ M t Y ω).1 - dist X Y ≤ (Γ M t X ω).1 ∧ (Γ M t Y ω).2 - dist X Y ≤ (Γ M t X ω).2 := by
    intro X Y hX hY ω
    set c := dist X Y
    have hle : X ≤ Y + (fun _ => (c, c)) := by
      intro ω'
      have hd := dist_le_pi_dist X Y ω'
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hd
      have h1 := (abs_sub_le_iff.1 (le_trans (le_max_left _ _) hd)).1
      have h2 := (abs_sub_le_iff.1 (le_trans (le_max_right _ _) hd)).1
      exact Prod.le_def.2 ⟨by simp; linarith, by simp; linarith⟩
    have hm := Γ_mono M hM ht hX (hY.add stronglyMeasurable_const) hle
    rw [Γ_trans M hM ht hY stronglyMeasurable_const] at hm
    have := Prod.le_def.1 (hm ω)
    simp at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [dist_pi_le_iff dist_nonneg]
  intro ω
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have a := key X Y hX hY ω
  have b := key Y X hY hX ω
  rw [dist_comm Y X] at b
  refine max_le (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)
    (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)

lemma Γ_rec (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t < M.T) {X : Ω → ℝ × ℝ}
    (hX : StronglyMeasurable X) : Γ M t (-Γ M (t + 1) X) = Γ M t X := by
  have := hM.space.isProb
  have hR1 := hM.risk.risk (t + 1) ht
  have hR := hM.risk.risk t ht.le
  have hX2 := sm_snd hX
  -- first component: tower property
  have h1 : M.P[fun ω => ((-Γ M (t + 1) X) ω).1 | M.ℱ t] = M.P[fun ω => (X ω).1 | M.ℱ t] := by
    have he : (fun ω => ((-Γ M (t + 1) X) ω).1) = M.P[fun ω => (X ω).1 | M.ℱ (t + 1)] := by
      funext ω; simp [Γ]
    rw [he]
    exact ae_eq_to_eq M hM (stronglyMeasurable_condExp.mono (M.ℱ.le t))
      (stronglyMeasurable_condExp.mono (M.ℱ.le t))
      (condExp_condExp_of_le (M.ℱ.mono (Nat.le_succ t)) (M.ℱ.le (t + 1)))
  -- second component: recursiveness of ρ from time consistency
  have hZ : StronglyMeasurable[M.ℱ (t + 1)] (fun ω => -(M.ρ (t + 1) (fun ω => (X ω).2) ω)) :=
    (hR1.stronglyMeasurable _ (memLp_of_sm M hM hX2)).neg
  have hZ' := hZ.mono (M.ℱ.le (t + 1))
  have h2 : M.ρ (t + 1) (fun ω => -(M.ρ (t + 1) (fun ω => (X ω).2) ω)) =
      M.ρ (t + 1) (fun ω => (X ω).2) := by
    have htr := rho_trans M hM ht (f := 0) stronglyMeasurable_const hZ
    have h0 : M.ρ (t + 1) 0 = 0 := ae_eq_to_eq M hM
      ((hR1.stronglyMeasurable _ (memLp_of_sm M hM stronglyMeasurable_const)).mono (M.ℱ.le _))
      stronglyMeasurable_const hR1.map_zero
    rw [zero_add, h0] at htr
    rw [htr]; funext ω; simp
  have h3 := hM.timeConsistent t ht _ _ hX2.measurable hZ'.measurable h2.symm
  have he2 : (fun ω => ((-Γ M (t + 1) X) ω).2) = fun ω => -(M.ρ (t + 1) (fun ω => (X ω).2) ω) := by
    funext ω; simp [Γ]
  funext ω
  refine Prod.ext ?_ ?_
  · show -(M.P[fun ω => ((-Γ M (t + 1) X) ω).1 | M.ℱ t]) ω = _
    rw [h1]; rfl
  · show M.ρ t (fun ω => ((-Γ M (t + 1) X) ω).2) ω = _
    rw [he2, ← h3]; rfl

lemma sm_of_mem_closure {m : MeasurableSpace Ω} {S : Set (Ω → ℝ × ℝ)}
    (hS : ∀ f ∈ S, StronglyMeasurable[m] f) {x : Ω → ℝ × ℝ} (hx : x ∈ closure S) :
    StronglyMeasurable[m] x := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  exact stronglyMeasurable_of_tendsto atTop (fun n => hS _ (hu n)) hlim

lemma value_sm (M : Market Ω) {s : ℕ} {θ : Ω → Fin M.d → ℝ}
    (hS : StronglyMeasurable (M.S s)) (hθ : StronglyMeasurable θ) :
    StronglyMeasurable (value M s θ) :=
  (continuous_fst.dotProduct continuous_snd).comp_stronglyMeasurable (hS.prodMk hθ)

lemma VT_sm (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t < M.T) {v : Ω → ℝ}
    {ψ : ℕ → Ω → Fin M.d → ℝ} (hψ : ψ ∈ feasible M t v) : StronglyMeasurable (VT M ψ) := by
  have hmem : ψ (M.T - 1) ∈ M.Φ (M.T - 1) := by
    rcases Nat.lt_or_ge t (M.T - 1) with h | h
    · exact (hψ.2.2 (M.T - 1) (by omega) le_rfl).2
    · have : M.T - 1 = t := by omega
      rw [this]; exact hψ.2.1
  have hθ := (hM.Φ_meas (M.T - 1) (by omega) _ hmem).mono (M.ℱ.le _)
  have hv := value_sm M ((hM.adapted M.T le_rfl).mono (M.ℱ.le _)) hθ
  exact hv.prodMk hv


lemma feas_shift (M : Market Ω) {t : ℕ} (h1 : t + 1 < M.T) {v : Ω → ℝ}
    {ψ : ℕ → Ω → Fin M.d → ℝ} (hψ : ψ ∈ feasible M t v) :
    ψ ∈ feasible M (t + 1) (value M (t + 1) (ψ t)) :=
  ⟨(hψ.2.2 (t + 1) le_rfl (by omega)).1.symm, (hψ.2.2 (t + 1) le_rfl (by omega)).2,
    fun s hs1 hs2 => hψ.2.2 s (by omega) hs2⟩

lemma feas_update (M : Market Ω) {t : ℕ} (h1 : t + 1 < M.T) {v : Ω → ℝ}
    {θ : Ω → Fin M.d → ℝ} (hθv : value M t θ = v) (hθΦ : θ ∈ M.Φ t)
    {ψ : ℕ → Ω → Fin M.d → ℝ} (hψ : ψ ∈ feasible M (t + 1) (value M (t + 1) θ)) :
    Function.update ψ t θ ∈ feasible M t v ∧ VT M (Function.update ψ t θ) = VT M ψ := by
  set ψ' := Function.update ψ t θ with hψ'def
  have hψ't : ψ' t = θ := Function.update_self _ _ _
  have hψ's : ∀ s, t + 1 ≤ s → ψ' s = ψ s := fun s hs =>
    Function.update_of_ne (by omega) _ _
  refine ⟨⟨by rw [hψ't]; exact hθv, by rw [hψ't]; exact hθΦ, fun s hs1 hs2 => ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge (t + 1) s with h | h
    · rw [hψ's s (by omega), hψ's (s - 1) (by omega)]
      exact hψ.2.2 s h hs2
    · have hs : s = t + 1 := by omega
      subst hs
      rw [hψ's (t + 1) le_rfl, Nat.add_sub_cancel, hψ't]
      exact ⟨hψ.1.symm, hψ.2.1⟩
  · funext ω; simp only [VT, hψ's (M.T - 1) (by omega)]

lemma feas_const (M : Market Ω) {t : ℕ} (hT : M.T = t + 1) {v : Ω → ℝ}
    {θ : Ω → Fin M.d → ℝ} (hθv : value M t θ = v) (hθΦ : θ ∈ M.Φ t) :
    (fun _ => θ : ℕ → Ω → Fin M.d → ℝ) ∈ feasible M t v ∧
      VT M (fun _ => θ) = fun ω => (value M (t + 1) θ ω, value M (t + 1) θ ω) := by
  refine ⟨⟨hθv, hθΦ, fun s hs1 hs2 => by omega⟩, ?_⟩
  funext ω; simp [VT, hT]

lemma image_sm (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {v : Ω → ℝ}
    (hv : StronglyMeasurable[M.ℱ t] v) {p : Ω → ℝ × ℝ} (hp : p ∈ image M t v) :
    StronglyMeasurable[M.ℱ t] p := by
  unfold image at hp
  split_ifs at hp with h
  · obtain ⟨ψ, hψ, rfl⟩ := hp
    exact Γ_sm M hM ht (VT_sm M hM h hψ)
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    exact hv.neg.prodMk hv.neg

lemma upper_sm (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {v : Ω → ℝ}
    (hv : StronglyMeasurable[M.ℱ t] v) {p : Ω → ℝ × ℝ} (hp : p ∈ upperImage M t v) :
    StronglyMeasurable[M.ℱ t] p := by
  have hS : ∀ f ∈ image M t v + cone M t, StronglyMeasurable[M.ℱ t] f := by
    rintro f ⟨a, ha, r, hr, rfl⟩
    exact (image_sm M hM ht hv ha).add hr.1
  unfold upperImage at hp
  split_ifs at hp
  · exact sm_of_mem_closure hS hp
  · exact hS p hp

lemma add_cone_subset (M : Market Ω) {t : ℕ} (A : Set (Ω → ℝ × ℝ)) {c : Ω → ℝ × ℝ}
    (hc : c ∈ cone M t) {p : Ω → ℝ × ℝ} (hp : p ∈ A + cone M t) : p + c ∈ A + cone M t := by
  obtain ⟨a, ha, r, hr, rfl⟩ := hp
  refine ⟨a, ha, r + c, ⟨hr.1.add hc.1, ?_⟩, by rw [add_assoc]⟩
  exact add_nonneg hr.2 hc.2

lemma upper_mono (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t ≤ M.T) {v : Ω → ℝ}
    (hv : StronglyMeasurable[M.ℱ t] v) {p q : Ω → ℝ × ℝ} (hp : p ∈ upperImage M t v)
    (hq : StronglyMeasurable[M.ℱ t] q) (hpq : p ≤ q) : q ∈ upperImage M t v := by
  have hc : q - p ∈ cone M t := ⟨hq.sub (upper_sm M hM ht hv hp), sub_nonneg.2 hpq⟩
  have hqe : q = p + (q - p) := by abel
  rw [hqe]
  unfold upperImage at hp ⊢
  split_ifs at hp ⊢
  · have h1 := image_closure_subset_closure_image (f := fun x => x + (q - p))
      (continuous_add_right (q - p)) (Set.mem_image_of_mem _ hp)
    refine closure_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    exact add_cone_subset M _ hc hy
  · exact add_cone_subset M _ hc hp

/-- Step 2 of the proof of Theorem 5.1. -/
lemma step2 (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t < M.T) {v : Ω → ℝ}
    {y : Ω → ℝ × ℝ} (hy : y ∈ image M t v + cone M t) :
    ∃ θ : Ω → Fin M.d → ℝ, ∃ x : Ω → ℝ × ℝ,
      value M t θ = v ∧ θ ∈ M.Φ t ∧ x ∈ upperImage M (t + 1) (value M (t + 1) θ) ∧
      y = Γ M t (-x) := by
  rw [image, if_pos ht] at hy
  obtain ⟨a, ⟨ψ, hψ, rfl⟩, r, hr, rfl⟩ := hy
  have hVT := VT_sm M hM ht hψ
  by_cases h1 : t + 1 < M.T
  · have hψ1 := feas_shift M h1 hψ
    have hGa := Γ_sm M hM h1.le hVT
    refine ⟨ψ t, Γ M (t + 1) (VT M ψ) + r, hψ.1, hψ.2.1, ?_, ?_⟩
    · rw [upperImage, if_pos h1, image, if_pos h1]
      exact subset_closure (Set.add_mem_add ⟨ψ, hψ1, rfl⟩
        ⟨hr.1.mono (M.ℱ.mono (Nat.le_succ t)), hr.2⟩)
    · have : -(Γ M (t + 1) (VT M ψ) + r) = -Γ M (t + 1) (VT M ψ) + -r := neg_add _ _
      rw [this, Γ_trans M hM ht.le (hGa.mono (M.ℱ.le _)).neg hr.1.neg, Γ_rec M hM ht hVT,
        sub_neg_eq_add]
  · have hT : M.T = t + 1 := by omega
    set w := value M (t + 1) (ψ t) with hw
    refine ⟨ψ t, (fun ω => (-w ω, -w ω)) + r, hψ.1, hψ.2.1, ?_, ?_⟩
    · rw [upperImage, if_neg h1, image, if_neg h1]
      exact Set.add_mem_add rfl ⟨hr.1.mono (M.ℱ.mono (Nat.le_succ t)), hr.2⟩
    · have hV : VT M ψ = fun ω => (w ω, w ω) := by
        funext ω; simp only [VT, hw, hT, Nat.add_sub_cancel]
      have : -((fun ω => (-w ω, -w ω)) + r) = VT M ψ + -r := by
        rw [hV]; funext ω; simp [add_comm]
      rw [this, Γ_trans M hM ht.le hVT hr.1.neg, sub_neg_eq_add]

/-- Step 3 of the proof of Theorem 5.1. -/
lemma step3 (M : Market Ω) (hM : M.Assumptions) {t : ℕ} (ht : t < M.T) {v : Ω → ℝ}
    {θ : Ω → Fin M.d → ℝ} {x : Ω → ℝ × ℝ} (hθv : value M t θ = v) (hθΦ : θ ∈ M.Φ t)
    (hx : x ∈ upperImage M (t + 1) (value M (t + 1) θ)) :
    Γ M t (-x) ∈ closure (image M t v + cone M t) := by
  rw [image, if_pos ht]
  by_cases h1 : t + 1 < M.T
  · rw [upperImage, if_pos h1, image, if_pos h1] at hx
    have hxm : StronglyMeasurable x := by
      refine (sm_of_mem_closure (m := M.ℱ (t + 1)) ?_ hx).mono (M.ℱ.le _)
      rintro f ⟨a, ⟨ψ, hψ, rfl⟩, r, hr, rfl⟩
      exact (Γ_sm M hM h1.le (VT_sm M hM h1 hψ)).add hr.1
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hx ε hε
    obtain ⟨a, ⟨ψ, hψ, rfl⟩, r, hr, rfl⟩ := hz
    have hVT := VT_sm M hM h1 hψ
    have hGa := (Γ_sm M hM h1.le hVT).mono (M.ℱ.le _)
    have hrm : StronglyMeasurable r := hr.1.mono (M.ℱ.le _)
    obtain ⟨hψ', hVT'⟩ := feas_update M h1 hθv hθΦ hψ
    have hz : StronglyMeasurable (-(Γ M (t + 1) (VT M ψ) + r)) := (hGa.add hrm).neg
    refine ⟨Γ M t (-(Γ M (t + 1) (VT M ψ) + r)),
      Set.mem_add.2 ⟨Γ M t (VT M (Function.update ψ t θ)), ⟨_, hψ', rfl⟩,
      Γ M t (-(Γ M (t + 1) (VT M ψ) + r)) - Γ M t (VT M (Function.update ψ t θ)), ⟨?_, ?_⟩,
      add_sub_cancel _ _⟩, ?_⟩
    · exact (Γ_sm M hM ht.le hz).sub (Γ_sm M hM ht.le (hVT' ▸ hVT))
    · rw [sub_nonneg, hVT', ← Γ_rec M hM ht hVT]
      apply Γ_mono M hM ht.le hz hGa.neg
      intro ω
      have := hr.2 ω
      simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply] at this ⊢
      exact Prod.le_def.2 ⟨by have := (Prod.le_def.1 this).1; simp at this ⊢; linarith,
        by have := (Prod.le_def.1 this).2; simp at this ⊢; linarith⟩
    · calc dist (Γ M t (-x)) (Γ M t (-(Γ M (t + 1) (VT M ψ) + r)))
          ≤ dist (-x) (-(Γ M (t + 1) (VT M ψ) + r)) := Γ_lip M hM ht.le hxm.neg hz
        _ = dist x (Γ M (t + 1) (VT M ψ) + r) := dist_neg_neg _ _
        _ < ε := hdist
  · have hT : M.T = t + 1 := by omega
    rw [upperImage, if_neg h1, image, if_neg h1] at hx
    obtain ⟨c, hc, r, hr, rfl⟩ := hx
    rw [Set.mem_singleton_iff] at hc
    subst hc
    obtain ⟨hψ, hV0⟩ := feas_const M hT hθv hθΦ
    have hVT := VT_sm M hM ht hψ
    have hV : VT M (fun _ => θ) = -(fun ω => (-value M (t + 1) θ ω, -value M (t + 1) θ ω)) := by
      rw [hV0]; funext ω; simp
    have hrm : StronglyMeasurable r := hr.1.mono (M.ℱ.le _)
    have hcm : StronglyMeasurable (fun ω => (-value M (t + 1) θ ω, -value M (t + 1) θ ω)) := by
      rw [← neg_neg (fun ω => (-value M (t + 1) θ ω, -value M (t + 1) θ ω)), ← hV]
      exact hVT.neg
    have hz : StronglyMeasurable (-((fun ω => (-value M (t + 1) θ ω, -value M (t + 1) θ ω)) + r)) :=
      (hcm.add hrm).neg
    apply subset_closure
    refine Set.mem_add.2 ⟨Γ M t (VT M (fun _ => θ)), ⟨_, hψ, rfl⟩,
      _ - Γ M t (VT M (fun _ => θ)), ⟨?_, ?_⟩, add_sub_cancel _ _⟩
    · exact (Γ_sm M hM ht.le hz).sub (Γ_sm M hM ht.le hVT)
    · rw [sub_nonneg]
      apply Γ_mono M hM ht.le hz hVT
      rw [hV]
      intro ω
      have := hr.2 ω
      simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply] at this ⊢
      exact Prod.le_def.2 ⟨by have := (Prod.le_def.1 this).1; simp at this ⊢; linarith,
        by have := (Prod.le_def.1 this).2; simp at this ⊢; linarith⟩

end MRBThm51Aux

open MeanRiskBellman.Recursion MRBThm51Aux in
theorem solution {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t < M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) :
    upperImageTilde M t v = upperImage M t v := by
  have hU : upperImage M t v = closure (image M t v + cone M t) := if_pos ht
  unfold upperImageTilde
  rw [hU]
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨b, ⟨⟨θ, x⟩, ⟨hθv, hθΦ, hx⟩, rfl⟩, c, hc, rfl⟩
    have hb : Γ M t (-x) ∈ upperImage M t v := by
      rw [hU]; exact step3 M hM ht hθv hθΦ hx
    have hbm := upper_sm M hM ht.le hv hb
    have := upper_mono M hM ht.le hv hb (hbm.add hc.1) (le_add_of_nonneg_right hc.2)
    rwa [hU] at this
  · apply closure_mono
    intro y hy
    obtain ⟨θ, x, hθv, hθΦ, hx, rfl⟩ := step2 M hM ht hy
    exact ⟨Γ M t (-x), ⟨(θ, x), ⟨hθv, hθΦ, hx⟩, rfl⟩, 0,
      ⟨stronglyMeasurable_zero, le_refl _⟩, add_zero _⟩
