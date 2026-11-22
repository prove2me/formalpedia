-- Prove2me | solution 1 for LeiBR.Async.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:42:58.11411+00:00
-- url     : https://prove2.me/submissions/b4581b96-9ce4-45a4-851e-3e12e0539f37

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Theorems.Thm_LeiBR_Sync_eq_5

open LeiBR.Async MeasureTheory

private lemma hasFDerivAt_profile_update {N : ℕ} {n : Fin N → ℕ}
    (x : LeiBR.Sync.Profile n) (i : Fin N) :
    HasFDerivAt (fun z : LeiBR.Sync.Strat n i => Function.update x i z)
      (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i) (x i) := by
  have hEq : (fun z : LeiBR.Sync.Strat n i => Function.update x i z) =
      fun z => x + ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i (z - x i) := by
    funext z j
    by_cases hji : j = i
    · subst hji
      simp [ContinuousLinearMap.single_apply]
    · simp [Function.update, hji, ContinuousLinearMap.single_apply]
  rw [hEq]
  have h1 : HasFDerivAt (fun z : LeiBR.Sync.Strat n i => z - x i)
      (ContinuousLinearMap.id ℝ (LeiBR.Sync.Strat n i)) (x i) :=
    (hasFDerivAt_id (x i)).sub_const (x i)
  have h2 : HasFDerivAt
      (fun z : LeiBR.Sync.Strat n i =>
        ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i (z - x i))
      (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i) (x i) := by
    simpa using (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i).hasFDerivAt.comp (x i) h1
  simpa using h2.const_add x

theorem solution {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) :
    ∀ y ∈ profileSet X, ∀ y' ∈ profileSet X, ∀ i : Fin N,
      ‖xhat y' i - xhat y i‖ ≤ ∑ j, LeiBR.Sync.Gamma X f μ i j * ‖y' j - y j‖ := by
  let _ : MeasurableSpace Unit := ⊤
  let P : Measure Unit := Measure.dirac ()
  let ξ : Unit → EuclideanSpace ℝ (Fin 0) := fun _ => 0
  let ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin 0) → ℝ := fun i x _ => f i x
  let gψ : ∀ i : Fin N, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin 0) → LeiBR.Sync.Strat n i :=
    fun i x _ => LeiBR.Sync.partialGrad f i x
  have hpayoff : LeiBR.Sync.payoff P ξ ψ = f := by
    funext i x
    simp [LeiBR.Sync.payoff, P, ψ]
  obtain ⟨U, hU, hC2, hconv⟩ := hA1.smooth
  have hU_open : IsOpen (Set.univ.pi U) :=
    isOpen_set_pi Set.finite_univ (fun i _ => (hU i).1)
  have hX_sub_U : LeiBR.Sync.stratSet X ⊆ Set.univ.pi U :=
    Set.pi_mono (fun i _ => (hU i).2.2)
  have hX_compact : IsCompact (LeiBR.Sync.stratSet X) :=
    isCompact_univ_pi hA1.compact
  have hgrad_formula : ∀ (i : Fin N) (x : LeiBR.Sync.Profile n), x ∈ Set.univ.pi U →
      DifferentiableAt ℝ (fun z : LeiBR.Sync.Strat n i => f i (Function.update x i z)) (x i) ∧
      LeiBR.Sync.partialGrad f i x =
        (InnerProductSpace.toDual ℝ (LeiBR.Sync.Strat n i)).symm
          ((fderiv ℝ (f i) x).comp (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i)) := by
    intro i x hx
    have hfi : DifferentiableAt ℝ (f i) x :=
      ((hC2 i).differentiableOn (by norm_num)).differentiableAt (hU_open.mem_nhds hx)
    have hcomp : HasFDerivAt (fun z : LeiBR.Sync.Strat n i => f i (Function.update x i z))
        ((fderiv ℝ (f i) x).comp (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i)) (x i) := by
      have h1 : HasFDerivAt (f i) (fderiv ℝ (f i) x) (Function.update x i (x i)) := by
        simpa using hfi.hasFDerivAt
      exact h1.comp (x i) (hasFDerivAt_profile_update x i)
    refine ⟨hcomp.differentiableAt, ?_⟩
    simp [LeiBR.Sync.partialGrad, gradient, hcomp.fderiv]
  have hM_exists : ∀ i : Fin N, ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ LeiBR.Sync.stratSet X, ‖LeiBR.Sync.partialGrad f i x‖ ≤ c := by
    intro i
    have hcont_fderiv : ContinuousOn (fderiv ℝ (f i)) (Set.univ.pi U) :=
      (hC2 i).continuousOn_fderiv_of_isOpen hU_open (by norm_num)
    have hcont_rhs : ContinuousOn
        (fun x : LeiBR.Sync.Profile n =>
          (InnerProductSpace.toDual ℝ (LeiBR.Sync.Strat n i)).symm
            ((fderiv ℝ (f i) x).comp (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i)))
        (Set.univ.pi U) := by
      have hpre : Continuous (fun L : LeiBR.Sync.Profile n →L[ℝ] ℝ =>
          L.comp (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i)) :=
        (ContinuousLinearMap.compL ℝ (LeiBR.Sync.Strat n i) (LeiBR.Sync.Profile n) ℝ).flip
          (ContinuousLinearMap.single ℝ (LeiBR.Sync.Strat n) i) |>.continuous
      exact (InnerProductSpace.toDual ℝ (LeiBR.Sync.Strat n i)).symm.continuous.comp_continuousOn
        (hpre.comp_continuousOn hcont_fderiv)
    have hcont_pg : ContinuousOn (LeiBR.Sync.partialGrad f i) (LeiBR.Sync.stratSet X) :=
      (hcont_rhs.congr (fun x hx => (hgrad_formula i x hx).2)).mono hX_sub_U
    obtain ⟨C, hC⟩ := hX_compact.exists_bound_of_continuousOn hcont_pg
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx => ?_⟩
    exact le_trans (hC x hx) (le_max_right _ _)
  choose M hM_pos hM_bound using hM_exists
  have hA1_sync : LeiBR.Sync.Assumption1 P ξ X ψ gψ M := by
    refine ⟨fun i => ⟨hA1.closed i, hA1.compact i, hA1.convex i, hA1.nonempty i⟩, U, hU, ?_, ?_, ?_, ?_, ?_⟩
    · intro i x _
      exact integrable_const _
    · intro i
      simpa [hpayoff] using hC2 i
    · intro i y hy
      simpa [hpayoff] using hconv i y hy
    · intro i x hx_ne hx_i
      have hxU : x ∈ Set.univ.pi U := by
        intro j _
        by_cases hji : j = i
        · subst hji; exact hx_i
        · exact (hU j).2.2 (hx_ne j hji)
      refine ⟨fun _ => (hgrad_formula i x hxU).1.hasGradientAt, integrable_const _, ?_⟩
      simp [hpayoff, P, gψ]
    · intro i
      refine ⟨hM_pos i, fun x hx => ⟨?_, ?_⟩⟩
      · simp [gψ]
      · have hb : ‖LeiBR.Sync.partialGrad f i x‖ ≤ M i := hM_bound i x hx
        have hsq : ‖LeiBR.Sync.partialGrad f i x‖ ^ 2 ≤ M i ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
        simpa [P, gψ] using hsq
  have hres := LeiBR.Sync.eq_5 P ξ X ψ gψ M hA1_sync μ hμ xhat (by simpa [hpayoff] using hxhat)
  rw [hpayoff] at hres
  exact hres
