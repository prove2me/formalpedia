-- Prove2me | solution 1 for ImplicitCalculus.local_level_retraction_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:17:25.334006+00:00
-- url     : https://prove2.me/submissions/0d187457-3144-4910-9443-7dcbc2db4386

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Set Filter
open scoped Topology NNReal
set_option autoImplicit false

theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (F : V → W) (D : V →L[ℝ] W) (y : V)
    (hF : HasStrictFDerivAt F D y) (hD : Function.Surjective D) :
    ∃ r : V → V, ContinuousAt r y ∧ r y = y ∧
      ∃ C : ℝ≥0, ∀ᶠ z in 𝓝 y,
        F (r z) = F y ∧ dist z (r z) ≤ C * ‖F z - F y‖ := by
  classical
  letI := FiniteDimensional.complete ℝ W
  have hr : D.range = ⊤ := LinearMap.range_eq_top.mpr hD
  let d := hF.implicitFunctionDataOfComplemented F D hr
    D.ker_closedComplemented_of_finiteDimensional_range
  let e := D.equivProdOfSurjectiveOfIsCompl d.rightDeriv d.range_leftDeriv
    d.range_rightDeriv d.isCompl_ker
  let inv := d.hasStrictFDerivAt.localInverse d.prodFun e y
  let q : V → W × D.ker := fun z => (F y, d.rightFun z)
  let r : V → V := fun z => inv (q z)
  have hdy : d.prodFun y = (F y, (0 : D.ker)) := by simp [d, ImplicitFunctionData.prodFun]
  have hq : ContinuousAt q y := continuousAt_const.prodMk
    d.hasStrictFDerivAt_rightFun.continuousAt
  have hqy : q y = d.prodFun y := by simp [q, d, ImplicitFunctionData.prodFun]
  have hinv : ContinuousAt inv (d.prodFun y) := d.hasStrictFDerivAt.localInverse_continuousAt
  have hrc : ContinuousAt r y := by
    exact (hqy ▸ hinv).comp hq
  have hry : r y = y := by
    change inv (q y) = y
    rw [hqy]
    exact d.hasStrictFDerivAt.localInverse_apply_image
  obtain ⟨C, U, hU, hLip⟩ := d.hasStrictFDerivAt.to_localInverse.exists_lipschitzOnWith
  have hpu : ∀ᶠ z in 𝓝 y, d.prodFun z ∈ U :=
    d.hasStrictFDerivAt.continuousAt.eventually hU
  have hqt : Tendsto q (𝓝 y) (𝓝 (d.prodFun y)) := hqy ▸ hq.tendsto
  have hqu : ∀ᶠ z in 𝓝 y, q z ∈ U := hqt.eventually hU
  have hleft := d.hasStrictFDerivAt.eventually_left_inverse
  have hright : ∀ᶠ z in 𝓝 y, d.prodFun (r z) = q z :=
    hqt.eventually d.hasStrictFDerivAt.eventually_right_inverse
  refine ⟨r, hrc, hry, C, ?_⟩
  filter_upwards [hpu, hqu, hleft, hright] with z hz hqz hl hrr
  change inv (d.prodFun z) = z at hl
  refine ⟨congrArg Prod.fst hrr, ?_⟩
  calc
    dist z (r z) = dist (inv (d.prodFun z)) (inv (q z)) := by rw [hl]
    _ ≤ C * dist (d.prodFun z) (q z) := hLip.dist_le_mul _ hz _ hqz
    _ = C * ‖F z - F y‖ := by simp [q, d, ImplicitFunctionData.prodFun, Prod.dist_eq, dist_eq_norm]
