-- Prove2me | solution 1 for GlobalTheory.fderiv_eq_mul_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:42.945016+00:00
-- url     : https://prove2.me/submissions/74138701-796b-4f35-9ccf-4d5f5b2f2b2b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (θ : κ → E → ℂ)
    (hθ : ∀ c, Differentiable ℂ (θ c)) (c : κ) (z w : E) (hc : θ c z ≠ 0) (v : κ → E → ℂ)
    (hv : ∀ c' y, θ c y ≠ 0 → v c' y = θ c' y / θ c y) (hw : ∀ c', fderiv ℂ (v c') z w = 0)
    (f : E → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range θ)) :
    fderiv ℂ f z w = (fderiv ℂ (θ c) z w / θ c z) * f z := by

  have hbase : ∀ c', fderiv ℂ (θ c') z w = (fderiv ℂ (θ c) z w / θ c z) * θ c' z := by
    intro c'
    have hev : ∀ᶠ y in 𝓝 z, θ c y ≠ 0 := (hθ c).continuous.continuousAt.eventually_ne hc
    have hq : DifferentiableAt ℂ (fun y => θ c' y / θ c y) z := by
      have h3 := ((hθ c') z).mul (((hθ c) z).inv hc)
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [div_eq_mul_inv]
    have hvq : v c' =ᶠ[𝓝 z] fun y => θ c' y / θ c y := hev.mono fun y hy => hv c' y hy
    have hvd : DifferentiableAt ℂ (v c') z := hq.congr_of_eventuallyEq hvq
    have hprod : θ c' =ᶠ[𝓝 z] fun y => v c' y * θ c y := by
      filter_upwards [hev] with y hy
      rw [hv c' y hy, div_mul_cancel₀ _ hy]
    have hd := (hvd.hasFDerivAt.mul ((hθ c) z).hasFDerivAt).congr_of_eventuallyEq hprod
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hw c',
      mul_zero, add_zero]
    rw [hv c' z hc]
    ring

  have key : ∀ f ∈ Submodule.span ℂ (Set.range θ),
      Differentiable ℂ f ∧ fderiv ℂ f z w = (fderiv ℂ (θ c) z w / θ c z) * f z := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c', rfl⟩ := hx
      exact ⟨hθ c', hbase c'⟩
    | zero =>
      refine ⟨differentiable_const 0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      have hs : HasFDerivAt (x + y) (fderiv ℂ x z + fderiv ℂ y z) z :=
        ((hx.1 z).hasFDerivAt.add (hy.1 z).hasFDerivAt)
      rw [hs.fderiv, ContinuousLinearMap.add_apply, hx.2, hy.2, Pi.add_apply]
      ring
    | smul a x _ hx =>
      refine ⟨hx.1.const_smul a, ?_⟩
      have hs : HasFDerivAt (a • x) (a • fderiv ℂ x z) z := (hx.1 z).hasFDerivAt.const_smul a
      rw [hs.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, hx.2, Pi.smul_apply, smul_eq_mul]
      ring
  exact (key f hf).2
end GlobalTheory
