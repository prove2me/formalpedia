-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.hasSum_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:54.938849+00:00
-- url     : https://prove2.me/submissions/406b874c-6e0a-4290-8111-e366af842d18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_locally_normal
import Theorems.Thm_GlobalTheory_SW_ExpSum_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_hasSum_fderiv_of_locally_normal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (hp : p ∈ U) (v : V) :
    HasSum (fun i => c i * L i v * cexp (L i p))
      (deriv (fun s : ℂ => ∑' i, c i * cexp (L i (p + s • v))) 0) := by
  have h1 := GlobalTheory.SCV.hasSum_fderiv_of_locally_normal (F := fun i p => c i * cexp (L i p)) hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs) hp
  have h2 := (ContinuousLinearMap.apply ℂ ℂ v).hasSum h1
  have h3 := ((differentiableOn hU c L hs).differentiableAt (hU.mem_nhds hp)).lineDeriv_eq_fderiv
    (v := v)
  rw [lineDeriv] at h3
  rw [h3]
  have e : (fun i => c i * L i v * cexp (L i p)) = fun i =>
      ContinuousLinearMap.apply ℂ ℂ v (fderiv ℂ (fun p => c i * cexp (L i p)) p) := by
    funext i
    have : HasFDerivAt (fun p => c i * cexp (L i p)) (c i • cexp (L i p) • L i) p :=
      ((L i).hasFDerivAt.cexp).const_mul (c i)
    rw [this.fderiv]
    simp
    ring
  rw [e]
  exact h2
end GlobalTheory.SW.ExpSum
