-- Prove2me | solution 1 for GlobalTheory.ConvexCutOff.iteratedFDeriv_eq_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:47.622844+00:00
-- url     : https://prove2.me/submissions/53781747-9596-4afc-9d37-afdda1b9ac84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
import Theorems.Thm_GlobalTheory_ConvexCutOff_fderiv_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff
namespace GlobalTheory.ConvexCutOff
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (n : ℕ) : ∀ z, z ∉ K → iteratedFDeriv ℂ n F z = 0 := by
  induction n with
  | zero =>
    intro z hz
    ext m
    simp [hF z hz]
  | succ n ih =>
    intro z hz
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      fderiv_eq_zero hK ih (fun h => hz (interior_subset h))]
    exact map_zero _
end GlobalTheory.ConvexCutOff
