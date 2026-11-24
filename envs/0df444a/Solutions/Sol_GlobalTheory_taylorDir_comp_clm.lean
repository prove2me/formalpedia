-- Prove2me | solution 1 for GlobalTheory.taylorDir_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:40.585293+00:00
-- url     : https://prove2.me/submissions/672b23d0-09ed-4c46-bc26-13d825910f50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_lineDerivList_comp_linearMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}
namespace GlobalTheory
theorem _root_.solution {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℂ W']
    (L : W' →L[ℂ] W) (v : σ → W') (hf : AnalyticAt ℂ f 0) :
    taylorDir v (fun z => f (L z)) = taylorDir (fun i => L (v i)) f := by
  ext m
  have hc : AnalyticAt ℂ (fun z => f (L z)) 0 := hf.comp_of_eq (L.analyticAt 0) (map_zero L)
  have h := congrFun (lineDerivList_comp_linearMap (L : W' →ₗ[ℂ] W)
    ((Finsupp.toMultiset m).toList.map v) f) 0
  rw [map_zero, List.map_map] at h
  rw [coeff_taylorDir_eq_lineDerivList v hc (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList _ hf (Multiset.coe_toList _)]
  exact congrArg _ h
end GlobalTheory
