-- Prove2me | solution 1 for GlobalTheory.SW.posDef_map_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:05.618331+00:00
-- url     : https://prove2.me/submissions/d9ff2620-a84f-4b3e-adec-04d0205b8761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent

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
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {E m n : Type} [Field E] [Fintype m] [Fintype n]
    {W : Matrix n m E} (hW : LinearIndependent E fun i => W i) (σ : E →+* ℂ) :
    (W.map σ * (W.map σ)ᴴ).PosDef := by
  let _ := σ.toAlgebra
  exact PosDef.mul_conjTranspose_self _
    (vecMul_injective_iff.2 ((linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hW))
end GlobalTheory.SW
