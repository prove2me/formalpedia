-- Prove2me | solution 1 for GlobalTheory.SimMult.norm_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:12.367549+00:00
-- url     : https://prove2.me/submissions/c9a0b240-79b6-483e-9c16-09aabfa6c061

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution (I : Ideal O) {c c' : O} (h : c' - c ∈ I) (h' : σ (c' - c) ∈ I) {ν : O}
    (hc : c * σ c - ν ∈ I) : c' * σ c' - ν ∈ I := by
  have : c' * σ c' - ν = (c * σ c - ν) + (σ c' * (c' - c) + c * σ (c' - c)) := by
    rw [map_sub]; ring
  rw [this]
  exact I.add_mem hc (I.add_mem (I.mul_mem_left _ h) (I.mul_mem_left _ h'))
end GlobalTheory.SimMult
