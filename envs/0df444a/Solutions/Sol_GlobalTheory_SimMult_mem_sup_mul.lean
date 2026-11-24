-- Prove2me | solution 1 for GlobalTheory.SimMult.mem_sup_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:12.974884+00:00
-- url     : https://prove2.me/submissions/f6e8a905-0f09-4f29-a1d5-a13f5135d7de

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
theorem _root_.solution (J : Ideal O) {a b u v x : O} (h : u * a + v * b = 1)
    (ha : x ∈ J ⊔ Ideal.span {a}) (hb : x ∈ J ⊔ Ideal.span {b}) : x ∈ J ⊔ Ideal.span {a * b} := by
  obtain ⟨j, hj, y, hy, h1⟩ := Submodule.mem_sup.1 ha
  obtain ⟨j', hj', y', hy', h2⟩ := Submodule.mem_sup.1 hb
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨y', rfl⟩ := Ideal.mem_span_singleton'.1 hy'
  refine Submodule.mem_sup.2 ⟨u * a * j' + v * b * j, J.add_mem (J.mul_mem_left _ hj')
    (J.mul_mem_left _ hj), (u * y' + v * y) * (a * b), Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, ?_⟩
  linear_combination u * a * h2 + v * b * h1 + x * h
end GlobalTheory.SimMult
