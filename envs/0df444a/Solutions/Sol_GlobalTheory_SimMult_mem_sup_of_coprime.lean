-- Prove2me | solution 1 for GlobalTheory.SimMult.mem_sup_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:13.685054+00:00
-- url     : https://prove2.me/submissions/3359227b-1f5b-4470-b2e8-7990df264c3b

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
theorem _root_.solution (J : Ideal O) {m n : ℕ} (hm : (m : O) ∈ J) (h : Nat.Coprime m n) (x : O) :
    x ∈ J ⊔ Ideal.span {(n : O)} := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := O) h
  refine Submodule.mem_sup.2 ⟨x * u * m, J.mul_mem_left _ hm, x * v * n,
    Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, ?_⟩
  linear_combination x * huv
end GlobalTheory.SimMult
