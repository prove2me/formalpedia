-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.exists_conj_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:09.456906+00:00
-- url     : https://prove2.me/submissions/6573603c-8cf4-4324-a0ff-cca271ab627c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
open GlobalTheory.UnitLemma
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (K : UQ) :
    ∃ c : K.O →+* K.O, ∀ x, algebraMap K.O K.E (c x) = K.c (algebraMap K.O K.E x) := by
  choose c hc using K.c_int
  have inj := IsFractionRing.injective K.O K.E
  refine ⟨⟨⟨⟨c, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, fun x => (hc x).symm⟩
  · rw [← hc]; simp
  · simp only [map_mul, ← hc]
  · simp only [← hc]; simp
  · simp only [map_add, ← hc]
end GlobalTheory.LocalFiniteOddFixed
