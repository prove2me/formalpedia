-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Witt.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:54.383826+00:00
-- url     : https://prove2.me/submissions/5fe00cb0-7ff8-4b23-ba56-1f98e95059e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Witt
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Witt
theorem _root_.solution (K : UQ) : ∃ s : K.O →+* K.O,
    ∀ x, algebraMap K.O K.E (s x) = K.c (algebraMap K.O K.E x) := by
  choose f hf using K.c_int
  have inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [← hf]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, ← hf, ← hf, ← hf]; simp)
            map_zero' := inj (by rw [← hf]; simp)
            map_add' := fun x y => inj (by rw [map_add, ← hf, ← hf, ← hf]; simp) }, fun x => (hf x).symm⟩
end GlobalTheory.UnitLemma.Witt
