-- Prove2me | solution 1 for GlobalTheory.T.truncated_set_empty_outside_norm_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:42.111921+00:00
-- url     : https://prove2.me/submissions/57083c1b-35e0-41ed-835b-e09600d508f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedSetEmptyOutsideNormCoset
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedSetEmptyOutsideNormCosetStatement
import Theorems.Thm_GlobalTheory_JR_norm_sub_notMem_of_not_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ∀ (x : A.Kˣ) (a : A.K) (D : Set A.K), (∀ b ∈ D, ∃ s s' : A.K, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b) → IsUnit a → (¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ y : A.L, (x : A.K) * A.NL y - a ∉ D := by
  first | exact @GlobalTheory.JR.norm_sub_notMem_of_not_norm | exact GlobalTheory.JR.norm_sub_notMem_of_not_norm | (intros; apply GlobalTheory.JR.norm_sub_notMem_of_not_norm <;> assumption)
end _root_.GlobalTheory.T
