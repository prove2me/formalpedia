-- Prove2me | solution 1 for GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:21:13.790797+00:00
-- url     : https://prove2.me/submissions/c1f7da63-3973-4bbf-9e3d-7e2a93224552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvertStatement
import Theorems.Thm_GlobalTheory_exists_isUnit_matrix_of_pow_smul_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  first | exact @GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | exact GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | (intros; apply GlobalTheory.exists_isUnit_matrix_of_pow_smul_span <;> assumption)
end _root_.GlobalTheory.T
