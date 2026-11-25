-- Prove2me | solution 1 for GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:36.577272+00:00
-- url     : https://prove2.me/submissions/67f59091-f829-43ef-8e31-ef353b36b89d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRingStatement
import Theorems.Thm_GlobalTheory_exact_dualMap_of_exact_fibres_of_isRegularLocalRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) → (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) → ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by
  first | exact @GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing | exact GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing | (intros; apply GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing <;> assumption)
end _root_.GlobalTheory.T
