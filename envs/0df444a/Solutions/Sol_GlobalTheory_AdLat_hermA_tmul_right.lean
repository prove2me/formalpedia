-- Prove2me | solution 1 for GlobalTheory.AdLat.hermA_tmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:02:04.402118+00:00
-- url     : https://prove2.me/submissions/6daa439b-6c6f-4973-80e8-f34ba4b8a99c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicHermitianFormGaloisMemOfMemCompletion
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.AdLat
theorem _root_.solution (z : Fin n → RA F E) (t : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    hermA c G z (fun i => t ⊗ₜ[F] x i) = (t ⊗ₜ[F] (1 : E)) * hermA c G z (fv F x) := by
  simp only [hermA, fv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : sg (FiniteAdeleRing (𝓞 F) F) c (t ⊗ₜ[F] x b) = (t ⊗ₜ[F] (1 : E)) *
      sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x b) := by
    simp [sg, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h]; ring
end GlobalTheory.AdLat
