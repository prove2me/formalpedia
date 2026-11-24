-- Prove2me | solution 1 for GlobalTheory.AdLat.cap_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:47:36.237208+00:00
-- url     : https://prove2.me/submissions/f4df84bd-2a26-4c2d-a4c1-93ac28116638

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
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
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
omit [NumberField E]
namespace GlobalTheory.AdLat
theorem _root_.solution (r : F) (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (algebraMap F (FiniteAdeleRing (𝓞 F) F) r + d • a) ⊗ₜ[F] x i : Fin n → RA F E)
      = fv F (algebraMap F E r • x) + d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, algebraMap_smul]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
end GlobalTheory.AdLat
