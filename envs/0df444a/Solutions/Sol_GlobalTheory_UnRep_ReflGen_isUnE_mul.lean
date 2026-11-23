-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflGen.isUnE_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:30.854827+00:00
-- url     : https://prove2.me/submissions/6f2cfd32-34fc-40be-9d7c-0daa57a76be2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
omit [NumberField F] [NumberField E]
namespace GlobalTheory.UnRep.ReflGen
theorem _root_.solution {a b : Matrix (Fin n) (Fin n) E} (ha : IsUnE c G a) (hb : IsUnE c G b) :
    IsUnE c G (a * b) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
end GlobalTheory.UnRep.ReflGen
