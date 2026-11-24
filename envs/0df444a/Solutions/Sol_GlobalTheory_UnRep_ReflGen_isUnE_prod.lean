-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflGen.isUnE_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:07.132854+00:00
-- url     : https://prove2.me/submissions/6dabaab5-2dc9-4570-9a09-3a2c7c161802

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_isUnE_mul
import Theorems.Thm_GlobalTheory_T_unitaryQuasiReflection_laws


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
namespace GlobalTheory.UnRep.ReflGen
theorem _root_.solution (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    IsUnE c G (l.map fun p => refl c G p.1 p.2).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isUnE_mul ((GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).2.2.2 p.2 hp.2)
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
end GlobalTheory.UnRep.ReflGen
