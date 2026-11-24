-- Prove2me | solution 1 for GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:10.370123+00:00
-- url     : https://prove2.me/submissions/00ce3214-5cb2-4341-a9f0-1954cb1de49b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Theorems.Thm_GlobalTheory_UnRep_exists_refl_prod_mulVec_eq


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  first | exact @GlobalTheory.UnRep.exists_refl_prod_mulVec_eq | exact GlobalTheory.UnRep.exists_refl_prod_mulVec_eq | (intros; apply GlobalTheory.UnRep.exists_refl_prod_mulVec_eq <;> assumption)
end _root_.GlobalTheory.T
