-- Prove2me | solution 1 for GlobalTheory.UnRep.isUnE_eq_prod_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:11.987968+00:00
-- url     : https://prove2.me/submissions/f66c67a7-9d25-4f22-bfcb-449cd2da6a59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_exists_inv
import Theorems.Thm_GlobalTheory_UnRep_ReflGen_exists_fix
import Theorems.Thm_GlobalTheory_T_exists_anisotropic_orthogonal_basis_hermitian


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
namespace GlobalTheory.UnRep
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  intro F E _ _ _ _ _ c n G hG γ hγ
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian F E c n G hG
  obtain ⟨l, hl, hfix⟩ := ReflGen.exists_fix hG hγ x h1 h2 n
  obtain ⟨l', hl', hinv⟩ := ReflGen.exists_inv hG l hl
  refine ⟨l', hl', ?_⟩
  have hone : (l.map fun p => refl c G p.1 p.2).prod * γ = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range h3 fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
  rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
end GlobalTheory.UnRep
