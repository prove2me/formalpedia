-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.toMatrix_basis_dualBasis_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:41.25637+00:00
-- url     : https://prove2.me/submissions/aa8e1cf9-1285-467c-880b-32f3f02a62a2

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
import Theorems.Thm_GlobalTheory_UnitaryStd_form_basis_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.UnitaryStd
namespace GlobalTheory.UnitaryStd
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) :
    LinearMap.toMatrix (basis ρ g) (basis ρ g).dualBasis (form ρ g S) =
      Matrix.kroneckerMap (· * ·) S.transpose (Matrix.J (Fin g) ℤ) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr, form_basis_basis]
  rfl
end GlobalTheory.UnitaryStd
