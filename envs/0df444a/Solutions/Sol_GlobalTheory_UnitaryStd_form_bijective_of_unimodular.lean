-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.form_bijective_of_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:26:03.819917+00:00
-- url     : https://prove2.me/submissions/9d4b2375-f271-4188-936d-fc3ee8793f38

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
import Theorems.Thm_GlobalTheory_UnitaryStd_toMatrix_basis_dualBasis_form

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
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  intro E _ _ r ρ g S hS
  set b := basis ρ g
  set M := LinearMap.toMatrix b b.dualBasis (form ρ g S) with hMdef
  have hM : IsUnit M.det := by
    rw [hMdef, toMatrix_basis_dualBasis_form, Matrix.det_kronecker, Matrix.det_transpose]
    exact (hS.pow _).mul ((Matrix.isUnit_det_J (Fin g) ℤ).pow _)
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hf : form ρ g S = Matrix.toLin b b.dualBasis M := by rw [hMdef, Matrix.toLin_toMatrix]
  set Ψ := Matrix.toLin b.dualBasis b M⁻¹
  have hl : ∀ x, Ψ (form ρ g S x) = x := fun x => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h2, Matrix.toLin_one, LinearMap.id_apply]
  have hr : ∀ f, form ρ g S (Ψ f) = f := fun f => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h1, Matrix.toLin_one, LinearMap.id_apply]
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
end GlobalTheory.UnitaryStd
