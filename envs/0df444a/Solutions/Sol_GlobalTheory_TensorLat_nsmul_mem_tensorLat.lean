-- Prove2me | solution 1 for GlobalTheory.TensorLat.nsmul_mem_tensorLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:43:19.916049+00:00
-- url     : https://prove2.me/submissions/da40beeb-3330-4425-a0df-048aa4473a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_TensorLat_actE_natCast
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat_iff_herm
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_stdLat_fg
import Theorems.Thm_GlobalTheory_TensorLat_sum_tens_single
import Theorems.Thm_GlobalTheory_TensorLat_tens_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


section
namespace GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
private lemma tens_nsmul (x : Vsp dim) (v : Fin n → E) (N : ℕ) :
    tens x (N • v) = N • tens x v := by
  rw [← Nat.cast_smul_eq_nsmul E N v, tens_smul_right, actE_natCast]
  funext k
  simp only [tens_apply, Pi.smul_apply]
  rw [← actL_apply, map_nsmul, actL_apply]
example (X : PT E) (φ : tensorLat X (stdLat E n) →+ ℤ) :
    ∃ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) ∧ ∀ γ' : tensorLat X (stdLat E n),
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im := by
  obtain ⟨γ, hγ, h⟩ := exists_im_HC_eq stdLat_fg (fun _ hx => mem_stdLat_iff_herm.1 hx)
    (fun _ hx => mem_stdLat_iff_herm.2 hx) φ
  exact ⟨γ, mem_tensorLat_stdLat.1 hγ, h⟩
end GlobalTheory.TensorLat
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
namespace GlobalTheory.TensorLat
theorem _root_.solution (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {N : ℕ}
    (hN : ∀ u ∈ stdLat E n, N • u ∈ Λ') {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    N • γ ∈ tensorLat X Λ' := by
  have hs : ∀ k, N • (Pi.single k (1 : E) : Fin n → E) ∈ Λ' := fun k =>
    hN _ (mem_stdLat.2 fun j => by
      by_cases hjk : j = k <;> simp [hjk, isIntegral_one, isIntegral_zero])
  have heq : N • γ = ∑ k, tens (γ k) (N • (Pi.single k (1 : E) : Fin n → E)) := by
    conv_lhs => rw [← sum_tens_single γ]
    rw [Finset.smul_sum]
    simp_rw [tens_nsmul]
  rw [heq]
  exact Submodule.sum_mem _ fun k _ => tens_mem_of_integral hint (hγ k) (hs k)
end GlobalTheory.TensorLat
