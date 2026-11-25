-- Prove2me | solution 1 for GlobalTheory.TensorLat.nsmul_apply_mem_of_mem_tensorLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:34.246151+00:00
-- url     : https://prove2.me/submissions/1dcbe4f7-efe0-48bb-8da0-48717d0dce43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_TensorLat_actE_natCast
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat
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



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
namespace GlobalTheory.TensorLat
theorem _root_.solution {N : ℕ} (hN : ∀ u ∈ stdLat E n, N • u ∈ Λ')
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (k : Fin n) : (N • γ) k ∈ X.L := by
  have h1 : N • (Pi.single k (1 : E) : Fin n → E) ∈ Λ' :=
    hN _ (mem_stdLat.2 fun j => by
      by_cases hjk : j = k <;> simp [hjk, isIntegral_one, isIntegral_zero])
  have h2 := mem_tensorLat.1 hγ _ h1
  rw [← Nat.cast_smul_eq_nsmul E N (Pi.single k (1 : E) : Fin n → E), contr_smul_right,
    contr_single] at h2
  have hcc : cc (N : E) = N := by
    unfold cc
    exact map_natCast _ N
  rw [hcc, actE_natCast] at h2
  exact h2
end GlobalTheory.TensorLat
