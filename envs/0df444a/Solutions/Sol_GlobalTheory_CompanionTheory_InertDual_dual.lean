-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDual.dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:59:22.932709+00:00
-- url     : https://prove2.me/submissions/a53e6d32-e453-4176-8518-16ce34a9c4d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_antiJ_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_antiJ_mul_self
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_isInt_antiJ
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_cT_add
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_isInt_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_iff_of_inverse
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDual
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertDual
theorem _root_.solution : Dual := by
  unfold GlobalTheory.InertZeta.Dual
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσv, -, -, -, -, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hAi, hUVC⟩ := hF
  have hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N := g.2
  have hJJ : antiJ L N * antiJ L N = 1 := antiJ_mul_self
  have hJi : IsInt (antiJ L N) := isInt_antiJ
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  have hsub : ∀ {X Y : Matrix (Fin N) (Fin N) L}, IsInt X → IsInt Y → IsInt (X - Y) :=
    fun hX hY i j => sub_mem (hX i j) (hY i j)
  have hcTmul : ∀ X Y : Matrix (Fin N) (Fin N) L, cT σ (X * Y) = cT σ Y * cT σ X := by
    intro X Y
    simp [cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcTone : cT σ (1 : Matrix (Fin N) (Fin N) L) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have hGJ : mat g * antiJ L N * cT σ (mat g) = antiJ L N := by
    have h1 : (antiJ L N * cT σ (mat g) * antiJ L N) * mat g = 1 := by
      rw [show antiJ L N * cT σ (mat g) * antiJ L N * mat g
          = antiJ L N * (cT σ (mat g) * antiJ L N * mat g) by simp only [Matrix.mul_assoc], hg, hJJ]
    have h2 := mul_eq_one_comm.mp h1
    calc mat g * antiJ L N * cT σ (mat g)
        = mat g * (antiJ L N * cT σ (mat g) * antiJ L N) * antiJ L N := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = antiJ L N := by rw [h2, Matrix.one_mul]
  have hCUV : C * (U + V * mat g) = 1 := mul_eq_one_comm.mp hUVC
  have hCUV' : C * U + C * V * mat g = 1 := by
    rw [Matrix.mul_assoc C V, ← Matrix.mul_add]
    exact hCUV
  have hED : (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N) = 1 := by
    calc (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N)
        = antiJ L N * cT σ (C * (U + V * mat g)) * antiJ L N := by
          rw [hcTmul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCUV, hcTone, Matrix.mul_one, hJJ]
  have hD : IsInt (cT σ C * antiJ L N) := (isInt_cT hσv hCi).mul hJi
  have hDg : IsInt (cT σ (mat g * C) * antiJ L N) := (isInt_cT hσv hAi).mul hJi
  have he : cT σ C * antiJ L N
      = cT σ (mat g * C) * antiJ L N * (mat g * C * U) + cT σ C * antiJ L N * (C * V * mat g) := by
    have h1 : cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U) = cT σ C * antiJ L N * (C * U) := by
      calc cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U)
          = cT σ C * (cT σ (mat g) * antiJ L N * mat g) * (C * U) := by simp only [Matrix.mul_assoc]
        _ = cT σ C * antiJ L N * (C * U) := by rw [hg]
    rw [hcTmul, h1, ← Matrix.mul_add, hCUV', Matrix.mul_one]
  have hcTU : IsInt (cT σ U) := isInt_cT hσv hUi
  have hcTV : IsInt (cT σ V) := isInt_cT hσv hVi
  have hQE : IsInt (C * V * mat g * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCVG : C * V * mat g = 1 - C * U := eq_sub_of_add_eq' hCUV'
    have h2 : C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V)) = C * V * (antiJ L N * cT σ V) := by
      calc C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V))
          = C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h2, hCVG, Matrix.sub_mul, Matrix.one_mul]
    exact (hsub (hJi.mul hcTU) ((hCi.mul hUi).mul (hJi.mul hcTU))).add ((hCi.mul hVi).mul (hJi.mul hcTV))
  have hRE : IsInt (mat g * C * U * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCU : C * U = 1 - C * V * mat g := eq_sub_of_add_eq hCUV'
    have hA : mat g * (antiJ L N * cT σ (mat g)) * cT σ V = antiJ L N * cT σ V := by
      rw [← Matrix.mul_assoc (mat g) (antiJ L N), hGJ]
    have hB : mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
        = mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
          = mat g * C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    have h3 : mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
        = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
          = mat g * (C * U) * (antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * (1 - C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V := by rw [hCU]
        _ = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, hA, hB]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h3]
    exact ((hAi.mul hUi).mul (hJi.mul hcTU)).add (hsub (hJi.mul hcTV) ((hAi.mul hVi).mul (hJi.mul hcTV)))
  have hJb : antiJ L N *ᵥ b = fun k => b k.rev := funext (antiJ_mulVec b)
  have hσvec : ∀ j, σ (vecMul r C j) = -((cT σ C * antiJ L N) *ᵥ b) j := by
    intro j
    rw [← Matrix.mulVec_mulVec, hJb]
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul, hr, map_neg, hσσ, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hL : ∀ j, (t * vecMul r C j ∈ intL L ↔ t * ((cT σ C * antiJ L N) *ᵥ b) j ∈ intL L) := by
    intro j
    rw [hmem, hmem, Valuation.map_mul, Valuation.map_mul, ← hσv (vecMul r C j), hσvec j, Valuation.map_neg]
  have key := iff_of_inverse (D := cT σ C * antiJ L N) (E := antiJ L N * cT σ (U + V * mat g))
    (Q := C * V * mat g) (R := mat g * C * U) (Dg := cT σ (mat g * C) * antiJ L N)
    hED hQE hRE hDg hD he (t • b)
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at key
  rw [forall_congr' hL]
  exact key
end GlobalTheory.CompanionTheory.InertDual
