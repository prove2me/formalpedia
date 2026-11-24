-- Prove2me | solution 1 for GlobalTheory.InertZeta.latIndex_of_smith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:11.057994+00:00
-- url     : https://prove2.me/submissions/b69576ca-c5e2-49a9-840b-9aee117b42b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
import Theorems.Thm_GlobalTheory_InertZeta_intV_vecMul
import Theorems.Thm_GlobalTheory_InertZeta_latIndex_diagonal
import Theorems.Thm_GlobalTheory_InertZeta_relIndex_preLat_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_v_det_eq_one
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : Smith → LatIndex := by
  intro hS L _ _ ϖ σ q n hU A k hA hdet
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hA0 : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hdet; exact WithZero.exp_ne_zero hdet.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hv A hA0
  set D := Matrix.diagonal fun i => ϖ ^ d i with hD
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb2 : b' * b = 1 := mul_eq_one_comm.1 eb

  have hDint : IsInt D := by
    have : D = a' * (a * D * b) * b' := by
      rw [show a' * (a * D * b) * b' = (a' * a) * D * (b * b') by simp only [Matrix.mul_assoc], ea, eb,
        Matrix.one_mul, Matrix.mul_one]
    rw [this]
    exact (ha'.mul hA).mul hb'
  have hvz : ∀ z : ℤ, Valued.v (ϖ ^ z) = WithZero.exp (-z) := fun z => by
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]; congr 1; simp
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hDint i i
    rw [hD, Matrix.diagonal_apply_eq] at h
    have h' : Valued.v (ϖ ^ d i) ≤ 1 := h
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at h'
    omega
  set e : Fin n → ℕ := fun i => (d i).toNat with he
  have hde : ∀ i, d i = (e i : ℤ) := fun i => (Int.toNat_of_nonneg (hd i)).symm
  have hDe : D = Matrix.diagonal fun i => ϖ ^ e i := by
    rw [hD]; congr 1; funext i; rw [hde i, zpow_natCast]

  have hk : k = ∑ i, e i := by
    have hva : Valued.v a.det = 1 := v_det_eq_one ha ha' ea2
    have hvb : Valued.v b.det = 1 := v_det_eq_one hb hb' eb
    rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hva, hvb, one_mul, mul_one, hDe,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← zpow_natCast, hvz, WithZero.exp_inj] at hdet
    exact_mod_cast (neg_inj.1 hdet).symm

  have hpre : ∀ r, r ∈ preLat (a * D * b) ↔ r ᵥ* a ∈ preLat D := fun r => by
    show r ᵥ* (a * D * b) ∈ intV L n ↔ (r ᵥ* a) ᵥ* D ∈ intV L n
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    refine ⟨fun h => ?_, fun h => intV_vecMul h hb⟩
    have := intV_vecMul h hb'
    rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this
  rw [relIndex_preLat_mul ha ha' ea hpre, hDe, latIndex_diagonal hU, hk]
end GlobalTheory.InertZeta
