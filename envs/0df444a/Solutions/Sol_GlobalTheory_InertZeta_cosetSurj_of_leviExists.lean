-- Prove2me | solution 1 for GlobalTheory.InertZeta.cosetSurj_of_leviExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:10.468256+00:00
-- url     : https://prove2.me/submissions/a18907cf-f347-4a4d-94c7-b1ea00acffdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCosetSurjOfLeviElementExists
import Theorems.Thm_GlobalTheory_InertZeta_rev_zero_eq_last
import Theorems.Thm_GlobalTheory_InertZeta_rev_last_eq_zero
import Theorems.Thm_GlobalTheory_InertZeta_blk_rev_of_eq
import Theorems.Thm_GlobalTheory_InertZeta_lt_of_blk_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_P_fIwasawa_iwasawa
import Theorems.Thm_Formalism_UG_P_fSatake_K_int
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ
import Theorems.Thm_Formalism_UG_P_fSatake_unit_diag
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
import Theorems.Thm_GlobalTheory_SatakeWeyl_leviPart
import Theorems.Thm_GlobalTheory_SatakeWeyl_leviRad
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_inv_apply
import Theorems.Thm_GlobalTheory_SatakeWeyl_mem_KU_iff
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
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : LeviExists → CosetSurj := by
  intro _ L _ _ ϖ σ q N hU g
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hσσ hσv g
  have hbT : (mat b).BlockTriangular (blk N) := fun i j h => hb i j (lt_of_blk_lt h)
  obtain ⟨m', hm'L, hm'e, hu'⟩ := leviPart L σ (N + 2) (blk N) blk_rev_of_eq b hbT
  set M₀ : Matrix (Fin N) (Fin N) L := Matrix.of fun i j => mat m' (mid i) (mid j) with hM₀
  have hM₀U : cT σ M₀ * antiJ L N * M₀ = antiJ L N := by
    have h1 : cT σ (mat m') * antiJ L (N + 2) * mat m' = antiJ L (N + 2) := m'.2
    ext i j
    have h2 := congrFun (congrFun h1 (mid i)) (mid j)
    rw [Matrix.mul_apply, sum_idx] at h2
    have e0 : mat m' 0 (mid j) = 0 := hm'L _ _ (by simp)
    have eL : mat m' (Fin.last (N + 1)) (mid j) = 0 := hm'L _ _ (by simp)
    rw [e0, eL, mul_zero, mul_zero, zero_add, add_zero] at h2
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      simp only [antiJ]
      exact if_congr (by simp only [val_mid]; omega) rfl rfl
    rw [hJ] at h2
    rw [← h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [P.fSatake_cTJ, P.fSatake_cTJ, ← mid_rev]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_mat M₀ hM₀U
  obtain ⟨⟨k₀, hk₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g₀
  have hxL : σ (mat m' 0 0) * mat m' (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
    rw [hm'e 0 0 rfl, hm'e _ _ rfl]
    have := P.fSatake_unit_diag hb 0
    rwa [rev_zero_eq_last] at this
  have hx0 : mat m' 0 0 ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hxL; exact zero_ne_one hxL
  have hvx0 : Valued.v (mat m' 0 0) ≠ 0 := by simpa using hx0
  have hvx : Valued.v (mat m' 0 0) = WithZero.exp (-(-(Valued.v (mat m' 0 0)).log)) := by
    rw [neg_neg, WithZero.exp_log hvx0]
  refine ⟨-(Valued.v (mat m' 0 0)).log, (g₀ : GU σ N ⧸ KU σ N), fun m hm => ?_⟩
  obtain ⟨hmL, hm0, hmLL, hmM⟩ := hm
  generalize -(Valued.v (mat m' 0 0)).log = a at hvx hm0 hmLL
  have hmiL : m⁻¹ ∈ leviU σ (blk N) := inv_mem hmL
  have hcL : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hmiL hm'L
  have hcK : m⁻¹ * m' ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hσv]
    intro i j
    by_cases hij : blk N i = blk N j
    swap
    · rw [hcL i j hij]; exact zero_mem _
    rw [mat_mul, Matrix.mul_apply, sum_idx]
    rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp at hij
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL 0 (mid l) (by simp), zero_mul]),
        hmiL 0 (Fin.last _) (by simp), zero_mul, add_zero, add_zero, mat_inv_apply, rev_zero_eq_last, hmLL,
        map_zpow₀, hσϖ]
      rw [intL, Valuation.mem_integer_iff]
      rw [map_mul, map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_add,
        show (-a) • (-1 : ℤ) + -a = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
    · rw [hmiL (mid i) 0 (by simp), zero_mul, zero_add, hmiL (mid i) (Fin.last _) (by simp), zero_mul, add_zero]
      have e : ∑ l, mat m⁻¹ (mid i) (mid l) * mat m' (mid l) (mid j) = mat ((g₀ * k₀)⁻¹ * g₀) i j := by
        rw [mat_mul, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, hmM, hout, hg₀]
        rfl
      rw [e, show (g₀ * k₀)⁻¹ * g₀ = k₀⁻¹ by group]
      exact P.fSatake_K_int (inv_mem hk₀) i j
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL (Fin.last _) (mid l) (by simp), zero_mul]),
        hmiL (Fin.last _) 0 (by simp), zero_mul, zero_add, zero_add, mat_inv_apply, rev_last_eq_zero, hm0,
        map_zpow₀, hσϖ, eq_inv_of_mul_eq_one_right hxL, intL, Valuation.mem_integer_iff, map_mul, map_inv₀, hσv,
        map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add,
        show a • (-1 : ℤ) + -(-a) = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
  obtain ⟨hr, -⟩ := leviRad L σ (N + 2) (blk N) hσv (m⁻¹ * m') hcL (m'⁻¹ * b) hu'
  exact ⟨(m⁻¹ * m') * (m'⁻¹ * b) * (m⁻¹ * m')⁻¹, hr, (m⁻¹ * m') * k, mul_mem hcK hk, by group⟩
end GlobalTheory.InertZeta
