-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.cosetInj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:38.436211+00:00
-- url     : https://prove2.me/submissions/7ed5888e-46bf-4fc4-8aad-63e403a1930f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_rad_levi_rad_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_levi_mul_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_levi_mul_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_levi_mul_mid
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
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
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hk
  obtain ⟨-, hσ, hσϖ, hϖ, -, -, -⟩ := hU
  obtain ⟨hl, h0, h1, h2⟩ := hm
  obtain ⟨hl', h0', h1', h2'⟩ := hm'
  have hli : m⁻¹ ∈ leviU σ (blk N) := inv_mem hl
  have hp : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hli hl'
  have e : (m * u)⁻¹ * (m' * u') = u⁻¹ * (m⁻¹ * m') * u' := by group
  rw [e] at hk
  have hint : ∀ i j, blk N j ≤ blk N i → mat (m⁻¹ * m') i j ∈ intL L := fun i j hij => by
    rw [← rad_levi_rad_apply (inv_mem hu) hp hu' hij]
    exact (mem_KU_iff hσ _).1 hk i j
  have e0 : mat (m⁻¹ * m') 0 0 = ϖ ^ (a' - a) := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_zero hli, mat_inv_apply, Fin.rev_zero, h1, h0', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have e1 : mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_last hli, mat_inv_apply, Fin.rev_last, h0, h1', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have hv0 : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
  have hv1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    exact WithZero.coe_lt_one.2 (by decide)
  have i0 : Valued.v ϖ ^ (a' - a) ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') 0 0) ≤ 1 := hint 0 0 le_rfl
    rwa [e0, map_zpow₀] at this
  have i1 : Valued.v ϖ ^ (a - a') ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 :=
      hint _ _ (le_refl (blk N (Fin.last (N + 1))))
    rwa [e1, map_zpow₀] at this
  rw [zpow_le_one_iff_right_of_lt_one₀ hv0 hv1] at i0 i1
  refine ⟨by omega, (mem_KU_iff hσ _).2 fun i j => ?_⟩
  have := hint (mid i) (mid j) (by simp)
  have e2 : ∀ i j, mat m⁻¹ (mid i) (mid j) = mat g₀⁻¹ i j := fun i j => by
    rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, h2]
  rw [levi_mul_mid hli] at this
  simp only [e2, h2'] at this
  rw [mat_mul, Matrix.mul_apply]
  exact this
end GlobalTheory.CompanionTheory.InertZeta
