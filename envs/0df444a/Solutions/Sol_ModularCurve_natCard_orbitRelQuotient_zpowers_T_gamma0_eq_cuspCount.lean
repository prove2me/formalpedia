-- Prove2me | solution 1 for ModularCurve.natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3bddf388-35f0-5c42-82e9-fb98e3928d2b

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount

set_option autoImplicit false

open OnePoint
open scoped MatrixGroups

namespace BassSerreCuspCount

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularCurve ModularCurve.CuspSpace MulAction

theorem eq_T_zpow_or_neg (δ : SL(2, ℤ)) (h : δ 1 0 = 0) :
    ∃ n : ℤ, δ = ModularGroup.T ^ n ∨ δ = -(ModularGroup.T ^ n) := by
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe δ
    rwa [Matrix.det_fin_two] at this
  rw [h, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · refine ⟨δ 0 1, Or.inl ?_⟩
    ext i j
    rw [ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [ha, hd, h]
  · refine ⟨-(δ 0 1), Or.inr ?_⟩
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [ha, hd, h]

theorem mapGL_T_zpow_smul_infty (n : ℤ) :
    mapGL ℚ (ModularGroup.T ^ n) • (∞ : OnePoint ℚ) = ∞ := by
  rw [mapGL_smul_infty, ratPoint_eq_infty_iff]
  show (↑(ModularGroup.T ^ n) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
  rw [ModularGroup.coe_T_zpow]
  simp

variable (N : ℕ)

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp

theorem fromCoset_T_zpow_smul (n : ℤ) (x : SL(2, ℤ) ⧸ Gamma0 N) :
    fromCoset N (ModularGroup.T ^ n • x) = fromCoset N x := by
  induction x using QuotientGroup.induction_on with | H g =>
  show fromCoset N ((ModularGroup.T ^ n * g : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 N) = _
  rw [fromCoset_mk, fromCoset_mk, _root_.mul_inv_rev, map_mul, mul_smul, ← _root_.zpow_neg,
    mapGL_T_zpow_smul_infty]

noncomputable def toCuspSpace :
    orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Gamma0 N) → CuspSpace N :=
  Quotient.lift (fromCoset N) fun x y hxy => by
    obtain ⟨⟨_, n, rfl⟩, rfl⟩ := hxy
    exact fromCoset_T_zpow_smul N n y

theorem toCuspSpace_mk (x : SL(2, ℤ) ⧸ Gamma0 N) :
    toCuspSpace N (Quotient.mk _ x) = fromCoset N x := rfl

theorem toCuspSpace_surjective : Function.Surjective (toCuspSpace N) := by
  intro c
  obtain ⟨x, rfl⟩ := fromCoset_surjective N c
  exact ⟨Quotient.mk _ x, rfl⟩

theorem toCuspSpace_injective : Function.Injective (toCuspSpace N) := by
  intro c c' h
  induction c using Quotient.inductionOn with | h x =>
  induction c' using Quotient.inductionOn with | h y =>
  induction x using QuotientGroup.induction_on with | H g =>
  induction y using QuotientGroup.induction_on with | H g' =>
  change fromCoset N (g : SL(2, ℤ) ⧸ Gamma0 N) = fromCoset N (g' : SL(2, ℤ) ⧸ Gamma0 N) at h
  rw [fromCoset_mk, fromCoset_mk, mk_eq_mk_iff] at h
  obtain ⟨γ, hγ, hγeq⟩ := h

  have hfix : mapGL ℚ (g * γ * g'⁻¹) • (∞ : OnePoint ℚ) = ∞ := by
    rw [map_mul, map_mul, mul_smul, mul_smul, hγeq, ← mul_smul, ← map_mul, mul_inv_cancel,
      map_one, one_smul]
  have h10 : (g * γ * g'⁻¹) 1 0 = 0 := by
    rw [mapGL_smul_infty, ratPoint_eq_infty_iff] at hfix
    exact hfix
  obtain ⟨n, hn⟩ := eq_T_zpow_or_neg (g * γ * g'⁻¹) h10
  apply Quotient.sound
  refine ⟨⟨ModularGroup.T ^ n, n, rfl⟩, ?_⟩
  show ((ModularGroup.T ^ n * g' : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 N) = (g : SL(2, ℤ) ⧸ Gamma0 N)
  have hg : (g : SL(2, ℤ) ⧸ Gamma0 N) = ((g * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 N) := by
    rw [QuotientGroup.eq, inv_mul_cancel_left]
    exact hγ
  rw [hg, QuotientGroup.eq]
  rcases hn with hn | hn
  · have : g * γ = ModularGroup.T ^ n * g' := by rw [← hn, inv_mul_cancel_right]
    rw [this, inv_mul_cancel]
    exact one_mem _
  · have : g * γ = -(ModularGroup.T ^ n) * g' := by rw [← hn, inv_mul_cancel_right]
    rw [this, neg_mul, mul_neg, inv_mul_cancel]
    exact neg_one_mem_Gamma0 N

noncomputable def orbitEquivCuspSpace :
    orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Gamma0 N) ≃ CuspSpace N :=
  Equiv.ofBijective (toCuspSpace N) ⟨toCuspSpace_injective N, toCuspSpace_surjective N⟩

end BassSerreCuspCount

theorem solution (N : ℕ) [NeZero N] :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
        (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N))
      = ModularCurve.cuspCount N := by
  rw [Nat.card_congr (BassSerreCuspCount.orbitEquivCuspSpace N)]
  exact ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount (NeZero.ne N)

#print axioms solution

end S_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount
end P2MW
export P2MW.S_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount (solution)
