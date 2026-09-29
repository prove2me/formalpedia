-- Prove2me | solution 1 for ModularCurve.frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/47184fae-a944-5954-81e1-53d2392615e3

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Theorems.Thm_P2M_Dup_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero.ModularCurve AlgebraicCurve HahnSeries IntermediateField"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand_ell_qExpand_jqModC_eq_pow charP_laurentSeriesC frobeniusModL coe_frobeniusModL frobeniusModL_injective exists_frobeniusModL_eq_pow frobeniusModL_isIntegral FrobeniusInputsModL coe_frobeniusDegZeroPullbackModL frobeniusPullbackModL frobeniusPullbackModL_mk frobeniusPullbackModL_of_not modularFunctionFieldFullC jqModCd_mem_full JZeroC jqModC qExpand qExpand_single algebraMap_laurentSeries_eq_single"
p2m_open "ModularCurve"

namespace FrobPullbackTorsion

variable (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (N : ℕ) [NeZero N]

theorem exists_pow_eq_frobeniusModL (x : modularFunctionFieldFullC K N) :
    ∃ y : modularFunctionFieldFullC K N, frobeniusModL K N ℓ x = y ^ ℓ := by
  haveI : CharP (LaurentSeries K) ℓ := charP_laurentSeriesC K ℓ
  suffices h : ∀ {z : LaurentSeries K}, z ∈ modularFunctionFieldFullC K N →
      ∃ y : LaurentSeries K, y ∈ modularFunctionFieldFullC K N ∧ qExpand K ℓ z = y ^ ℓ by
    obtain ⟨y, hy, hyx⟩ := h x.2
    exact ⟨⟨y, hy⟩, Subtype.ext (by rw [coe_frobeniusModL]; push_cast; exact hyx)⟩
  intro z hz
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    exact ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hdvd, qExpand_ell_qExpand_jqModC_eq_pow K ℓ d⟩
  | algebraMap c =>
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c hℓ.out.pos
    refine ⟨algebraMap K (LaurentSeries K) r, (modularFunctionFieldFullC K N).algebraMap_mem _, ?_⟩
    rw [← map_pow, hr, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', hyy⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hz
    exact ⟨y' + z', add_mem hy' hz', by rw [map_add, hyy, hzz, add_pow_char]⟩
  | inv y _ hy =>
    obtain ⟨y', hy', hyy⟩ := hy
    exact ⟨y'⁻¹, inv_mem hy', by rw [map_inv₀, hyy, inv_pow]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨y', hy', hyy⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hz
    exact ⟨y' * z', mul_mem hy' hz', by rw [map_mul, hyy, hzz, mul_pow]⟩

theorem isFrobeniusEndo : IsFrobeniusEndo ℓ (frobeniusModL K N ℓ) :=
  ⟨exists_frobeniusModL_eq_pow K N ℓ, exists_pow_eq_frobeniusModL K ℓ N⟩

variable {K ℓ N}

theorem main (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) : frobeniusPullbackModL K N ℓ x = 0 := by
  classical
  by_cases hinp : FrobeniusInputsModL K N ℓ
  swap
  · rw [frobeniusPullbackModL_of_not hinp]; rfl
  obtain ⟨hP, hfin, hFI, hN⟩ := hinp

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hmk : (Pic0.mk ((ℓ : ℤ) • D) : JZeroC K N) = 0 := by
    rw [Pic0.mk, QuotientAddGroup.mk_zsmul]; exact hx
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hmk
  obtain ⟨f, hf, hDf⟩ := hmk

  obtain ⟨g, hg⟩ := exists_pow_eq_frobeniusModL K ℓ N f
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, zero_pow hℓ.out.ne_zero] at hg
    exact hf (frobeniusModL_injective K N ℓ (by rw [hg, map_zero]))

  rw [frobeniusPullbackModL_mk hfin hFI hN, Pic0.mk, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, coe_frobeniusDegZeroPullbackModL]
  refine ⟨g, hg0, fun w => ?_⟩
  change Divisor.pullbackAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
    (D : Divisor K (modularFunctionFieldFullC K N)) w = w.ord g
  rw [Divisor.pullbackAlong_apply,
    (isFrobeniusEndo K ℓ N).ramificationIndexAlong_eq hℓ.out.ne_zero w]
  have hord := Place.ord_restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) w f
  rw [(isFrobeniusEndo K ℓ N).ramificationIndexAlong_eq hℓ.out.ne_zero w, hg,
    ← zpow_natCast, w.ord_zpow g ℓ] at hord
  have hDf' := hDf (Place.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) w)
  change (ℓ : ℤ) * (D : Divisor K (modularFunctionFieldFullC K N))
    (Place.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) w) = _ at hDf'
  rw [hDf']
  have hℓ0 : ((ℓ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  exact (mul_left_cancel₀ hℓ0 hord).symm

end FrobPullbackTorsion

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero.ModularCurve AlgebraicCurve in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) :
    frobeniusPullbackModL K N ℓ x = 0 :=
  ModularCurve.FrobPullbackTorsion.main x hx

end S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
end P2MW
export P2MW.S_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero (solution)
