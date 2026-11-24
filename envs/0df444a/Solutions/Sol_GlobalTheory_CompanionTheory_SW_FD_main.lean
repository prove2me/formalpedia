-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:33.015712+00:00
-- url     : https://prove2.me/submissions/a549758c-cf8c-41ec-9f39-dc8ea1af52d9

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_latR_eq_range
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_mem_latR_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_card_places
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_exists_integral_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_exists_real_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_integral_char_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ N : ℕ, 0 < N → (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume) ∧ Countable (latR ρ N) ∧ (∀ y, y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))) ∧ ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹) ∧ ∀ β : F, β ≠ 0 → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  intro F _ _ hF ρ hρ N hN
  classical
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis hF ρ hρ
  set M : Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
    Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F) with hM
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdisc : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hdet : M.det ≠ 0 := by
    intro h
    apply hdisc
    rw [← hB, h]
    simp
  have hAdet : ((N : ℝ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hN') hdet
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_real_basis _ hAdet
  have hbi : ∀ i, b i = GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N (B i) := by
    intro i
    rw [hb]
    ext w
    simp [GlobalTheory.CompanionTheory.SW.FD.scaleMap, hM]
  have hspan : latR ρ N = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range, Submodule.span_int_eq_addSubgroupClosure]
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      rw [← B.sum_repr r, map_sum]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← hbi]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B i, (hbi i).symm⟩
  have hfd : IsAddFundamentalDomain (latR ρ N) (ZSpan.fundamentalDomain b) volume := by
    rw [hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hcount : Countable (latR ρ N) := by
    haveI : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range]
    exact (Set.countable_range (GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N)).to_subtype
  refine ⟨⟨_, hfd⟩, hcount, GlobalTheory.CompanionTheory.SW.FD.mem_latR_iff ρ N, fun D hD => ⟨?_, fun β hβ hint =>
    GlobalTheory.CompanionTheory.SW.FD.integral_char_eq_zero hF ρ hρ N D hD β hβ hint⟩⟩
  rw [hD.measure_eq hfd, ZSpan.volume_fundamentalDomain]
  have hof : Matrix.of (b : InfinitePlace F → InfinitePlace F → ℝ) = (N : ℝ) • M := by
    ext i w
    rw [Matrix.of_apply, hb]
  rw [hof, Matrix.det_smul, GlobalTheory.CompanionTheory.SW.FD.card_places hF, abs_mul, abs_of_nonneg (by positivity)]
  congr 2
  rw [kap, inv_inv, ← hB, abs_of_nonneg (sq_nonneg M.det), Real.sqrt_sq_eq_abs]
end GlobalTheory.CompanionTheory.SW.FD
