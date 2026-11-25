-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.valuation_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:10:46.864673+00:00
-- url     : https://prove2.me/submissions/4e44c367-e277-49a6-b2e3-6742284cd1e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_GlobalTheory_Mass_SameBad_mem_locR_iff
import Theorems.Thm_GlobalTheory_Mass_SameBad_star_mem_locR
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_MassOrth_mem_locR_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hc : conjIdeal (K := K) v.asIdeal = v.asIdeal) (a : K) :
    v.valuation K (star a) = v.valuation K a := by
  have le1 : ∀ a : K, v.valuation K a ≤ 1 → v.valuation K (star a) ≤ 1 := fun a ha =>
    (mem_locR_iff v hc _).1 (star_mem_locR v.isMaximal hc ((mem_locR_iff v hc _).2 ha))
  have mono : ∀ a b : K, b ≠ 0 → v.valuation K a ≤ v.valuation K b →
      v.valuation K (star a) ≤ v.valuation K (star b) := by
    intro a b hb hab
    have hb' : v.valuation K b ≠ 0 := by simpa using hb
    have hb'' : v.valuation K (star b) ≠ 0 := by simpa using hb
    have := le1 (a / b) (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le')
    rw [star_div₀, map_div₀] at this
    exact (div_le_one₀ (zero_lt_iff.2 hb'')).1 this
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have π0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have s0 : v.valuation K (star π) ≠ 0 := by simpa using π0
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v.valuation K (star π) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log s0).symm⟩
  have gen : ∀ (a : K) (m : ℤ), v.valuation K a = WithZero.exp m →
      v.valuation K (star a) = WithZero.exp (-m * n) := by
    intro a m hm
    have a0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hm
      exact WithZero.exp_ne_zero hm.symm
    have e1 : v.valuation K (π ^ (-m)) = v.valuation K a := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, hm]; simp
    have e2 : v.valuation K (star (π ^ (-m))) = WithZero.exp (-m * n) := by
      rw [star_zpow₀, map_zpow₀, hn, ← WithZero.exp_zsmul]; simp
    rw [← e2]
    exact le_antisymm (mono _ _ (zpow_ne_zero _ π0) e1.ge) (mono _ _ a0 e1.le)
  have h1 := gen _ _ hn
  rw [star_star, hπ, WithZero.exp_inj] at h1
  have h2 : n ≤ 0 := by
    have := le1 π (by rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    rwa [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  have h3 : n = -1 := by nlinarith
  rcases eq_or_ne a 0 with rfl | a0
  · simp
  · have : v.valuation K a ≠ 0 := by simpa using a0
    have h4 := gen a _ (WithZero.exp_log this).symm
    rw [h4, h3]; simp [WithZero.exp_log this]
end GlobalTheory.Mass.SameBad
