-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.normUnit_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:25.233931+00:00
-- url     : https://prove2.me/submissions/e73a650e-2012-4a15-bf13-d5bb57e9218e

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
import Theorems.Thm_GlobalTheory_Mass_SameBad_valuation_star
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
    (hc : conjIdeal (K := K) v.asIdeal = v.asIdeal) {x : K} {m : ℤ}
    (hx : v.valuation K x = WithZero.exp m) : NormUnit v.asIdeal x ↔ Even m := by
  have key : ∀ (c : K) (k : ℤ), v.valuation K c = WithZero.exp k →
      v.valuation K (star c * c * x) = WithZero.exp (k + k + m) := by
    intro c k hk
    rw [map_mul, map_mul, valuation_star v hc, hk, hx, WithZero.exp_add, WithZero.exp_add]
  constructor
  · rintro ⟨c, c0, h1, h2⟩
    have : v.valuation K c ≠ 0 := by simpa using c0
    have e := key c _ (WithZero.exp_log this).symm
    rw [mem_locR_iff v hc] at h1 h2
    rw [map_inv₀, e, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact ⟨-(WithZero.log (v.valuation K c)), by omega⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    have π0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have e1 : v.valuation K (π ^ k) = WithZero.exp (-k) := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]; simp
    have e := key _ _ e1
    have e0 : -k + -k + (k + k) = 0 := by ring
    rw [e0, WithZero.exp_zero] at e
    refine ⟨π ^ k, zpow_ne_zero _ π0, ?_, ?_⟩
    · rw [mem_locR_iff v hc, e]
    · rw [mem_locR_iff v hc, map_inv₀, e, inv_one]
end GlobalTheory.Mass.SameBad
