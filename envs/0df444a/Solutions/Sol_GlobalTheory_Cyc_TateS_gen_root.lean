-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.gen_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:55.414077+00:00
-- url     : https://prove2.me/submissions/0ad3fa4d-e3db-44f4-8a98-1e6e36ad6f74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_root_mem
import Theorems.Thm_GlobalTheory_Cyc_TateS_Gj_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (hχ : IsCyc χ) (K : FinExt l) {i : ℕ} {g : GQ l} (hg : IsGen χ K i g) {z : Om l}
    (hz : IsPrimitiveRoot z (l ^ (i + 1))) : ∃ η : Om l, IsPrimitiveRoot η l ∧ g z = η * z := by
  have hp : l.Prime := Fact.out
  have hz0 : z ≠ 0 := hz.ne_zero (pow_ne_zero _ hp.ne_zero)
  have h1 : g (z ^ l) = z ^ l :=
    Gj_fix K hg.1 (root_mem K (by rw [← pow_mul, ← pow_succ', hz.pow_eq_one]))
  have h2 : (g z / z) ^ l = 1 := by
    rw [div_pow, ← map_pow, h1, div_self (pow_ne_zero _ hz0)]
  have h3 : g z / z ≠ 1 := by
    intro h
    have hgz : g z = z := by rwa [div_eq_one_iff_eq hz0] at h
    obtain ⟨a, ha, hga⟩ := hχ g (i + 1) z hz.pow_eq_one
    have h4 : z ^ ((a : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hz0, zpow_natCast, ← hga, hgz, zpow_one, div_self hz0]
    rw [hz.zpow_eq_one_iff_dvd] at h4
    have h5 := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) (i + 1)).2 (by exact_mod_cast h4)
    have h6 : ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((i + 1 : ℕ) : ℤ)) := by
      have : (χ g : ℚ_[l]) - 1 = ((χ g : ℚ_[l]) - a) + (((a : ℤ) - 1 : ℤ) : ℚ_[l]) := by
        push_cast; ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha h5)
    rw [hg.2] at h6
    have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
    rw [zpow_le_zpow_iff_right₀ hl] at h6
    push_cast at h6
    omega
  refine ⟨g z / z, ?_, (div_mul_cancel₀ _ hz0).symm⟩
  have := orderOf_eq_prime h2 h3
  have h7 := IsPrimitiveRoot.orderOf (g z / z)
  rwa [this] at h7
end GlobalTheory.Cyc.TateS
