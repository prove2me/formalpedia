-- Prove2me | solution 1 for GlobalTheory.SatakeBound.satakeTrivialBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:59.062835+00:00
-- url     : https://prove2.me/submissions/ee83a766-0ab6-4b76-bbfa-b407a79392c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_norm_le_pow
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SatakeBound_Rep_exists_sph
import Theorems.Thm_GlobalTheory_SatakeFlip_exists_isBorelSph_rev_inv
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
namespace GlobalTheory.SatakeBound
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound := by
  intro k _ _ _ _ n V _ _ π α _ _ hu _ hs i
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k).le
  obtain ⟨φ, h, hb⟩ := GlobalTheory.SatakeBound.Rep.exists_sph k n V π α hu hs
  obtain ⟨ψ, h', hb'⟩ := GlobalTheory.SatakeFlip.exists_isBorelSph_rev_inv k n _ φ h hb
  have h1 := norm_le_pow h hb i
  have h2 := norm_le_pow h' hb' i.rev
  have hr : ((i.rev : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℕ) := by
    have := i.2
    rw [Fin.val_rev, Nat.cast_sub (by omega)]; push_cast; ring
  have ha : 0 < ‖(α i : ℂ)‖ := norm_pos_iff.2 (α i).ne_zero
  simp only [Fin.rev_rev, norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _),
    ← Real.rpow_natCast, hr] at h1 h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h1
  rw [inv_le_comm₀ (by positivity) (by positivity), ← div_le_iff₀ (Real.rpow_pos_of_pos hq _),
    ← Real.rpow_neg hq.le, ← Real.rpow_sub hq] at h2
  constructor
  · exact le_of_eq_of_le (congrArg _ (by ring)) h2
  · exact h1.trans_eq (congrArg _ (by ring))
end GlobalTheory.SatakeBound
