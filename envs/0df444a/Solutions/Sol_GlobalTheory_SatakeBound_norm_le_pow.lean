-- Prove2me | solution 1 for GlobalTheory.SatakeBound.norm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:58.407491+00:00
-- url     : https://prove2.me/submissions/1d908c38-3576-4020-9cb8-b4a6059e6497

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
import Theorems.Thm_GlobalTheory_SatakeBound_exists_cosets_sum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_norm_le_of_completeHomogeneous_le
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SatakeBound_isBorelSph_one
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (h : IsBorelSph k γ φ) (hb : HasBoundedSums k φ)
    (i : Fin n) : ‖γ i‖ ≤ (resCard k : ℝ) ^ (i : ℕ) := by
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have key := GlobalTheory.CompleteHomogeneousBound.norm_le_of_completeHomogeneous_le n (fun i => (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i)
    (fun i => (resCard k : ℝ) ^ (n - 1 - (i : ℕ))) ((resCard k : ℝ) ^ (n - 1)) (fun _ => by positivity)
    (fun i => pow_le_pow_right₀ hq.le (Nat.sub_le _ _)) (fun m => by
      obtain ⟨S, hS, hs⟩ := exists_cosets_sum k n m
      have h1 := hs _ _ (isBorelSph_one k)
      rw [← hs γ φ h]
      refine (hb S hS).trans (le_of_eq ?_)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
      exact_mod_cast h1) i
  have hi : n - 1 = (n - 1 - (i : ℕ)) + i := by have := i.2; omega
  rw [norm_mul, norm_pow, Complex.norm_natCast] at key
  conv_rhs at key => rw [hi, pow_add]
  exact le_of_mul_le_mul_left key (by positivity)
end GlobalTheory.SatakeBound
