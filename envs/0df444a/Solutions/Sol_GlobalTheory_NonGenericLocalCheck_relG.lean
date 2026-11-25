-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.relG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:29.961915+00:00
-- url     : https://prove2.me/submissions/5d00e736-88ef-4b5c-b2a2-782d7193183b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_theta_ne
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_theta_some
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_unit_some
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_D0
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_D1
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable (M) (m : ℕ)
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution [CharZero F] : (pair M m).RelG (theta M) := by
  haveI : Nontrivial E := by
    by_contra hE
    rw [not_nontrivial_iff_subsingleton] at hE
    have h2 := M.L.rank
    rw [Module.finrank_zero_of_subsingleton] at h2
    norm_num at h2
  have hθ := theta_ne M
  have hd1 : (pair M m).Dm 1 = 1 := D1 M m
  have hd0 : (pair M m).Dm 0 = 1 := D0 M m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨h1, h2⟩ := hx
    simp only [HermSp.Xp, pair, frame, Set.range_const, Submodule.mem_span_singleton] at h1 h2
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hc := congrFun hb 1
    simp only [Pi.smul_apply, smul_eq_mul, vec_one, map_zero, mul_zero] at hc
    have hu : IsUnit (algebraMap F E (theta M)) := (isUnit_iff_ne_zero.mpr hθ).map _
    have hb0 : b = 0 := (hu.mul_left_eq_zero).mp hc
    rw [Submodule.mem_bot, ← hb, hb0, zero_smul]
  · change IsUnit ((pair M m).Dm 1)
    rw [hd1]
    exact isUnit_one
  · have hG : (pair M m).Gv = -algebraMap F E (theta M * theta M) := by
      simp only [FPair.Dm] at hd1 hd0
      simp only [FPair.Gv, HermSp.Gdet, HermSp.normE, zero_add, hd1, hd0, map_one, mul_one]
      simp only [pair, frame, map_mul, map_neg, map_add, map_one, mul_zero, add_zero]
      ring
    rw [hG, neg_ne_zero]
    exact (map_ne_zero _).mpr (mul_ne_zero hθ hθ)
  · intro l hl
    interval_cases l
    · exact Or.inr (by rw [hd0]; exact isUnit_one)
    · exact Or.inr (by rw [hd1]; exact isUnit_one)
  · intro g _
    simp [FrameD.psiN, FrameD.psiOf, FrameD.coefSum]
  · refine ⟨⟨[(1, 1)], by simp⟩, fun a b => ?_⟩
    fin_cases a
    fin_cases b
    simp [Pt.mat, ptEntryL, HermSp.Zhat, pair, frame, h_vec]
  · have hT : (1 + theta M * theta M) ≠ 0 := by
      rcases h : M.split with _ | g
      · have e : theta M = 1 := by simp only [theta, h]
        rw [e]
        norm_num
      · obtain ⟨v, hv⟩ := unit_some M g
        rw [theta_some M h]
        intro h0
        rw [h0, neg_zero, mul_zero] at hv
        exact zero_ne_one hv
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · change -(1 + (0 : F) * 0) ∈ 𝒪[F]
      exact neg_mem (add_mem (one_mem _) (mul_mem (zero_mem _) (zero_mem _)))
    · change -(1 + (0 : F) * 0) ≠ 0
      norm_num
    · change -(1 + theta M * theta M) ∈ 𝒪[F]
      exact neg_mem (add_mem (one_mem _) (mul_mem (theta_int M) (theta_int M)))
    · change -(1 + theta M * theta M) ≠ 0
      exact neg_ne_zero.mpr hT
    · obtain ⟨v, hv⟩ := unit_some M g
      refine ⟨-1, v, ?_, ?_⟩
      · change ((-1 : 𝒪[F]) : F) * -(1 + (0 : F) * 0) = 1
        simp
      · change (v : F) * -(1 + theta M * theta M) = 1
        rw [theta_some M hg]
        exact hv
    · refine ⟨1, ?_⟩
      change -(1 + (0 : F) * 0) - -(1 + theta M * theta M) = (g.q : F) ^ 2 * ((1 : 𝒪[F]) : F)
      rw [theta_some M hg]
      push_cast
      ring
end GlobalTheory.NonGenericLocalCheck
