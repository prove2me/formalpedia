-- Prove2me | solution 1 for GlobalTheory.FunObj.flatTensor_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:49.262555+00:00
-- url     : https://prove2.me/submissions/c9de863d-703c-4d3d-a605-57429cf6eb1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_FunObj_fill_theta
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)
variable (hs)
namespace GlobalTheory.FunObj
theorem _root_.solution (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) :
    Integrable (flatIntegrand hs ψ S 0 0) (varsVol G ν) ∧ flatTensor hs ψ ν S 0 0 = 1 := by
  classical
  have hb : ∀ {n n' : Type} {c : ℕ} r s, basePt c (0 : Matrix n n' k) r s ∈ 𝒪[k] := by
    rintro n n' c (r | r) (s | s) <;> simp only [basePt, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, of_apply, Matrix.zero_apply, zero_mem]
    split_ifs <;> simp
  let B : Set (Vars G) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hp : ∀ e ∈ B, ∀ (j : Fin (G.m - 1)) r s, stepPt ((0 : ColArgs G) j) (e j) r s ∈ 𝒪[k] := fun e he j r s => by
    refine add_mem (hb r s) ?_
    rw [of_apply]
    split_ifs
    · exact he j trivial _ trivial
    · exact zero_mem _
  have key : flatIntegrand hs ψ S 0 0 = B.indicator 1 := by
    funext e
    by_cases he : e ∈ B
    · rw [Set.indicator_of_mem he, flatIntegrand, h1, hψ]
      · simp
      · refine neg_mem (sum_mem fun j _ => add_mem (sum_mem fun i _ => hp e he j _ _) ?_)
        split_ifs
        · refine sum_mem fun r _ => mul_mem ?_ (hp e he j _ _)
          unfold rowVar
          split_ifs with h
          · refine sum_mem fun l _ => ?_
            split_ifs
            · exact hp e he ⟨_, h⟩ _ _
            · exact zero_mem _
          · exact zero_mem _
        · exact zero_mem _
      · rintro (⟨i, j⟩ | ⟨i, j⟩) - r s <;> simp only [fill] <;> split_ifs
        · simp only [transpose_apply, submatrix_apply, downMap]
          split_ifs with h
          · exact hp e he ⟨_, h⟩ _ _
          · exact zero_mem _
          · exact zero_mem _
        all_goals exact zero_mem _
    · rw [Set.indicator_of_notMem he, flatIntegrand, h0, zero_mul]
      refine fun H => he fun j _ rs _ => ?_
      have h2 := H (.theta G.m j) (by have := j.2; simp [oppositePath]; omega)
        (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega) rs.1.2)
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) rs.1.1)
      rw [fill_theta, transpose_apply, downMap, dif_pos j.2] at h2
      simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, Matrix.add_apply, of_apply] at h2
      rw [dif_pos rs.2] at h2
      exact (add_mem_cancel_left (hb _ _)).1 h2
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have := hν.1
  have hm : MeasurableSet B :=
    MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => Model.isOpen_int.measurableSet
  have hv : varsVol G ν B = 1 := by simp [varsVol, B, Measure.pi_pi, hν.2]
  rw [flatTensor, key]
  exact ⟨(integrable_indicator_iff hm).2 (integrableOn_const (by simp [hv])), by
    rw [integral_indicator hm]; simp [Measure.real, hv]⟩
end GlobalTheory.FunObj
