-- Prove2me | solution 1 for GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:25.749554+00:00
-- url     : https://prove2.me/submissions/87b0d4cb-c10e-4caa-a0fe-2120d5de6895

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Theorems.Thm_GlobalTheory_FiniteGL_mem_unipRadical
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
variable (k : Type) [Field k] {N : ℕ}
variable {k}
variable (k)
variable {k}
namespace GlobalTheory.FiniteGL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal ρ ↔ ∀ a : ℕ, 0 < a → a < N →
      ∀ v : V, (∀ u ∈ unipRadical k (twoBlocks N a), ρ u v = v) → v = 0 := by
  constructor
  · intro h a ha0 haN v hv
    refine h (twoBlocks N a) ?_ ⟨⟨0, by omega⟩, ⟨a, haN⟩, ?_⟩ v hv
    · intro i j hij
      have hij' : (i : ℕ) ≤ j := hij
      simp only [twoBlocks]
      split_ifs <;> omega
    · simp [twoBlocks, ha0]
  · intro h b hb hne v hv
    classical
    obtain ⟨i₁, j₁, h₁⟩ := hne
    have hN : 0 < N := i₁.pos
    let i0 : Fin N := ⟨0, hN⟩
    have hmin : ∀ i : Fin N, b i0 ≤ b i := fun i => hb (Fin.mk_le_of_le_val (Nat.zero_le _))
    have hex : ∃ m, ∃ hm : m < N, b i0 < b ⟨m, hm⟩ := by
      by_cases hi : b i0 < b i₁
      · exact ⟨i₁, i₁.isLt, hi⟩
      · refine ⟨j₁, j₁.isLt, lt_of_le_of_ne (hmin j₁) fun he => h₁ ?_⟩
        have := hmin i₁
        change b i0 = b j₁ at he
        omega
    obtain ⟨a, haN, key⟩ : ∃ a, a < N ∧ ∀ i : Fin N, (i : ℕ) < a ↔ ¬ b i0 < b i := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun i => ⟨fun hi hlt => ?_, fun hi => ?_⟩⟩
      · exact Nat.find_min hex hi ⟨i.isLt, hlt⟩
      · by_contra hge
        obtain ⟨_, hlt⟩ := Nat.find_spec hex
        exact hi (lt_of_lt_of_le hlt (hb (Fin.mk_le_of_le_val (not_lt.mp hge))))
    refine h a ((key i0).mpr (lt_irrefl _)) haN v fun u hu => hv u ?_
    rw [mem_unipRadical] at hu ⊢
    intro i j hij
    apply hu i j
    simp only [twoBlocks]
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := (key j).mpr fun hlt => (key i).mp hi (lt_of_lt_of_le hlt hij)
      simp [hi, hj]
    · simp only [hi, if_false]
      split_ifs <;> omega
end GlobalTheory.FiniteGL
