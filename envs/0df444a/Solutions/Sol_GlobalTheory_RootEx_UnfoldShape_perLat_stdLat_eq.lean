-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.perLat_stdLat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:21.529809+00:00
-- url     : https://prove2.me/submissions/90676c73-dace-4095-b52a-56236ae317fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_chainLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_perLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) :
    ((perLat ϖ n' c (stdLat k n) : AddSubgroup _) :
      Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) =
      Set.univ.pi fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} =>
        {x | (ϖ : k) ^ boxExp rs.1 * x ∈ 𝒪[k]} := by
  have key : ∀ (i l : ℕ) (x : k), l ≤ i →
      ((∃ a : 𝒪[k], (ϖ : k) ^ (i + 1) * x = a * (ϖ : k) ^ (l + 1)) ↔
        (ϖ : k) ^ (i + 1 - (l + 1)) * x ∈ 𝒪[k]) := by
    intro i l x hl
    have hp : (ϖ : k) ^ (i + 1) = (ϖ : k) ^ (i + 1 - (l + 1)) * (ϖ : k) ^ (l + 1) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · rintro ⟨a, ha⟩
      have : (ϖ : k) ^ (i + 1 - (l + 1)) * x = a := by
        apply mul_right_cancel₀ (pow_ne_zero (l + 1) h0)
        rw [← ha, hp]; ring
      rw [this]; exact a.2
    · intro h
      exact ⟨⟨_, h⟩, by rw [hp]; ring⟩
  ext e
  simp only [SetLike.mem_coe, mem_perLat, mem_chainLat, mem_stdLat, Set.mem_pi, Set.mem_univ,
    Set.mem_ofPred_eq, forall_true_left, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro h ⟨⟨r, s | j⟩, hf⟩
    · rcases r with r | l <;> simp [Free] at hf
    · have hj : j ≠ 0 := by
        rintro rfl
        rcases r with r | l <;> simp [Free] at hf
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj
      rcases r with r | l
      · have := (h i).1 r
        simp only [UnfoldShape.col, dif_pos hf] at this
        exact this
      · have := (h i).2 l
        simp only [UnfoldShape.col, dif_pos hf] at this
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).1 this
  · intro h i
    refine ⟨fun r => ?_, fun l => ?_⟩
    · have hf : Free 1 ((Sum.inl r, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
        simp [Free]
      simp only [UnfoldShape.col, dif_pos hf]
      exact h ⟨_, hf⟩
    · by_cases hf : Free 1 ((Sum.inr l, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
      · simp only [UnfoldShape.col, dif_pos hf]
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).2 (h ⟨_, hf⟩)
      · simp only [UnfoldShape.col, dif_neg hf]
        exact ⟨0, by simp⟩
end GlobalTheory.RootEx.UnfoldShape
