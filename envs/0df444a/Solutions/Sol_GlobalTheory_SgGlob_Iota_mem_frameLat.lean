-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.mem_frameLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:13.393468+00:00
-- url     : https://prove2.me/submissions/0718e789-217b-4b36-ba30-93f5888b9125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ frameLat P ↔ ∃ a : Fin (r + 1) → E, (∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) ∧ P *ᵥ a = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, a, ha, rfl⟩ := hx
      refine ⟨Pi.single b a, fun b' => ?_, by ext i; simp [mul_comm]⟩
      by_cases h : b' = b
      · subst h
        simpa using ha
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    | zero => exact ⟨0, fun b => FractionalIdeal.zero_mem _, Matrix.mulVec_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, fun i => Submodule.add_mem (dInv E (r - (i : ℕ))).coeToSubmodule (ha i) (hb i),
        Matrix.mulVec_add _ _ _⟩
    | smul t x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨t • a, fun i => Submodule.smul_mem (dInv E (r - (i : ℕ))).coeToSubmodule t (ha i),
        Matrix.mulVec_smul _ _ _⟩
  · rintro ⟨a, ha, rfl⟩
    have : P *ᵥ a = ∑ b, a b • fun i => P i b := by
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨b, a b, ha b, rfl⟩
end GlobalTheory.SgGlob.Iota
