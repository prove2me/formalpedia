-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:39.832978+00:00
-- url     : https://prove2.me/submissions/41c2fac2-c8ab-4d8e-83f0-5c80936f1a45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Model
theorem _root_.solution {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ N k n c p := by
  rw [mem_N_iff] at hu ⊢
  rw [← map_inv]
  have h11 : u.val.toBlocks₁₁ = 1 := by
    ext r s
    have := hu (Sum.inl r) (Sum.inl s) le_rfl
    simpa [Matrix.one_apply, toBlocks₁₁] using this
  have hv : ((embX c g⁻¹) * u * embX c g).val = fromBlocks 1 ((g⁻¹).val * u.val.toBlocks₁₂)
      (u.val.toBlocks₂₁ * g.val) u.val.toBlocks₂₂ := by
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val, h11]
    simp [embX, fromBlocks_multiply]
  rintro (r | r) (s | s) h <;> rw [hv]
  · simp [Matrix.one_apply]
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [Matrix.mul_apply, toBlocks₁₂, this]
  · have : ∀ t, u.val (Sum.inr r) (Sum.inl t) = 0 := fun t => by
      simpa using hu (Sum.inr r) (Sum.inl t) h
    simp [Matrix.mul_apply, toBlocks₂₁, this]
  · simpa [toBlocks₂₂] using hu (Sum.inr r) (Sum.inr s) h
end GlobalTheory.RootEx.Model
