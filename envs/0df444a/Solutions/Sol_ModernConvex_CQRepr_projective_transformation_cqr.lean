-- Prove2me | solution 1 for ModernConvex.CQRepr.projective_transformation_cqr
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:52:44.656118+00:00
-- url     : https://prove2.me/submissions/00188b78-8a72-4fae-a4f2-375087902724

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

open ModernConvex.CQRepr

theorem solution : ¬ (∀ {n q : ℕ} (K : IceCreamProduct)
    (A : Matrix K.Idx (Fin n) ℝ) (p : K.Idx → ℝ) (B : Matrix K.Idx (Fin q) ℝ) (b : K.Idx → ℝ)
    (f : (Fin n → ℝ) → EReal) (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hf : ∀ (x : Fin n → ℝ) (t : ℝ),
      f x ≤ (t : EReal) ↔ ∃ u : Fin q → ℝ, A *ᵥ x + t • p + B *ᵥ u + b ∈ K.cone)
    (hB : ∀ u : Fin q → ℝ, B *ᵥ u ∈ K.cone → B *ᵥ u = 0),
    projectiveEpi f =
      {z : (Fin n → ℝ) × ℝ × ℝ | 0 ≤ z.2.2 ∧
        ∃ u : Fin q → ℝ, A *ᵥ z.1 + z.2.1 • p + B *ᵥ u + z.2.2 • b ∈ K.cone}) := by
  intro H
  let K : IceCreamProduct := ⟨1, fun _ => 1, fun _ => le_refl 1⟩
  let b : K.Idx → ℝ := fun i => if i.2 = Fin.last 1 then -1 else 0
  have hbK : b ∉ K.cone := by
    intro hv
    have h := hv 0
    have h2 : b ⟨0, Fin.last 1⟩ = -1 := by simp [b]
    have h3 := Real.sqrt_nonneg (∑ i : Fin (K.d 0), b ⟨0, Fin.castSucc i⟩ ^ 2)
    change _ ≤ b ⟨0, Fin.last 1⟩ at h
    linarith
  have := @H 0 0 K 0 0 0 b (fun _ => ⊤) (fun _ => by simp) lowerSemicontinuous_const
    (fun x t => by
      simp only [top_le_iff, EReal.coe_ne_top, false_iff, not_exists]
      intro u hu
      apply hbK
      simpa using hu)
    (fun u _ => by simp)
  have hmem : ((0 : Fin 0 → ℝ), (0:ℝ), (0:ℝ)) ∈ projectiveEpi (n := 0) (fun _ => ⊤) := by
    rw [this]
    refine ⟨le_refl 0, 0, ?_⟩
    intro j
    simp
  unfold projectiveEpi at hmem
  have he : {z : (Fin 0 → ℝ) × ℝ × ℝ | 0 < z.2.2 ∧ (fun _ => (⊤ : EReal)) (z.2.2⁻¹ • z.1) ≤
      ((z.2.2⁻¹ * z.2.1 : ℝ) : EReal)} = ∅ := by
    ext z; simp only [Set.mem_setOf_eq, top_le_iff, EReal.coe_ne_top, and_false, Set.mem_empty_iff_false]
  rw [he, closure_empty] at hmem
  exact hmem
