-- Prove2me | solution 1 for Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1ba9a314-d8b8-5921-815f-7fca850ab053

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top

set_option autoImplicit false

open scoped Matrix

namespace SL2Lines

variable {F : Type*} [Field F]

theorem mulVec_two (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) (i : Fin 2) :
    (A *ᵥ v) i = A i 0 * v 0 + A i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem vec_ne_zero_iff (v : Fin 2 → F) : v ≠ 0 ↔ v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  constructor
  · intro hv
    by_contra h
    push Not at h
    apply hv
    ext i; fin_cases i <;> simp [h.1, h.2]
  · rintro (h | h) hv <;> exact h (by rw [hv]; rfl)

theorem exists_mulVec_eq (v t : Fin 2 → F) (hv : v ≠ 0) : ∃ X : Matrix (Fin 2) (Fin 2) F, X *ᵥ v = t := by
  rcases (vec_ne_zero_iff v).1 hv with h0 | h1
  · refine ⟨Matrix.of fun i j => if j = 0 then t i * (v 0)⁻¹ else 0, ?_⟩
    ext i
    rw [mulVec_two]
    simp
    field_simp
  · refine ⟨Matrix.of fun i j => if j = 1 then t i * (v 1)⁻¹ else 0, ?_⟩
    ext i
    rw [mulVec_two]
    simp
    field_simp

theorem exists_eq_smul {w u : Fin 2 → F} (hw : w ≠ 0) (h : w 0 * u 1 - w 1 * u 0 = 0) :
    ∃ lam : F, u = lam • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1; apply hw; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨u 1 * (w 1)⁻¹, ?_⟩
    have hu0 : u 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    ext i; fin_cases i
    · simp [h0, hu0]
    · simp; field_simp
  · refine ⟨u 0 * (w 0)⁻¹, ?_⟩
    ext i; fin_cases i
    · simp; field_simp
    · simp; field_simp; linear_combination h

theorem eq_zero_of_mulVec_eq_zero {w u : Fin 2 → F} (h : w 0 * u 1 - w 1 * u 0 ≠ 0)
    {D : Matrix (Fin 2) (Fin 2) F} (hw : D *ᵥ w = 0) (hu : D *ᵥ u = 0) : D = 0 := by
  ext i j
  have e1 : D i 0 * w 0 + D i 1 * w 1 = 0 := by rw [← mulVec_two]; rw [hw]; rfl
  have e2 : D i 0 * u 0 + D i 1 * u 1 = 0 := by rw [← mulVec_two]; rw [hu]; rfl
  fin_cases j
  · have : D i 0 * (w 0 * u 1 - w 1 * u 0) = 0 := by linear_combination u 1 * e1 - w 1 * e2
    simpa using (mul_eq_zero.mp this).resolve_right h
  · have : D i 1 * (w 0 * u 1 - w 1 * u 0) = 0 := by linear_combination (-(u 0)) * e1 + w 0 * e2
    simpa using (mul_eq_zero.mp this).resolve_right h

theorem exists_annihilator (I : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ A : Matrix (Fin 2) (Fin 2) F, A ∈ I ↔ A *ᵥ w = 0 := by
  classical
  obtain ⟨A₀, hA₀I, hA₀⟩ := (Submodule.ne_bot_iff I).1 hI0
  have hdet : A₀.det = 0 := by
    by_contra hdet
    apply hI1
    exact Ideal.eq_top_of_isUnit_mem I hA₀I ((Matrix.isUnit_iff_isUnit_det A₀).2 (isUnit_iff_ne_zero.2 hdet))
  obtain ⟨w, hw, hA₀w⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → F, A₀ *ᵥ u ≠ 0 := by
    by_contra h
    push Not at h
    apply hA₀
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  have hcross : w 0 * u 1 - w 1 * u 0 ≠ 0 := by
    intro hc
    obtain ⟨lam, rfl⟩ := exists_eq_smul hw hc
    apply hu
    rw [Matrix.mulVec_smul, hA₀w, smul_zero]
  refine ⟨w, hw, fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · by_contra hAw
    apply hI1
    obtain ⟨X, hX⟩ := exists_mulVec_eq (A *ᵥ w) w hAw
    obtain ⟨Y, hY⟩ := exists_mulVec_eq (A₀ *ᵥ u) (u - X *ᵥ (A *ᵥ u)) hu
    have h1 : X * A + Y * A₀ = 1 := by
      have hD := eq_zero_of_mulVec_eq_zero hcross (D := X * A + Y * A₀ - 1) ?_ ?_
      · exact sub_eq_zero.mp hD
      · rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hX, hA₀w,
          Matrix.mulVec_zero, Matrix.one_mulVec]
        simp
      · rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hY,
          Matrix.one_mulVec]
        abel
    rw [Ideal.eq_top_iff_one, ← h1]
    exact I.add_mem (Ideal.mul_mem_left I X hA) (Ideal.mul_mem_left I Y hA₀I)
  · obtain ⟨X, hX⟩ := exists_mulVec_eq (A₀ *ᵥ u) (A *ᵥ u) hu
    have hAX : A = X * A₀ := by
      have hD := eq_zero_of_mulVec_eq_zero hcross (D := A - X * A₀) ?_ ?_
      · exact sub_eq_zero.mp hD
      · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hA₀w, hA, Matrix.mulVec_zero, sub_zero]
      · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hX, sub_self]
    rw [hAX]
    exact Ideal.mul_mem_left I X hA₀I

theorem det_one_add_eq_one {N : Matrix (Fin 2) (Fin 2) F} (h : N * N = 0) : (1 + N).det = 1 := by
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
  by_cases ht : N 0 0 + N 1 1 = 0
  · have h11 : N 1 1 = -N 0 0 := by linear_combination ht
    rw [h11]
    linear_combination (-1 : F) * e00
  · have h01 : N 0 1 = 0 := by
      have : N 0 1 * (N 0 0 + N 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right ht
    have h10 : N 1 0 = 0 := by
      have : N 1 0 * (N 0 0 + N 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right ht
    have h00 : N 0 0 = 0 := by
      have : N 0 0 * N 0 0 = 0 := by rw [h01] at e00; linear_combination e00
      exact mul_self_eq_zero.mp this
    have h11 : N 1 1 = 0 := by
      have : N 1 1 * N 1 1 = 0 := by rw [h10] at e11; linear_combination e11
      exact mul_self_eq_zero.mp this
    exact absurd (by rw [h00, h11, add_zero]) ht

end SL2Lines

open SL2Lines in
theorem solution
    {F : Type*} [Field F] (I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧ g ≠ 1 ∧ ∀ A ∈ I, A * g ∈ I' := by
  classical
  obtain ⟨w, hw, hIw⟩ := exists_annihilator I hI0 hI1
  obtain ⟨w', hw', hIw'⟩ := exists_annihilator I' hI'0 hI'1

  suffices hN : ∃ N : Matrix (Fin 2) (Fin 2) F, N * N = 0 ∧ N ≠ 0 ∧
      (N *ᵥ w' = w - w' ∨ (N *ᵥ w' = 0 ∧ ∃ lam : F, w' = lam • w)) by
    obtain ⟨N, hNN, hN0, hNw⟩ := hN
    refine ⟨1 + N, det_one_add_eq_one hNN, by simpa using hNN, ?_, ?_⟩
    · intro h
      apply hN0
      have : (1 : Matrix (Fin 2) (Fin 2) F) + N - 1 = 0 := by rw [h, sub_self]
      simpa using this
    · intro A hA
      have hAw : A *ᵥ w = 0 := (hIw A).1 hA
      apply (hIw' _).2
      rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      rcases hNw with h | ⟨h, lam, hlam⟩
      · rw [h, add_sub_cancel, hAw]
      · rw [h, add_zero, hlam, Matrix.mulVec_smul, hAw, smul_zero]
  by_cases hc : w 0 * w' 1 - w 1 * w' 0 = 0
  ·
    obtain ⟨lam, hlam⟩ := exists_eq_smul hw hc
    obtain hw'01 := (vec_ne_zero_iff w').1 hw'
    refine ⟨Matrix.of fun i j => w' i * ![w' 1, -(w' 0)] j, ?_, ?_, Or.inr ⟨?_, lam, hlam⟩⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · intro h
      have e := fun i j => congrFun (congrFun h i) j
      have e01 := e 0 1
      have e10 := e 1 0
      simp at e01 e10
      rcases hw'01 with h0 | h1
      · exact h0 e01
      · exact h1 e10
    · ext i
      rw [mulVec_two]
      simp
      ring
  ·
    set δ : F := w 0 * w' 1 - w 1 * w' 0 with hδ
    refine ⟨Matrix.of fun i j => (w i - w' i) * ![(w' 1 - w 1) * δ⁻¹, (w 0 - w' 0) * δ⁻¹] j, ?_, ?_, Or.inl ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    · intro h

      have hne : w - w' ≠ 0 := by
        intro h0
        have : w = w' := sub_eq_zero.mp h0
        apply hc; rw [hδ, this]; ring
      apply hne
      have key : (Matrix.of fun i j => (w i - w' i) * ![(w' 1 - w 1) * δ⁻¹, (w 0 - w' 0) * δ⁻¹] j) *ᵥ w' = w - w' := by
        ext i
        rw [mulVec_two]
        simp
        field_simp
        ring
      rw [← key, h, Matrix.zero_mulVec]
    · ext i
      rw [mulVec_two]
      simp
      field_simp
      ring

end S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
end P2MW
export P2MW.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top (solution)
