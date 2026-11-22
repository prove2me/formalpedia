-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:23:15.877349+00:00
-- url     : https://prove2.me/submissions/b142ac1f-c2be-4002-8d3f-55d09123dc55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MixedCloning_Optimal_proposition_20

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## The partial transpose on the first tensor factor -/

/-- Partial transpose on the first Kronecker factor:
`PT(X)((i,j),(i',j')) = X((i',j),(i,j'))`. It is an involutive linear equivalence. -/
def l19PT (a b : Type) : Matrix (a × b) (a × b) ℂ ≃ₗ[ℂ] Matrix (a × b) (a × b) ℂ where
  toFun X := fun p p' => X (p'.1, p.2) (p.1, p'.2)
  invFun X := fun p p' => X (p'.1, p.2) (p.1, p'.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma l19PT_apply {a b : Type} (X : Matrix (a × b) (a × b) ℂ) (p p' : a × b) :
    l19PT a b X p p' = X (p'.1, p.2) (p.1, p'.2) := rfl

/-- `PT(A ⊗ B) = Aᵀ ⊗ B`. -/
lemma l19PT_kronecker {a b : Type} (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    l19PT a b (Matrix.kronecker A B) = Matrix.kronecker Aᵀ B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  rfl

/-- `PT(1) = 1`, for whatever decidable-equality instance sits inside `1`. -/
lemma l19PT_one {a b : Type} [DecidableEq (a × b)] :
    l19PT a b (1 : Matrix (a × b) (a × b) ℂ) = 1 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  rw [l19PT_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : (i, j) = (i', j')
  · rw [if_pos h, if_pos]
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1.symm, h.2⟩
  · rw [if_neg h, if_neg]
    simp only [Prod.mk.injEq] at h ⊢
    exact fun h' => h ⟨h'.1.symm, h'.2⟩

/-- The partial transpose commutes with the Bochner integral (it is a continuous linear
equivalence of a finite-dimensional space, so no integrability hypothesis is needed). -/
lemma l19PT_integral {a b : Type} [Fintype a] [Fintype b] {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f : X → Matrix (a × b) (a × b) ℂ) :
    l19PT a b (∫ x, f x ∂μ) = ∫ x, l19PT a b (f x) ∂μ := by
  have h := ContinuousLinearEquiv.integral_comp_comm (μ := μ)
    (l19PT a b).toContinuousLinearEquiv f
  exact h.symm

/-! ## Step 1: the partial transpose of `delta` -/

lemma l19PT_delta {d : ℕ} (r : ℕ) (L M : YoungDiagram) (b : SchurBasis L d)
    (c : SchurBasis M d) :
    l19PT _ _ (delta r L M b c) =
      ((ratio (L ⊔ M) r d : ℂ) • 1) - transposedIntegral r L M b c := by
  unfold delta schurIntegral transposedIntegral
  rw [map_sub, map_smul, l19PT_one, l19PT_integral]
  simp only [l19PT_kronecker]

/-! ## Steps 2–3: the partial transpose of a separable matrix is positive semidefinite -/

lemma l19PT_separable_psd {a b : Type} [Fintype a] [Fintype b] (X : Matrix (a × b) (a × b) ℂ)
    (hX : Separable X) : (l19PT a b X).PosSemidef := by
  obtain ⟨N, w, A, B, hpos, rfl⟩ := hX
  rw [map_sum]
  refine Matrix.posSemidef_sum _ fun j _ => ?_
  rw [map_smul, l19PT_kronecker]
  obtain ⟨hw, hA, hB⟩ := hpos j
  exact (Matrix.PosSemidef.kronecker (Matrix.posSemidef_transpose_iff.mpr hA) hB).smul
    (Complex.zero_le_real.mpr hw)

/-! ## Lemma 19 -/

theorem solution (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L M : YoungDiagram) (hL : height L ≤ d) (hM : height M ≤ d)
    (b : SchurBasis L d) (c : SchurBasis M d) :
    (((ratio (L ⊔ M) r d : ℂ) • 1) - transposedIntegral r L M b c).PosSemidef := by
  rw [← l19PT_delta]
  exact l19PT_separable_psd _ (proposition_20 d r hr hrd L M hL hM b c)
