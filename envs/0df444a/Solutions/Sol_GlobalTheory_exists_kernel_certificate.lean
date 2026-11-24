-- Prove2me | solution 1 for GlobalTheory.exists_kernel_certificate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:41.028673+00:00
-- url     : https://prove2.me/submissions/3f662167-4b44-4962-b105-d917152e395f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsMulEqSmulOneOfMulVecInjective
import Theorems.Thm_GlobalTheory_exists_mul_eq_smul_one_of_mulVec_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by
  classical
  obtain ⟨κ, s, hs, hspan, hli⟩ := exists_linearIndependent' K (fun j : a => (D₀.map g).col j)
  have : Fintype κ := Fintype.ofInjective s hs
  let S : Matrix a κ R := (1 : Matrix a a R).submatrix id s
  have hDS : D₀ * S = D₀.submatrix id s := by
    ext i j
    simp [S, Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x =
      ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k := by
    intro x
    funext i
    simp [hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨r₀, T₀, hr₀, hT₀⟩ := exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by
    intro x hx
    rw [hsum] at hx
    funext k
    exact Fintype.linearIndependent_iff.1 hli x hx k)
  obtain ⟨r₁, T₁, hr₁, hT₁⟩ := exists_mul_eq_smul_one_of_mulVec_injective g
    (Matrix.fromRows T₀ D₁) (by
    intro w hw
    have hw1 : (T₀.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inl k)
    have hw2 : (D₁.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inr k)
    obtain ⟨v, hv⟩ := hex w hw2
    have hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s)) := by
      rw [hspan, ← hv]
      have : (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [← hsum] at hu
    rw [← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀] at hw1
    have hu0 : u = 0 := by
      funext k
      have := congrFun hw1 k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this
      rcases this with h | h
      · exact absurd h hr₀
      · exact h
    rw [← hu, hu0, Matrix.mulVec_zero])
  let Q : Matrix a a R := r₀ • (1 : Matrix a a R) - S * T₀ * D₀
  have hQS : Q * S = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hDQ : r₁ • (D₀ * Q) = 0 := by
    have h1 : T₀ * (D₀ * Q) = 0 := by
      have : T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀) := by
        simp only [Matrix.mul_assoc]
      simp only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : D₁ * (D₀ * Q) = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    have h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0 := by
      rw [Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]
    calc r₁ • (D₀ * Q) = (T₁ * Matrix.fromRows T₀ D₁) * (D₀ * Q) := by
          rw [hT₁, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  let t := {j : a // j ∉ Set.range s}
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → a := fun i => (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfs : ∀ i k, f i ≠ s k := fun i k h => (e i).2 ⟨k, h.symm⟩
  let E : Matrix a (Fin (Fintype.card t)) R := (1 : Matrix a a R).submatrix id f
  have hEE : E.transpose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hES : E.transpose * S = 0 := by
    ext i j
    simp [E, S, Matrix.mul_apply, Matrix.one_apply, hfs]
  have hQE : Q * E * E.transpose = Q := by
    ext i j
    have hQE' : Q * E = Q.submatrix id f := by
      ext i j
      simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hQE']
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k, rfl⟩ := hj
      have : Q i (s k) = (Q * S) i k := by
        simp [S, Matrix.mul_apply, Matrix.one_apply]
      rw [this, hQS]
      simp [E, Matrix.mul_apply, Matrix.one_apply, hfs]
    · obtain ⟨k, hk⟩ : ∃ k, f k = j := ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
      subst hk
      simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  refine ⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hr₁ hr₀
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]
  · have : E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E) := by
      simp only [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul,
      sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]
    simp only [Q, sub_add_cancel]
end GlobalTheory
