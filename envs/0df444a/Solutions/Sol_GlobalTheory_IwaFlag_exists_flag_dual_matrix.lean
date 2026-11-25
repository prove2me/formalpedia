-- Prove2me | solution 1 for GlobalTheory.IwaFlag.exists_flag_dual_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:03.922881+00:00
-- url     : https://prove2.me/submissions/70120092-d0a1-4ba2-b689-3f0fcbc76b0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
import Theorems.Thm_GlobalTheory_IwaFlag_exists_flag_dual
import Theorems.Thm_GlobalTheory_IwaFlag_sesq_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
open Matrix
namespace GlobalTheory.IwaFlag
theorem _root_.solution {n : ℕ} {M : AddSubgroup (Fin n → R)} (G : Matrix (Fin n) (Fin n) R)
    (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ∀ i, ε * y i = y i)
    (hM₂ : ∀ y : Fin n → R, (∀ i, ε * y i = y i) → (y ∈ M ↔ ∀ x ∈ M, ∑ i, ∑ j, c (x i) * G i j * y j ∈ O))
    (E F : Matrix (Fin n) (Fin ρ) R) (hEF : (F.map c)ᵀ * (G * E) = 1) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, (fun l => (N : R) * ε * E l k) ∈ M) (hf : ∀ k, (fun l => (N : R) * ε * F l k) ∈ M) :
    ∃ b : Matrix (Fin ρ) (Fin ρ) R, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, ε * b i j = b i j) ∧
      (∀ i, (fun k => (E * b) k i) ∈ M) ∧ ∃ c' : Matrix (Fin n) (Fin ρ) R, (∀ i, (fun k => c' k i) ∈ M) ∧
        (c'.map c)ᵀ * (G * (E * b)) = ε • (1 : Matrix (Fin ρ) (Fin ρ) R) := by
  classical
  obtain ⟨b, h1, h2, h3, y, h4, h5⟩ := exists_flag_dual (h := sesq c G) (M := M) hcc hεε hεc hεO hOε hmul hcO hP
    (fun y hy => funext (hM₁ y hy)) (fun y hy => hM₂ y (congrFun hy)) E.mulVecLin (fun k l => F l k)
    (fun t k => by
      have := sesq_col (c := c) G (E * Matrix.of fun l (_ : Fin 1) => t l) F 0 k
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ G, hEF, Matrix.one_mul] at this
      exact this) N hN
    (fun k => by
      convert he k using 1
      ext l
      simp [mul_comm]) hf
  refine ⟨Matrix.of fun i j => b j i, fun i j hij => h1 j i hij, fun i j => h2 j i, h3, Matrix.of fun k j => y j k, h4, ?_⟩
  ext j i
  rw [← sesq_col]
  refine (h5 i j).trans ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.one_apply_ne (Ne.symm hij)]
end GlobalTheory.IwaFlag
