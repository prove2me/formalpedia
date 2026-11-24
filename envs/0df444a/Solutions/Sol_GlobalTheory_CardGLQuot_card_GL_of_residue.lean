-- Prove2me | solution 1 for GlobalTheory.CardGLQuot.card_GL_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:59.246875+00:00
-- url     : https://prove2.me/submissions/35dfe4e8-5824-4c03-98e0-cacb062a5870

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors
import Theorems.Thm_GlobalTheory_CardGLQuot_card_GL_field_real
import Theorems.Thm_GlobalTheory_CardGLQuot_card_GL_eq_card_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot
namespace GlobalTheory.CardGLQuot
theorem _root_.solution {R k : Type} [CommRing R] [Finite R] [Field k] (π : R →+* k)
    (hπ : Function.Surjective π) (hu : ∀ x, IsUnit x ↔ π x ≠ 0) (n : ℕ) :
    (Nat.card (GL (Fin n) R) : ℝ) = (Nat.card R : ℝ) ^ (n ^ 2) * glVol (Nat.card k) n := by
  classical
  haveI := Fintype.ofFinite R
  haveI : Finite k := Finite.of_surjective π hπ
  haveI := Fintype.ofFinite k
  let φ : Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) k := (π.mapMatrix).toAddMonoidHom
  have hφ : ∀ A, φ A = A.map π := fun A => rfl
  have hsurj : Function.Surjective φ := by
    intro B
    refine ⟨Matrix.of fun i j => (hπ (B i j)).choose, ?_⟩
    ext i j
    exact (hπ (B i j)).choose_spec
  have hunit : ∀ A, IsUnit A ↔ IsUnit (φ A) := by
    intro A
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, hu, isUnit_iff_ne_zero, hφ,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  set K := (Finset.univ.filter (fun A => φ A = 0)).card with hK
  have hfib : ∀ B, (Finset.univ.filter (fun A => φ A = B)).card = K :=
    fun B => AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj B) (hsurj 0)
  have h1 : (Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) R => IsUnit A)).card =
      (Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B)).card * K := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ)
      (t := Finset.univ.filter (fun B : Matrix (Fin n) (Fin n) k => IsUnit B))]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul]
      intro B hB
      rw [← hfib B, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr (fun A _ => ?_)
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨(hunit A).2 ?_, h⟩
        rw [h]; exact (Finset.mem_filter.1 hB).2
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
      exact (hunit A).1 hA
  have h2 : Fintype.card (Matrix (Fin n) (Fin n) R) = Fintype.card (Matrix (Fin n) (Fin n) k) * K := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)]
    · rw [Finset.sum_congr rfl (g := fun _ => K), Finset.sum_const, smul_eq_mul, Finset.card_univ]
      intro B _
      exact hfib B
    · intro A _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  have hcard : ∀ (S : Type) [Fintype S],
      (Fintype.card (Matrix (Fin n) (Fin n) S) : ℝ) = (Nat.card S : ℝ) ^ (n ^ 2) := by
    intro S _
    rw [← Nat.card_eq_fintype_card, show Nat.card (Matrix (Fin n) (Fin n) S) = Nat.card (Fin n → Fin n → S) from rfl,
      Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, ← sq]
    push_cast; rfl
  have hR : (Nat.card R : ℝ) ^ (n ^ 2) = (Nat.card k : ℝ) ^ (n ^ 2) * K := by
    rw [← hcard R, ← hcard k, h2, Nat.cast_mul]
  rw [card_GL_eq_card_isUnit, h1, Nat.cast_mul, ← card_GL_eq_card_isUnit, card_GL_field_real]
  linear_combination (-(glVol (Nat.card k) n)) * hR
end GlobalTheory.CardGLQuot
