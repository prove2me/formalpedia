-- Prove2me | solution 1 for LinearOptimization.lagrangean_dual_eq_lp_over_hull
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T03:34:41.745586+00:00
-- url     : https://prove2.me/submissions/fc074dc1-33ac-4c39-a823-2f1ebe269cfa

import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic
import Theorems.Thm_LinearOptimization_integer_hull_is_polyhedron
import Theorems.Thm_LinearOptimization_lp_general_strong_duality
import Theorems.Thm_LinearOptimization_lp_general_weak_duality
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded

open Matrix
open LinearOptimization

private lemma iInf_affine_convexHull {n : ℕ} (S : Set (Fin n → ℝ))
    (a : Fin n → ℝ) (r : ℝ) :
    (⨅ y ∈ convexHull ℝ S, ((r + a ⬝ᵥ y : ℝ) : EReal)) =
      ⨅ x ∈ S, ((r + a ⬝ᵥ x : ℝ) : EReal) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro x
    apply le_iInf
    intro hx
    exact iInf_le_of_le x (iInf_le_of_le (subset_convexHull ℝ S hx) le_rfl)
  · apply le_iInf
    intro y
    apply le_iInf
    intro hy
    let v : EReal := ⨅ x ∈ S, ((r + a ⬝ᵥ x : ℝ) : EReal)
    change v ≤ ((r + a ⬝ᵥ y : ℝ) : EReal)
    induction hv : v using EReal.rec with
    | bot => exact bot_le
    | coe t =>
        norm_cast
        have hsub : S ⊆ {z : Fin n → ℝ | t ≤ r + a ⬝ᵥ z} := by
          intro x hx
          have hle : (v : EReal) ≤ ((r + a ⬝ᵥ x : ℝ) : EReal) :=
            iInf_le_of_le x (iInf_le_of_le hx le_rfl)
          rw [hv] at hle
          apply EReal.coe_le_coe_iff.mp
          simpa only [← EReal.coe_add] using hle
        have hconv : Convex ℝ {z : Fin n → ℝ | t ≤ r + a ⬝ᵥ z} := by
          intro u hu w hw α β hα hβ hab
          change t ≤ r + a ⬝ᵥ (α • u + β • w)
          rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
            smul_eq_mul]
          have hu' := mul_le_mul_of_nonneg_left hu hα
          have hw' := mul_le_mul_of_nonneg_left hw hβ
          calc
            t = α * t + β * t := by rw [← add_mul, hab, one_mul]
            _ ≤ α * (r + a ⬝ᵥ u) + β * (r + a ⬝ᵥ w) := add_le_add hu' hw'
            _ = (α + β) * r + (α * (a ⬝ᵥ u) + β * (a ⬝ᵥ w)) := by ring
            _ = r + (α * (a ⬝ᵥ u) + β * (a ⬝ᵥ w)) := by rw [hab, one_mul]
        exact convexHull_min hsub hconv hy
    | top =>
        have hSne : S.Nonempty := convexHull_nonempty_iff.mp ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hSne
        have hle : v ≤ ((r + a ⬝ᵥ x : ℝ) : EReal) :=
          iInf_le_of_le x (iInf_le_of_le hx le_rfl)
        rw [hv] at hle
        have hfalse : False := by
          apply (not_le_of_gt (EReal.coe_lt_top (r + a ⬝ᵥ x)))
          exact hle
        exact hfalse.elim

private lemma lagrangeanObjective_convexHull {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S : Set (Fin n → ℝ)) (p : Fin m → ℝ) :
    lagrangeanObjective A b c (convexHull ℝ S) p =
      lagrangeanObjective A b c S p := by
  have hform (y : Fin n → ℝ) :
      c ⬝ᵥ y + p ⬝ᵥ (b - A.mulVec y) =
        p ⬝ᵥ b + (c - Aᵀ.mulVec p) ⬝ᵥ y := by
    rw [dotProduct_sub, sub_dotProduct, Matrix.dotProduct_mulVec]
    have hpA : p ᵥ* A = Aᵀ.mulVec p := by
      ext j
      simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
    rw [hpA]
    ring
  unfold lagrangeanObjective
  simp_rw [hform]
  exact iInf_affine_convexHull S (c - Aᵀ.mulVec p) (p ⬝ᵥ b)

private lemma lpValue_eq_coe_of_optimal {n : ℕ} (c : Fin n → ℝ)
    (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) (hx : IsLpOptimal c S x) :
    lpValue c S = ((c ⬝ᵥ x : ℝ) : EReal) := by
  apply le_antisymm
  · exact iInf_le_of_le x (iInf_le_of_le hx.1 le_rfl)
  · unfold lpValue
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact EReal.coe_le_coe_iff.mpr (hx.2 y hy)

/-- Bertsimas--Tsitsiklis, Theorem 11.4, p. 496. -/
theorem solution {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℤ) (b : Fin m₁ → ℤ) (c : Fin n → ℤ)
    (D : Matrix (Fin m₂) (Fin n) ℤ) (d : Fin m₂ → ℤ)
    (hguard :
      lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)) = ∅ ∨
      {x : Fin n → ℝ | (fun i => (b i : ℝ)) ≤
          (A.map ((↑) : ℤ → ℝ)).mulVec x ∧
        x ∈ convexHull ℝ (lagrangeanIntegerSet
          (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)))}.Nonempty) :
    lagrangeanDualValue (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))
        (fun j => (c j : ℝ))
        (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))) =
      lpValue (fun j => (c j : ℝ))
        {x : Fin n → ℝ |
          (fun i => (b i : ℝ)) ≤ (A.map ((↑) : ℤ → ℝ)).mulVec x ∧
          x ∈ convexHull ℝ (lagrangeanIntegerSet
            (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)))} := by
  classical
  rcases hguard with hXempty | hprimalne
  · simp [hXempty, lagrangeanDualValue, lagrangeanObjective, lpValue]
    apply top_unique
    exact le_iSup_of_le (0 : Fin m₁ → ℝ)
      (le_iSup_of_le (show (0 : Fin m₁ → ℝ) ≤ 0 by simp) le_rfl)
  · let Ar : Matrix (Fin m₁) (Fin n) ℝ := A.map ((↑) : ℤ → ℝ)
    let br : Fin m₁ → ℝ := fun i ↦ (b i : ℝ)
    let cr : Fin n → ℝ := fun j ↦ (c j : ℝ)
    let Dr : Matrix (Fin m₂) (Fin n) ℝ := D.map ((↑) : ℤ → ℝ)
    let dr : Fin m₂ → ℝ := fun i ↦ (d i : ℝ)
    let X : Set (Fin n → ℝ) := lagrangeanIntegerSet Dr dr
    let C : Set (Fin n → ℝ) := convexHull ℝ X
    let P : Set (Fin n → ℝ) := {x | br ≤ Ar.mulVec x ∧ x ∈ C}
    change lagrangeanDualValue Ar br cr X = lpValue cr P
    have hPne : P.Nonempty := by simpa [P, C, X, Ar, br, Dr, dr] using hprimalne
    have hCne : C.Nonempty := by
      obtain ⟨x, hx⟩ := hPne
      exact ⟨x, hx.2⟩
    have hXne : X.Nonempty := (convexHull_nonempty_iff (𝕜 := ℝ)).mp
      (by simpa [C] using hCne)
    have hDfeas : (polyhedron Dr dr).Nonempty := by
      obtain ⟨x, hx⟩ := hXne
      exact ⟨x, hx.1⟩
    obtain ⟨k, F, f, hCpoly⟩ := integer_hull_is_polyhedron D d (by
      simpa [Dr, dr] using hDfeas)
    have hCeq : C = polyhedron F f := by simpa [C, X, Dr, dr] using hCpoly
    let e : Fin m₁ ⊕ Fin k ≃ Fin (m₁ + k) := finSumFinEquiv
    let G : Matrix (Fin (m₁ + k)) (Fin n) ℝ := fun q j ↦
      Sum.elim (fun i ↦ Ar i j) (fun i ↦ F i j) (e.symm q)
    let g : Fin (m₁ + k) → ℝ := fun q ↦ Sum.elim br f (e.symm q)
    have hPG : P = polyhedron G g := by
      ext x
      constructor
      · rintro ⟨hxA, hxC⟩ q
        have hxF : x ∈ polyhedron F f := by simpa [hCeq] using hxC
        rcases hq : e.symm q with i | i
        · have hi := hxA i
          simpa [G, g, hq, Matrix.mulVec, dotProduct] using hi
        · have hi := hxF i
          simpa [G, g, hq, Matrix.mulVec, dotProduct] using hi
      · intro hx
        constructor
        · intro i
          have hi := hx (e (Sum.inl i))
          simpa [G, g, e, Matrix.mulVec, dotProduct] using hi
        · rw [hCeq]
          intro i
          have hi := hx (e (Sum.inr i))
          simpa [G, g, e, Matrix.mulVec, dotProduct] using hi
    have hGne : (polyhedron G g).Nonempty := by simpa [← hPG] using hPne
    rcases lp_attains_or_unbounded G g cr hGne with hbot | ⟨xstar, hxoptG⟩
    · have hPbot : lpValue cr P = ⊥ := by simpa [hPG] using hbot
      rw [hPbot]
      apply le_antisymm
      · unfold lagrangeanDualValue
        apply iSup_le
        intro p
        apply iSup_le
        intro hp
        have hweak : lagrangeanObjective Ar br cr X p ≤ lpValue cr P := by
          unfold lpValue
          apply le_iInf
          intro y
          apply le_iInf
          intro hy
          have hw := lp_general_weak_duality Ar br cr F f y hy.1
            (by simpa [← hCeq] using hy.2) p hp
          rw [← lagrangeanObjective_convexHull Ar br cr X p]
          rw [show convexHull ℝ X = polyhedron F f by simpa [C] using hCeq]
          exact hw
        rw [hPbot] at hweak
        exact hweak
      · exact bot_le
    · have hxoptP : IsLpOptimal cr P xstar := by
        simpa [hPG] using hxoptG
      have hxoptGeneral :
          IsLpOptimal cr {y | br ≤ Ar.mulVec y ∧ y ∈ polyhedron F f} xstar := by
        simpa [P, hCeq] using hxoptP
      obtain ⟨p, hp, hpmax, hpeq⟩ :=
        lp_general_strong_duality Ar br cr F f xstar hxoptGeneral
      have hobj (q : Fin m₁ → ℝ) :
          lagrangeanObjective Ar br cr (polyhedron F f) q =
            lagrangeanObjective Ar br cr X q := by
        rw [← hCeq]
        exact lagrangeanObjective_convexHull Ar br cr X q
      have hpmaxX : ∀ q : Fin m₁ → ℝ, 0 ≤ q →
          lagrangeanObjective Ar br cr X q ≤
            lagrangeanObjective Ar br cr X p := by
        intro q hq
        rw [← hobj q, ← hobj p]
        exact hpmax q hq
      have hpeqX : lagrangeanObjective Ar br cr X p =
          ((cr ⬝ᵥ xstar : ℝ) : EReal) := (hobj p).symm.trans hpeq
      have hdual : lagrangeanDualValue Ar br cr X =
          ((cr ⬝ᵥ xstar : ℝ) : EReal) := by
        rw [← hpeqX]
        apply le_antisymm
        · unfold lagrangeanDualValue
          apply iSup_le
          intro q
          apply iSup_le
          intro hq
          exact hpmaxX q hq
        · unfold lagrangeanDualValue
          exact le_iSup_of_le p (le_iSup_of_le hp le_rfl)
      rw [hdual]
      exact (lpValue_eq_coe_of_optimal cr P xstar hxoptP).symm
