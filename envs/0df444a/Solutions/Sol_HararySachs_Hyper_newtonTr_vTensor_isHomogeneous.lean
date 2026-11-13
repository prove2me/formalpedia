-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_vTensor_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:39:55.820556+00:00
-- url     : https://prove2.me/submissions/29a21925-ed58-4634-9df0-e8de4b862774

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper MvPolynomial Finset

namespace VHomAux

variable {σ : Type*}

/-- the coefficient of `z^j` is homogeneous of degree `j * r` -/
def GrW (r : ℕ) (Φ : Polynomial (MvPolynomial σ ℚ)) : Prop :=
  ∀ j, (Φ.coeff j).IsHomogeneous (j * r)

lemma GrW_add {r : ℕ} {Φ Ψ : Polynomial (MvPolynomial σ ℚ)} (h1 : GrW r Φ) (h2 : GrW r Ψ) :
    GrW r (Φ + Ψ) :=
  fun j => by rw [Polynomial.coeff_add]; exact (h1 j).add (h2 j)

lemma GrW_neg {r : ℕ} {Φ : Polynomial (MvPolynomial σ ℚ)} (h : GrW r Φ) : GrW r (-Φ) :=
  fun j => by rw [Polynomial.coeff_neg]; exact (h j).neg

lemma GrW_sub {r : ℕ} {Φ Ψ : Polynomial (MvPolynomial σ ℚ)} (h1 : GrW r Φ) (h2 : GrW r Ψ) :
    GrW r (Φ - Ψ) := by
  rw [sub_eq_add_neg]; exact GrW_add h1 (GrW_neg h2)

lemma GrW_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial σ ℚ))
    (h : ∀ x ∈ s, GrW r (f x)) : GrW r (∑ x ∈ s, f x) :=
  fun j => by
    rw [Polynomial.finsetSum_coeff]
    exact IsHomogeneous.sum _ _ _ fun x hx => h x hx j

lemma GrW_mul {r : ℕ} {Φ Ψ : Polynomial (MvPolynomial σ ℚ)} (h1 : GrW r Φ) (h2 : GrW r Ψ) :
    GrW r (Φ * Ψ) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine IsHomogeneous.sum _ _ _ fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  have := (h1 x.1).mul (h2 x.2)
  rwa [← add_mul, hx] at this

lemma GrW_intCast (r : ℕ) (c : ℤ) : GrW r (c : Polynomial (MvPolynomial σ ℚ)) := by
  intro j
  rw [← map_intCast (Polynomial.C : MvPolynomial σ ℚ →+* _) c, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [← map_intCast (C : ℚ →+* MvPolynomial σ ℚ) c, zero_mul]
    exact isHomogeneous_C _ _
  · exact isHomogeneous_zero _ _ _

lemma GrW_eval₂ {r : ℕ} {τ : Type*} (res : MvPolynomial τ ℤ)
    (g : τ → Polynomial (MvPolynomial σ ℚ)) (hg : ∀ v, GrW r (g v)) :
    GrW r (MvPolynomial.eval₂ (Int.castRingHom _) g res) := by
  induction res using MvPolynomial.induction_on with
  | C a => rw [eval₂_C]; exact GrW_intCast r a
  | add p q hp hq => rw [eval₂_add]; exact GrW_add hp hq
  | mul_X p v hp => rw [eval₂_mul, eval₂_X]; exact GrW_mul hp (hg v)

lemma newtonTr_homW {r : ℕ} {Φ : Polynomial (MvPolynomial σ ℚ)} (h : GrW r Φ) (d : ℕ) :
    (newtonTr Φ d).IsHomogeneous (d * r) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => rw [newtonTr]; exact isHomogeneous_zero _ _ _
    | succ d =>
      rw [newtonTr]
      refine IsHomogeneous.sub ?_ ?_
      · refine IsHomogeneous.neg ?_
        rw [← map_natCast (C : ℚ →+* MvPolynomial σ ℚ) (d + 1)]
        have := (isHomogeneous_C σ ((d + 1 : ℕ) : ℚ)).mul (h (d + 1))
        rwa [zero_add] at this
      · refine IsHomogeneous.sum _ _ _ fun j _ => ?_
        have := (ih j j.isLt).mul (h (d + 1 - j))
        rwa [← add_mul, show (j : ℕ) + (d + 1 - j) = d + 1 by omega] at this

end VHomAux

open VHomAux in
theorem solution (n k : ℕ)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (d : ℕ) :
    (newtonTr (phiPoly (k := k) (vTensor n k) res) d).IsHomogeneous (d * (k - 1)) := by
  classical
  refine newtonTr_homW ?_ d
  have hΦ : phiPoly (k := k) (vTensor n k) res =
      MvPolynomial.eval₂ (Int.castRingHom _)
        (fun v : ResVar n (fun _ => k - 1) => coeff v.2.1 (zcoord (k := k) (vTensor n k) v.1))
        res := by
    unfold phiPoly
    rw [aeval_def, eval₂_map]
    congr 1
  rw [hΦ]
  refine GrW_eval₂ res _ fun v => ?_
  unfold zcoord
  rw [coeff_sub, coeff_monomial, coeff_sum]
  refine GrW_sub ?_ (GrW_sum _ _ fun t _ => ?_)
  · split_ifs
    · intro j; rw [Polynomial.coeff_one]; split_ifs with h
      · subst h; rw [zero_mul]; exact isHomogeneous_one _ _
      · exact isHomogeneous_zero _ _ _
    · intro j; rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
  · rw [coeff_monomial]
    split_ifs
    · intro j
      rw [Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        rw [one_mul]
        have := IsHomogeneous.prod (univ : Finset (Fin (k - 1)))
          (fun s => (X (v.1, t s) : AuxPoly n)) (fun _ => 1) fun s _ => isHomogeneous_X _ _
        simpa [vTensor] using this
      · exact isHomogeneous_zero _ _ _
    · intro j; rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
