-- Prove2me | solution 1 for HararySachs.Hyper.det_generic_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T22:26:10.108217+00:00
-- url     : https://prove2.me/submissions/340c8d4a-db49-489a-8a43-0b75bde48041

import Mathlib

open Finset

namespace DetIrrAux

/-- `a T + b` is irreducible over a domain if `a` is irreducible and `a ∤ b`. -/
lemma irreducible_linear {R : Type*} [CommRing R] [IsDomain R] (a b : R) (ha : Irreducible a)
    (hab : ¬ a ∣ b) : Irreducible (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hdeg : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 :=
    Polynomial.natDegree_linear ha0
  have hp0 : (Polynomial.C a * Polynomial.X + Polynomial.C b) ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hdeg; exact zero_ne_one hdeg
  have hc1 : (Polynomial.C a * Polynomial.X + Polynomial.C b).coeff 1 = a := by simp
  have hc0 : (Polynomial.C a * Polynomial.X + Polynomial.C b).coeff 0 = b := by simp
  -- if the polynomial is `p * C c`, then `C c` is a unit
  have key : ∀ (p : Polynomial R) (c : R),
      Polynomial.C a * Polynomial.X + Polynomial.C b = p * Polynomial.C c →
        IsUnit (Polynomial.C c) := by
    intro p c h
    have h1 : a = p.coeff 1 * c := by rw [← hc1, h, Polynomial.coeff_mul_C]
    have h0 : b = p.coeff 0 * c := by rw [← hc0, h, Polynomial.coeff_mul_C]
    rcases ha.isUnit_or_isUnit h1 with hu | hu
    · exfalso
      apply hab
      obtain ⟨u, hu⟩ := hu
      refine ⟨p.coeff 0 * ↑u⁻¹, ?_⟩
      rw [h0, h1, ← hu, show (↑u : R) * c * (p.coeff 0 * ↑u⁻¹) =
        (↑u * ↑u⁻¹) * (p.coeff 0 * c) by ring, Units.mul_inv, one_mul]
    · exact Polynomial.isUnit_C.mpr hu
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun f g hfg => ?_⟩
  · rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at hdeg; exact zero_ne_one hdeg
  have hf0 : f ≠ 0 := fun h => hp0 (by rw [hfg, h, zero_mul])
  have hg0 : g ≠ 0 := fun h => hp0 (by rw [hfg, h, mul_zero])
  have hsum := Polynomial.natDegree_mul hf0 hg0
  rw [← hfg, hdeg] at hsum
  rcases (show g.natDegree = 0 ∨ f.natDegree = 0 by omega) with h | h
  · have hg := Polynomial.eq_C_of_natDegree_eq_zero h
    right
    rw [hg]
    exact key f (g.coeff 0) (by rw [hfg, ← hg])
  · have hf := Polynomial.eq_C_of_natDegree_eq_zero h
    left
    rw [hf]
    exact key g (f.coeff 0) (by rw [hfg, ← hf, mul_comm])

variable (K : Type*) [Field K]

/-- isolating one variable: `K[σ] ≃ K[σ \ {s₀}][T]` with `X s₀ ↦ T` -/
noncomputable def iso {σ : Type} [DecidableEq σ] (s0 : σ) :
    MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {s // s ≠ s0} K) :=
  (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe s0).symm).trans
    (MvPolynomial.optionEquivLeft K {s // s ≠ s0})

lemma iso_X_self {σ : Type} [DecidableEq σ] (s0 : σ) : iso K s0 (MvPolynomial.X s0) = Polynomial.X := by
  simp [iso, Equiv.optionSubtypeNe_symm_self, MvPolynomial.optionEquivLeft_X_none]

lemma iso_X_ne {σ : Type} [DecidableEq σ] (s0 s : σ) (h : s ≠ s0) :
    iso K s0 (MvPolynomial.X s) = Polynomial.C (MvPolynomial.X ⟨s, h⟩) := by
  simp [iso, Equiv.optionSubtypeNe_symm_of_ne h, MvPolynomial.optionEquivLeft_X_some]

lemma det_map_C {R : Type*} [CommRing R] {N : ℕ} (Z : Matrix (Fin N) (Fin N) R) :
    (Z.map Polynomial.C).det = Polynomial.C Z.det :=
  (RingHom.map_det Polynomial.C Z).symm

/-- the generic determinant, in any set of variables, is irreducible -/
lemma det_irr_aux :
    ∀ (m : ℕ) (σ : Type) (g : Fin (m + 1) × Fin (m + 1) → σ), Function.Injective g →
      Irreducible (Matrix.det (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.X (g (i, j)) : MvPolynomial σ K))) := by
  intro m
  induction m with
  | zero =>
    intro σ g hg
    classical
    refine (MulEquiv.irreducible_iff (iso K (g (0, 0)))).mp ?_
    rw [Matrix.det_fin_one, Matrix.of_apply, iso_X_self]
    exact Polynomial.irreducible_X
  | succ m ih =>
    intro σ g hg
    classical
    set s0 := g (0, 0) with hs0
    have hne : ∀ i j, (i, j) ≠ ((0 : Fin (m + 2)), (0 : Fin (m + 2))) → g (i, j) ≠ s0 :=
      fun i j h he => h (hg he)
    -- the matrix with the `(0,0)` entry removed, over `K[σ \ {s₀}]`
    set Y : Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial {s // s ≠ s0} K) :=
      Matrix.of fun i j => if h : (i, j) = (0, 0) then 0 else MvPolynomial.X ⟨g (i, j), hne i j h⟩
      with hY
    have hentry : ∀ i j, iso K s0 (MvPolynomial.X (g (i, j))) =
        (if (i, j) = (0, 0) then Polynomial.X else 0) + Polynomial.C (Y i j) := by
      intro i j
      by_cases h : (i, j) = (0, 0)
      · rw [if_pos h]
        simp only [hY, Matrix.of_apply, dif_pos h, map_zero, add_zero]
        rw [Prod.mk.injEq] at h
        rw [h.1, h.2, iso_X_self]
      · rw [if_neg h, zero_add]
        simp only [hY, Matrix.of_apply, dif_neg h]
        exact iso_X_ne K s0 _ (hne i j h)
    have hM : (Matrix.of fun i j : Fin (m + 2) => (MvPolynomial.X (g (i, j)) : MvPolynomial σ K)).map
        (iso K s0) = (Y.map Polynomial.C).updateRow 0
          ((Y.map Polynomial.C) 0 + Polynomial.X • Pi.single 0 1) := by
      ext i j : 1
      rw [Matrix.map_apply, Matrix.of_apply, hentry]
      by_cases hi : i = 0
      · subst hi
        rw [Matrix.updateRow_self, Pi.add_apply, Matrix.map_apply, Pi.smul_apply]
        by_cases hj : j = 0
        · subst hj; simp [add_comm]
        · simp [hj]
      · rw [Matrix.updateRow_ne hi, Matrix.map_apply]
        have : (i, j) ≠ ((0 : Fin (m + 2)), (0 : Fin (m + 2))) := fun h =>
          hi (congrArg Prod.fst h)
        rw [if_neg this, zero_add]
    -- `Φ(det) = C a * T + C b`
    set a := (Y.submatrix Fin.succ Fin.succ).det with ha_def
    set b := Y.det with hb_def
    have hminor : ((Y.map Polynomial.C).updateRow 0 (Pi.single 0 1)).det = Polynomial.C a := by
      rw [Matrix.det_succ_row_zero, sum_eq_single 0]
      · rw [Matrix.updateRow_self, Pi.single_eq_same, Fin.succAbove_zero, Fin.val_zero, pow_zero,
          one_mul, one_mul, ha_def, ← det_map_C]
        congr 1
      · intro j _ hj
        rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
      · simp
    have hdet : iso K s0 (Matrix.det (Matrix.of fun i j : Fin (m + 2) =>
        (MvPolynomial.X (g (i, j)) : MvPolynomial σ K))) =
          Polynomial.C a * Polynomial.X + Polynomial.C b := by
      rw [AlgEquiv.map_det, AlgEquiv.mapMatrix_apply, hM, Matrix.det_updateRow_add,
        Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hminor, det_map_C, hb_def]
      ring
    -- the minor is irreducible by induction
    have ha : Irreducible a := by
      have hg' : Function.Injective (fun p : Fin (m + 1) × Fin (m + 1) =>
          (⟨g (p.1.succ, p.2.succ), hne _ _ (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h))⟩ :
            {s // s ≠ s0})) := by
        intro p q hpq
        simp only [Subtype.mk.injEq] at hpq
        have := hg hpq
        simp only [Prod.mk.injEq] at this
        exact Prod.ext (Fin.succ_injective _ this.1) (Fin.succ_injective _ this.2)
      have := ih {s // s ≠ s0} _ hg'
      convert this using 2
      ext i j
      simp only [Matrix.submatrix_apply, hY, Matrix.of_apply]
      rw [dif_neg (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h))]
    -- `a ∤ b`: evaluate at the transposition `(0 1)`
    have hab : ¬ a ∣ b := by
      rintro ⟨q, hq⟩
      set P : Matrix (Fin (m + 2)) (Fin (m + 2)) K := (Equiv.swap 0 1).permMatrix K with hP
      have hP00 : P 0 0 = 0 := by simp [hP, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply]
      have hP1 : ∀ j : Fin (m + 1), P 1 j.succ = 0 := by
        intro j
        simp [hP, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, Equiv.swap_apply_of_ne_of_ne,
          Fin.succ_ne_zero]
        exact (Fin.succ_ne_zero j).symm
      set x : {s // s ≠ s0} → K := fun s => Function.extend g (fun p => P p.1 p.2) 0 s.1 with hx
      have hYx : Y.map (MvPolynomial.eval x) = P := by
        ext i j
        simp only [Matrix.map_apply, hY, Matrix.of_apply]
        split_ifs with h
        · rw [map_zero]
          rw [Prod.mk.injEq] at h
          rw [h.1, h.2, hP00]
        · rw [MvPolynomial.eval_X, hx]
          exact hg.extend_apply _ _ (i, j)
      have hb : MvPolynomial.eval x b = -1 := by
        rw [hb_def, RingHom.map_det, RingHom.mapMatrix_apply, hYx, hP, Matrix.det_permutation,
          Equiv.Perm.sign_swap (by simp)]
        simp
      have ha0 : MvPolynomial.eval x a = 0 := by
        rw [ha_def, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hYx]
        refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
        rw [Matrix.submatrix_apply, Fin.succ_zero_eq_one]
        exact hP1 j
      have := congrArg (MvPolynomial.eval x) hq
      rw [map_mul, ha0, zero_mul, hb] at this
      exact neg_ne_zero.mpr one_ne_zero this
    refine (MulEquiv.irreducible_iff (iso K s0)).mp ?_
    rw [hdet]
    exact irreducible_linear a b ha hab

end DetIrrAux

open DetIrrAux in
theorem solution (K : Type*) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (Matrix.det (Matrix.of fun i j : Fin n =>
      (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) K))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact det_irr_aux K m (Fin (m + 1) × Fin (m + 1)) id Function.injective_id
