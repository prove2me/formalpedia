-- Prove2me | solution 1 for HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker2D_gridT
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:29:50.673525+00:00
-- url     : https://prove2.me/submissions/29434cf0-ba1a-4c0b-bfa7-14e562a7a338

import Definitions.Def_HodgeComputerFormal_PolyEncoding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace PolynomialEncoding.KroneckerCheck
open scoped BigOperators Polynomial
lemma poly_eq_zero_of_eval_base (f : Polynomial ℤ) (B : ℕ)
    (hM : polyL1 f < B) (hev : f.eval (B : ℤ) = 0) : f = 0 := by
  suffices h : ∀ n (g : Polynomial ℤ), g.natDegree ≤ n → polyL1 g < B → g.eval (B : ℤ) = 0 → g = 0 from
    h f.natDegree f le_rfl hM hev
  intro n
  induction n with
  | zero =>
    intro g hdeg hMg hevg
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg] at hevg ⊢
    simp only [Polynomial.eval_C] at hevg
    simp [hevg]
  | succ n ih =>
    intro g hdeg hMg hevg
    by_cases hg0 : g = 0
    · exact hg0
    · have hc0_le : (g.coeff 0).natAbs ≤ polyL1 g := by
        by_cases h0 : g.coeff 0 = 0
        · simp [h0]
        · unfold polyL1
          exact Finset.single_le_sum (f := fun i => (g.coeff i).natAbs) (fun _ _ => Nat.zero_le _)
            (Polynomial.mem_support_iff.mpr h0)
      have hsplit : g = Polynomial.C (g.coeff 0) + Polynomial.X * g.divX := by
        rw [add_comm]; exact (Polynomial.X_mul_divX_add g).symm
      have hev' : g.coeff 0 + (B : ℤ) * g.divX.eval (B : ℤ) = 0 := by
        have h := congrArg (fun p : Polynomial ℤ => p.eval (B : ℤ)) hsplit
        simp only [hevg, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] at h
        exact h.symm
      have hdvdZ : (B : ℤ) ∣ g.coeff 0 := ⟨-g.divX.eval (B : ℤ), by linarith⟩
      have hdvdN : B ∣ (g.coeff 0).natAbs := Int.natCast_dvd.mp hdvdZ
      have hc0_abs : (g.coeff 0).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvdN (lt_of_le_of_lt hc0_le hMg)
      have hc0 : g.coeff 0 = 0 := Int.natAbs_eq_zero.mp hc0_abs
      rw [hc0, zero_add] at hev'
      have hB_ne : (B : ℤ) ≠ 0 := by omega
      have hdiv_ev : g.divX.eval (B : ℤ) = 0 := (mul_eq_zero.mp hev').resolve_left hB_ne
      have hdiv_L1 : polyL1 g.divX ≤ polyL1 g := by
        rw [polyL1_eq_sum_range g.divX g.natDegree (fun i hi => by
          have hlt := Polynomial.le_natDegree_of_mem_supp i hi
          have hle := natDegree_divX_le_pred g
          have hne : g.natDegree ≠ 0 := by
            intro hz
            have hgC := Polynomial.eq_C_of_natDegree_eq_zero hz
            rw [hgC, Polynomial.divX_C] at hi
            simp at hi
          omega),
          polyL1_eq_sum_range g (g.natDegree + 1) (fun i hi => Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi)),
          Finset.sum_range_succ']
        simp only [Polynomial.coeff_divX]
        exact Nat.le_add_right _ _
      have hdiv_deg : g.divX.natDegree ≤ n := (natDegree_divX_le_pred g).trans (by omega)
      have hdiv0 : g.divX = 0 := ih g.divX hdiv_deg (lt_of_le_of_lt hdiv_L1 hMg) hdiv_ev
      rw [hsplit, hc0, hdiv0]; simp

/-- Soundness of 1D Kronecker (in variable `0`) × 2D grid (in variables `1, 2`) vanishing check. -/

theorem mvPoly3_eq_zero_of_kronecker2D_gridT (p : P3Z) (b : PB) (D Tmax B : ℕ)
    (T_pts : Finset ℤ)
    (hR : RespectsBound2D D Tmax p b)
    (hS_deg : b.dS < D)
    (hT_deg : b.dT < T_pts.card) (hT_bd : ∀ t ∈ T_pts, t.natAbs ≤ Tmax)
    (hB : b.M < B)
    (hev : ∀ t ∈ T_pts, MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = 0) :
    p = 0 := by
  have hevalT_zero : ∀ t ∈ T_pts, evalT2D D t p = 0 := fun t ht => by
    apply poly_eq_zero_of_eval_base (evalT2D D t p) B
    · exact lt_of_le_of_lt (hR.2 t (hT_bd t ht)) hB
    · rw [eval_evalT2D]; exact hev t ht
  let polyT_of (i j : ℕ) : Polynomial ℤ :=
    ∑ m ∈ p.support.filter (fun m => m 0 = i ∧ m 1 = j), Polynomial.C (p.coeff m) * Polynomial.X ^ m 2
  have hpolyT_eval (i j : ℕ) (hi : i < D) (t : ℤ) : (polyT_of i j).eval t = (evalT2D D t p).coeff (i + D * j) := by
    conv_rhs => rw [p.as_sum]
    dsimp only [polyT_of]
    rw [Finset.sum_filter, show ∀ f : Polynomial ℤ, f.eval t = Polynomial.evalRingHom t f from fun _ => rfl,
      map_sum, map_sum, ← Polynomial.lcoeff_apply, map_sum]
    apply Finset.sum_congr rfl; intro m hm
    simp only [Polynomial.coe_evalRingHom, Polynomial.lcoeff_apply, evalT2D, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
    have hrew : Polynomial.C (p.coeff m) * (Polynomial.X ^ m 0 * (Polynomial.X ^ D) ^ m 1 * Polynomial.C t ^ m 2) =
        Polynomial.C (p.coeff m * t ^ m 2) * Polynomial.X ^ (m 0 + D * m 1) := by
      rw [← pow_mul, ← pow_add]; simp only [map_mul, map_pow]; ring
    rw [hrew, Polynomial.coeff_C_mul_X_pow]
    have hlt0 : m 0 < D := lt_of_le_of_lt (hR.1 m hm).1 hS_deg
    have hiff : i + D * j = m 0 + D * m 1 ↔ m 0 = i ∧ m 1 = j := by
      constructor
      · intro h
        have h1 : m 1 = j := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
        subst h1
        exact ⟨by omega, rfl⟩
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases h : m 0 = i ∧ m 1 = j
    · rw [if_pos h, if_pos (hiff.mpr h)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    · rw [if_neg h, if_neg (fun heq => h (hiff.mp heq)), Polynomial.eval_zero]
  have hpolyT_zero (i j : ℕ) (hi : i < D) : polyT_of i j = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (polyT_of i j) T_pts
    · intro t ht; rw [hpolyT_eval i j hi t, hevalT_zero t ht, Polynomial.coeff_zero]
    · refine lt_of_le_of_lt ?_ hT_deg
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun m hm => ?_⟩
      have hm' := (Finset.mem_filter.mp hm).1
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (hR.1 m hm').2.2
  ext m
  by_cases hm : m ∈ p.support
  · have hlt0 : m 0 < D := lt_of_le_of_lt (hR.1 m hm).1 hS_deg
    have hcm : (polyT_of (m 0) (m 1)).coeff (m 2) = p.coeff m := by
      dsimp only [polyT_of]
      rw [Finset.sum_filter, ← Polynomial.lcoeff_apply, map_sum]
      have hterm : ∀ m' : Fin 3 →₀ ℕ,
          Polynomial.lcoeff ℤ (m 2) (if m' 0 = m 0 ∧ m' 1 = m 1 then Polynomial.C (p.coeff m') * Polynomial.X ^ m' 2 else 0) =
          if m' = m then p.coeff m' else 0 := fun m' => by
        simp only [Polynomial.lcoeff_apply]
        by_cases heq : m' = m
        · subst heq; simp
        · have hne : ¬(m' 0 = m 0 ∧ m' 1 = m 1 ∧ m 2 = m' 2) := by
            rintro ⟨h0, h1, h2⟩
            apply heq; ext j; fin_cases j
            · exact h0
            · exact h1
            · exact h2.symm
          by_cases h01 : m' 0 = m 0 ∧ m' 1 = m 1
          · have h2 : m 2 ≠ m' 2 := fun h => hne ⟨h01.1, h01.2, h⟩
            simp [heq, h01, h2]
          · simp [heq, h01]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq' p.support m p.coeff, if_pos hm]
    rw [← hcm, hpolyT_zero (m 0) (m 1) hlt0, Polynomial.coeff_zero]
    simp
  · simp [MvPolynomial.notMem_support_iff.mp hm]

end PolynomialEncoding.KroneckerCheck

theorem solution
    (p : PolynomialEncoding.KroneckerCheck.P3Z)
    (b : PolynomialEncoding.KroneckerCheck.PB) (D Tmax B : ℕ)
    (T_pts : Finset ℤ)
    (hR : PolynomialEncoding.KroneckerCheck.RespectsBound2D D Tmax p b)
    (hS_deg : b.dS < D)
    (hT_deg : b.dT < T_pts.card) (hT_bd : ∀ t ∈ T_pts, t.natAbs ≤ Tmax)
    (hB : b.M < B)
    (hev : ∀ t ∈ T_pts,
      MvPolynomial.eval (PolynomialEncoding.KroneckerCheck.v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = 0) :
    p = 0 :=
  PolynomialEncoding.KroneckerCheck.mvPoly3_eq_zero_of_kronecker2D_gridT
    p b D Tmax B T_pts hR hS_deg hT_deg hT_bd hB hev
