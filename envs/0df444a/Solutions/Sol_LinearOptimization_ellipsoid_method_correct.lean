-- Prove2me | solution 1 for LinearOptimization.ellipsoid_method_correct
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T02:43:53.151422+00:00
-- url     : https://prove2.me/submissions/f48a4d2a-db94-43fe-9936-48dff983166b

import Theorems.Thm_LinearOptimization_ellipsoid_update_halfspace_volume
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

open Matrix MeasureTheory
open LinearOptimization

private theorem ellipsoid_iteration_factor_le {n t : ℕ} (v V : ℝ)
    (hv : 0 < v) (hV : 0 < V)
    (ht : t = ⌈2 * ((n : ℝ) + 1) * Real.log (V / v)⌉₊) :
    ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) ^ t *
        ENNReal.ofReal V ≤ ENNReal.ofReal v := by
  let c : ℝ := -(1 : ℝ) / (2 * ((n : ℝ) + 1))
  let L : ℝ := 2 * ((n : ℝ) + 1) * Real.log (V / v)
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hc : c < 0 := by
    dsimp [c]
    exact div_neg_of_neg_of_pos (by norm_num) hden
  have hceil : L ≤ (t : ℝ) := by
    rw [ht]
    exact Nat.le_ceil L
  have hmul : (t : ℝ) * c ≤ -Real.log (V / v) := by
    calc
      (t : ℝ) * c ≤ L * c := mul_le_mul_of_nonpos_right hceil hc.le
      _ = -Real.log (V / v) := by
        dsimp [L, c]
        field_simp
  have hratio : Real.exp (-Real.log (V / v)) = v / V := by
    rw [Real.exp_neg, Real.exp_log (div_pos hV hv)]
    field_simp
  have hpow : Real.exp c ^ t ≤ v / V := by
    calc
      Real.exp c ^ t = Real.exp ((t : ℝ) * c) := (Real.exp_nat_mul c t).symm
      _ ≤ Real.exp (-Real.log (V / v)) := Real.exp_le_exp.mpr hmul
      _ = v / V := hratio
  have hreal : Real.exp c ^ t * V ≤ v := by
    calc
      Real.exp c ^ t * V ≤ (v / V) * V :=
        mul_le_mul_of_nonneg_right hpow hV.le
      _ = v := by field_simp
  rw [show Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1))) = Real.exp c by rfl,
    ← ENNReal.ofReal_pow (Real.exp_pos c).le,
    ← ENNReal.ofReal_mul (pow_nonneg (Real.exp_pos c).le t)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Bertsimas--Tsitsiklis, Theorem 8.2, p. 372: the containment and volume
invariants for the central-cut ellipsoid run, followed by the iteration-count
calculation `exp (-t/(2(n+1))) * V ≤ v`. -/
theorem solution {m n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x0 : Fin n → ℝ) (r v V : ℝ) (hr : 0 < r) (hv : 0 < v)
    (hbdd : IsBoundedSet (polyhedron A b))
    (hdim : polyhedron A b = ∅ ∨ IsFullDimensional (polyhedron A b))
    (hcover : polyhedron A b ⊆ ellipsoidBall x0 r)
    (hV : volume (ellipsoidBall x0 r) ≤ ENNReal.ofReal V)
    (hvol : polyhedron A b ≠ ∅ →
      ENNReal.ofReal v < volume (polyhedron A b))
    (tstar : ℕ)
    (htstar : tstar = ⌈2 * ((n : ℝ) + 1) * Real.log (V / v)⌉₊)
    (x : ℕ → Fin n → ℝ) (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hx0 : x 0 = x0)
    (hD0 : D 0 = r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hrun : IsEllipsoidRun A b x D tstar)
    (hmiss : ∀ t < tstar, x t ∉ polyhedron A b) :
    polyhedron A b = ∅ := by
  classical
  by_contra hPne
  have hPnonempty : (polyhedron A b).Nonempty := Set.nonempty_iff_ne_empty.mpr hPne
  let q : ENNReal := ENNReal.ofReal
    (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1))))
  have hDinit : (D 0).PosDef := by
    rw [hD0]
    exact Matrix.PosDef.smul Matrix.PosDef.one (sq_pos_of_pos hr)
  have hinv : ∀ t ≤ tstar,
      (D t).PosDef ∧
      polyhedron A b ⊆ ellipsoid (x t) (D t) ∧
      volume (ellipsoid (x t) (D t)) ≤
        q ^ t * volume (ellipsoid (x 0) (D 0)) := by
    intro t ht
    induction t with
    | zero =>
        refine ⟨hDinit, ?_, ?_⟩
        · simpa [ellipsoidBall, hx0, hD0] using hcover
        · simp
    | succ t ih =>
        have htlt : t < tstar := Nat.lt_of_succ_le ht
        have iht := ih (Nat.le_trans (Nat.le_succ t) ht)
        rcases hrun t htlt (hmiss t htlt) with ⟨i, hviol, hxnext, hDnext⟩
        have hai : A i ≠ 0 := by
          intro hai0
          obtain ⟨y, hy⟩ := hPnonempty
          have hyi : b i ≤ A i ⬝ᵥ y := by
            exact hy i
          rw [hai0] at hviol hyi
          simp [dotProduct] at hviol hyi
          linarith
        have hup := ellipsoid_update_halfspace_volume hn (x t) (D t) iht.1 (A i) hai
        refine ⟨?_, ?_, ?_⟩
        · rw [hDnext]
          exact hup.1
        · intro y hy
          rw [hxnext, hDnext]
          apply hup.2.1
          refine ⟨iht.2.1 hy, ?_⟩
          have hyi : b i ≤ A i ⬝ᵥ y := hy i
          exact hviol.le.trans hyi
        · rw [hxnext, hDnext]
          calc
            volume (ellipsoid (ellipsoidUpdateCenter (x t) (D t) (A i))
                (ellipsoidUpdateMatrix (D t) (A i))) ≤
                q * volume (ellipsoid (x t) (D t)) := by
              exact hup.2.2.le
            _ ≤ q * (q ^ t * volume (ellipsoid (x 0) (D 0))) :=
              mul_le_mul_of_nonneg_left iht.2.2 zero_le
            _ = q ^ (t + 1) * volume (ellipsoid (x 0) (D 0)) := by
              rw [pow_succ]
              ac_rfl
  have hfinal := hinv tstar le_rfl
  have hP_le_E : volume (polyhedron A b) ≤
      volume (ellipsoid (x tstar) (D tstar)) := measure_mono hfinal.2.1
  have hE0_le : volume (ellipsoid (x 0) (D 0)) ≤ ENNReal.ofReal V := by
    simpa [ellipsoidBall, hx0, hD0] using hV
  have hvol_iter : volume (polyhedron A b) ≤ q ^ tstar * ENNReal.ofReal V :=
    hP_le_E.trans (hfinal.2.2.trans (mul_le_mul_of_nonneg_left hE0_le zero_le))
  have hP_le_V : volume (polyhedron A b) ≤ ENNReal.ofReal V :=
    (measure_mono hcover).trans hV
  have hvVenn : ENNReal.ofReal v < ENNReal.ofReal V :=
    (hvol hPne).trans_le hP_le_V
  have hVpos : 0 < V := by
    rw [← ENNReal.ofReal_pos]
    exact (ENNReal.ofReal_pos.mpr hv).trans hvVenn
  have hfactor : q ^ tstar * ENNReal.ofReal V ≤ ENNReal.ofReal v := by
    simpa [q] using ellipsoid_iteration_factor_le v V hv hVpos htstar
  exact (not_le_of_gt (hvol hPne)) (hvol_iter.trans hfactor)
