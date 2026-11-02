-- Prove2me | solution 1 for HighDimProbAudit.Grothendieck.sphere_linearization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:11:41.539884+00:00
-- url     : https://prove2.me/submissions/c0b895f6-14ad-4055-bed4-647786364701

import Mathlib

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace SolSphereLinearization

noncomputable def tp {n : ℕ} (k : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin k → Fin n) :=
  WithLp.toLp 2 (fun t : Fin k → Fin n => ∏ r : Fin k, u (t r))

lemma tp_inner (n k : ℕ) (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (tp k u) (tp k v) = (inner ℝ u v) ^ k := by
  simp only [tp, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  have h1 : ∑ t : Fin k → Fin n, (∏ r : Fin k, v (t r)) * (∏ r : Fin k, u (t r)) =
      ∑ t : Fin k → Fin n, ∏ r : Fin k, (v (t r) * u (t r)) := by
    refine Finset.sum_congr rfl fun t _ => (Finset.prod_mul_distrib).symm
  rw [h1, ← Fintype.prod_sum (fun (_ : Fin k) (i : Fin n) => v i * u i)]
  simp

lemma tp_norm_sq (n k : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    ‖tp k u‖ ^ 2 = ‖u‖ ^ (2 * k) := by
  have h1 : ‖tp k u‖ ^ 2 = inner ℝ (tp k u) (tp k u) := by
    rw [real_inner_self_eq_norm_mul_norm, sq]
  have h2 : inner ℝ u u = ‖u‖ ^ 2 := by
    rw [real_inner_self_eq_norm_mul_norm, sq]
  rw [h1, tp_inner, h2, ← pow_mul]

noncomputable def c : ℝ := Real.log (1 + Real.sqrt 2)

lemma c_nonneg : 0 ≤ c := by
  unfold c
  refine Real.log_nonneg ?_
  linarith [Real.sqrt_nonneg 2]

lemma c_le_pi_div_two : c ≤ Real.pi / 2 := by
  unfold c
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hexp : 3 / 2 + 1 ≤ Real.exp (3 / 2) := Real.add_one_le_exp (3 / 2)
  have hpi : (3 : ℝ) / 2 ≤ Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  have hexp_mono : Real.exp (3 / 2) ≤ Real.exp (Real.pi / 2) :=
    Real.exp_le_exp.mpr hpi
  linarith

lemma sinh_c : Real.sinh c = 1 := by
  unfold c
  rw [Real.sinh_eq]
  have hpos : 0 < 1 + Real.sqrt 2 := by positivity
  rw [Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc (1 + Real.sqrt 2) * (Real.sqrt 2 - 1)
      _ = (Real.sqrt 2) ^ 2 - 1 := by ring
      _ = 2 - 1 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 1 := by ring
  rw [hinv]
  ring

noncomputable def coeff (m : ℕ) : ℝ :=
  c ^ (2 * m + 1) / (2 * m + 1).factorial

lemma coeff_nonneg (m : ℕ) : 0 ≤ coeff m := by
  unfold coeff
  exact div_nonneg (pow_nonneg c_nonneg _) (Nat.cast_nonneg _)

lemma hasSum_coeff : HasSum coeff 1 := by
  rw [← sinh_c]
  exact Real.hasSum_sinh c

lemma hasSum_signed_coeff (x : ℝ) :
    HasSum (fun m : ℕ => (-1 : ℝ) ^ m * coeff m * x ^ (2 * m + 1)) (Real.sin (c * x)) := by
  have h : (fun m : ℕ => (-1 : ℝ) ^ m * coeff m * x ^ (2 * m + 1)) =
      fun m : ℕ => (-1 : ℝ) ^ m * (c * x) ^ (2 * m + 1) / (2 * m + 1).factorial := by
    ext m
    unfold coeff
    rw [mul_pow]
    ring
  rw [h]
  exact Real.hasSum_sin (c * x)

end SolSphereLinearization

open SolSphereLinearization

theorem solution (n : ℕ) :
    ∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧
          ∃ Φ Ψ : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1} → {z : H // ‖z‖ = 1},
            ∀ u v, (2 / Real.pi) * Real.arcsin (inner ℝ (Φ u).val (Ψ v).val) =
              ((2 / Real.pi) * Real.log (1 + Real.sqrt 2)) * inner ℝ u.val v.val := by
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let E (m : ℕ) := EuclideanSpace ℝ (Fin (2 * m + 1) → Fin n)
  let H := lp E 2
  refine ⟨H, inferInstance, inferInstance, inferInstance, ?_⟩
  let seqPhi (u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}) (m : ℕ) : E m :=
    Real.sqrt (coeff m) • tp (2 * m + 1) u.val
  let seqPsi (u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}) (m : ℕ) : E m :=
    ((-1 : ℝ) ^ m * Real.sqrt (coeff m)) • tp (2 * m + 1) u.val
  have h_norm_phi : ∀ (u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}) (m : ℕ),
      ‖seqPhi u m‖ ^ 2 = coeff m := by
    intro u m
    dsimp [seqPhi]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (coeff_nonneg m),
      tp_norm_sq, u.property, one_pow, mul_one]
  have h_norm_psi : ∀ (u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}) (m : ℕ),
      ‖seqPsi u m‖ ^ 2 = coeff m := by
    intro u m
    dsimp [seqPsi]
    have hneg : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow, hneg,
      Real.sq_sqrt (coeff_nonneg m), tp_norm_sq, u.property, one_pow, one_mul, mul_one]
  have h_mem_phi : ∀ u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}, Memℓp (seqPhi u) 2 := by
    intro u
    rw [memℓp_gen_iff (by norm_num)]
    refine hasSum_coeff.summable.congr fun m => ?_
    rw [← h_norm_phi u m, ENNReal.toReal_ofNat, Real.rpow_two]
  have h_mem_psi : ∀ u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}, Memℓp (seqPsi u) 2 := by
    intro u
    rw [memℓp_gen_iff (by norm_num)]
    refine hasSum_coeff.summable.congr fun m => ?_
    rw [← h_norm_psi u m, ENNReal.toReal_ofNat, Real.rpow_two]
  let rawPhi (u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}) : H := ⟨seqPhi u, h_mem_phi u⟩
  let rawPsi (u : {u : EuclideanSpace ℝ (Fin n) // ‖u‖ = 1}) : H := ⟨seqPsi u, h_mem_psi u⟩
  have h_unit_phi : ∀ u, ‖rawPhi u‖ = 1 := by
    intro u
    have h_inner := lp.hasSum_inner (𝕜 := ℝ) (rawPhi u) (rawPhi u)
    have h_eq : inner ℝ (rawPhi u) (rawPhi u) = ‖rawPhi u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, sq]
    have h_term : (fun m : ℕ => inner ℝ ((rawPhi u) m) ((rawPhi u) m)) = coeff := by
      ext m
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
      exact h_norm_phi u m
    rw [h_term, h_eq] at h_inner
    have h_sq : ‖rawPhi u‖ ^ 2 = 1 := h_inner.unique hasSum_coeff
    nlinarith [norm_nonneg (rawPhi u)]
  have h_unit_psi : ∀ u, ‖rawPsi u‖ = 1 := by
    intro u
    have h_inner := lp.hasSum_inner (𝕜 := ℝ) (rawPsi u) (rawPsi u)
    have h_eq : inner ℝ (rawPsi u) (rawPsi u) = ‖rawPsi u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, sq]
    have h_term : (fun m : ℕ => inner ℝ ((rawPsi u) m) ((rawPsi u) m)) = coeff := by
      ext m
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
      exact h_norm_psi u m
    rw [h_term, h_eq] at h_inner
    have h_sq : ‖rawPsi u‖ ^ 2 = 1 := h_inner.unique hasSum_coeff
    nlinarith [norm_nonneg (rawPsi u)]
  refine ⟨fun u => ⟨rawPhi u, h_unit_phi u⟩, fun v => ⟨rawPsi v, h_unit_psi v⟩, fun u v => ?_⟩
  have h_lp := lp.hasSum_inner (𝕜 := ℝ) (rawPhi u) (rawPsi v)
  have h_term : (fun m : ℕ => inner ℝ ((rawPhi u) m) ((rawPsi v) m)) =
      fun m : ℕ => (-1 : ℝ) ^ m * coeff m * (inner ℝ u.val v.val) ^ (2 * m + 1) := by
    ext m
    change inner ℝ (Real.sqrt (coeff m) • tp (2 * m + 1) u.val)
      (((-1 : ℝ) ^ m * Real.sqrt (coeff m)) • tp (2 * m + 1) v.val) = _
    rw [real_inner_smul_left, real_inner_smul_right, tp_inner]
    have hsq : Real.sqrt (coeff m) * Real.sqrt (coeff m) = coeff m :=
      Real.mul_self_sqrt (coeff_nonneg m)
    calc Real.sqrt (coeff m) * ((-1 : ℝ) ^ m * Real.sqrt (coeff m) * (inner ℝ u.val v.val) ^ (2 * m + 1))
      _ = (-1 : ℝ) ^ m * (Real.sqrt (coeff m) * Real.sqrt (coeff m)) * (inner ℝ u.val v.val) ^ (2 * m + 1) := by ring
      _ = (-1 : ℝ) ^ m * coeff m * (inner ℝ u.val v.val) ^ (2 * m + 1) := by rw [hsq]
  rw [h_term] at h_lp
  have h_inner_eq : inner ℝ (rawPhi u) (rawPsi v) = Real.sin (c * inner ℝ u.val v.val) :=
    h_lp.unique (hasSum_signed_coeff (inner ℝ u.val v.val))
  change (2 / Real.pi) * Real.arcsin (inner ℝ (rawPhi u) (rawPsi v)) =
    ((2 / Real.pi) * c) * inner ℝ u.val v.val
  rw [h_inner_eq]
  have huv_abs : |inner ℝ u.val v.val| ≤ 1 := by
    calc |inner ℝ u.val v.val|
      _ ≤ ‖u.val‖ * ‖v.val‖ := abs_real_inner_le_norm u.val v.val
      _ = 1 * 1 := by rw [u.property, v.property]
      _ = 1 := one_mul 1
  have huv_bounds := abs_le.mp huv_abs
  have hc_nonneg := c_nonneg
  have hc_pi := c_le_pi_div_two
  have h_low : -(Real.pi / 2) ≤ c * inner ℝ u.val v.val := by
    nlinarith
  have h_high : c * inner ℝ u.val v.val ≤ Real.pi / 2 := by
    nlinarith
  rw [Real.arcsin_sin h_low h_high]
  ring
