-- Prove2me | solution 1 for ModernConvex.PathFollowing.scaled_direction_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:07:51.981219+00:00
-- url     : https://prove2.me/submissions/617920bb-016a-4661-93ae-ab51642ac0c8

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

theorem g70mc2_sqrt_diag {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i) :
    CFC.sqrt (diagonal x) = diagonal fun i => Real.sqrt (x i) := by
  apply CFC.sqrt_unique
  · rw [diagonal_mul_diagonal]
    congr 1; ext i; exact Real.mul_self_sqrt (hx i)
  · rw [Matrix.nonneg_iff_posSemidef, posSemidef_diagonal_iff]
    intro i; exact Real.sqrt_nonneg _

theorem g70mc2_inv_diag {k : ℕ} (y : Fin k → ℝ) (hy : ∀ i, y i ≠ 0) :
    (diagonal y)⁻¹ = diagonal fun i => (y i)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [inv_mul_cancel₀ (hy i)]
  · simp [h, one_apply_ne h]

theorem g70mc2_diag_le {k : ℕ} (a : Fin k → Fin k → ℝ) :
    ∑ i, a i i ^ 2 ≤ ∑ i, ∑ j, a i j ^ 2 :=
  Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j => a i j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem g70mc2_gen {k : ℕ} (a b c : Fin k → Fin k → ℝ) (r : Fin k → ℝ) (lo hi M : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hM : 0 ≤ M) (hc : ∀ i j, lo ≤ c i j ∧ c i j ≤ hi)
    (hb : ∀ i j, b i j = (if i = j then r i else 0) - c i j * a i j)
    (hab : ∑ i, ∑ j, a i j * b i j = 0) (hr : ∑ i, r i ^ 2 ≤ M ^ 2) :
    Real.sqrt (∑ i, ∑ j, a i j ^ 2) ≤ M / lo ∧ Real.sqrt (∑ i, ∑ j, b i j ^ 2) ≤ hi * M / lo := by
  have hcpos : ∀ i j, 0 < c i j := fun i j => lt_of_lt_of_le hlo (hc i j).1
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have hsqrtr : Real.sqrt (∑ i, r i ^ 2) ≤ M := by
    rw [← Real.sqrt_sq hM]; exact Real.sqrt_le_sqrt hr
  constructor
  · set A := ∑ i, ∑ j, a i j ^ 2
    have e1 : ∑ i, ∑ j, c i j * a i j ^ 2 = ∑ i, a i i * r i := by
      have : ∑ i, ∑ j, a i j * b i j =
          ∑ i, a i i * r i - ∑ i, ∑ j, c i j * a i j ^ 2 := by
        simp_rw [hb, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        congr 1
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      linarith
    have h1 : lo * A ≤ ∑ i, ∑ j, c i j * a i j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc i j).1 (sq_nonneg _)
    have h2 : ∑ i, a i i * r i ≤ Real.sqrt A * M := by
      refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
      exact mul_le_mul (Real.sqrt_le_sqrt (g70mc2_diag_le a)) hsqrtr (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    have hA : Real.sqrt A ^ 2 = A := Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [le_div_iff₀ hlo]
    have hs := Real.sqrt_nonneg A
    have key : lo * Real.sqrt A ^ 2 ≤ Real.sqrt A * M := by rw [hA]; linarith
    by_contra hlt
    push Not at hlt
    have hpos : 0 < Real.sqrt A := by
      by_contra h0; push Not at h0
      have : Real.sqrt A = 0 := le_antisymm h0 hs
      rw [this] at hlt; linarith
    have := mul_lt_mul_of_pos_left hlt hpos
    nlinarith
  · set Bs := ∑ i, ∑ j, b i j ^ 2
    have ha : ∀ i j, a i j = ((if i = j then r i else 0) - b i j) / c i j := by
      intro i j; rw [hb]; field_simp [(hcpos i j).ne']; ring
    have e1 : ∑ i, ∑ j, b i j ^ 2 / c i j = ∑ i, r i * b i i / c i i := by
      have : ∑ i, ∑ j, a i j * b i j =
          ∑ i, r i * b i i / c i i - ∑ i, ∑ j, b i j ^ 2 / c i j := by
        simp_rw [ha]
        have : ∀ i j, ((if i = j then r i else 0) - b i j) / c i j * b i j =
            (if i = j then r i * b i i / c i i else 0) - b i j ^ 2 / c i j := by
          intro i j
          by_cases h : i = j
          · subst h; simp; ring
          · simp [h]; ring
        simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      linarith
    have h1 : Bs / hi ≤ ∑ i, ∑ j, b i j ^ 2 / c i j := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun j _ =>
        div_le_div_of_nonneg_left (sq_nonneg _) (hcpos i j) (hc i j).2
    have h2 : ∑ i, r i * b i i / c i i ≤ Real.sqrt Bs * M / lo := by
      calc ∑ i, r i * b i i / c i i ≤ ∑ i, |r i| * |b i i| / lo := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [div_le_div_iff₀ (hcpos i i) hlo]
            have h3 : r i * b i i * lo ≤ |r i| * |b i i| * lo :=
              mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_mul _ _).le) hlo.le
            have h4 : |r i| * |b i i| * lo ≤ |r i| * |b i i| * c i i :=
              mul_le_mul_of_nonneg_left (hc i i).1 (by positivity)
            linarith
        _ = (∑ i, |r i| * |b i i|) / lo := by rw [Finset.sum_div]
        _ ≤ Real.sqrt Bs * M / lo := by
            apply div_le_div_of_nonneg_right _ hlo.le
            refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
            simp only [sq_abs]
            rw [mul_comm (Real.sqrt Bs)]
            exact mul_le_mul hsqrtr (Real.sqrt_le_sqrt (g70mc2_diag_le b)) (Real.sqrt_nonneg _) hM
    have hB : Real.sqrt Bs ^ 2 = Bs := Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)
    have hs := Real.sqrt_nonneg Bs
    have h3 : Real.sqrt Bs ^ 2 / hi ≤ Real.sqrt Bs * M / lo := by rw [hB]; linarith
    rw [div_le_div_iff₀ hhi hlo] at h3
    rw [le_div_iff₀ hlo]
    by_contra hlt
    push Not at hlt
    have hpos : 0 < Real.sqrt Bs := by
      by_contra h0; push Not at h0
      have : Real.sqrt Bs = 0 := le_antisymm h0 hs
      rw [this] at hlt; nlinarith
    have := mul_lt_mul_of_pos_left hlt hpos
    nlinarith

theorem g70mc2_sd {k : ℕ} (hk : 0 < k) (κ χ : ℝ) (sx s : Fin k → ℝ) (hsx : ∀ i, 0 < sx i)
    (hs : ∀ i, 0 < s i) (htr : ∑ i, sx i ^ 2 * s i = k)
    (hclose : ∑ i, (sx i ^ 2 * s i - 1) ^ 2 ≤ κ ^ 2) (hχ : 0 < χ) (hχκ : χ ≤ κ) (hκ : κ ≤ 0.1)
    (dX dS : Matrix (Fin k) (Fin k) ℝ) (hsym : ∀ i j, dS j i = dS i j)
    (htrace : ∑ i, ∑ j, dX i j * dS j i = 0)
    (heq : ∀ i j, dX i j * s j + sx i ^ 2 * dS i j + dS i j * sx j ^ 2 + s i * dX i j =
      if i = j then 2 * ModernConvex.PathFollowing.muPlus k χ - 2 * (sx i ^ 2 * s i) else 0) :
    Real.sqrt (∑ i, ∑ j, ((sx i)⁻¹ * dX i j * (sx j)⁻¹) ^ 2) ≤ ModernConvex.PathFollowing.rho κ χ ∧
      Real.sqrt (∑ i, ∑ j, (sx i * dS i j * sx j) ^ 2) ≤
        (1 + κ) * ModernConvex.PathFollowing.rho κ χ := by
  set μ := ModernConvex.PathFollowing.muPlus k χ with hμ
  set w : Fin k → ℝ := fun i => sx i ^ 2 * s i with hw
  have hwb : ∀ i, 1 - κ ≤ w i ∧ w i ≤ 1 + κ := by
    intro i
    have h1 : (w i - 1) ^ 2 ≤ κ ^ 2 := le_trans (Finset.single_le_sum
      (f := fun i => (sx i ^ 2 * s i - 1) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hclose
    constructor <;> nlinarith
  set c : Fin k → Fin k → ℝ := fun i j => (w i * sx j ^ 2 + w j * sx i ^ 2) / (sx i ^ 2 + sx j ^ 2)
  set a : Fin k → Fin k → ℝ := fun i j => (sx i)⁻¹ * dX i j * (sx j)⁻¹
  set b : Fin k → Fin k → ℝ := fun i j => sx i * dS i j * sx j
  set r : Fin k → ℝ := fun i => μ - w i
  have hc : ∀ i j, 1 - κ ≤ c i j ∧ c i j ≤ 1 + κ := by
    intro i j
    have hd : 0 < sx i ^ 2 + sx j ^ 2 := by have := hsx i; positivity
    have hi2 : 0 < sx i ^ 2 := by have := hsx i; positivity
    have hj2 : 0 < sx j ^ 2 := by have := hsx j; positivity
    obtain ⟨a1, a2⟩ := hwb i
    obtain ⟨b1, b2⟩ := hwb j
    constructor
    · rw [le_div_iff₀ hd]; nlinarith
    · rw [div_le_iff₀ hd]; nlinarith
  have hb : ∀ i j, b i j = (if i = j then r i else 0) - c i j * a i j := by
    intro i j
    have e := heq i j
    have hi := (hsx i).ne'
    have hj := (hsx j).ne'
    have hd : sx i ^ 2 + sx j ^ 2 ≠ 0 := by have := hsx i; have := hsx j; positivity
    by_cases hij : i = j
    · subst hij
      simp only [if_true] at e ⊢
      have hcii : c i i = w i := by
        simp only [c]; field_simp
      have hwa : w i * a i i = s i * dX i i := by
        simp only [w, a]; field_simp
      rw [hcii, hwa]
      simp only [b, r, w]
      linear_combination e / 2
    · simp only [hij, if_false] at e ⊢
      simp only [b, c, a, w]
      field_simp
      linear_combination (sx i * sx j) * e
  have hab : ∑ i, ∑ j, a i j * b i j = 0 := by
    rw [← htrace]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [a, b, hsym]
    field_simp [(hsx i).ne', (hsx j).ne']
  have hr : ∑ i, r i ^ 2 ≤ Real.sqrt (χ ^ 2 + κ ^ 2) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    have hsum : ∑ i, (w i - 1) = 0 := by
      rw [Finset.sum_sub_distrib]; simp [w, htr]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hsk : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk'.le
    have hμ1 : (μ - 1) ^ 2 * k = χ ^ 2 := by
      rw [hμ]; unfold ModernConvex.PathFollowing.muPlus
      have : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hk').ne'
      field_simp; rw [hsk]; ring
    have : ∑ i, r i ^ 2 = (μ - 1) ^ 2 * k - 2 * (μ - 1) * ∑ i, (w i - 1) +
        ∑ i, (w i - 1) ^ 2 := by
      simp only [r, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      rw [show (μ - 1) ^ 2 * (k : ℝ) = ∑ _i : Fin k, (μ - 1) ^ 2 by simp [mul_comm]]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsum, hμ1]
    have : ∑ i, (w i - 1) ^ 2 ≤ κ ^ 2 := hclose
    linarith
  have hκ1 : 0 < 1 - κ := by linarith
  obtain ⟨g1, g2⟩ := g70mc2_gen a b c r (1 - κ) (1 + κ) (Real.sqrt (χ ^ 2 + κ ^ 2)) hκ1
    (by linarith) (Real.sqrt_nonneg _) hc hb hab hr
  refine ⟨g1, ?_⟩
  unfold ModernConvex.PathFollowing.rho
  rw [mul_div_assoc] at g2
  exact g2

open ModernConvex.PathFollowing

theorem solution {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (hd : P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) dX dS) :
    frobNorm ((CFC.sqrt (diagonal x))⁻¹ * dX * (CFC.sqrt (diagonal x))⁻¹) ≤ rho κ χ ∧
      frobNorm (CFC.sqrt (diagonal x) * dS * CFC.sqrt (diagonal x)) ≤ (1 + κ) * rho κ χ := by
  set sx : Fin k → ℝ := fun i => Real.sqrt (x i) with hsxdef
  have hsx : ∀ i, 0 < sx i := fun i => Real.sqrt_pos.mpr (h.x_pos i)
  have hxsq : ∀ i, sx i ^ 2 = x i := fun i => Real.sq_sqrt (h.x_pos i).le
  have hsqrt : CFC.sqrt (diagonal x) = diagonal sx :=
    g70mc2_sqrt_diag x fun i => (h.x_pos i).le
  have hinv : (diagonal sx)⁻¹ = diagonal fun i => (sx i)⁻¹ :=
    g70mc2_inv_diag sx fun i => (hsx i).ne'
  rw [hsqrt, hinv]
  unfold frobNorm
  simp only [mul_diagonal, diagonal_mul]
  obtain ⟨hdL, ⟨hSh, hSo⟩, heqM⟩ := hd
  apply g70mc2_sd hk κ χ sx s hsx h.s_pos
  · simp only [hxsq]; exact h.trace_eq
  · simp only [hxsq]; exact h.close
  · exact h.chi_pos
  · exact h.chi_le_kappa
  · exact h.kappa_le
  · intro i j; have := congrFun (congrFun hSh.eq i) j; simpa using this
  · have := hSo dX hdL
    rw [← this]; simp [trace, mul_apply]
  · intro i j
    have e := congrFun (congrFun heqM i) j
    simp only [hxsq]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.sub_apply, Matrix.smul_apply,
        diagonal_mul_diagonal] at e
      simp only [if_true]
      linarith
    · simp [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.sub_apply, Matrix.smul_apply,
        diagonal_mul_diagonal, hij, one_apply_ne hij] at e
      simp only [hij, if_false]
      linarith
