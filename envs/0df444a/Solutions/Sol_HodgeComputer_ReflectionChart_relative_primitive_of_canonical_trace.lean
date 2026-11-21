-- Prove2me | solution 1 for HodgeComputer.ReflectionChart.relative_primitive_of_canonical_trace
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T04:58:01.161549+00:00
-- url     : https://prove2.me/submissions/3bae39ee-e221-4675-8297-e4e0b969d4cd

import Definitions.Def_HodgeComputerReflectionChart
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTraceReduction
open MvPolynomial HodgeComputer.ReflectionChart
open scoped BigOperators

private def doubleLast (d : Fin 5 →₀ ℕ) : Fin 5 →₀ ℕ :=
  d + Finsupp.single 4 (d 4)

private lemma doubleLast_add (d₁ d₂ : Fin 5 →₀ ℕ) :
    doubleLast (d₁ + d₂) = doubleLast d₁ + doubleLast d₂ := by
  ext i
  simp only [doubleLast, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

private lemma doubleLast_injective : Function.Injective doubleLast := by
  intro d₁ d₂ h
  ext i
  have hi := Finsupp.ext_iff.mp h i
  simp only [doubleLast, Finsupp.add_apply, Finsupp.single_apply] at hi
  by_cases h4 : i = 4
  · subst h4; simp at hi; omega
  · have h4' : (4 : Fin 5) ≠ i := Ne.symm h4
    simpa [h4'] using hi

private lemma squareLift_monomial (d : Fin 5 →₀ ℕ) (c : ℂ) :
    squareLift (monomial d c) = monomial (doubleLast d) c := by
  rw [squareLift, eval₂Hom_monomial]
  have hprod : (∏ i ∈ d.support, (if i = (4 : Fin 5) then X i ^ 2 else (X i : ChartPoly)) ^ d i) =
      monomial (doubleLast d) 1 := by
    induction d using Finsupp.induction with
    | zero =>
      have h0 : doubleLast 0 = 0 := by ext i; simp [doubleLast]
      simp [h0]
    | single_add a b f ha hb ih =>
      rw [Finsupp.support_single_add ha hb, Finset.prod_cons]
      have hrest : (∏ x ∈ f.support, (if x = (4 : Fin 5) then X x ^ 2 else (X x : ChartPoly)) ^
          (Finsupp.single a b + f) x) =
          ∏ x ∈ f.support, (if x = (4 : Fin 5) then X x ^ 2 else (X x : ChartPoly)) ^ f x := by
        apply Finset.prod_congr rfl
        intro x hx
        have hxa : a ≠ x := fun h => ha (h ▸ hx)
        simp [Finsupp.single_apply, hxa]
      have hhead : (Finsupp.single a b + f) a = b := by
        simp [Finsupp.notMem_support_iff.mp ha]
      rw [hrest, hhead, ih, doubleLast_add]
      by_cases ha4 : a = 4
      · subst ha4
        have hdl : doubleLast (Finsupp.single 4 b) = Finsupp.single 4 (2 * b) := by
          ext i; simp [doubleLast, Finsupp.single_apply]; split_ifs <;> omega
        rw [if_pos rfl, ← pow_mul, X_pow_eq_monomial, hdl, monomial_mul, one_mul]
      · have hdl : doubleLast (Finsupp.single a b) = Finsupp.single a b := by
          ext i; simp [doubleLast, Finsupp.single_apply, ha4]
        rw [if_neg ha4, X_pow_eq_monomial, hdl, monomial_mul, one_mul]
  change C c * (∏ i ∈ d.support, (if i = (4 : Fin 5) then X i ^ 2 else (X i : ChartPoly)) ^ d i) = _
  rw [hprod, C_mul_monomial, mul_one]

private lemma coeff_squareLift_doubleLast (p : ChartPoly) (d : Fin 5 →₀ ℕ) :
    coeff (doubleLast d) (squareLift p) = coeff d p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [squareLift_monomial, coeff_monomial, coeff_monomial]
    simp [doubleLast_injective.eq_iff]
  | add p q hp hq =>
    simp [map_add, hp, hq]

private lemma coeff_squareLift_odd (p : ChartPoly) {m : Fin 5 →₀ ℕ} (hm : m 4 % 2 = 1) :
    coeff m (squareLift p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [squareLift_monomial, coeff_monomial]
    have hne : doubleLast d ≠ m := by
      intro h
      have h4 := congrArg (fun x : Fin 5 →₀ ℕ => x 4) h
      simp [doubleLast] at h4; omega
    simp [hne]
  | add p q hp hq =>
    simp [map_add, hp, hq]

private def halfLast (m : Fin 5 →₀ ℕ) : Fin 5 →₀ ℕ := m.update 4 (m 4 / 2)

private lemma doubleLast_halfLast {m : Fin 5 →₀ ℕ} (hm : m 4 % 2 = 0) :
    doubleLast (halfLast m) = m := by
  ext i; by_cases hi : i = 4
  · subst hi; simp [doubleLast, halfLast]; omega
  · simp [doubleLast, halfLast, hi]

private lemma halfLast_doubleLast (d : Fin 5 →₀ ℕ) : halfLast (doubleLast d) = d := by
  ext i; by_cases hi : i = 4
  · subst hi; simp [doubleLast, halfLast]; omega
  · simp [doubleLast, halfLast, hi]

private def evenProj (q : ChartPoly) : ChartPoly :=
  ∑ d ∈ q.support.image halfLast, monomial d (coeff (doubleLast d) q)

private lemma coeff_evenProj (q : ChartPoly) (d : Fin 5 →₀ ℕ) :
    coeff d (evenProj q) = coeff (doubleLast d) q := by
  simp only [evenProj, coeff_sum, coeff_monomial]
  by_cases hmem : d ∈ q.support.image halfLast
  · rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hbd; simp [hbd]
    · intro hnot; exact absurd hmem hnot
  · rw [Finset.sum_eq_zero (fun x hx => if_neg (by rintro rfl; exact hmem hx))]
    by_contra hne
    exact hmem (Finset.mem_image.mpr ⟨doubleLast d, mem_support_iff.mpr (Ne.symm hne), halfLast_doubleLast d⟩)

private lemma evenProj_one : evenProj 1 = 1 := by
  ext d
  rw [coeff_evenProj]
  change coeff (doubleLast d) (monomial 0 1) = coeff d (monomial 0 1)
  rw [coeff_monomial, coeff_monomial]
  have h0 : doubleLast 0 = 0 := by ext i; simp [doubleLast]
  conv_lhs => rw [← h0]
  simp [doubleLast_injective.eq_iff]

private lemma evenProj_mul_squareLift (a g : ChartPoly) :
    evenProj (squareLift a * g) = a * evenProj g := by
  ext d
  rw [coeff_evenProj, coeff_mul, coeff_mul]
  let emb : (Fin 5 →₀ ℕ) × (Fin 5 →₀ ℕ) ↪ (Fin 5 →₀ ℕ) × (Fin 5 →₀ ℕ) :=
    ⟨fun p => (doubleLast p.1, doubleLast p.2), fun p₁ p₂ h =>
      Prod.ext (doubleLast_injective (congrArg Prod.fst h))
        (doubleLast_injective (congrArg Prod.snd h))⟩
  have hsub : (Finset.antidiagonal d).map emb ⊆ Finset.antidiagonal (doubleLast d) := by
    intro uv huv
    rcases Finset.mem_map.mp huv with ⟨ab, hab, rfl⟩
    rw [Finset.mem_antidiagonal] at hab ⊢
    change doubleLast ab.1 + doubleLast ab.2 = doubleLast d
    rw [← doubleLast_add, hab]
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro ab _
    change coeff (doubleLast ab.1) (squareLift a) * coeff (doubleLast ab.2) g = _
    rw [coeff_squareLift_doubleLast, coeff_evenProj]
  · intro uv huv hnot
    by_cases hodd : uv.1 4 % 2 = 1
    · rw [coeff_squareLift_odd a hodd, zero_mul]
    · exfalso
      have hev1 : uv.1 4 % 2 = 0 := by omega
      rw [Finset.mem_antidiagonal] at huv
      have h4 := congrArg (fun x : Fin 5 →₀ ℕ => x 4) huv
      simp only [Finsupp.add_apply, doubleLast, Finsupp.single_apply, ↓reduceIte] at h4
      have hev2 : uv.2 4 % 2 = 0 := by omega
      apply hnot
      refine Finset.mem_map.mpr ⟨(halfLast uv.1, halfLast uv.2), ?_, ?_⟩
      · rw [Finset.mem_antidiagonal]
        apply doubleLast_injective
        rw [doubleLast_add, doubleLast_halfLast hev1, doubleLast_halfLast hev2, huv]
      · change (doubleLast (halfLast uv.1), doubleLast (halfLast uv.2)) = uv
        rw [doubleLast_halfLast hev1, doubleLast_halfLast hev2]

private lemma irreducible_of_squareLift {f : ChartPoly} (h : Irreducible (squareLift f)) :
    Irreducible f := by
  have hunit : ∀ a : ChartPoly, IsUnit (squareLift a) → IsUnit a := by
    rintro a ⟨u, hu⟩
    refine isUnit_iff_exists_inv.mpr ⟨evenProj (↑u⁻¹), ?_⟩
    have h1 : squareLift a * (↑u⁻¹ : ChartPoly) = 1 := by rw [← hu]; exact Units.mul_inv u
    have h2 := congrArg evenProj h1
    rw [evenProj_mul_squareLift, evenProj_one] at h2
    exact h2
  refine ⟨fun hu => h.not_isUnit (hu.map squareLift), ?_⟩
  intro a b hab
  have hsq : squareLift f = squareLift a * squareLift b := by rw [hab, map_mul]
  exact (h.isUnit_or_isUnit hsq).imp (hunit a) (hunit b)

end CubicTraceReduction

theorem solution
    (f P ell c2 c1 c0 p0 p1 p2 p3 : HodgeComputer.ReflectionChart.ChartPoly)
    (hf : f = ell * MvPolynomial.X 4 ^ 3 + c2 * MvPolynomial.X 4 ^ 2 + c1 * MvPolynomial.X 4 + c0)
    (hP : P = p0 + p1 * MvPolynomial.X 4 + p2 * MvPolynomial.X 4 ^ 2 + p3 * MvPolynomial.X 4 ^ 3)
    (hH_irred : Irreducible (HodgeComputer.ReflectionChart.squareLift f))
    (h_pt_zero : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift f) = 0)
    (h_pt_ell : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift ell) ≠ 0)
    (hell_base : ∀ k : Fin 4, MvPolynomial.pderiv k.succ ell = 0)
    (hc2_u : MvPolynomial.pderiv 4 c2 = 0)
    (hc1_u : MvPolynomial.pderiv 4 c1 = 0)
    (hc0_u : MvPolynomial.pderiv 4 c0 = 0)
    (hp0_u : MvPolynomial.pderiv 4 p0 = 0)
    (hp1_u : MvPolynomial.pderiv 4 p1 = 0)
    (hp2_u : MvPolynomial.pderiv 4 p2 = 0)
    (hp3_u : MvPolynomial.pderiv 4 p3 = 0)
    (h_lin : HodgeComputer.ReflectionChart.RelativePrimitive f
      (HodgeComputer.ReflectionChart.cubicTraceK0 ell c2 c1 c0 p0 p2 p3 +
        HodgeComputer.ReflectionChart.cubicTraceK1 ell c2 p1 p2 p3 * MvPolynomial.X 4)) :
    HodgeComputer.ReflectionChart.RelativePrimitive f P := by
  open CubicTraceReduction MvPolynomial HodgeComputer.ReflectionChart in
  obtain ⟨D, Cvec, Q_lin, _, h_coprime, hdefect⟩ := h_lin
  have hf_irred : Irreducible f := irreducible_of_squareLift hH_irred
  have hf_prime : Prime f := irreducible_iff_prime.mp hf_irred
  let E : ChartPoly := C 6 * ell ^ 2
  have hnot_f_dvd_E : ¬ f ∣ E := by
    intro hdiv
    have hmap := map_dvd ((eval normalPoint).comp squareLift) hdiv
    simp only [RingHom.comp_apply, h_pt_zero, zero_dvd_iff, E, map_mul, map_pow] at hmap
    have h6 : eval normalPoint (squareLift (C 6)) ≠ 0 := by norm_num [squareLift]
    exact mul_ne_zero h6 (pow_ne_zero 2 h_pt_ell) hmap
  have hnot_f_dvd_D : ¬ f ∣ D := hf_irred.isRelPrime_iff_not_dvd.mp h_coprime
  have hnot_f_dvd_ED : ¬ f ∣ E * D := hf_prime.not_dvd_mul hnot_f_dvd_E hnot_f_dvd_D
  have hED_ne : E * D ≠ 0 := fun hz => hnot_f_dvd_ED (hz ▸ dvd_zero _)
  have hED_coprime : IsRelPrime f (E * D) := hf_irred.isRelPrime_iff_not_dvd.mpr hnot_f_dvd_ED
  have hell_u : pderiv 4 ell = 0 := hell_base 3
  have hE_deriv : ∀ k : Fin 4, pderiv k.succ E = 0 := by
    intro k
    simp [E, Derivation.leibniz, Derivation.leibniz_pow, hell_base k]
  let K0 := cubicTraceK0 ell c2 c1 c0 p0 p2 p3
  let K1 := cubicTraceK1 ell c2 p1 p2 p3
  have hK0_u : pderiv 4 K0 = 0 := by
    simp [K0, cubicTraceK0, Derivation.leibniz, Derivation.leibniz_pow,
      hell_u, hc2_u, hc1_u, hc0_u, hp0_u, hp2_u, hp3_u]
  have hK1_u : pderiv 4 K1 = 0 := by
    simp [K1, cubicTraceK1, Derivation.leibniz, Derivation.leibniz_pow,
      hell_u, hc2_u, hp1_u, hp2_u, hp3_u]
  have hfu : pderiv 4 f = C 3 * ell * X 4 ^ 2 + C 2 * c2 * X 4 + c1 := by
    rw [hf]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self,
      hell_u, hc2_u, hc1_u, hc0_u, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      zero_mul, zero_add, add_zero, mul_one]
    have hc3 : (C (3 : ℂ) : ChartPoly) = 3 := by simp [map_ofNat]
    have hc2 : (C (2 : ℂ) : ChartPoly) = 2 := by simp [map_ofNat]
    rw [hc3, hc2]; ring
  have hfuu : pderiv 4 (pderiv 4 f) = C 6 * ell * X 4 + C 2 * c2 := by
    rw [hfu]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, pderiv_C, pderiv_X_self,
      hell_u, hc2_u, hc1_u, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      zero_mul, zero_add, add_zero, mul_one]
    have hc6 : (C (6 : ℂ) : ChartPoly) = 6 := by simp [map_ofNat]
    have hc3 : (C (3 : ℂ) : ChartPoly) = 3 := by simp [map_ofNat]
    have hc2 : (C (2 : ℂ) : ChartPoly) = 2 := by simp [map_ofNat]
    rw [hc6, hc3, hc2]; ring
  have hPu : pderiv 4 P = p1 + C 2 * p2 * X 4 + C 3 * p3 * X 4 ^ 2 := by
    rw [hP]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self,
      hp0_u, hp1_u, hp2_u, hp3_u, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      zero_mul, zero_add, mul_one]
    have hc3 : (C (3 : ℂ) : ChartPoly) = 3 := by simp [map_ofNat]
    have hc2 : (C (2 : ℂ) : ChartPoly) = 2 := by simp [map_ofNat]
    rw [hc3, hc2]; ring
  have hKlin_u : pderiv 4 (K0 + K1 * X 4) = K1 := by
    simp [Derivation.leibniz, hK0_u, hK1_u]
  have htrace_id : E * (pderiv 4 f * pderiv 4 P - pderiv 4 (pderiv 4 f) * P) =
      (pderiv 4 f * pderiv 4 (K0 + K1 * X 4) - pderiv 4 (pderiv 4 f) * (K0 + K1 * X 4)) +
        C 6 * ell * p3 * (C 3 * ell * X 4 + c2) * f := by
    rw [hfuu, hfu, hPu, hKlin_u]
    rw [hf, hP]
    dsimp [E, K0, K1, cubicTraceK0, cubicTraceK1]
    have hc6 : (C (6 : ℂ) : ChartPoly) = 6 := by simp [map_ofNat]
    have hc4 : (C (4 : ℂ) : ChartPoly) = 4 := by simp [map_ofNat]
    have hc3 : (C (3 : ℂ) : ChartPoly) = 3 := by simp [map_ofNat]
    have hc2 : (C (2 : ℂ) : ChartPoly) = 2 := by simp [map_ofNat]
    rw [hc6, hc4, hc3, hc2]
    ring
  have hW_scale : ∀ j : Fin 3,
      (pderiv 4 f * ((E * D) * pderiv j.succ.castSucc (Cvec j) - Cvec j * pderiv j.succ.castSucc (E * D)) -
        pderiv j.succ.castSucc f * ((E * D) * pderiv 4 (Cvec j) - Cvec j * pderiv 4 (E * D))) =
      E * (pderiv 4 f * (D * pderiv j.succ.castSucc (Cvec j) - Cvec j * pderiv j.succ.castSucc D) -
        pderiv j.succ.castSucc f * (D * pderiv 4 (Cvec j) - Cvec j * pderiv 4 D)) := by
    intro j
    have hjE : pderiv j.succ.castSucc E = 0 := by
      fin_cases j
      · exact hE_deriv 0
      · exact hE_deriv 1
      · exact hE_deriv 2
    have h4E : pderiv 4 E = 0 := hE_deriv 3
    simp only [Derivation.leibniz, hjE, h4E, smul_eq_mul, mul_zero, add_zero]
    ring
  refine ⟨E * D, Cvec, E * Q_lin - C 2 * E * D ^ 2 * (C 6 * ell * p3 * (C 3 * ell * X 4 + c2)),
    hED_ne, hED_coprime, ?_⟩
  unfold cubicResidueDefect at hdefect ⊢
  simp_rw [hW_scale, ← Finset.mul_sum]
  change (pderiv 4 f) ^ 2 * (E * _) - C 2 * (E * D) ^ 2 * _ = _
  have hDsq : C 2 * (E * D) ^ 2 * (pderiv 4 f * pderiv 4 P - pderiv 4 (pderiv 4 f) * P) =
      E * (C 2 * D ^ 2 * (E * (pderiv 4 f * pderiv 4 P - pderiv 4 (pderiv 4 f) * P))) := by ring
  rw [hDsq, htrace_id]
  change (pderiv 4 f) ^ 2 * (E * _) - E * (C 2 * D ^ 2 *
    ((pderiv 4 f * pderiv 4 (K0 + K1 * X 4) - pderiv 4 (pderiv 4 f) * (K0 + K1 * X 4)) +
      C 6 * ell * p3 * (C 3 * ell * X 4 + c2) * f)) = _
  linear_combination E * hdefect
