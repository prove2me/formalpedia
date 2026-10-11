-- Prove2me | solution 1 for NAGFlow.GSSpectrum.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:35:35.80575+00:00
-- url     : https://prove2.me/submissions/f967b38a-69ea-454c-bad5-cd7e3c8db39e

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace RRAux_NAGFlow_GSSpectrum_theorem_2_1

open Matrix NAGFlow.GSSpectrum


lemma quad_root (a b c : ℝ) (ha : 0 < a) (hdisc : b ^ 2 ≤ 4 * a * c) (z : ℂ)
    (hz : (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0) :
    z.re ^ 2 + z.im ^ 2 = c / a := by
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp [pow_two] at h1 h2
  rw [eq_div_iff ha.ne']
  by_cases hy : z.im = 0
  · rw [hy] at h1 ⊢
    have : (2 * a * z.re + b) ^ 2 = 0 := by nlinarith
    have h3 : 2 * a * z.re + b = 0 := by simpa using this
    nlinarith
  · have h3 : 2 * a * z.re + b = 0 := by
      have : z.im * (2 * a * z.re + b) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hy
      · exact h
    linear_combination -h1 + z.re * h3

lemma spec_eig {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ spectrum ℂ M) : ∃ v : n → ℂ, v ≠ 0 ∧ M *ᵥ v = z • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff] at hz
  obtain ⟨v, hv, h⟩ := hz
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at h
  exact h.symm

open ComplexOrder in
lemma herm_eig {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (u : n → ℂ) (hu : u ≠ 0) (c : ℂ) (h : (A.map (algebraMap ℝ ℂ)) *ᵥ u = c • u) :
    c.im = 0 ∧ c.re ∈ spectrum ℝ A := by
  set A' := A.map (algebraMap ℝ ℂ)
  have hT : A'ᵀ = A' := by
    rw [← transpose_map]
    have : Aᵀ = A := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hA
    rw [this]
  have hstar : A' *ᵥ star u = star c • star u := by
    have : A' *ᵥ star u = star (A' *ᵥ u) := by
      ext i; simp [A', Matrix.mulVec, dotProduct, star_sum]
    rw [this, h]; ext i; simp
  have hN : star u ⬝ᵥ u ≠ 0 := fun h0 => hu (dotProduct_star_self_eq_zero.mp h0)
  have key : c * (star u ⬝ᵥ u) = star c * (star u ⬝ᵥ u) := by
    have e1 : star u ⬝ᵥ (A' *ᵥ u) = c * (star u ⬝ᵥ u) := by
      rw [h, dotProduct_smul, smul_eq_mul]
    have e2 : star u ⬝ᵥ (A' *ᵥ u) = star c * (star u ⬝ᵥ u) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hT, hstar, smul_dotProduct, smul_eq_mul,
        dotProduct_comm]
    rw [← e1, e2]
  have hc : star c = c := (mul_right_cancel₀ hN key).symm
  have him : c.im = 0 := by
    have := congrArg Complex.im hc
    simp at this; linarith
  refine ⟨him, ?_⟩
  have hcre : (c.re : ℂ) = c := by
    apply Complex.ext <;> simp [him]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  set B := algebraMap ℝ (Matrix n n ℝ) c.re - A
  have hB : B.map (algebraMap ℝ ℂ) *ᵥ u = 0 := by
    have : B.map (algebraMap ℝ ℂ) = (c.re : ℂ) • (1 : Matrix n n ℂ) - A' := by
      ext i j
      simp only [B, A', map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.algebraMap_matrix_apply,
        one_apply]
      split_ifs <;> simp
    rw [this, sub_mulVec, smul_mulVec, one_mulVec, h, hcre, sub_self]
  have h0 : (B.map (algebraMap ℝ ℂ)).det = 0 := exists_mulVec_eq_zero_iff.mp ⟨u, hu, hB⟩
  have h1 := RingHom.map_det (algebraMap ℝ ℂ) B
  rw [RingHom.mapMatrix_apply, h0] at h1
  exact (algebraMap ℝ ℂ).injective (by rw [h1, map_zero])

lemma hb_eqs {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ α : ℝ) (v : Fin d ⊕ Fin d → ℂ) (z : ℂ)
    (h : ((1 + α • (GHB A μ - blockLower (GHB A μ))).map (algebraMap ℝ ℂ)) *ᵥ v
      = z • (((1 - α • blockLower (GHB A μ)).map (algebraMap ℝ ℂ)) *ᵥ v)) (i : Fin d) :
    v (Sum.inl i) + α * v (Sum.inr i) = z * v (Sum.inl i) ∧
    v (Sum.inr i) = z * ((α / μ) * ∑ j, (A i j : ℂ) * v (Sum.inl j) + (1 + 2 * α) * v (Sum.inr i)) := by
  have h1 := congrFun h (Sum.inl i)
  have h2 := congrFun h (Sum.inr i)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, GHB, blockLower, one_apply] at h1 h2
  simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
    Complex.ofReal_ofNat] at h1 h2
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero, mul_one, add_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1 h2
  refine ⟨h1, ?_⟩
  have hs : ∑ x, (α : ℂ) * ((μ : ℂ)⁻¹ * (A i x : ℂ)) * v (Sum.inl x)
      = (α : ℂ) / μ * ∑ j, (A i j : ℂ) * v (Sum.inl j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hs] at h2
  linear_combination h2

lemma nag_eqs {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ α : ℝ) (v : Fin d ⊕ Fin d → ℂ) (z : ℂ)
    (h : ((1 + α • (GNAG A μ - blockLower (GNAG A μ))).map (algebraMap ℝ ℂ)) *ᵥ v
      = z • (((1 - α • blockLower (GNAG A μ)).map (algebraMap ℝ ℂ)) *ᵥ v)) (i : Fin d) :
    v (Sum.inl i) + α * v (Sum.inr i) = z * ((1 + α) * v (Sum.inl i)) ∧
    v (Sum.inr i) = z * (-α * v (Sum.inl i) + (α / μ) * ∑ j, (A i j : ℂ) * v (Sum.inl j) + (1 + α) * v (Sum.inr i)) := by
  have h1 := congrFun h (Sum.inl i)
  have h2 := congrFun h (Sum.inr i)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, GNAG, blockLower, one_apply] at h1 h2
  simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
    Complex.ofReal_ofNat] at h1 h2
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero, mul_one, add_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1 h2
  refine ⟨by linear_combination h1, ?_⟩
  have hs : ∑ x, (α : ℂ) * ((if i = x then 1 else 0) - (μ : ℂ)⁻¹ * (A i x : ℂ)) * v (Sum.inl x)
      = (α : ℂ) * v (Sum.inl i) - (α : ℂ) / μ * ∑ j, (A i j : ℂ) * v (Sum.inl j) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring
  rw [hs] at h2
  linear_combination h2
lemma disc_hb (α t : ℝ) (hα : 0 < α) (ht1 : α ^ 2 ≤ t) (ht2 : t ≤ 4) :
    (-(2 + 2 * α - t)) ^ 2 ≤ 4 * (1 + 2 * α) * 1 := by
  have hα2 : α ≤ 2 := by nlinarith
  have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2)
  have h2 : 0 ≤ α ^ 3 * (4 - α) := mul_nonneg (by positivity) (by linarith)
  have h3 : 0 ≤ α * (4 - α) := mul_nonneg hα.le (by linarith)
  nlinarith
lemma disc_nag (α t : ℝ) (hα : 0 < α) (ht1 : α ^ 2 ≤ t) (ht2 : t ≤ 4) :
    (-(2 + 2 * α + α ^ 2 - t)) ^ 2 ≤ 4 * (1 + α) ^ 2 * 1 := by
  nlinarith

lemma gs_rel {n : Type*} [Fintype n] [DecidableEq n] (α : ℝ) (M N : Matrix n n ℝ) (z : ℂ)
    (hz : z ∈ cspec (gsE α M N)) :
    z = 0 ∨ ∃ v : n → ℂ, v ≠ 0 ∧ ((1 + α • N).map (algebraMap ℝ ℂ)) *ᵥ v
      = z • (((1 - α • M).map (algebraMap ℝ ℂ)) *ᵥ v) := by
  obtain ⟨v, hv, hE⟩ := spec_eig _ z hz
  by_cases hP : IsUnit (1 - α • M).det
  · right
    refine ⟨v, hv, ?_⟩
    have hPE : (1 - α • M) * gsE α M N = 1 + α • N := by
      unfold gsE; rw [← mul_assoc, mul_nonsing_inv _ hP, one_mul]
    have := congrArg (fun X => X.map (algebraMap ℝ ℂ)) hPE
    simp only [Matrix.map_mul] at this
    rw [← this, ← mulVec_mulVec, hE, mulVec_smul]
  · left
    have h0 : gsE α M N = 0 := by
      unfold gsE; rw [nonsing_inv_apply_not_isUnit _ hP, zero_mul]
    rw [h0, Matrix.map_zero _ (map_zero _), zero_mulVec] at hE
    rcases smul_eq_zero.mp hE.symm with h | h
    · exact h
    · exact absurd h hv


lemma core {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (u : Fin d → ℂ)
    (hu : u ≠ 0) (k : ℂ) (hk : k ≠ 0) (r : ℂ)
    (h : ∀ i, k * ∑ j, (A i j : ℂ) * u j = r * u i) :
    ∃ lam ∈ spectrum ℝ A, k * (lam : ℂ) = r := by
  have hmv : (A.map (algebraMap ℝ ℂ)) *ᵥ u = (r / k) • u := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.coe_algebraMap, Pi.smul_apply,
      smul_eq_mul]
    have := h i
    field_simp
    linear_combination this
  obtain ⟨him, hspec⟩ := herm_eig A hA u hu _ hmv
  refine ⟨(r / k).re, hspec, ?_⟩
  have : (((r / k).re : ℝ) : ℂ) = r / k := Complex.ext (by simp) (by simp [him])
  rw [this]; field_simp

lemma vnz {d : ℕ} (α : ℝ) (hα : 0 < α) (v : Fin d ⊕ Fin d → ℂ) (hv : v ≠ 0)
    (hz : ∀ i, v (Sum.inl i) = 0 → v (Sum.inl i) + α * v (Sum.inr i) = 0) :
    (fun i => v (Sum.inl i)) ≠ 0 := by
  intro hu
  apply hv
  have hu' : ∀ i, v (Sum.inl i) = 0 := fun i => congrFun hu i
  funext x
  rcases x with i | i
  · exact hu' i
  · have := hz i (hu' i)
    rw [hu' i, zero_add] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (Complex.ofReal_eq_zero.mp h) hα.ne'
    · exact h

lemma hb_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ α : ℝ) (hA : A.IsHermitian)
    (hμ : 0 < μ) (hα : 0 < α) (hlo : ∀ lam ∈ spectrum ℝ A, μ ≤ lam)
    (h4 : ∀ lam ∈ spectrum ℝ A, α ^ 2 * (lam / μ) ≤ 4) (z : ℂ)
    (hz : z ∈ cspec (EG α (GHB A μ))) : z.re ^ 2 + z.im ^ 2 ≤ 1 / (1 + 2 * α) := by
  by_cases hz0 : z = 0
  · subst hz0; simp; positivity
  rcases gs_rel α _ _ z hz with h | ⟨v, hv, hE⟩
  · exact absurd h hz0
  have e := hb_eqs A μ α v z hE
  have hu := vnz α hα v hv (fun i hi => by have := (e i).1; rw [hi, mul_zero] at this; rw [hi]; exact this)
  have hk : (z * (α : ℂ) ^ 2 / μ) ≠ 0 := by
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
    exact div_ne_zero (mul_ne_zero hz0 (pow_ne_zero _ hαc)) hμc
  obtain ⟨lam, hlam, hkl⟩ := core A hA _ hu (z * (α : ℂ) ^ 2 / μ) hk
    (-(z - 1) * ((1 + 2 * α) * z - 1)) (fun i => by
      obtain ⟨e1, e2⟩ := e i
      linear_combination (-(α : ℂ)) * e2 + (1 - (1 + 2 * α) * z) * e1)
  have hq := quad_root (1 + 2 * α) (-(2 + 2 * α - α ^ 2 * (lam / μ))) 1 (by linarith)
    (disc_hb α (α ^ 2 * (lam / μ)) hα
      (by have := hlo lam hlam
          have : 1 ≤ lam / μ := (one_le_div hμ).mpr this
          nlinarith [sq_nonneg α])
      (h4 lam hlam)) z (by
      have : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
      push_cast
      linear_combination hkl)
  rw [hq]

lemma nag_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ α : ℝ) (hA : A.IsHermitian)
    (hμ : 0 < μ) (hα : 0 < α) (hlo : ∀ lam ∈ spectrum ℝ A, μ ≤ lam)
    (h4 : ∀ lam ∈ spectrum ℝ A, α ^ 2 * (lam / μ) ≤ 4) (z : ℂ)
    (hz : z ∈ cspec (EG α (GNAG A μ))) : z.re ^ 2 + z.im ^ 2 ≤ 1 / (1 + 2 * α) := by
  by_cases hz0 : z = 0
  · subst hz0; simp; positivity
  rcases gs_rel α _ _ z hz with h | ⟨v, hv, hE⟩
  · exact absurd h hz0
  have e := nag_eqs A μ α v z hE
  have hu := vnz α hα v hv (fun i hi => by have := (e i).1; rw [hi, mul_zero, mul_zero] at this; rw [hi]; exact this)
  have hk : (z * (α : ℂ) ^ 2 / μ) ≠ 0 := by
    have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
    exact div_ne_zero (mul_ne_zero hz0 (pow_ne_zero _ hαc)) hμc
  obtain ⟨lam, hlam, hkl⟩ := core A hA _ hu (z * (α : ℂ) ^ 2 / μ) hk
    (-(z * (1 + α) - 1) ^ 2 + z * α ^ 2) (fun i => by
      obtain ⟨e1, e2⟩ := e i
      linear_combination (-(α : ℂ)) * e2 + (1 - (1 + α) * z) * e1)
  have hq := quad_root ((1 + α) ^ 2) (-(2 + 2 * α + α ^ 2 - α ^ 2 * (lam / μ))) 1 (by positivity)
    (disc_nag α (α ^ 2 * (lam / μ)) hα
      (by have := hlo lam hlam
          have : 1 ≤ lam / μ := (one_le_div hμ).mpr this
          nlinarith [sq_nonneg α])
      (h4 lam hlam)) z (by
      have : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
      push_cast
      linear_combination hkl)
  rw [hq]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg α]

end RRAux_NAGFlow_GSSpectrum_theorem_2_1

open NAGFlow.GSSpectrum Matrix in
theorem solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ L α : ℝ) (hA : IsQuadModel A μ L)
    (hμ : 0 < μ) (hα : 0 < α) (h127 : α ≤ 2 / Real.sqrt (kappa μ L)) :
    ∀ G, (G = GHB A μ ∨ G = GNAG A μ) →
      (∀ z ∈ cspec (EG α G), ‖z‖ < 1) ∧
        ∀ z ∈ cspec (EG α G), ‖z‖ ≤ 1 / Real.sqrt (1 + 2 * α) := by
  have hμL : μ ≤ L := (hA.bounds μ hA.mu_mem).2
  have hlo : ∀ lam ∈ spectrum ℝ A, μ ≤ lam := fun lam h => (hA.bounds lam h).1
  have hκ : 0 < kappa μ L := div_pos (by linarith) hμ
  have hαk : α ^ 2 * kappa μ L ≤ 4 := by
    have hs := Real.sqrt_pos.mpr hκ
    have h1 : α * Real.sqrt (kappa μ L) ≤ 2 := by rwa [le_div_iff₀ hs] at h127
    have h2 := Real.sq_sqrt hκ.le
    have h3 : 0 ≤ α * Real.sqrt (kappa μ L) := by positivity
    nlinarith
  have h4 : ∀ lam ∈ spectrum ℝ A, α ^ 2 * (lam / μ) ≤ 4 := by
    intro lam hlam
    have : lam / μ ≤ kappa μ L := div_le_div_of_nonneg_right (hA.bounds lam hlam).2 hμ.le
    nlinarith [sq_nonneg α]
  intro G hG
  have hb : ∀ z ∈ cspec (EG α G), ‖z‖ ≤ 1 / Real.sqrt (1 + 2 * α) := by
    intro z hz
    have hsq : z.re ^ 2 + z.im ^ 2 ≤ 1 / (1 + 2 * α) := by
      rcases hG with rfl | rfl
      · exact RRAux_NAGFlow_GSSpectrum_theorem_2_1.hb_bound A μ α hA.symm hμ hα hlo h4 z hz
      · exact RRAux_NAGFlow_GSSpectrum_theorem_2_1.nag_bound A μ α hA.symm hμ hα hlo h4 z hz
    rw [Complex.norm_def, Complex.normSq_apply, one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    rw [← one_div]; nlinarith
  have hlt : 1 / Real.sqrt (1 + 2 * α) < 1 := by
    rw [div_lt_one (Real.sqrt_pos.mpr (by linarith)), Real.lt_sqrt (by norm_num)]
    linarith
  exact ⟨fun z hz => lt_of_le_of_lt (hb z hz) hlt, hb⟩

#print axioms solution
