-- Prove2me | solution 1 for HighDimStat.Pca.pca_eigenvector_perturbation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:50:20.658392+00:00
-- url     : https://prove2.me/submissions/57894219-6588-4b10-89ea-220e9425c36a

import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_OpNormSymm
import Definitions.Def_HighDimStat_Pca_Ptilde
import Definitions.Def_HighDimStat_Pca_L2Norm

open Matrix

namespace HighDimStat.Pca

variable {d : ℕ}

lemma sq_sum_eq (v : Fin d → ℝ) : ∑ j, (v j) ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

lemma quad_eq (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    ∑ i, v i * (A.mulVec v) i = v ⬝ᵥ (A *ᵥ v) := rfl

lemma sym_bil {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = A) (u v : Fin d → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

lemma self_nonneg (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [← sq_sum_eq]; positivity

lemma eq_zero_of_self (v : Fin d → ℝ) (h : v ⬝ᵥ v = 0) : v = 0 := by
  rw [← sq_sum_eq] at h
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 h j
    (Finset.mem_univ j)
  simpa using this

/-- homogeneous version of a statement about unit vectors -/
lemma homog (Q : (Fin d → ℝ) → ℝ) (hQ : ∀ (a : ℝ) v, Q (a • v) = a ^ 2 * Q v) (c : ℝ)
    (h : ∀ v : Fin d → ℝ, v ⬝ᵥ v = 1 → Q v ≤ c) (v : Fin d → ℝ) (hQ0 : Q 0 = 0) :
    Q v ≤ c * (v ⬝ᵥ v) := by
  by_cases hv : v ⬝ᵥ v = 0
  · rw [eq_zero_of_self v hv, hQ0]; simp
  · have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (self_nonneg v) (Ne.symm hv)
    set a := Real.sqrt (v ⬝ᵥ v) with ha
    have ha0 : 0 < a := Real.sqrt_pos.2 hpos
    have ha2 : a ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
    have hu : (a⁻¹ • v) ⬝ᵥ (a⁻¹ • v) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← ha2]
      field_simp
    have := h _ hu
    rw [hQ] at this
    have e : Q v = a ^ 2 * (a⁻¹ ^ 2 * Q v) := by field_simp
    rw [e, ha2.symm]
    nlinarith [sq_nonneg a]

lemma quad_smul (A : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) (v : Fin d → ℝ) :
    (a • v) ⬝ᵥ (A *ᵥ (a • v)) = a ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

/-- the operator norm bound -/
lemma opNorm_bound (P : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    |v ⬝ᵥ (P *ᵥ v)| ≤ opNormSymm P * (v ⬝ᵥ v) := by
  have hbdd : BddAbove (Set.range fun u : {u : Fin d → ℝ // ∑ j, (u j) ^ 2 = 1} =>
      |∑ i, u.1 i * (P.mulVec u.1) i|) := by
    refine ⟨∑ i, ∑ j, |P i j|, ?_⟩
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    have hui : ∀ i, |u i| ≤ 1 := fun i => by
      have : u i ^ 2 ≤ ∑ j, u j ^ 2 :=
        Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [hu] at this
      exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
    simp only [mulVec, dotProduct]
    calc |∑ i, u i * ∑ j, P i j * u j| ≤ ∑ i, |u i * ∑ j, P i j * u j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |P i j| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          calc |u i| * |∑ j, P i j * u j| ≤ 1 * ∑ j, |P i j| := by
                apply mul_le_mul (hui i) _ (abs_nonneg _) zero_le_one
                refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
                rw [abs_mul]
                calc |P i j| * |u j| ≤ |P i j| * 1 :=
                      mul_le_mul_of_nonneg_left (hui j) (abs_nonneg _)
                  _ = |P i j| := mul_one _
            _ = ∑ j, |P i j| := one_mul _
  refine homog (fun v => |v ⬝ᵥ (P *ᵥ v)|) (fun a v => ?_) _ (fun v hv => ?_) v (by simp)
  · rw [quad_smul, abs_mul, abs_of_nonneg (sq_nonneg a)]
  · have hv' : ∑ j, (v j) ^ 2 = 1 := by rw [sq_sum_eq]; exact hv
    exact le_ciSup hbdd ⟨v, hv'⟩

theorem pca_main (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hMsym : M.transpose = M)
    (hPsym : P.transpose = P)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hPop : opNormSymm P < ν / 2)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat)
    (hsign : 0 ≤ ∑ j, θhat j * θstar j) :
    l2Norm (fun j => θhat j - θstar j) ≤
      (2 * l2Norm (ptilde P θstar)) / (ν - 2 * opNormSymm P) := by
  obtain ⟨hs1, hsmax⟩ := hmax_star
  obtain ⟨hν, hgapv⟩ := hgap
  obtain ⟨hh1, hhmax⟩ := hmax_hat
  rw [sq_sum_eq] at hs1 hh1
  set γ := θstar ⬝ᵥ (M *ᵥ θstar) with hγ
  set c := θhat ⬝ᵥ θstar with hc
  have hc0 : 0 ≤ c := hsign
  set w := θhat - c • θstar with hw
  have hwθ : w ⬝ᵥ θstar = 0 := by
    rw [hw, sub_dotProduct, smul_dotProduct, hs1, smul_eq_mul, mul_one, ← hc, sub_self]
  have hww : w ⬝ᵥ w = 1 - c ^ 2 := by
    rw [hw, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, hh1, hs1, dotProduct_comm θstar θhat, ← hc]
    simp only [smul_eq_mul]; ring
  have hc1 : c ≤ 1 := by nlinarith [self_nonneg w]
  have hθ : θhat = c • θstar + w := by rw [hw]; abel
  -- homogeneous maximality of θstar
  have hmaxh : ∀ u, u ⬝ᵥ (M *ᵥ u) ≤ γ * (u ⬝ᵥ u) := fun u =>
    homog (fun v => v ⬝ᵥ (M *ᵥ v)) (quad_smul M) γ
      (fun v hv => hsmax v (by rw [sq_sum_eq]; exact hv)) u (by simp)
  -- θstar is an eigenvector direction: w ⬝ M θstar = 0
  have hB : w ⬝ᵥ (M *ᵥ θstar) = 0 := by
    set B := w ⬝ᵥ (M *ᵥ θstar)
    set K := γ * (w ⬝ᵥ w) - w ⬝ᵥ (M *ᵥ w)
    have key : ∀ t : ℝ, 2 * t * B ≤ t ^ 2 * K := by
      intro t
      have h := hmaxh (θstar + t • w)
      have e1 : (θstar + t • w) ⬝ᵥ (M *ᵥ (θstar + t • w)) =
          γ + 2 * t * B + t ^ 2 * (w ⬝ᵥ (M *ᵥ w)) := by
        rw [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
          sym_bil hMsym θstar w]
        simp only [smul_eq_mul]; ring
      have e2 : (θstar + t • w) ⬝ᵥ (θstar + t • w) = 1 + t ^ 2 * (w ⬝ᵥ w) := by
        rw [dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_smul, smul_dotProduct,
          smul_dotProduct, dotProduct_smul, hs1, dotProduct_comm θstar w, hwθ]
        simp only [smul_eq_mul]; ring
      rw [e1, e2] at h
      nlinarith
    have hK : K ≤ |K| := le_abs_self K
    have h := key (B / (|K| + 1))
    have hK1 : 0 < |K| + 1 := by positivity
    have e : 2 * (B / (|K| + 1)) * B * (|K| + 1) ^ 2 = 2 * B ^ 2 * (|K| + 1) := by
      field_simp
    have e' : (B / (|K| + 1)) ^ 2 * K * (|K| + 1) ^ 2 = B ^ 2 * K := by field_simp
    have h2 := mul_le_mul_of_nonneg_right h (sq_nonneg (|K| + 1))
    rw [e, e'] at h2
    have : B ^ 2 * (|K| + 2) ≤ 0 := by nlinarith [sq_nonneg B]
    have hB2 : B ^ 2 = 0 := le_antisymm (by nlinarith [abs_nonneg K]) (sq_nonneg B)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 hB2
  -- eigengap in homogeneous form
  have hgaph : w ⬝ᵥ (M *ᵥ w) ≤ (γ - ν) * (w ⬝ᵥ w) := by
    by_cases hw0 : w ⬝ᵥ w = 0
    · rw [eq_zero_of_self w hw0]; simp
    · have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne (self_nonneg w) (Ne.symm hw0)
      set a := Real.sqrt (w ⬝ᵥ w)
      have ha0 : 0 < a := Real.sqrt_pos.2 hpos
      have ha2 : a ^ 2 = w ⬝ᵥ w := Real.sq_sqrt hpos.le
      have hu : (a⁻¹ • w) ⬝ᵥ (a⁻¹ • w) = 1 := by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← ha2]; field_simp
      have hu0 : (a⁻¹ • w) ⬝ᵥ θstar = 0 := by rw [smul_dotProduct, hwθ, smul_zero]
      have := hgapv (a⁻¹ • w) (by rw [sq_sum_eq]; exact hu) hu0
      rw [quad_eq, quad_eq, quad_smul] at this
      have e : w ⬝ᵥ (M *ᵥ w) = a ^ 2 * (a⁻¹ ^ 2 * (w ⬝ᵥ (M *ᵥ w))) := by field_simp
      rw [e, ← ha2]
      nlinarith [sq_nonneg a]
  -- expansion of the quadratic forms at θhat
  have hexpM : θhat ⬝ᵥ (M *ᵥ θhat) = c ^ 2 * γ + w ⬝ᵥ (M *ᵥ w) := by
    rw [hθ, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, hB,
      sym_bil hMsym θstar w, hB]
    simp only [smul_eq_mul, hγ]; ring
  set pt := ptilde P θstar with hpt
  have hwP : w ⬝ᵥ (P *ᵥ θstar) = w ⬝ᵥ pt := by
    have : pt = P *ᵥ θstar - ((P *ᵥ θstar) ⬝ᵥ θstar) • θstar := by
      funext j; simp [hpt, ptilde, dotProduct]
    rw [this, dotProduct_sub, dotProduct_smul, hwθ, smul_zero, sub_zero]
  have hexpP : θhat ⬝ᵥ (P *ᵥ θhat) =
      c ^ 2 * (θstar ⬝ᵥ (P *ᵥ θstar)) + 2 * c * (w ⬝ᵥ pt) + w ⬝ᵥ (P *ᵥ w) := by
    rw [hθ, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      sym_bil hPsym θstar w, hwP]
    simp only [smul_eq_mul]; ring
  -- basic inequality
  have hbasic : γ + θstar ⬝ᵥ (P *ᵥ θstar) ≤ θhat ⬝ᵥ (M *ᵥ θhat) + θhat ⬝ᵥ (P *ᵥ θhat) := by
    have := hhmax θstar (by rw [sq_sum_eq]; exact hs1)
    rw [quad_eq, quad_eq, add_mulVec, add_mulVec, dotProduct_add, dotProduct_add] at this
    exact this
  set Pn := opNormSymm P with hPn
  have b1 : |θstar ⬝ᵥ (P *ᵥ θstar)| ≤ Pn := by
    have := opNorm_bound P θstar; rwa [hs1, mul_one] at this
  have b2 : |w ⬝ᵥ (P *ᵥ w)| ≤ Pn * (1 - c ^ 2) := by rw [← hww]; exact opNorm_bound P w
  set L := l2Norm pt with hL
  have hL' : L = Real.sqrt (pt ⬝ᵥ pt) := by rw [hL, l2Norm, sq_sum_eq]
  have hL0 : 0 ≤ L := by rw [hL']; exact Real.sqrt_nonneg _
  set S := Real.sqrt (w ⬝ᵥ w) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = 1 - c ^ 2 := by rw [hS, Real.sq_sqrt (self_nonneg w), hww]
  have hCS : |w ⬝ᵥ pt| ≤ S * L := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w pt
    rw [sq_sum_eq, sq_sum_eq] at h
    have h' : (w ⬝ᵥ pt) ^ 2 ≤ (w ⬝ᵥ w) * (pt ⬝ᵥ pt) := h
    rw [hS, hL', ← Real.sqrt_mul (self_nonneg w)]
    exact Real.abs_le_sqrt h'
  have hwpt : c * (w ⬝ᵥ pt) ≤ c * (S * L) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hCS) hc0
  have hgap2 : ν * (1 - c ^ 2) ≤ 2 * Pn * (1 - c ^ 2) + 2 * c * (S * L) := by
    have hq := hgaph
    rw [hww] at hq
    have a1 := (abs_le.1 b1).1
    have a2 := (abs_le.1 b2).2
    have hc2 : 0 ≤ 1 - c ^ 2 := by rw [← hww]; exact self_nonneg w
    have a3 : c ^ 2 * (θstar ⬝ᵥ (P *ᵥ θstar)) - θstar ⬝ᵥ (P *ᵥ θstar) ≤ (1 - c ^ 2) * Pn := by
      have : -(θstar ⬝ᵥ (P *ᵥ θstar)) ≤ Pn := by linarith [(abs_le.1 b1).1]
      have := mul_le_mul_of_nonneg_left this hc2
      linarith
    rw [hexpM, hexpP] at hbasic
    linarith
  set g := ν - 2 * Pn with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  have hgS : g * S ≤ 2 * c * L := by
    have h1 : g * S ^ 2 ≤ 2 * c * L * S := by rw [hS2, hg]; linarith
    rcases eq_or_lt_of_le hS0 with h | h
    · rw [← h]; simp only [mul_zero]; positivity
    · exact le_of_mul_le_mul_right (by linarith [h1] : (g * S) * S ≤ (2 * c * L) * S) h
  -- final estimate
  have hΔ : (fun j => θhat j - θstar j) ⬝ᵥ (fun j => θhat j - θstar j) = 2 - 2 * c := by
    have : (fun j => θhat j - θstar j) = θhat - θstar := rfl
    rw [this, sub_dotProduct, dotProduct_sub, dotProduct_sub, hh1, hs1,
      dotProduct_comm θstar θhat, ← hc]; ring
  have hsq : (2 - 2 * c) * g ^ 2 ≤ (2 * L) ^ 2 := by
    have h1 : g ^ 2 * S ^ 2 ≤ 4 * c ^ 2 * L ^ 2 := by
      have := mul_le_mul hgS hgS (by positivity) (by positivity)
      linarith
    rw [hS2] at h1
    have h2 : 2 * c ^ 2 ≤ 1 + c := by
      have := mul_le_mul_of_nonneg_left hc1 hc0
      linarith
    have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
    have h3 : ((2 - 2 * c) * g ^ 2) * (1 + c) ≤ (2 * L) ^ 2 * (1 + c) := by linarith
    exact le_of_mul_le_mul_right h3 (by linarith)
  rw [l2Norm, sq_sum_eq, hΔ]
  have hR : 0 ≤ 2 * L / g := by positivity
  rw [← Real.sqrt_sq hR]
  apply Real.sqrt_le_sqrt
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact hsq

end HighDimStat.Pca

open HighDimStat.Pca

theorem solution {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hMsym : M.transpose = M)
    (hMpsd : ∀ v : Fin d → ℝ, 0 ≤ ∑ i, v i * (M.mulVec v) i)
    (hPsym : P.transpose = P)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hPop : opNormSymm P < ν / 2)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat)
    (hsign : 0 ≤ ∑ j, θhat j * θstar j) :
    l2Norm (fun j => θhat j - θstar j) ≤
      (2 * l2Norm (ptilde P θstar)) / (ν - 2 * opNormSymm P) := by
  exact pca_main M P θstar θhat ν hMsym hPsym hmax_star hgap hPop hmax_hat hsign
