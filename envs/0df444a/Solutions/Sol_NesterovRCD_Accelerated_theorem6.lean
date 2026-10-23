-- Prove2me | solution 1 for NesterovRCD.Accelerated.theorem6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T01:34:16.174341+00:00
-- url     : https://prove2.me/submissions/cb98d4bc-7c70-4d09-b1be-a488dd4692e9

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb NesterovRCD.Accelerated

namespace ACDMProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]

noncomputable def energy (L : Fin n → ℝ) (x : Blocks E) : ℝ :=
  ∑ i, L i * ‖x i‖ ^ 2

noncomputable def weightedInner (L : Fin n → ℝ) (x y : Blocks E) : ℝ :=
  ∑ i, L i * inner ℝ (x i) (y i)

end ACDMProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb NesterovRCD.Accelerated
open InnerProductSpace

namespace ACDMProof

theorem sharp_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (s : F →L[ℝ] ℝ) (v : F) (hv : IsSharp s v) (w : F) :
    inner ℝ v w = s w := by
  let r := (InnerProductSpace.toDual ℝ F).symm s
  have hr (u : F) : inner ℝ r u = s u := toDual_symm_apply
  have hh := hv r
  rw [← hr r, ← hr v, real_inner_self_eq_norm_sq] at hh
  have hz : ‖v-r‖^2 = 0 := by
    have he := norm_sub_sq_real v r
    have hc : inner ℝ v r = inner ℝ r v := real_inner_comm _ _
    rw [hc] at he
    nlinarith [sq_nonneg ‖v-r‖]
  have hvr : v = r := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  rw [hvr]
  exact hr w

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem energy_nonneg (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (x : Blocks E) :
    0 ≤ energy L x := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hL i) (sq_nonneg _)

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem wnorm_sq (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (x : Blocks E) :
    wnorm L 1 x ^ 2 = energy L x := by
  simp only [wnorm, Real.rpow_one]
  exact Real.sq_sqrt (energy_nonneg L hL x)

theorem energy_single_update (L : Fin n → ℝ) (x : Blocks E) (i : Fin n)
    (t : ℝ) (v : E i) :
    energy L (x - t • Pi.single i v) = energy L x
      - 2 * t * L i * inner ℝ (x i) v + t ^ 2 * L i * ‖v‖ ^ 2 := by
  classical
  have hi : ‖x i - t • v‖^2 = ‖x i‖^2 - 2*t*inner ℝ (x i) v + t^2*‖v‖^2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hh : energy L (x-t•Pi.single i v) =
      ∑ j, (L j*‖x j‖^2 + if j=i then
        -2*t*L i*inner ℝ (x i) v+t^2*L i*‖v‖^2 else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j=i
    · subst j
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, ite_true, hi]
      ring
    · simp [Pi.sub_apply, Pi.smul_apply, hji]
  rw [hh, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold energy
  ring

theorem energy_mix_le (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i)
    (x y : Blocks E) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    energy L (t • x + (1-t) • y) ≤ t * energy L x + (1-t) * energy L y := by
  unfold energy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hh : ‖t•x i+(1-t)•y i‖^2 ≤ t*‖x i‖^2+(1-t)*‖y i‖^2 := by
    have he := norm_sub_sq_real (x i) (y i)
    have hn := sq_nonneg ‖x i-y i‖
    have hp := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) hn
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs]
    rw [he] at hp
    nlinarith only [hp]
  have hm := mul_le_mul_of_nonneg_left hh (hL i)
  simpa only [Pi.add_apply, Pi.smul_apply] using hm.trans_eq (by ring)

end ACDMProof

open scoped BigOperators
open Set InnerProductSpace
open NesterovRCD.Sublinear NesterovRCD.HighProb NesterovRCD.Accelerated

namespace ACDMProof

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]

theorem fderiv_eq_sum (f : Blocks E → ℝ) (x d : Blocks E) :
    fderiv ℝ f x d = ∑ i, partialGrad f x i (d i) := by
  exact (ContinuousLinearMap.sum_comp_single ℝ E (fderiv ℝ f x) d).symm

theorem coordinate_model (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (hLip : CoordLipschitz f L) (x : Blocks E) (i : Fin n) (d : E i) :
    f (x + Pi.single i d) ≤ f x + partialGrad f x i d + L i / 2 * ‖d‖ ^ 2 := by
  classical
  let a : Blocks E := Pi.single i d
  let φ : ℝ → ℝ := fun t => f (x+t•a)-f x-t*partialGrad f x i d-(L i/2*‖d‖^2)*t^2
  have ha (t : ℝ) : t•a = Pi.single i (t•d) := by
    ext j
    by_cases hj : j=i
    · subst j; simp [a]
    · simp [a, hj]
  have hd (t : ℝ) : HasDerivAt φ
      ((partialGrad f (x+t•a) i-partialGrad f x i) d-L i*t*‖d‖^2) t := by
    have hp : HasDerivAt (fun t : ℝ => x+t•a) a t := by
      simpa using ((hasDerivAt_id t).smul_const a).const_add x
    have hh := (((hLip.1 (x+t•a)).hasFDerivAt.comp_hasDerivAt t hp).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const (partialGrad f x i d))
    have hh' := hh.sub (((hasDerivAt_id t).pow 2).const_mul (L i/2*‖d‖^2))
    convert! hh' using 1
    simp only [sub_apply, partialGrad, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, a, id_eq]
    ring
  have hn (t : ℝ) (ht : 0 ≤ t) :
      (partialGrad f (x+t•a) i-partialGrad f x i) d-L i*t*‖d‖^2 ≤ 0 := by
    have hb : ‖partialGrad f (x+t•a) i-partialGrad f x i‖ ≤ L i*(t*‖d‖) := by
      simpa only [ha, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] using hLip.2.2 i x (t•d)
    have ho := (partialGrad f (x+t•a) i-partialGrad f x i).le_opNorm d
    have hh := le_abs_self ((partialGrad f (x+t•a) i-partialGrad f x i) d)
    have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg d)
    rw [Real.norm_eq_abs] at ho
    nlinarith only [ho, hh, hm]
  have hanti : AntitoneOn φ (Ici (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => hn t (interior_subset ht))
  have hh := hanti (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
    (show (1 : ℝ) ∈ Ici 0 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [φ, zero_smul, add_zero, zero_mul, sub_self, zero_pow (by decide : 2 ≠ 0),
    one_smul, one_mul, one_pow, mul_one, a] at hh
  linarith

variable [∀ i, FiniteDimensional ℝ (E i)]

theorem coordinate_decrease (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hLip : CoordLipschitz f L)
    (hsharp : IsSharpSelection sharp) (x : Blocks E) (i : Fin n) :
    ‖sharp i (partialGrad f x i)‖ ^ 2 / (2 * L i) ≤
      f x - f (coordStep f L sharp i x) := by
  classical
  let v := sharp i (partialGrad f x i)
  have hs : partialGrad f x i v = ‖v‖^2 := by
    rw [← sharp_inner _ v (hsharp i _) v, real_inner_self_eq_norm_sq]
  have hm := coordinate_model f L hLip x i (-(L i)⁻¹ • v)
  have hstep : x+Pi.single i (-(L i)⁻¹•v) = coordStep f L sharp i x := by
    ext j
    by_cases hj : j=i
    · subst j; simp [coordStep, v, sub_eq_add_neg]
    · simp [coordStep, hj]
  rw [hstep, map_smul, smul_eq_mul, hs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hm
  have hLi := hLip.2.1 i
  have he : -(L i)⁻¹*‖v‖^2+L i/2*(-(L i)⁻¹)^2*‖v‖^2 =
      -(‖v‖^2/(2*L i)) := by field_simp; ring
  nlinarith only [hm, he]

end ACDMProof

namespace ACDMProof

open NesterovRCD.Accelerated

lemma gamma_properties (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    0 < gammaOf n σ a b ∧ (n : ℝ)⁻¹ < gammaOf n σ a b ∧
    0 < 1-gammaOf n σ a b*σ/n ∧ 1-gammaOf n σ a b*σ/n ≤ 1 ∧
    gammaOf n σ a b^2-gammaOf n σ a b/n =
      (1-gammaOf n σ a b*σ/n)*a^2/b^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hb0 : b ≠ 0 := ne_of_gt hb
  let q := a^2/b^2
  let c := (1-σ*q)/n
  let d := Real.sqrt (c^2+4*q)
  let γ := gammaOf n σ a b
  have hq : 0 < q := div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2=c^2+4*q := Real.sq_sqrt (by positivity)
  have hdc : c < d := by
    by_contra h
    have hcd : d ≤ c := le_of_not_gt h
    have := mul_nonneg (sub_nonneg.mpr hcd) (show 0 ≤ c+d by linarith)
    nlinarith
  have hdn : -c < d := by
    by_contra h
    have hcd : d ≤ -c := le_of_not_gt h
    have := mul_nonneg (sub_nonneg.mpr hcd) (show 0 ≤ -c+d by linarith)
    nlinarith
  have hγdef : γ=(c+d)/2 := by
    dsimp [γ, gammaOf, c, d, q]
    congr 2 <;> ring
  have hγ : 0 < γ := by linarith
  have hγc : 0 < γ-c := by linarith
  have heq : γ^2-c*γ-q=0 := by
    rw [hγdef]
    nlinarith only [hd2]
  have hfactor (t : ℝ) : (t-γ)*(t+γ-c)=t^2-c*t-q := by
    nlinarith only [heq]
  have hN : 0 < (n : ℝ)^2-σ := sub_pos.mpr hσn
  have htest : (n : ℝ)⁻¹^2-c*(n : ℝ)⁻¹-q < 0 := by
    have hid : (n : ℝ)⁻¹^2-c*(n : ℝ)⁻¹-q =
        -((n : ℝ)^2-σ)*q/(n : ℝ)^2 := by
      dsimp [c]
      field_simp
      ring
    rw [hid]
    exact div_neg_of_neg_of_pos (by nlinarith) (sq_pos_of_pos hnR)
  have hγn : (n : ℝ)⁻¹ < γ := by
    have hsecond : 0 < (n : ℝ)⁻¹+γ-c := by
      have := inv_pos.mpr hnR
      linarith only [this,hγc]
    have hprod := hfactor (n : ℝ)⁻¹
    by_contra h
    have := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hsecond.le
    linarith
  have hroot : γ^2-γ/n=(1-γ*σ/n)*a^2/b^2 := by
    dsimp [c, q] at heq
    field_simp at heq ⊢
    nlinarith only [heq]
  have hβ : 0 < 1-γ*σ/n := by
    by_cases hσ : σ=0
    · simp [hσ]
    · have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσ)
      have htest' : (n/σ)^2-c*(n/σ)-q > 0 := by
        have hid : (n/σ)^2-c*(n/σ)-q = ((n : ℝ)^2-σ)/σ^2 := by
          dsimp [c]
          field_simp
          ring
        rw [hid]
        exact div_pos hN (sq_pos_of_pos hσp)
      have hsecond : 0 < n/σ+γ-c := by
        have := div_pos hnR hσp
        linarith only [this,hγc]
      have hprod := hfactor (n/σ)
      have hupper : γ < n/σ := by
        by_contra h
        have := mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (le_of_not_gt h)) hsecond.le
        linarith
      have hgσ : γ*σ < n := (lt_div_iff₀ hσp).mp hupper
      have : γ*σ/n < 1 := (div_lt_one hnR).mpr hgσ
      linarith
  exact ⟨hγ, hγn, hβ, sub_le_self _ (div_nonneg (mul_nonneg hγ.le hσ0) hnR.le), hroot⟩

lemma coefficient_ab_positive (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    0 < acdmA n σ k ∧ 0 < acdmB n σ k := by
  induction k with
  | zero =>
    simp only [acdmA, acdmB, coeffAB]
    exact ⟨inv_pos.mpr (by exact_mod_cast hn), by norm_num⟩
  | succ k ih =>
    obtain ⟨hg, _, hβ, _, _⟩ := gamma_properties n hn σ hσ0 hσn _ _ ih.1 ih.2
    have hs := Real.sqrt_pos.mpr hβ
    change 0 < gammaOf n σ (acdmA n σ k) (acdmB n σ k) *
      (acdmB n σ k / Real.sqrt (1-gammaOf n σ (acdmA n σ k) (acdmB n σ k)*σ/n)) ∧
      0 < acdmB n σ k / Real.sqrt (1-gammaOf n σ (acdmA n σ k) (acdmB n σ k)*σ/n)
    exact ⟨mul_pos hg (div_pos ih.2 hs), div_pos ih.2 hs⟩

theorem coefficient_positive (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    0 < acdmA n σ k ∧ 0 < acdmB n σ k ∧
    0 < acdmGamma n σ k ∧
    0 < acdmAlpha n σ k ∧ acdmAlpha n σ k ≤ 1 ∧
    0 < acdmBeta n σ k ∧ acdmBeta n σ k ≤ 1 := by
  obtain ⟨ha,hb⟩ := coefficient_ab_positive n hn σ hσ0 hσn k
  obtain ⟨hg,hgn,hβ,hβ1,_⟩ := gamma_properties n hn σ hσ0 hσn _ _ ha hb
  change 0 < acdmGamma n σ k at hg
  change (n : ℝ)⁻¹ < acdmGamma n σ k at hgn
  change 0 < acdmBeta n σ k at hβ
  change acdmBeta n σ k ≤ 1 at hβ1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum : 0 < (n : ℝ)-acdmGamma n σ k*σ := by
    have := (div_lt_one hnR).mp (show acdmGamma n σ k*σ/n < 1 by
      dsimp [acdmBeta] at hβ; linarith)
    linarith
  have hden : 0 < acdmGamma n σ k*((n : ℝ)^2-σ) :=
    mul_pos hg (sub_pos.mpr hσn)
  have hα : 0 < acdmAlpha n σ k := div_pos hnum hden
  have hγN : 1 ≤ acdmGamma n σ k*n := by
    have := (div_lt_iff₀ hnR).mp (show 1/(n : ℝ) < acdmGamma n σ k by simpa using hgn)
    linarith
  have hα1 : acdmAlpha n σ k ≤ 1 := by
    apply (div_le_one hden).mpr
    have := mul_le_mul_of_nonneg_right hγN hnR.le
    nlinarith only [this]
  exact ⟨ha,hb,hg,hα,hα1,hβ,hβ1⟩

theorem coefficient_relations (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    acdmBeta n σ k * acdmB n σ (k+1)^2 = acdmB n σ k^2 ∧
    acdmA n σ (k+1) = acdmGamma n σ k * acdmB n σ (k+1) ∧
    acdmGamma n σ k^2 - acdmGamma n σ k / n =
      acdmBeta n σ k * acdmA n σ k^2 / acdmB n σ k^2 ∧
    acdmGamma n σ k^2 - acdmGamma n σ k / n =
      acdmBeta n σ k * acdmGamma n σ k / n *
        (1-acdmAlpha n σ k) / acdmAlpha n σ k ∧
    1-acdmBeta n σ k = acdmGamma n σ k * σ / n := by
  obtain ⟨ha,hb,hg,hα,_,hβ,_⟩ := coefficient_positive n hn σ hσ0 hσn k
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNs : (n : ℝ)^2-σ ≠ 0 := ne_of_gt (sub_pos.mpr hσn)
  have hnum : (n : ℝ)-acdmGamma n σ k*σ ≠ 0 := by
    have : 0 < (n : ℝ)*acdmBeta n σ k := mul_pos hnR hβ
    dsimp [acdmBeta] at this
    field_simp at this
    nlinarith only [this]
  have hbnext : acdmB n σ (k+1) = acdmB n σ k / Real.sqrt (acdmBeta n σ k) := rfl
  have hanext : acdmA n σ (k+1) = acdmGamma n σ k * acdmB n σ (k+1) := rfl
  have hbb : acdmBeta n σ k * acdmB n σ (k+1)^2 = acdmB n σ k^2 := by
    rw [hbnext, div_pow, Real.sq_sqrt hβ.le]
    field_simp
  have hroot := (gamma_properties n hn σ hσ0 hσn _ _ ha hb).2.2.2.2
  change acdmGamma n σ k^2-acdmGamma n σ k/n =
    acdmBeta n σ k*acdmA n σ k^2/acdmB n σ k^2 at hroot
  refine ⟨hbb,hanext,hroot,?_,by simp [acdmBeta]⟩
  dsimp [acdmAlpha, acdmBeta]
  field_simp
  ring

end ACDMProof

namespace ACDMProof

open NesterovRCD.Accelerated

lemma coefficient_square_differences (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    acdmA n σ (k+1)^2-acdmA n σ k^2 =
      acdmA n σ (k+1)*acdmB n σ (k+1)/n ∧
    acdmB n σ (k+1)^2-acdmB n σ k^2 =
      σ*acdmA n σ (k+1)*acdmB n σ (k+1)/n := by
  obtain ⟨hbb,hab,hroot,_,hβ⟩ := coefficient_relations n hn σ hσ0 hσn k
  obtain ⟨_,hb,_,_,_,_,_⟩ := coefficient_positive n hn σ hσ0 hσn k
  have hb0 : acdmB n σ k ≠ 0 := ne_of_gt hb
  have hr : (acdmGamma n σ k^2-acdmGamma n σ k/n)*acdmB n σ (k+1)^2 = acdmA n σ k^2 := by
    rw [hroot]
    calc
      acdmBeta n σ k*acdmA n σ k^2/acdmB n σ k^2*acdmB n σ (k+1)^2 =
          acdmA n σ k^2*(acdmBeta n σ k*acdmB n σ (k+1)^2)/acdmB n σ k^2 := by ring
      _ = acdmA n σ k^2 := by rw [hbb]; field_simp
  have haa : acdmGamma n σ k^2*acdmB n σ (k+1)^2 = acdmA n σ (k+1)^2 := by
    rw [hab]; ring
  have hag : acdmGamma n σ k*acdmB n σ (k+1)^2 =
      acdmA n σ (k+1)*acdmB n σ (k+1) := by rw [hab]; ring
  constructor
  · calc
      acdmA n σ (k+1)^2-acdmA n σ k^2 =
          acdmGamma n σ k^2*acdmB n σ (k+1)^2-
            (acdmGamma n σ k^2-acdmGamma n σ k/n)*acdmB n σ (k+1)^2 := by rw [haa,hr]
      _ = (acdmGamma n σ k*acdmB n σ (k+1)^2)/n := by ring
      _ = _ := by rw [hag]
  · calc
      acdmB n σ (k+1)^2-acdmB n σ k^2 =
          (1-acdmBeta n σ k)*acdmB n σ (k+1)^2 := by rw [← hbb]; ring
      _ = σ*(acdmGamma n σ k*acdmB n σ (k+1)^2)/n := by rw [hβ]; ring
      _ = _ := by rw [hag]; ring

theorem coefficient_increment (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    acdmA n σ k + acdmB n σ k / (2*n) ≤ acdmA n σ (k+1) ∧
    acdmB n σ k + σ * acdmA n σ k / (2*n) ≤ acdmB n σ (k+1) := by
  obtain ⟨ha,hb⟩ := coefficient_ab_positive n hn σ hσ0 hσn k
  obtain ⟨ha',hb'⟩ := coefficient_ab_positive n hn σ hσ0 hσn (k+1)
  obtain ⟨hA,hB⟩ := coefficient_square_differences n hn σ hσ0 hσn k
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAm : acdmA n σ k ≤ acdmA n σ (k+1) := by
    have := div_nonneg (mul_nonneg ha'.le hb'.le) hnR.le
    nlinarith only [this,hA,ha,ha']
  have hBm : acdmB n σ k ≤ acdmB n σ (k+1) := by
    have := div_nonneg (mul_nonneg (mul_nonneg hσ0 ha'.le) hb'.le) hnR.le
    nlinarith only [this,hB,hb,hb']
  have hA' : (acdmA n σ (k+1)^2-acdmA n σ k^2)*n =
      acdmA n σ (k+1)*acdmB n σ (k+1) := (eq_div_iff hnR.ne').mp hA
  have hB' : (acdmB n σ (k+1)^2-acdmB n σ k^2)*n =
      σ*acdmA n σ (k+1)*acdmB n σ (k+1) := (eq_div_iff hnR.ne').mp hB
  have hda : acdmB n σ (k+1)/(2*n) ≤ acdmA n σ (k+1)-acdmA n σ k := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*n)).mpr
    have hz := mul_nonneg (sub_nonneg.mpr hAm) (sub_nonneg.mpr hAm)
    have hz' := mul_nonneg hnR.le hz
    nlinarith only [hA',hz',ha']
  have hdb : σ*acdmA n σ (k+1)/(2*n) ≤ acdmB n σ (k+1)-acdmB n σ k := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*n)).mpr
    have hz := mul_nonneg (sub_nonneg.mpr hBm) (sub_nonneg.mpr hBm)
    have hz' := mul_nonneg hnR.le hz
    nlinarith only [hB',hz',hb']
  constructor
  · have := div_le_div_of_nonneg_right hBm (by positivity : (0 : ℝ)≤2*n)
    linarith
  · have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAm hσ0)
      (by positivity : (0 : ℝ)≤2*n)
    linarith

lemma acdmB_two (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) : 2 ≤ acdmB n σ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := (coefficient_increment n hn σ hσ0 hσn k).2
    have ha := (coefficient_ab_positive n hn σ hσ0 hσn k).1
    have : 0 ≤ σ*acdmA n σ k/(2*n) := by positivity
    linarith

theorem acdmA_linear (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    ((k+1 : ℕ) : ℝ)/n ≤ acdmA n σ k := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  induction k with
  | zero => simp [acdmA,coeffAB]
  | succ k ih =>
    have h := (coefficient_increment n hn σ hσ0 hσn k).1
    have hb := acdmB_two n hn σ hσ0 hσn k
    have hb' := div_le_div_of_nonneg_right hb (show (0 : ℝ)≤2*n by positivity)
    have heq : ((k+1 : ℕ) : ℝ)/n+2/(2*n)=((k+1+1 : ℕ) : ℝ)/n := by
      push_cast
      field_simp
    linarith

lemma power_gap_sum (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    2*(j : ℝ)*t ≤ (1+t)^j-(1-t)^j ∧ 2 ≤ (1+t)^j+(1-t)^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hX : (1+t)^(j+1)-(1-t)^(j+1) =
        ((1+t)^j-(1-t)^j)+t*((1+t)^j+(1-t)^j) := by rw [pow_succ,pow_succ]; ring
    have hY : (1+t)^(j+1)+(1-t)^(j+1) =
        ((1+t)^j+(1-t)^j)+t*((1+t)^j-(1-t)^j) := by rw [pow_succ,pow_succ]; ring
    have htY := mul_le_mul_of_nonneg_left ih.2 ht
    have hX0 : 0 ≤ (1+t)^j-(1-t)^j := le_trans (by positivity) ih.1
    have htX := mul_nonneg ht hX0
    constructor <;> push_cast <;> linarith

lemma coefficient_geometric_pair (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ : 0 < σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    (1+Real.sqrt σ/(2*n))^(k+1)-(1-Real.sqrt σ/(2*n))^(k+1) ≤
      Real.sqrt σ * acdmA n σ k ∧
    (1+Real.sqrt σ/(2*n))^(k+1)+(1-Real.sqrt σ/(2*n))^(k+1) ≤ acdmB n σ k := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hs2 := Real.sq_sqrt hσ.le
  let t := Real.sqrt σ/(2*n)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  change (1+t)^(k+1)-(1-t)^(k+1) ≤ Real.sqrt σ*acdmA n σ k ∧
    (1+t)^(k+1)+(1-t)^(k+1) ≤ acdmB n σ k
  induction k with
  | zero =>
    simp only [acdmA,acdmB,coeffAB]
    dsimp [t]
    constructor
    · field_simp
      nlinarith
    · ring_nf
      exact le_rfl
  | succ k ih =>
    obtain ⟨hA,hB⟩ := coefficient_increment n hn σ hσ.le hσn k
    have hA' := mul_le_mul_of_nonneg_left hA hs.le
    have hX : (1+t)^(k+1+1)-(1-t)^(k+1+1) =
        ((1+t)^(k+1)-(1-t)^(k+1))+t*((1+t)^(k+1)+(1-t)^(k+1)) := by
      rw [pow_succ,pow_succ]; ring
    have hY : (1+t)^(k+1+1)+(1-t)^(k+1+1) =
        ((1+t)^(k+1)+(1-t)^(k+1))+t*((1+t)^(k+1)-(1-t)^(k+1)) := by
      rw [pow_succ,pow_succ]; ring
    have hx := add_le_add ih.1 (mul_le_mul_of_nonneg_left ih.2 ht)
    have hy := add_le_add ih.2 (mul_le_mul_of_nonneg_left ih.1 ht)
    have hcA : Real.sqrt σ*(acdmA n σ k+acdmB n σ k/(2*n)) =
        Real.sqrt σ*acdmA n σ k+t*acdmB n σ k := by dsimp [t]; ring
    have hcB : acdmB n σ k+t*(Real.sqrt σ*acdmA n σ k) =
        acdmB n σ k+σ*acdmA n σ k/(2*n) := by
      dsimp [t]
      calc
        _ = acdmB n σ k+(Real.sqrt σ)^2*acdmA n σ k/(2*n) := by ring
        _ = _ := by rw [hs2]
    exact ⟨by linarith, by linarith⟩

theorem acdmA_geometric (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ : 0 < σ) (hσn : σ < (n : ℝ)^2) (k : ℕ) :
    ((1+Real.sqrt σ/(2*n))^(k+1)-(1-Real.sqrt σ/(2*n))^(k+1))/
      Real.sqrt σ ≤ acdmA n σ k := by
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hσ)).mpr
  simpa [mul_comm] using (coefficient_geometric_pair n hn σ hσ hσn k).1

theorem scalar_rates (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ)^2) (k : ℕ)
    (D g : ℝ) (hD : 0 ≤ D) (hg : 0 ≤ g)
    (hpot : acdmA n σ k^2*g ≤ D) :
    (0 < σ →
      g ≤ σ*D/((1+Real.sqrt σ/(2*n))^(k+1)-(1-Real.sqrt σ/(2*n))^(k+1))^2 ∧
      σ*D/((1+Real.sqrt σ/(2*n))^(k+1)-(1-Real.sqrt σ/(2*n))^(k+1))^2 ≤
        ((n : ℝ)/(k+1))^2*D) ∧ g ≤ ((n : ℝ)/(k+1))^2*D := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hkR : (0 : ℝ)<(k+1 : ℕ) := by positivity
  have hA := acdmA_linear n hn σ hσ0 hσn k
  have hA0 := (coefficient_ab_positive n hn σ hσ0 hσn k).1
  have hsq : (((k+1 : ℕ) : ℝ)/n)^2 ≤ acdmA n σ k^2 := by
    gcongr
  have hbase := (mul_le_mul_of_nonneg_right hsq hg).trans hpot
  have hout : g ≤ ((n : ℝ)/(k+1))^2*D := by
    have h := mul_le_mul_of_nonneg_left hbase (show 0 ≤ ((n : ℝ)/(k+1))^2 by positivity)
    have heq : ((n : ℝ)/(k+1))^2*((((k+1 : ℕ) : ℝ)/n)^2*g)=g := by push_cast; field_simp
    rwa [heq] at h
  refine ⟨?_,hout⟩
  intro hσ
  have hs := Real.sqrt_pos.mpr hσ
  have hs2 := Real.sq_sqrt hσ.le
  let X := (1+Real.sqrt σ/(2*n))^(k+1)-(1-Real.sqrt σ/(2*n))^(k+1)
  have hXlow : ((k+1 : ℕ) : ℝ)*Real.sqrt σ/n ≤ X := by
    have h := (power_gap_sum (Real.sqrt σ/(2*n)) (by positivity) (k+1)).1
    dsimp [X]
    convert h using 1
    ring
  have hX : 0 < X := lt_of_lt_of_le (by positivity) hXlow
  have hgeom := (coefficient_geometric_pair n hn σ hσ hσn k).1
  change X ≤ Real.sqrt σ*acdmA n σ k at hgeom
  have hgeom2 : X^2 ≤ σ*acdmA n σ k^2 := by
    have h : X^2 ≤ (Real.sqrt σ*acdmA n σ k)^2 := by gcongr
    simpa [mul_pow,hs2] using h
  have hgap : X^2*g ≤ σ*D := calc
    X^2*g ≤ (σ*acdmA n σ k^2)*g := mul_le_mul_of_nonneg_right hgeom2 hg
    _ = σ*(acdmA n σ k^2*g) := by ring
    _ ≤ σ*D := mul_le_mul_of_nonneg_left hpot hσ.le
  refine ⟨(le_div_iff₀ (sq_pos_of_pos hX)).mpr (by simpa [mul_comm] using hgap), ?_⟩
  have hlow2 : (((k+1 : ℕ) : ℝ)*Real.sqrt σ/n)^2 ≤ X^2 := by gcongr
  have hscaled := mul_le_mul_of_nonneg_left hlow2
    (show 0 ≤ ((n : ℝ)/(k+1))^2*D by positivity)
  have hcancel : ((n : ℝ)/(k+1))^2*D*((((k+1 : ℕ) : ℝ)*Real.sqrt σ/n)^2)=σ*D := by
    push_cast
    simp only [div_pow,mul_pow,hs2]
    field_simp
  apply (div_le_iff₀ (sq_pos_of_pos hX)).mpr
  rwa [hcancel] at hscaled

end ACDMProof

namespace ACDMProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.Accelerated

theorem expect_snoc {n : ℕ} (p : Fin n → ℝ) (k : ℕ)
    (F : (Fin (k+1) → Fin n) → ℝ) :
    expect p (k+1) F = expect p k
      (fun idx => ∑ i, p i * F (Fin.snoc idx i)) := by
  classical
  unfold expect
  rw [← (Fin.snocEquiv (fun _ : Fin (k+1) => Fin n)).sum_comp]
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro idx _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  ring

lemma expect_zero {n : ℕ} (p : Fin n → ℝ) (F : (Fin 0 → Fin n) → ℝ) :
    expect p 0 F = F Fin.elim0 := by
  simp only [expect, Finset.univ_eq_empty, Finset.prod_empty, one_mul, Fintype.sum_unique]
  exact congrArg F (Subsingleton.elim _ _)

lemma expect_add {n : ℕ} (p : Fin n → ℝ) (k : ℕ)
    (F G : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => F idx + G idx) = expect p k F + expect p k G := by
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_sub {n : ℕ} (p : Fin n → ℝ) (k : ℕ)
    (F G : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => F idx - G idx) = expect p k F - expect p k G := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

lemma expect_mul {n : ℕ} (p : Fin n → ℝ) (k : ℕ) (c : ℝ)
    (F : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => c * F idx) = c * expect p k F := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro idx _
  ring

theorem expect_const {n : ℕ} (hn : 0 < n) (k : ℕ) (c : ℝ) :
    expect (fun _ : Fin n => (n : ℝ)⁻¹) k (fun _ => c) = c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  induction k with
  | zero => exact expect_zero _ _
  | succ k ih =>
    rw [expect_snoc]
    simpa [Finset.sum_const, nsmul_eq_mul, hn0, mul_assoc] using ih

theorem expect_mono {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) (F G : (Fin k → Fin n) → ℝ) (h : ∀ idx, F idx ≤ G idx) :
    expect p k F ≤ expect p k G := by
  apply Finset.sum_le_sum
  intro idx _
  exact mul_le_mul_of_nonneg_left (h idx) (Finset.prod_nonneg (fun _ _ => hp _))

lemma expect_nonneg {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) (F : (Fin k → Fin n) → ℝ) (h : ∀ idx, 0 ≤ F idx) :
    0 ≤ expect p k F := by
  exact Finset.sum_nonneg fun idx _ =>
    mul_nonneg (Finset.prod_nonneg (fun _ _ => hp _)) (h idx)

variable {n : ℕ} {E : Fin n → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

lemma acdm_snoc (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (σ : ℝ) (x0 : Blocks E)
    (k : ℕ) (idx : Fin k → Fin n) (i : Fin n) :
    acdm f L sharp σ x0 (k+1) (Fin.snoc idx i) =
      let xv := acdm f L sharp σ x0 k idx
      let y := acdmAlpha n σ k • xv.2 + (1-acdmAlpha n σ k) • xv.1
      (coordStep f L sharp i y,
        acdmBeta n σ k • xv.2 + (1-acdmBeta n σ k) • y -
        (acdmGamma n σ k / L i) • Pi.single i (sharp i (partialGrad f y i))) := by
  rw [acdm]
  simp only [Fin.init_snoc]
  rw [Fin.snoc_last (α := fun _ => Fin n)]

end ACDMProof

namespace ACDMProof

open scoped BigOperators
open NesterovRCD.Sublinear NesterovRCD.HighProb NesterovRCD.Accelerated
open InnerProductSpace

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

omit [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] in
lemma energy_neg (L : Fin n → ℝ) (x : Blocks E) : energy L (-x)=energy L x := by
  simp [energy]

omit [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] in
lemma energy_sub_comm (L : Fin n → ℝ) (x y : Blocks E) : energy L (x-y)=energy L (y-x) := by
  simpa only [neg_sub] using energy_neg L (y-x)

lemma one_step_potential (hn : 0<n) (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : CoordLipschitz f L) (σ : ℝ) (hσ0 : 0≤σ) (hσn : σ<(n : ℝ)^2)
    (hsc : StronglyConvexW f L 1 σ) (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (hsharp : IsSharpSelection sharp) (x v xs : Blocks E) (k : ℕ) :
    let y := acdmAlpha n σ k • v+(1-acdmAlpha n σ k) • x
    let c := acdmBeta n σ k • v+(1-acdmBeta n σ k) • y
    (∑ i, (n : ℝ)⁻¹ *
      (2*acdmA n σ (k+1)^2*(f (coordStep f L sharp i y)-f xs)+
        acdmB n σ (k+1)^2*energy L
          (c-(acdmGamma n σ k/L i)•Pi.single i (sharp i (partialGrad f y i))-xs))) ≤
      2*acdmA n σ k^2*(f x-f xs)+acdmB n σ k^2*energy L (v-xs) := by
  classical
  let α := acdmAlpha n σ k
  let β := acdmBeta n σ k
  let γ := acdmGamma n σ k
  let a := acdmA n σ k
  let b := acdmB n σ k
  let ap := acdmA n σ (k+1)
  let bp := acdmB n σ (k+1)
  let y := α•v+(1-α)•x
  let c := β•v+(1-β)•y
  let τ := β*(1-α)/α
  let u := fun i => sharp i (partialGrad f y i)
  let fx := fun i => f (coordStep f L sharp i y)
  let ev := fun i => energy L (c-(γ/L i)•Pi.single i (u i)-xs)
  change (∑ i, (n : ℝ)⁻¹*(2*ap^2*(fx i-f xs)+bp^2*ev i)) ≤
    2*a^2*(f x-f xs)+b^2*energy L (v-xs)
  obtain ⟨ha,hb,hγ,hα,hα1,hβ,hβ1⟩ := coefficient_positive n hn σ hσ0 hσn k
  obtain ⟨hbb,hab,hroot,htau,hβeq⟩ := coefficient_relations n hn σ hσ0 hσn k
  change 0<γ at hγ
  change 0<α at hα
  change α≤1 at hα1
  change 0<β at hβ
  change β≤1 at hβ1
  change β*bp^2=b^2 at hbb
  change ap=γ*bp at hab
  change γ^2-γ/n=β*a^2/b^2 at hroot
  change γ^2-γ/n=β*γ/n*(1-α)/α at htau
  change 1-β=γ*σ/n at hβeq
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hn0 := ne_of_gt hnR
  have hLn : ∀ i,0≤L i := fun i => (hL.2.1 i).le
  have hτ : 0≤τ := div_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hα1)) hα.le
  have hτeq : γ^2-γ/n=γ*τ/n := by
    rw [htau]
    dsimp [τ]
    ring
  have hpoint (i : Fin n) : ev i ≤ energy L (c-xs)+2*γ^2*(f y-fx i)+
      2*γ*partialGrad f y i ((xs-c) i) := by
    have hLi := hL.2.1 i
    have hzero := ne_of_gt hLi
    have hdesc := coordinate_decrease f L sharp hL hsharp y i
    have hmul := mul_le_mul_of_nonneg_left hdesc (show 0≤2*γ^2 by positivity)
    have he : c-(γ/L i)•Pi.single i (u i)-xs = (c-xs)-(γ/L i)•Pi.single i (u i) := by abel
    have hs : inner ℝ ((c-xs) i) (u i) = -partialGrad f y i ((xs-c) i) := by
      rw [real_inner_comm,sharp_inner _ _ (hsharp i _) _]
      simp only [Pi.sub_apply,map_sub]
      ring
    have hcoef : (γ/L i)^2*L i*‖u i‖^2 = 2*γ^2*(‖u i‖^2/(2*L i)) := by
      field_simp
    have hcross : -2*(γ/L i)*L i*inner ℝ ((c-xs) i) (u i) =
        2*γ*partialGrad f y i ((xs-c) i) := by rw [hs]; field_simp
    dsimp [ev]
    rw [he,energy_single_update]
    have hnrm : ‖u i‖^2=‖sharp i (partialGrad f y i)‖^2 := rfl
    dsimp [fx]
    simp only [Pi.sub_apply] at hcross hcoef ⊢
    rw [hnrm]
    linarith only [hmul,hcoef,hcross]
  have hsum : (∑ i,ev i) ≤ (n : ℝ)*energy L (c-xs)+
      2*γ^2*((n : ℝ)*f y-∑ i,fx i)+2*γ*fderiv ℝ f y (xs-c) := calc
    (∑ i,ev i) ≤ ∑ i,(energy L (c-xs)+2*γ^2*(f y-fx i)+
      2*γ*partialGrad f y i ((xs-c) i)) := Finset.sum_le_sum fun i _ => hpoint i
    _ = _ := by
      rw [fderiv_eq_sum]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmix : energy L (c-xs) ≤ β*energy L (v-xs)+(1-β)*energy L (y-xs) := by
    have he : c-xs=β•(v-xs)+(1-β)•(y-xs) := by dsimp [c]; module
    rw [he]
    exact energy_mix_le L hLn _ _ β hβ.le hβ1
  have hdir : xs-c=(xs-y)+τ•(x-y) := by
    have hτa : τ*α=β*(1-α) := by dsimp [τ]; field_simp
    have he : α•(xs-c)=α•((xs-y)+τ•(x-y)) := calc
      α•(xs-c)=α•(xs-y)+(β*(1-α))•(x-y) := by dsimp [c,y]; module
      _ = α•((xs-y)+τ•(x-y)) := by rw [smul_add,smul_smul,mul_comm α τ,hτa]
    exact (smul_right_injective (Blocks E) hα.ne') he
  have hz := hsc.2 y xs
  have hx := hsc.2 y x
  rw [wnorm_sq L hLn,energy_sub_comm L xs y] at hz
  rw [wnorm_sq L hLn] at hx
  have hx0 : 0≤σ/2*energy L (x-y) := mul_nonneg (by positivity) (energy_nonneg L hLn _)
  have hx' : fderiv ℝ f y (x-y) ≤ f x-f y := by linarith only [hx,hx0]
  have hfd : fderiv ℝ f y (xs-c) ≤ f xs-f y-σ/2*energy L (y-xs)+τ*(f x-f y) := by
    rw [hdir,map_add,map_smul,smul_eq_mul]
    have hτx := mul_le_mul_of_nonneg_left hx' hτ
    linarith only [hz,hτx]
  have hmix' := mul_le_mul_of_nonneg_left hmix hnR.le
  have hfd' := mul_le_mul_of_nonneg_left hfd (show 0≤2*γ by positivity)
  have hβN : (1-β)*n=γ*σ := (eq_div_iff hn0).mp hβeq
  have hτN : γ^2*n=γ+γ*τ := by
    have ht := hτeq
    field_simp at ht
    rw [← ht]
    ring
  have hβE := congrArg (fun z : ℝ => z*energy L (y-xs)) hβN
  have hτF := congrArg (fun z : ℝ => z*(f y-f xs)) hτN
  have hcore : (∑ i,ev i)+2*γ^2*((∑ i,fx i)-(n : ℝ)*f xs) ≤
      (n : ℝ)*β*energy L (v-xs)+2*γ*τ*(f x-f xs) := by
    nlinarith only [hsum,hmix',hfd',hβE,hτF]
  have hscaled := mul_le_mul_of_nonneg_left hcore (show 0≤bp^2/(n : ℝ) by positivity)
  have hAeq : γ*τ*bp^2/(n : ℝ)=a^2 := by
    have hh := hroot.symm.trans hτeq
    have hb0 : b ≠ 0 := ne_of_gt hb
    calc
      γ*τ*bp^2/(n : ℝ) = (γ*τ/n)*bp^2 := by ring
      _ = (β*a^2/b^2)*bp^2 := by rw [← hh]
      _ = a^2*(β*bp^2)/b^2 := by ring
      _ = a^2 := by rw [hbb]; field_simp
  have hleft : (∑ i,(n : ℝ)⁻¹*(2*ap^2*(fx i-f xs)+bp^2*ev i)) =
      bp^2/n*((∑ i,ev i)+2*γ^2*((∑ i,fx i)-(n : ℝ)*f xs)) := by
    rw [hab]
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hright : bp^2/n*((n : ℝ)*β*energy L (v-xs)+2*γ*τ*(f x-f xs)) =
      2*a^2*(f x-f xs)+b^2*energy L (v-xs) := by
    have hb0 : bp^2/n*(n : ℝ)*β=b^2 := by field_simp; nlinarith only [hbb]
    calc
      _ = 2*(γ*τ*bp^2/n)*(f x-f xs)+(bp^2/n*n*β)*energy L (v-xs) := by ring
      _ = _ := by rw [hAeq,hb0]
  rw [hleft]
  exact hscaled.trans_eq hright

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem acdm_gap_nonneg (hn : 0<n) (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (σ : ℝ)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs) (k : ℕ) :
    0≤acdmPhi f L sharp σ x0 k-f xs := by
  have h := expect_mono (fun _ : Fin n => (n : ℝ)⁻¹) (by intro i; positivity) k
    (fun _ => f xs) (fun idx => f (acdm f L sharp σ x0 k idx).1) (fun _ => hxs _)
  rw [expect_const hn] at h
  exact sub_nonneg.mpr h

omit [∀ i, FiniteDimensional ℝ (E i)] in
theorem acdmR2_nonneg (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (σ : ℝ)
    (x0 xs : Blocks E) (k : ℕ) : 0≤acdmR2 f L sharp σ x0 xs k := by
  exact expect_nonneg _ (fun _ => by positivity) _ _ (fun _ => sq_nonneg _)

theorem potential_bound (hn : 0<n) (f : Blocks E → ℝ) (L : Fin n → ℝ)
    (hL : CoordLipschitz f L) (σ : ℝ) (hσ0 : 0≤σ)
    (hσn : σ<(n : ℝ)^2) (hsc : StronglyConvexW f L 1 σ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (x0 xs : Blocks E) (hxs : IsMinimizer f xs) (k : ℕ) :
    2*acdmA n σ k^2*(acdmPhi f L sharp σ x0 k-f xs)+
      acdmB n σ k^2*acdmR2 f L sharp σ x0 xs k ≤
    2*(2*wnorm L 1 (x0-xs)^2+1/(n : ℝ)^2*(f x0-f xs)) := by
  have _ := hxs
  let p : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  let P := fun (j : ℕ) (idx : Fin j → Fin n) =>
    2*acdmA n σ j^2*(f (acdm f L sharp σ x0 j idx).1-f xs)+
      acdmB n σ j^2*energy L ((acdm f L sharp σ x0 j idx).2-xs)
  have hLn : ∀i,0≤L i := fun i => (hL.2.1 i).le
  have hform (j : ℕ) : expect p j (P j) =
      2*acdmA n σ j^2*(acdmPhi f L sharp σ x0 j-f xs)+
        acdmB n σ j^2*acdmR2 f L sharp σ x0 xs j := by
    dsimp [P,acdmPhi,acdmR2]
    simp_rw [wnorm_sq L hLn]
    rw [expect_add,expect_mul,expect_sub,expect_mul,expect_const hn]
  rw [← hform]
  induction k with
  | zero =>
    rw [expect_zero]
    dsimp [P,acdm,acdmA,acdmB,coeffAB]
    rw [wnorm_sq L hLn]
    ring_nf
    exact le_rfl
  | succ k ih =>
    rw [expect_snoc]
    apply le_trans _ ih
    apply expect_mono p (fun _ => by dsimp [p]; positivity)
    intro idx
    have h := one_step_potential hn f L hL σ hσ0 hσn hsc sharp hsharp
      (acdm f L sharp σ x0 k idx).1 (acdm f L sharp σ x0 k idx).2 xs k
    simpa only [P,p,acdm_snoc] using h

end ACDMProof

namespace NesterovRCD.Accelerated

theorem theorem6 {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] (hn : 0 < n)
    (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (hsc : NesterovRCD.HighProb.StronglyConvexW f L 1 σ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs) (k : ℕ) :
    (0 < σ →
      acdmPhi f L sharp σ x0 k - f xs
        ≤ σ * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))
          / ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) ^ 2 ∧
      σ * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))
          / ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) ^ 2
        ≤ ((n : ℝ) / (k + 1)) ^ 2 * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))) ∧
    acdmPhi f L sharp σ x0 k - f xs
      ≤ ((n : ℝ) / (k + 1)) ^ 2 * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs)) := by
  have hp := ACDMProof.potential_bound hn f L hL σ hσ0 hσn hsc sharp hsharp x0 xs hxs k
  have hr := ACDMProof.acdmR2_nonneg f L sharp σ x0 xs k
  have hg := ACDMProof.acdm_gap_nonneg hn f L sharp σ x0 xs hxs k
  have hD : 0 ≤ 2 * NesterovRCD.Sublinear.wnorm L 1 (x0-xs)^2 +
      1/(n : ℝ)^2*(f x0-f xs) := by
    have hgap := sub_nonneg.mpr (hxs x0)
    positivity
  have hpot : acdmA n σ k^2*(acdmPhi f L sharp σ x0 k-f xs) ≤
      2*NesterovRCD.Sublinear.wnorm L 1 (x0-xs)^2+1/(n : ℝ)^2*(f x0-f xs) := by
    nlinarith only [hp, mul_nonneg (sq_nonneg (acdmB n σ k)) hr]
  exact ACDMProof.scalar_rates n hn σ hσ0 hσn k _ _ hD hg hpot

end NesterovRCD.Accelerated

open NesterovRCD.Accelerated

theorem solution {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)] (hn : 0 < n)
    (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (hsc : NesterovRCD.HighProb.StronglyConvexW f L 1 σ)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs) (k : ℕ) :
    (0 < σ →
      acdmPhi f L sharp σ x0 k - f xs
        ≤ σ * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))
          / ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) ^ 2 ∧
      σ * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))
          / ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) ^ 2
        ≤ ((n : ℝ) / (k + 1)) ^ 2 * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs))) ∧
    acdmPhi f L sharp σ x0 k - f xs
      ≤ ((n : ℝ) / (k + 1)) ^ 2 * (2 * NesterovRCD.Sublinear.wnorm L 1 (x0 - xs) ^ 2 + 1 / (n : ℝ) ^ 2 * (f x0 - f xs)) := by
  exact NesterovRCD.Accelerated.theorem6 hn f L hL σ hσ0 hσn hsc sharp hsharp x0 xs hxs k
