-- Prove2me | solution 1 for OAI.HochschildDomination.exists_quartic_hilbert_modulus
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:09:54.124999+00:00
-- url     : https://prove2.me/submissions/67261e7d-8171-4a83-8d53-1bc310bb767f

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildFourPoint

private theorem norm_exp_remainder {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (x : A) (hx : ‖x‖ ≤ 1 / 2) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ 2 * ‖x‖ ^ 2 := by
  let f : ℕ → A := fun n => ((n.factorial : ℂ)⁻¹) • x ^ n
  have hf : Summable f := NormedSpace.expSeries_summable' (𝕂 := ℂ) x
  have hfn : Summable (fun n => ‖f n‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x
  have htail : NormedSpace.exp x - 1 - x = ∑' n, f (n + 2) := by
    have h := hf.sum_add_tsum_nat_add 2
    have hs : (∑' n, f n) = NormedSpace.exp x :=
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x |>.tsum_eq
    rw [hs] at h
    have hsum : (∑ i ∈ Finset.range 2, f i) = 1 + x := by
      simp [f, Finset.sum_range_succ]
    rw [hsum] at h
    rw [← h]
    abel
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖x‖ ^ 2) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right _
  have hbound (n : ℕ) : ‖f (n+2)‖ ≤ (1 / 2 : ℝ)^n * ‖x‖^2 := by
    have hfac : (1 : ℝ) ≤ ((n+2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n+2)
    have hfac' : ‖(((n+2).factorial : ℂ)⁻¹)‖ ≤ 1 := by
      simpa using (inv_le_one_of_one_le₀ hfac)
    calc
      ‖f (n+2)‖ = ‖(((n+2).factorial : ℂ)⁻¹)‖ * ‖x^(n+2)‖ := norm_smul _ _
      _ ≤ 1 * ‖x^(n+2)‖ := mul_le_mul_of_nonneg_right hfac' (norm_nonneg _)
      _ ≤ ‖x‖^(n+2) := by simpa using norm_pow_le x (n+2)
      _ = ‖x‖^n * ‖x‖^2 := pow_add _ _ _
      _ ≤ (1/2)^n * ‖x‖^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx n) (sq_nonneg _)
  rw [htail]
  calc
    ‖∑' n, f (n+2)‖ ≤ ∑' n, ‖f (n+2)‖ :=
      norm_tsum_le_tsum_norm (hfn.comp_injective (fun _ _ h => Nat.add_right_cancel h))
    _ ≤ ∑' n : ℕ, (1/2 : ℝ)^n * ‖x‖^2 :=
      (hfn.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum hbound hgeom
    _ = 2 * ‖x‖^2 := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

section Dual
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

private def twist (a : A) (z : ℂ) (t : ℝ) : A :=
  ((t : ℂ) * star z) • a - ((t : ℂ) * z) • star a

omit [Nontrivial A] in
private lemma twist_skew (a : A) (z : ℂ) (t : ℝ) :
    twist a z t ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff]
  simp [twist, star_smul, mul_comm]

omit [Nontrivial A] in
private lemma norm_twist_le {a : A} (ha : ‖a‖ ≤ 1) {z : ℂ} (hz : ‖z‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : ‖twist a z t‖ ≤ 2 * t := by
  calc
    ‖twist a z t‖ ≤ ‖((t : ℂ) * star z) • a‖ + ‖((t : ℂ) * z) • star a‖ := norm_sub_le _ _
    _ = 2 * t * ‖a‖ := by simp [norm_smul, hz, Complex.norm_real, abs_of_nonneg ht]; ring
    _ ≤ 2 * t := by nlinarith

private lemma phase_test (f g : StrongDual ℂ A) {a : A} (ha : ‖a‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hfg : ‖f + z • g‖ ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    ((f + z • g) (1 + twist a z t)).re ≤ 1 + 8 * t ^ 2 := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  have hunit := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (twist_skew a z t)
  have hx := norm_twist_le ha hz ht
  have hr := norm_exp_remainder (twist a z t) (by linarith)
  have hr' : ‖NormedSpace.exp (twist a z t) - 1 - twist a z t‖ ≤ 8 * t ^ 2 := by
    nlinarith [norm_nonneg (twist a z t)]
  have h1 : ‖(f + z • g) (NormedSpace.exp (twist a z t))‖ ≤ 1 := by
    simpa [CStarRing.norm_of_mem_unitary hunit] using
      (f + z • g).le_of_opNorm_le hfg (NormedSpace.exp (twist a z t))
  have h2 : ‖(f + z • g) (NormedSpace.exp (twist a z t) - 1 - twist a z t)‖ ≤
      8 * t ^ 2 := by
    exact ((f + z • g).le_of_opNorm_le_of_le hfg hr').trans (by simp)
  have he : (f + z • g) (1 + twist a z t) =
      (f + z • g) (NormedSpace.exp (twist a z t)) -
      (f + z • g) (NormedSpace.exp (twist a z t) - 1 - twist a z t) := by
    simp only [map_add, map_sub]
    abel
  calc
    ((f + z • g) (1 + twist a z t)).re ≤ ‖(f + z • g) (1 + twist a z t)‖ :=
      Complex.re_le_norm _
    _ ≤ 1 + 8 * t^2 := by rw [he]; exact (norm_sub_le _ _).trans (add_le_add h1 h2)

theorem four_phase_real_bound (f g : StrongDual ℂ A)
    (h1 : ‖f + g‖ ≤ 1) (hm1 : ‖f - g‖ ≤ 1)
    (hI : ‖f + Complex.I • g‖ ≤ 1) (hmI : ‖f - Complex.I • g‖ ≤ 1)
    {a : A} (ha : ‖a‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    t * (g a).re ≤ 1 - (f 1).re + 8 * t^2 := by
  have h₁ := phase_test f g (z := 1) ha (by norm_num : ‖(1 : ℂ)‖ = 1) (by simpa using h1) ht ht'
  have h₂ := phase_test f g (z := -1) ha (by norm_num : ‖(-1 : ℂ)‖ = 1) (by
    have he : f + (-1 : ℂ) • g = f - g := by module
    rw [he]; exact hm1) ht ht'
  have h₃ := phase_test f g (z := Complex.I) ha Complex.norm_I hI ht ht'
  have h₄ := phase_test f g (z := -Complex.I) ha (by simp : ‖-Complex.I‖ = 1) (by
    have he : f + (-Complex.I) • g = f - Complex.I • g := by module
    rw [he]; exact hmI) ht ht'
  have h := add_le_add (add_le_add h₁ h₂) (add_le_add h₃ h₄)
  simp only [twist, map_add, map_sub, map_smul, add_apply,
    smul_apply, smul_eq_mul, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.star_def, map_neg, map_one,
    Complex.conj_re, Complex.conj_im] at h
  nlinarith

theorem four_phase_dual_bound (f g : StrongDual ℂ A)
    (h1 : ‖f + g‖ ≤ 1) (hm1 : ‖f - g‖ ≤ 1)
    (hI : ‖f + Complex.I • g‖ ≤ 1) (hmI : ‖f - Complex.I • g‖ ≤ 1) :
    ‖g‖^2 ≤ 128 * (1 - (f 1).re) := by
  have hg : ‖g‖ ≤ 1 := by
    have he : (2 : ℂ) • g = (f + g) - (f - g) := by module
    have hn := norm_sub_le (f + g) (f - g)
    rw [← he, norm_smul] at hn
    norm_num at hn
    linarith
  have hf : ‖f‖ ≤ 1 := by
    have he : (2 : ℂ) • f = (f + g) + (f - g) := by module
    have hn := norm_add_le (f + g) (f - g)
    rw [← he, norm_smul] at hn
    norm_num at hn
    linarith
  have hδ : 0 ≤ 1 - (f 1).re := by
    have hn : ‖f 1‖ ≤ 1 := by simpa using f.le_of_opNorm_le hf 1
    linarith [Complex.re_le_norm (f 1)]
  let t : ℝ := ‖g‖ / 32
  have ht : 0 ≤ t := by positivity
  have ht' : t ≤ 1/4 := by dsimp [t]; linarith
  have hb : ∀ a : A, ‖a‖ ≤ 1 → t * (g a).re ≤ 1 - (f 1).re + 8 * t^2 :=
    fun a ha => four_phase_real_bound f g h1 hm1 hI hmI ha ht ht'
  have hg' : ‖(t : ℂ) • g‖ ≤ 2 * (1 - (f 1).re + 8 * t^2) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro a ha
    have hpos := hb a ha.le
    have hneg := hb (-a) (by simpa using ha.le)
    have hipos := hb (Complex.I • a) (by simpa [norm_smul] using ha.le)
    have hineg := hb (-Complex.I • a) (by simpa [norm_smul] using ha.le)
    simp only [map_neg, map_smul, smul_eq_mul, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.neg_im] at hneg hipos hineg
    have hr : |(((t : ℂ) • g) a).re| ≤ 1 - (f 1).re + 8 * t^2 := by
      simp only [smul_apply, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      apply abs_le.mpr
      constructor <;> nlinarith
    have hi : |(((t : ℂ) • g) a).im| ≤ 1 - (f 1).re + 8 * t^2 := by
      simp only [smul_apply, smul_eq_mul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      apply abs_le.mpr
      constructor <;> nlinarith
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at hg'
  dsimp [t] at hg'
  nlinarith

end Dual

section UnitaryNorm
open scoped ComplexStarModule
variable {A : Type*} [CStarAlgebra A]

private def reRestrict (f : StrongDual ℂ A) : StrongDual ℝ (selfAdjoint A) :=
  LinearMap.mkContinuous
    { toFun := fun a => (f (a : A)).re
      map_add' := by intros; simp
      map_smul' := by intros; simp [← Complex.coe_smul] }
    ‖f‖ (by
      intro a
      exact (Complex.abs_re_le_norm _).trans (f.le_opNorm (a : A)))

private def imRestrict (f : StrongDual ℂ A) : StrongDual ℝ (selfAdjoint A) :=
  LinearMap.mkContinuous
    { toFun := fun a => (f (a : A)).im
      map_add' := by intros; simp
      map_smul' := by intros; simp [← Complex.coe_smul] }
    ‖f‖ (by
      intro a
      exact (Complex.abs_im_le_norm _).trans (f.le_opNorm (a : A)))

private def complexify (l : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (l (ℜ a):ℂ)+Complex.I*(l (ℑ a):ℂ)
  map_add' a b := by simp; ring
  map_smul' c a := by
    apply Complex.ext <;> simp [realPart_smul,imaginaryPart_smul]

private lemma norm_complexify_le (l : StrongDual ℝ (selfAdjoint A)) (a : A) :
    ‖complexify l.toLinearMap a‖ ≤ ‖l‖ * ‖a‖ := by
  obtain ⟨c, hc, he⟩ := Complex.exists_norm_eq_mul_self (complexify l.toLinearMap a)
  have h1 : ‖complexify l.toLinearMap a‖ =
      (complexify l.toLinearMap (c • a)).re := by
    rw [map_smul, smul_eq_mul, ← he]
    simp
  rw [h1]
  simp only [complexify, LinearMap.coe_mk, AddHom.coe_mk, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, sub_zero, mul_zero, add_zero]
  calc
    l (ℜ (c • a)) ≤ |l (ℜ (c • a))| := le_abs_self _
    _ ≤ ‖l‖ * ‖ℜ (c • a)‖ := l.le_opNorm _
    _ ≤ ‖l‖ * ‖a‖ := by
      have h := realPart.norm_le (c • a)
      simp only [norm_smul, hc, one_mul] at h
      exact mul_le_mul_of_nonneg_left h (norm_nonneg l)

private def complexifyCLM (l : StrongDual ℝ (selfAdjoint A)) : StrongDual ℂ A :=
  (complexify l.toLinearMap).mkContinuous ‖l‖ (norm_complexify_le l)

private lemma norm_complexifyCLM_le (l : StrongDual ℝ (selfAdjoint A)) :
    ‖complexifyCLM l‖ ≤ ‖l‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg l) (norm_complexify_le l)

private lemma re_im_decompose (f : StrongDual ℂ A) :
    f = complexifyCLM (reRestrict f) + Complex.I • complexifyCLM (imRestrict f) := by
  ext a
  have he := congrArg f (realPart_add_I_smul_imaginaryPart a)
  simp only [map_add, map_smul, smul_eq_mul] at he
  change f a = complexify (reRestrict f).toLinearMap a +
    Complex.I * complexify (imRestrict f).toLinearMap a
  rw [← he]
  apply Complex.ext <;>
    simp [complexify, reRestrict, imRestrict, Complex.mul_re, Complex.mul_im, add_comm]

private lemma norm_le_re_im (f : StrongDual ℂ A) :
    ‖f‖ ≤ ‖reRestrict f‖ + ‖imRestrict f‖ := by
  conv_lhs => rw [re_im_decompose f]
  exact (norm_add_le _ _).trans (add_le_add (norm_complexifyCLM_le _)
    (by simpa [norm_smul] using norm_complexifyCLM_le (imRestrict f)))

private lemma norm_reRestrict_le_unitary_bound [PartialOrder A] [StarOrderedRing A]
    (f : StrongDual ℂ A) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ u : unitary A, ‖f (u : A)‖ ≤ C) : ‖reRestrict f‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro a ha
  let u := selfAdjoint.unitarySelfAddISMul a ha.le
  have he : (a : A) = (2⁻¹ : ℝ) • ((u : A) + (star u : A)) := by
    have h := selfAdjoint.realPart_unitarySelfAddISMul a ha.le
    have h' := congrArg (fun b : selfAdjoint A => (b : A)) h
    simpa only [realPart_apply_coe, Unitary.coe_star] using h'.symm
  change |(f (a : A)).re| ≤ C
  apply (Complex.abs_re_le_norm _).trans
  rw [he, ← Complex.coe_smul, map_smul, map_add, norm_smul]
  have hu := norm_add_le_of_le (hf u) (hf (star u))
  simp only [Unitary.coe_star] at hu
  norm_num
  linarith

private lemma selfAdjoint_exp_test [Nontrivial A] (f : StrongDual ℂ A)
    {C : ℝ} (hf : ∀ u : unitary A, ‖f (u : A)‖ ≤ C)
    (a : selfAdjoint A) (ha : ‖a‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
    (f 1).re - t * (f (a : A)).im ≤ C + 2 * ‖f‖ * t^2 := by
  let x : A := Complex.I • (t • (a : A))
  have hx : ‖x‖ ≤ t := by
    dsimp [x]
    simp only [norm_smul, Complex.norm_I, one_mul, Real.norm_eq_abs, abs_of_nonneg ht]
    change t * ‖a‖ ≤ t
    nlinarith
  have hr := norm_exp_remainder x (hx.trans ht')
  have hr' : ‖NormedSpace.exp x - 1 - x‖ ≤ 2 * t^2 := by
    nlinarith [norm_nonneg x]
  have he : NormedSpace.exp x = (selfAdjoint.expUnitary (t • a) : A) := rfl
  have h1 : ‖f (NormedSpace.exp x)‖ ≤ C := by rw [he]; exact hf _
  have h2 : ‖f (NormedSpace.exp x - 1 - x)‖ ≤ 2 * ‖f‖ * t^2 := by
    exact (f.le_opNorm _).trans (by nlinarith [norm_nonneg f])
  have h3 : ‖f (1+x)‖ ≤ C + 2 * ‖f‖ * t^2 := by
    have hlin : f (1+x) = f (NormedSpace.exp x) - f (NormedSpace.exp x - 1 - x) := by
      simp only [map_add, map_sub]; abel
    rw [hlin]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have h4 := (Complex.re_le_norm (f (1+x))).trans h3
  simpa [x, map_add, ← Complex.coe_smul, map_smul, smul_eq_mul,
    Complex.mul_re, Complex.mul_im] using h4

private lemma imRestrict_small [Nontrivial A] (f : StrongDual ℂ A)
    {C : ℝ} (hf : ∀ u : unitary A, ‖f (u : A)‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
    t * ‖imRestrict f‖ ≤ C - (f 1).re + 2 * ‖f‖ * t^2 := by
  have hC : (f 1).re ≤ C :=
    (Complex.re_le_norm _).trans (by simpa using hf 1)
  have hnorm : ‖t • imRestrict f‖ ≤ C - (f 1).re + 2 * ‖f‖ * t^2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by nlinarith [norm_nonneg f, sq_nonneg t])
    intro a ha
    have hpos := selfAdjoint_exp_test f hf a ha.le ht ht'
    have hneg := selfAdjoint_exp_test f hf (-a) (by simpa using ha.le) ht ht'
    change |t * (f (a : A)).im| ≤ _
    simp only [AddSubgroup.coe_neg, map_neg, Complex.neg_im] at hneg
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  let : NormSMulClass ℝ (StrongDual ℝ (selfAdjoint A)) :=
    @NormedSpace.toNormSMulClass ℝ (StrongDual ℝ (selfAdjoint A)) _ _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hnorm
  exact hnorm

private lemma near_unit_norm_bound [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
    (f : StrongDual ℂ A) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ u : unitary A, ‖f (u : A)‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
    t * ‖f‖ ≤ t * C + C - (f 1).re + 2 * ‖f‖ * t^2 := by
  have h := norm_le_re_im f
  have hr := norm_reRestrict_le_unitary_bound f hC hf
  have hi := imRestrict_small f hf ht ht'
  nlinarith

private def unitSup (f : StrongDual ℂ A) : ℝ :=
  sSup (Set.range fun u : unitary A => ‖f (u : A)‖)

private lemma unitSup_bdd [Nontrivial A] (f : StrongDual ℂ A) :
    BddAbove (Set.range fun u : unitary A => ‖f (u : A)‖) := by
  refine ⟨‖f‖, ?_⟩
  rintro _ ⟨u, rfl⟩
  simpa using f.le_opNorm (u : A)

private lemma le_unitSup [Nontrivial A] (f : StrongDual ℂ A) (u : unitary A) :
    ‖f (u : A)‖ ≤ unitSup f :=
  le_csSup (unitSup_bdd f) ⟨u, rfl⟩

private lemma unitSup_nonneg [Nontrivial A] (f : StrongDual ℂ A) : 0 ≤ unitSup f :=
  (norm_nonneg _).trans (le_unitSup f 1)

private def translate (f : StrongDual ℂ A) (u : unitary A) : StrongDual ℂ A :=
  f.comp (Unitary.mulLeft ℂ A u).toContinuousLinearEquiv.toContinuousLinearMap

private lemma norm_translate (f : StrongDual ℂ A) (u : unitary A) :
    ‖translate f u‖ = ‖f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    exact (f.le_opNorm _).trans_eq (by simp [Unitary.mulLeft_apply])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    have h := (translate f u).le_opNorm ((Unitary.mulLeft ℂ A u).symm a)
    change ‖f ((Unitary.mulLeft ℂ A u) ((Unitary.mulLeft ℂ A u).symm a))‖ ≤
      ‖translate f u‖ * ‖(Unitary.mulLeft ℂ A u).symm a‖ at h
    simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using h

private lemma translate_apply (f : StrongDual ℂ A) (u : unitary A) (a : A) :
    translate f u a = f ((u : A) * a) := rfl

theorem norm_le_of_unitary_bound [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
    (f : StrongDual ℂ A) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ u : unitary A, ‖f (u : A)‖ ≤ C) : ‖f‖ ≤ C := by
  have hsup : unitSup f ≤ C := csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨u, rfl⟩; exact hf u)
  suffices hnorm : ‖f‖ ≤ unitSup f by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro element
    exact (f.le_opNorm element).trans
      (mul_le_mul_of_nonneg_right (hnorm.trans hsup) (norm_nonneg element))
  have hnear (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
      t * ‖f‖ ≤ t * unitSup f + 2 * ‖f‖ * t^2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨r, ⟨u, rfl⟩, hu⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty (fun u : unitary A => ‖f (u : A)‖))
      (show unitSup f - ε < unitSup f by linarith)
    obtain ⟨c, hc, he⟩ := Complex.exists_norm_eq_mul_self (f (u : A))
    let g := c • translate f u
    have hgn : ‖g‖ = ‖f‖ := by simp [g, norm_smul, hc, norm_translate]
    have hg1 : (g 1).re = ‖f (u : A)‖ := by
      simp only [g, smul_apply, translate_apply, mul_one, smul_eq_mul,
        ← he, Complex.ofReal_re]
    have hgunit (v : unitary A) : ‖g (v : A)‖ ≤ unitSup f := by
      change ‖c • f ((u : A) * (v : A))‖ ≤ unitSup f
      rw [norm_smul, hc, one_mul]
      exact le_unitSup f (u*v)
    have h := near_unit_norm_bound g (unitSup_nonneg f) hgunit ht ht'
    rw [hgn, hg1] at h
    linarith
  by_contra hn
  have hd : 0 < ‖f‖ - unitSup f := sub_pos.mpr (lt_of_not_ge hn)
  have hnpos : 0 < ‖f‖ := lt_of_le_of_lt (unitSup_nonneg f) (lt_of_not_ge hn)
  let t : ℝ := (‖f‖ - unitSup f) / (4 * ‖f‖)
  have ht : 0 < t := div_pos hd (by positivity)
  have ht' : t ≤ 1/2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 4 * ‖f‖)).mpr
    nlinarith [unitSup_nonneg f]
  have he : 4 * ‖f‖ * t = ‖f‖ - unitSup f := by
    dsimp [t]; field_simp
  have h := hnear t ht.le ht'
  nlinarith

end UnitaryNorm

section Disk
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

private def absoluteSA (a : selfAdjoint A) : A := cfc (fun r : ℝ => |r|) (a : A)

omit [Nontrivial A] in
private lemma absoluteSA_nonneg (a : selfAdjoint A) : 0 ≤ absoluteSA a := by
  exact cfc_nonneg (fun r _ => abs_nonneg r)

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma absoluteSA_sq (a : selfAdjoint A) : absoluteSA a * absoluteSA a = (a : A) * a := by
  dsimp [absoluteSA]
  calc
    _ = cfc (fun r : ℝ => r * r) (a : A) := by
      rw [← cfc_mul ..]
      apply cfc_congr
      intro r _
      nlinarith [sq_abs r]
    _ = _ := by rw [cfc_mul .., cfc_id' ℝ (a : A)]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma disk_contracts (a : selfAdjoint A) (ha : ‖a‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) : ‖1 - absoluteSA a + z • (a : A)‖ ≤ 1 := by
  have he : 1 - absoluteSA a + z • (a : A) =
      cfc (fun r : ℂ => 1 - ((|r.re| : ℝ) : ℂ) + z * r) (a : A) := by
    dsimp [absoluteSA]
    rw [cfc_real_eq_complex]
    rw [cfc_add .., cfc_sub .., cfc_const_one ℂ (a : A), cfc_const_mul_id z (a : A)]
  rw [he]
  apply norm_cfc_le (by norm_num)
  intro r hr
  have her := a.property.mem_spectrum_eq_re hr
  have habs : |r.re| ≤ 1 := by
    have hh := (spectrum.norm_le_norm_of_mem hr).trans ha
    rw [her] at hh
    simpa using hh
  calc
    ‖1 - ((|r.re| : ℝ) : ℂ) + z * r‖ ≤ ‖1 - ((|r.re| : ℝ) : ℂ)‖ + ‖z * r‖ := norm_add_le _ _
    _ = (1 - |r.re|) + |r.re| := by
      rw [norm_mul, hz, one_mul, her]
      have hreal : (1 : ℂ) - ((|r.re| : ℝ) : ℂ) = ((1 - |r.re| : ℝ) : ℂ) := by push_cast; rfl
      simp only [Complex.ofReal_re]
      rw [hreal, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith)]
    _ = 1 := by ring

end Disk

open scoped ComplexStarModule
namespace HochschildPositiveDecomposition
universe u
variable {M : Type u} [CStarAlgebra M]

lemma norm_pair_shift [Nontrivial M] (a : selfAdjoint M) (t : ℝ) :
    ‖a‖ + |t| ≤ ‖(a + t • (1 : selfAdjoint M), -a + t • (1 : selfAdjoint M))‖ := by
  let C := ‖(a + t • (1 : selfAdjoint M), -a + t • (1 : selfAdjoint M))‖
  have h₁ : ‖(a : M) + algebraMap ℝ M t‖ ≤ C := by
    rw [Algebra.algebraMap_eq_smul_one]
    change ‖(a : M) + t • (1:M)‖ ≤ max ‖(a : M)+t • (1:M)‖ ‖-(a : M)+t • (1:M)‖
    exact le_max_left _ _
  have h₂ : ‖-(a : M) + algebraMap ℝ M t‖ ≤ C := by
    rw [Algebra.algebraMap_eq_smul_one]
    change ‖-(a : M) + t • (1:M)‖ ≤ max ‖(a : M)+t • (1:M)‖ ‖-(a : M)+t • (1:M)‖
    exact le_max_right _ _
  have hs (r : ℝ) (hr : r ∈ spectrum ℝ (a : M)) : |r+t| ≤ C ∧ |-r+t| ≤ C := by
    constructor
    · have h := spectrum.norm_le_norm_of_mem (spectrum.add_mem_add_iff.mpr hr : r+t ∈ spectrum ℝ (algebraMap ℝ M t+(a : M)))
      exact h.trans (by simpa [add_comm] using h₁)
    · have hn : -r ∈ spectrum ℝ (-(a : M)) := by rw [← spectrum.neg_eq]; exact Set.neg_mem_neg.mpr hr
      have h := spectrum.norm_le_norm_of_mem (spectrum.add_mem_add_iff.mpr hn : -r+t ∈ spectrum ℝ (algebraMap ℝ M t+ -(a : M)))
      exact h.trans (by simpa [sub_eq_add_neg,add_comm] using h₂)
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a.property with ha|ha
  · obtain ⟨h₁,h₂⟩ := hs ‖a‖ ha
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]; linarith [le_abs_self (‖a‖+t)]
    · rw [abs_of_nonpos ht]; linarith [neg_le_abs (-‖a‖+t)]
  · obtain ⟨h₁,h₂⟩ := hs (-‖a‖) ha
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]; linarith [le_abs_self (-(-‖a‖)+t)]
    · rw [abs_of_nonpos ht]; linarith [neg_le_abs (-‖a‖+t)]

def shiftEmbedding : selfAdjoint M × ℝ →ₗ[ℝ] selfAdjoint M × selfAdjoint M where
  toFun p := (p.1+p.2 • 1,-p.1+p.2 • 1)
  map_add' p q := by ext <;> simp <;> module
  map_smul' r p := by ext <;> simp <;> module

lemma shiftEmbedding_injective [Nontrivial M] : Function.Injective (shiftEmbedding (M := M)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  have h := norm_pair_shift p.1 p.2
  have he : shiftEmbedding p=0 := hp
  change ‖p.1‖+|p.2|≤‖shiftEmbedding p‖ at h
  rw [he,norm_zero] at h
  have hp₁ : p.1=0 := norm_eq_zero.mp (by linarith [norm_nonneg p.1,abs_nonneg p.2])
  have hp₂ : p.2=0 := abs_eq_zero.mp (by linarith [norm_nonneg p.1,abs_nonneg p.2])
  exact Prod.ext hp₁ hp₂

lemma exists_pair_extension [Nontrivial M] (l : StrongDual ℝ (selfAdjoint M)) :
    ∃ g : StrongDual ℝ (selfAdjoint M × selfAdjoint M),
      ‖g‖ ≤ ‖l‖ ∧ g (1,1)=‖l‖ ∧ ∀ a, g (a,-a)=l a := by
  let j := LinearEquiv.ofInjective (shiftEmbedding (M := M)) shiftEmbedding_injective
  let L : selfAdjoint M × ℝ →ₗ[ℝ] ℝ := l.toLinearMap.coprod (‖l‖ • LinearMap.id)
  let L' := L.comp j.symm.toLinearMap
  have hbound (p : (shiftEmbedding (M := M)).range) : ‖L' p‖ ≤ ‖l‖*‖p‖ := by
    obtain ⟨q,rfl⟩ := j.surjective p
    change ‖L (j.symm (j q))‖ ≤ ‖l‖*‖shiftEmbedding q‖
    rw [j.symm_apply_apply]
    change ‖l q.1+‖l‖*q.2‖ ≤ ‖l‖*‖shiftEmbedding q‖
    calc
      _ ≤ ‖l q.1‖+‖‖l‖*q.2‖ := norm_add_le _ _
      _ ≤ ‖l‖*‖q.1‖+‖l‖*|q.2| := by simpa [abs_of_nonneg (norm_nonneg l)] using add_le_add (l.le_opNorm q.1) (le_refl ‖‖l‖*q.2‖)
      _ = ‖l‖*(‖q.1‖+|q.2|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pair_shift q.1 q.2) (norm_nonneg l)
  let F := L'.mkContinuous ‖l‖ hbound
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq (shiftEmbedding (M := M)).range F
  refine ⟨g,?_,?_,?_⟩
  · rw [hgn]; exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg l) hbound
  · have h := hg (j (0,1))
    change g (shiftEmbedding (0,1))=L (j.symm (j (0,1))) at h
    rw [j.symm_apply_apply] at h
    simpa [L,shiftEmbedding] using h
  · intro a
    have h := hg (j (a,0))
    change g (shiftEmbedding (a,0))=L (j.symm (j (a,0))) at h
    rw [j.symm_apply_apply] at h
    simpa [L,shiftEmbedding] using h

section Ordered
variable [PartialOrder M] [StarOrderedRing M]

lemma norm_orderUnit_sub (a : selfAdjoint M) (ha : 0≤(a:M)) {r : ℝ}
    (hr : 0≤r) (har : ‖a‖≤r) : ‖r • (1:selfAdjoint M)-a‖≤r := by
  change ‖r • (1:M)-(a:M)‖≤r
  have hle : (a:M)≤algebraMap ℝ M r := by
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (a:M) hr ha).mp har
  rw [Algebra.algebraMap_eq_smul_one] at hle
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hr (sub_nonneg.mpr hle)).mpr (by
    rw [Algebra.algebraMap_eq_smul_one]
    exact sub_le_self _ ha)

lemma pair_nonneg (g : StrongDual ℝ (selfAdjoint M × selfAdjoint M)) {C : ℝ}
    (hC : 0≤C) (hgn : ‖g‖≤C) (hg1 : g (1,1)=C)
    (a b : selfAdjoint M) (ha : 0≤(a:M)) (hb : 0≤(b:M)) : 0≤g (a,b) := by
  let r := ‖(a,b)‖
  have hr : 0≤r := norm_nonneg _
  have hn : ‖r • (1,1)-(a,b)‖ ≤ r := by
    change max ‖r • (1:selfAdjoint M)-a‖ ‖r • (1:selfAdjoint M)-b‖≤r
    exact max_le (norm_orderUnit_sub a ha hr (le_max_left _ _))
      (norm_orderUnit_sub b hb hr (le_max_right _ _))
  have h := (le_abs_self (g (r • (1,1)-(a,b)))).trans
    ((g.le_opNorm _).trans (mul_le_mul hgn hn (norm_nonneg _) hC))
  rw [map_sub,map_smul,hg1] at h
  change r*C-g (a,b)≤C*r at h
  nlinarith

lemma exists_real_positive_difference [Nontrivial M] (l : StrongDual ℝ (selfAdjoint M)) :
    ∃ p q : StrongDual ℝ (selfAdjoint M),
      (∀ a : selfAdjoint M, 0≤(a:M) → 0≤p a) ∧ (∀ a : selfAdjoint M, 0≤(a:M) → 0≤q a) ∧
      (∀ a, l a=p a-q a) ∧ p 1≤‖l‖ ∧ q 1≤‖l‖ := by
  obtain ⟨g,hgn,hg1,hgl⟩ := exists_pair_extension l
  let p := g.comp (ContinuousLinearMap.inl ℝ (selfAdjoint M) (selfAdjoint M))
  let q := g.comp (ContinuousLinearMap.inr ℝ (selfAdjoint M) (selfAdjoint M))
  refine ⟨p,q,?_,?_,?_,?_,?_⟩
  · intro a ha; exact pair_nonneg g (norm_nonneg l) hgn hg1 a 0 ha (by simp)
  · intro a ha; exact pair_nonneg g (norm_nonneg l) hgn hg1 0 a (by simp) ha
  · intro a
    rw [← hgl]
    change g (a,-a)=g (a,0)-g (0,a)
    rw [← map_sub]; congr 1; simp
  · have h := (le_abs_self (g (1,0))).trans (g.le_opNorm (1,0))
    have hn : ‖((1:selfAdjoint M), (0:selfAdjoint M))‖≤1 := by
      change max ‖(1:M)‖ ‖(0:M)‖≤1
      simp
    exact h.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg g)).trans (by simpa using hgn))
  · have h := (le_abs_self (g (0,1))).trans (g.le_opNorm (0,1))
    have hn : ‖((0:selfAdjoint M), (1:selfAdjoint M))‖≤1 := by
      change max ‖(0:M)‖ ‖(1:M)‖≤1
      simp
    exact h.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg g)).trans (by simpa using hgn))

end Ordered

section Ordered
variable [PartialOrder M] [StarOrderedRing M]
open scoped ComplexOrder

end Ordered

end HochschildPositiveDecomposition

section PositiveSquares
open scoped ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private def saSquare (a : selfAdjoint A) : selfAdjoint A :=
  ⟨(a : A) * a, by
    change IsSelfAdjoint ((a : A) * a)
    simpa only [a.property.star_eq] using IsSelfAdjoint.star_mul_self (a : A)⟩

private lemma real_positive_square_bound (p : StrongDual ℝ (selfAdjoint A))
    (hp : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ p a) (hp1 : p 1 ≤ 1)
    (a : selfAdjoint A) : (p a)^2 ≤ p (saSquare a) := by
  let t := p a
  let b : selfAdjoint A := a - t • 1
  have hb : 0 ≤ p (saSquare b) := by
    apply hp
    change 0 ≤ (b : A) * b
    simpa only [b.property.star_eq] using star_mul_self_nonneg (b : A)
  have he : saSquare b = saSquare a - (2*t) • a + (t^2) • 1 := by
    apply Subtype.ext
    change ((a : A) - t • 1) * ((a : A) - t • 1) =
      (a : A) * a - (2*t) • (a : A) + (t^2) • 1
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    module
  rw [he, map_add, map_sub, map_smul, map_smul] at hb
  change 0 ≤ p (saSquare a) - (2*t) * p a + t^2 * p 1 at hb
  dsimp [t] at hb
  nlinarith [sq_nonneg (p a)]

private lemma real_positive_norm_le (p : StrongDual ℝ (selfAdjoint A))
    (hp : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ p a) (hp1 : p 1 ≤ 1) : ‖p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
  intro a ha
  have hu := a.property.le_algebraMap_norm_self
  have hl := a.property.neg_algebraMap_norm_le_self
  change ‖(a : A)‖ = 1 at ha
  rw [ha, map_one] at hu hl
  have h1 := hp (1-a) (by simpa using sub_nonneg.mpr hu)
  have h2 := hp (1+a) (by simpa [add_comm] using neg_le_iff_add_nonneg.mp hl)
  simp only [map_sub, map_add] at h1 h2
  change |p a| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [PartialOrder A] [StarOrderedRing A] in
private lemma reRestrict_norm_le (f : StrongDual ℂ A) : ‖reRestrict f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro a
  exact (Complex.abs_re_le_norm _).trans (f.le_opNorm (a : A))

end PositiveSquares

section BilinearModulus
open scoped ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma bilinear_sa_disk_bound (B : A →L[ℂ] StrongDual ℂ A) (hB : ‖B‖ ≤ 1)
    (a : selfAdjoint A) (ha : ‖a‖ ≤ 1) :
    ‖B.flip (a : A)‖^2 ≤ 128 * (1 - (B 1 1).re + (B 1 (absoluteSA a)).re) := by
  let f := B.flip (1 - absoluteSA a)
  let g := B.flip (a : A)
  have hphase (z : ℂ) (hz : ‖z‖ = 1) : ‖f + z • g‖ ≤ 1 := by
    have he : f + z • g = B.flip (1 - absoluteSA a + z • (a : A)) := by
      simp only [map_add, map_smul, f, g]
    rw [he]
    calc
      _ ≤ ‖B.flip‖ * ‖1 - absoluteSA a + z • (a : A)‖ := B.flip.le_opNorm _
      _ ≤ 1 * 1 := mul_le_mul (by simpa using hB) (disk_contracts a ha z hz)
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have h1 : ‖f+g‖ ≤ 1 := by simpa using hphase 1 (by simp)
  have hm1 : ‖f-g‖ ≤ 1 := by simpa [sub_eq_add_neg] using hphase (-1) (by simp)
  have hI : ‖f+Complex.I • g‖ ≤ 1 := hphase Complex.I (by simp)
  have hmI : ‖f-Complex.I • g‖ ≤ 1 := by
    have he : (-Complex.I) • g = -(Complex.I • g) := by module
    simpa [he, sub_eq_add_neg] using hphase (-Complex.I) (by simp)
  have h := four_phase_dual_bound f g h1 hm1 hI hmI
  simp only [f, g, map_sub, sub_apply, ContinuousLinearMap.flip_apply, Complex.sub_re] at h
  linarith

private lemma exists_sa_modulus (B : A →L[ℂ] StrongDual ℂ A) (hB : ‖B‖ ≤ 1) :
    ∃ p : StrongDual ℝ (selfAdjoint A),
      (∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ p a) ∧ ‖p‖ ≤ 1 ∧ p 1 ≤ 1 ∧
      ∀ a : selfAdjoint A, ‖a‖ ≤ 1 →
        ‖B.flip (a : A)‖^2 ≤ 128 * (1 - (B 1 1).re + Real.sqrt (p (saSquare a))) := by
  obtain ⟨p,q,hp,hq,he,hp1,hq1⟩ :=
    HochschildPositiveDecomposition.exists_real_positive_difference (reRestrict (B 1))
  have hn : ‖reRestrict (B 1)‖ ≤ 1 :=
    (reRestrict_norm_le _).trans (by simpa using B.le_of_opNorm_le hB 1)
  have hp1' := hp1.trans hn
  refine ⟨p, hp, real_positive_norm_le p hp hp1', hp1', ?_⟩
  intro a ha
  let b : selfAdjoint A := ⟨absoluteSA a, IsSelfAdjoint.of_nonneg (absoluteSA_nonneg a)⟩
  have hq' : 0 ≤ q b := hq b (absoluteSA_nonneg a)
  have hp' : (B 1 (absoluteSA a)).re ≤ p b := by
    have h := he b
    change (B 1 (absoluteSA a)).re = p b - q b at h
    linarith
  have hb : p b ≤ Real.sqrt (p (saSquare a)) := by
    have hsq := real_positive_square_bound p hp hp1' b
    have heq : saSquare b = saSquare a := Subtype.ext (absoluteSA_sq a)
    rw [heq] at hsq
    have hnonneg : 0 ≤ p (saSquare a) := hp (saSquare a) (by
      change 0 ≤ (a : A) * a
      simpa only [a.property.star_eq] using star_mul_self_nonneg (a : A))
    exact (Real.le_sqrt (hp b (absoluteSA_nonneg a)) hnonneg).mpr hsq
  exact (bilinear_sa_disk_bound B hB a ha).trans (by linarith)

private def energySA (b : A) : selfAdjoint A :=
  ⟨star b * b + b * star b, (IsSelfAdjoint.star_mul_self b).add
    (IsSelfAdjoint.mul_star_self b)⟩

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma energySA_eq (b : A) :
    energySA b = (2 : ℝ) • (saSquare (ℜ b) + saSquare (ℑ b)) := by
  apply Subtype.ext
  change star b * b + b * star b = (2 : ℝ) •
    ((ℜ b : A) * (ℜ b : A) + (ℑ b : A) * (ℑ b : A))
  simpa only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat] using
    star_mul_self_add_self_mul_star b

omit [Nontrivial A] in
private lemma square_nonneg (a : selfAdjoint A) : 0 ≤ ((saSquare a : selfAdjoint A) : A) := by
  change 0 ≤ (a : A) * a
  simpa only [a.property.star_eq] using star_mul_self_nonneg (a : A)

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma complexifyCLM_sa (p : StrongDual ℝ (selfAdjoint A)) (a : selfAdjoint A) :
    complexifyCLM p (a : A) = (p a : ℂ) := by
  change complexify p.toLinearMap (a : A) = _
  simp only [complexify, LinearMap.coe_mk, AddHom.coe_mk,
    selfAdjoint.realPart_coe,
    (show IsSelfAdjoint (a : A) from a.property).imaginaryPart, map_zero, Complex.ofReal_zero,
    mul_zero, add_zero]
  rfl

private lemma exists_quartic_error (B : A →L[ℂ] StrongDual ℂ A) (hB : ‖B‖ ≤ 1) :
    ∃ φ : StrongDual ℂ A,
      (∀ a : A, 0 ≤ a → 0 ≤ (φ a).re ∧ (φ a).im = 0) ∧ ‖φ‖ ≤ 1 ∧
      ∀ b : A, ‖b‖ ≤ 1 →
        ‖B.flip b‖^4 ≤ 524288 * ((1 - (B 1 1).re)^2 + (φ (star b * b + b * star b)).re) := by
  obtain ⟨p,hp,hpn,hp1,hmod⟩ := exists_sa_modulus B hB
  refine ⟨complexifyCLM p, ?_, (norm_complexifyCLM_le p).trans hpn, ?_⟩
  · intro a ha
    have hs : IsSelfAdjoint a := .of_nonneg ha
    rw [complexifyCLM_sa p ⟨a,hs⟩]
    exact ⟨hp ⟨a,hs⟩ ha, rfl⟩
  intro b hb
  let x := ℜ b
  let y := ℑ b
  have hx : ‖x‖ ≤ 1 := (realPart.norm_le b).trans hb
  have hy : ‖y‖ ≤ 1 := (imaginaryPart.norm_le b).trans hb
  have hpx : 0 ≤ p (saSquare x) := hp _ (square_nonneg x)
  have hpy : 0 ≤ p (saSquare y) := hp _ (square_nonneg y)
  have he : p (energySA b) = 2 * (p (saSquare x) + p (saSquare y)) := by
    rw [energySA_eq, map_smul, map_add]
    rfl
  have hpe : 0 ≤ p (energySA b) := by linarith
  have hxe : Real.sqrt (p (saSquare x)) ≤ Real.sqrt (p (energySA b)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hye : Real.sqrt (p (saSquare y)) ≤ Real.sqrt (p (energySA b)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsx := hmod x hx
  have hsy := hmod y hy
  have hnb : ‖B.flip b‖ ≤ ‖B.flip (x : A)‖ + ‖B.flip (y : A)‖ := by
    have hd : b = (x : A) + Complex.I • (y : A) :=
      (realPart_add_I_smul_imaginaryPart b).symm
    rw [hd, map_add, map_smul]
    simpa only [norm_smul, Complex.norm_I, one_mul] using norm_add_le
      (B.flip (x : A)) (Complex.I • B.flip (y : A))
  have hsq : ‖B.flip b‖^2 ≤ 512 * (1 - (B 1 1).re) +
      512 * Real.sqrt (p (energySA b)) := by
    have hs : ‖B.flip b‖^2 ≤ 2 * ‖B.flip (x : A)‖^2 + 2 * ‖B.flip (y : A)‖^2 := by
      nlinarith [norm_nonneg (B.flip b), norm_nonneg (B.flip (x : A)),
        norm_nonneg (B.flip (y : A)), sq_nonneg (‖B.flip (x : A)‖ - ‖B.flip (y : A)‖)]
    linarith
  have hδ : 0 ≤ 1 - (B 1 1).re := by
    have heval := B.le_of_opNorm_le hB 1
    have hnorm : ‖B 1 1‖ ≤ 1 := by
      apply (B 1).le_of_opNorm_le (by simpa using heval) 1 |>.trans
      simp
    linarith [Complex.re_le_norm (B 1 1)]
  have hfour : ‖B.flip b‖^4 ≤ 524288 * ((1 - (B 1 1).re)^2 + p (energySA b)) := by
    have hrn := Real.sqrt_nonneg (p (energySA b))
    have hrs := Real.sq_sqrt hpe
    have ht := sq_nonneg ((1 - (B 1 1).re) - Real.sqrt (p (energySA b)))
    have hsq' := mul_self_le_mul_self (sq_nonneg ‖B.flip b‖) hsq
    nlinarith
  have hf := complexifyCLM_sa p (energySA b)
  have hre := congrArg Complex.re hf
  change (complexifyCLM p (star b * b + b * star b)).re = p (energySA b) at hre
  rw [hre]
  exact hfour

private lemma bilinear_norm_le_of_unitary (B : A →L[ℂ] StrongDual ℂ A) {C : ℝ}
    (hC : 0 ≤ C) (hB : ∀ u v : unitary A, ‖B (u : A) (v : A)‖ ≤ C) : ‖B‖ ≤ C := by
  have hf (v : unitary A) : ‖B.flip (v : A)‖ ≤ C :=
    norm_le_of_unitary_bound (B.flip (v : A)) hC (fun u => hB u v)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro a ha
  apply norm_le_of_unitary_bound (B a) hC
  intro v
  simpa only [ha, mul_one, ContinuousLinearMap.flip_apply] using
    (B.flip (v : A)).le_of_opNorm_le (hf v) a

private lemma exists_unitary_pair (B : A →L[ℂ] StrongDual ℂ A) {r : ℝ}
    (hr : 0 ≤ r) (hB : r < ‖B‖) :
    ∃ u v : unitary A, r < ‖B (u : A) (v : A)‖ := by
  by_contra h
  push Not at h
  exact hB.not_ge (bilinear_norm_le_of_unitary B hr h)

private def translateB (B : A →L[ℂ] StrongDual ℂ A) (u v : unitary A) :
    A →L[ℂ] StrongDual ℂ A :=
  B.bilinearComp (Unitary.mulLeft ℂ A u).toContinuousLinearEquiv.toContinuousLinearMap
    (Unitary.mulLeft ℂ A v).toContinuousLinearEquiv.toContinuousLinearMap

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma translateB_apply (B : A →L[ℂ] StrongDual ℂ A) (u v : unitary A) (a b : A) :
    translateB B u v a b = B ((u : A) * a) ((v : A) * b) := rfl

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma norm_translateB_le (B : A →L[ℂ] StrongDual ℂ A) (u v : unitary A) :
    ‖translateB B u v‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (translateB B u v) (norm_nonneg B) ?_
  intro a
  refine ContinuousLinearMap.opNorm_le_bound ((translateB B u v) a)
    (mul_nonneg (norm_nonneg B) (norm_nonneg a)) ?_
  intro b
  change ‖B ((Unitary.mulLeft ℂ A u) a) ((Unitary.mulLeft ℂ A v) b)‖ ≤ ‖B‖ * ‖a‖ * ‖b‖
  simpa only [LinearIsometryEquiv.norm_map] using
    B.le_opNorm₂ ((Unitary.mulLeft ℂ A u) a) ((Unitary.mulLeft ℂ A v) b)

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma translateB_flip_norm (B : A →L[ℂ] StrongDual ℂ A) (u v : unitary A) (b : A) :
    ‖(translateB B u v).flip b‖ = ‖B.flip ((v : A) * b)‖ := by
  change ‖translate (B.flip ((v : A) * b)) u‖ = _
  exact norm_translate _ _

private def conjugateCLM (v : unitary A) : A →L[ℂ] A :=
  (Unitary.mulRight ℂ v).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Unitary.mulLeft ℂ A (star v)).toContinuousLinearEquiv.toContinuousLinearMap

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma conjugateCLM_apply (v : unitary A) (a : A) :
    conjugateCLM v a = star (v : A) * a * (v : A) := rfl

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
private lemma conjugateCLM_norm (v : unitary A) (a : A) :
    ‖conjugateCLM v a‖ = ‖a‖ := by
  change ‖(Unitary.mulRight ℂ v) ((Unitary.mulLeft ℂ A (star v)) a)‖ = _
  simp only [LinearIsometryEquiv.norm_map]

omit [Nontrivial A] in
private lemma conjugateCLM_nonneg (v : unitary A) (a : A) (ha : 0 ≤ a) :
    0 ≤ conjugateCLM v a := by
  rw [conjugateCLM_apply]
  exact star_left_conjugate_nonneg ha (v : A)

private def FunctionalPositive (φ : StrongDual ℂ A) : Prop :=
  ∀ a : A, 0 ≤ a → 0 ≤ (φ a).re ∧ (φ a).im = 0

private lemma exists_quartic_near (B : A →L[ℂ] StrongDual ℂ A) (hB : ‖B‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ φ ψ : StrongDual ℂ A,
      FunctionalPositive φ ∧ FunctionalPositive ψ ∧ ‖φ‖ ≤ 1 ∧ ‖ψ‖ ≤ 1 ∧
      ∀ b : A, ‖b‖ ≤ 1 →
        ‖B.flip b‖^4 ≤ 524288 * (ε^2 + (φ (star b * b)).re + (ψ (b * star b)).re) := by
  obtain ⟨u,v,huv⟩ := exists_unitary_pair B (sub_nonneg.mpr hε1)
    (show 1-ε < ‖B‖ by rw [hB]; linarith)
  obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (B (u : A) (v : A))
  let D := c • translateB B u v
  have hDn : ‖D‖ ≤ 1 := by
    change ‖c • translateB B u v‖ ≤ 1
    let := @NormedSpace.toNormSMulClass ℂ (A →L[ℂ] StrongDual ℂ A) _ _ _
    rw [norm_smul, hc, one_mul]
    exact (norm_translateB_le B u v).trans hB.le
  have hD1 : (D 1 1).re = ‖B (u : A) (v : A)‖ := by
    simp only [D, smul_apply, translateB_apply, mul_one, smul_eq_mul, ← he,
      Complex.ofReal_re]
  obtain ⟨φ,hφ,hφn,hmod⟩ := exists_quartic_error D hDn
  let ψ := φ.comp (conjugateCLM v)
  have hψ : FunctionalPositive ψ := by
    intro a ha
    exact hφ _ (conjugateCLM_nonneg v a ha)
  have hψn : ‖ψ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro a
    exact (φ.le_of_opNorm_le hφn _).trans_eq (by
      change 1 * ‖conjugateCLM v a‖ = 1 * ‖a‖
      rw [conjugateCLM_norm])
  refine ⟨φ, ψ, hφ, hψ, hφn, hψn, ?_⟩
  intro b hb
  let b' := star (v : A) * b
  have hb' : ‖b'‖ ≤ 1 := by
    change ‖(Unitary.mulLeft ℂ A (star v)) b‖ ≤ 1
    simpa only [LinearIsometryEquiv.norm_map] using hb
  have hback : (v : A) * b' = b := by
    dsimp [b']
    rw [← mul_assoc, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]
  have hnorm : ‖D.flip b'‖ = ‖B.flip b‖ := by
    simp only [D, ContinuousLinearMap.flip_smul, smul_apply, norm_smul, hc, one_mul,
      translateB_flip_norm, hback]
  have he₁ : star b' * b' = star b * b := by
    dsimp [b']
    simp only [star_mul, star_star]
    rw [mul_assoc, ← mul_assoc (v : A), ← Unitary.coe_star,
      Unitary.coe_mul_star_self, one_mul]
  have he₂ : b' * star b' = conjugateCLM v (b * star b) := by
    simp only [b', star_mul, star_star, conjugateCLM_apply, mul_assoc]
  have hnuv : ‖B (u : A) (v : A)‖ ≤ 1 := by
    simpa only [hB, CStarRing.norm_coe_unitary, mul_one] using B.le_opNorm₂ (u : A) (v : A)
  have hδ : (1-(D 1 1).re)^2 ≤ ε^2 := by
    rw [hD1]
    exact pow_le_pow_left₀ (sub_nonneg.mpr hnuv) (by linarith) 2
  have h := hmod b' hb'
  rw [hnorm, he₁, he₂, map_add, Complex.add_re] at h
  change ‖B.flip b‖^4 ≤ 524288 * (ε^2 + (φ (star b * b)).re +
    (φ (conjugateCLM v (b * star b))).re)
  linarith

open Filter Topology in
private lemma exists_quartic_unit (B : A →L[ℂ] StrongDual ℂ A) (hB : ‖B‖ = 1) :
    ∃ φ ψ : StrongDual ℂ A,
      FunctionalPositive φ ∧ FunctionalPositive ψ ∧ ‖φ‖ ≤ 1 ∧ ‖ψ‖ ≤ 1 ∧
      ∀ b : A, ‖b‖ ≤ 1 →
        ‖B.flip b‖^4 ≤ 524288 * ((φ (star b * b)).re + (ψ (b * star b)).re) := by
  have hex (n : ℕ) := exists_quartic_near B hB
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    (by apply div_le_one_of_le₀ <;> linarith [Nat.cast_nonneg (α := ℝ) n] : 1 / ((n : ℝ)+1) ≤ 1)
  choose φ ψ hφ hψ hφn hψn hmod using hex
  let q : ℕ → WeakDual ℂ A × WeakDual ℂ A :=
    fun n => (StrongDual.toWeakDual (φ n), StrongDual.toWeakDual (ψ n))
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let S : Set (WeakDual ℂ A × WeakDual ℂ A) :=
    (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1) ×ˢ
    (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1)
  have hS : IsCompact S := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).prod
    (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1)
  have hmem (n : ℕ) : q n ∈ S := by
    constructor
    · change φ n ∈ Metric.closedBall (0 : StrongDual ℂ A) 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hφn n
    · change ψ n ∈ Metric.closedBall (0 : StrongDual ℂ A) 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hψn n
  obtain ⟨p,hp,hlim⟩ := hS.ultrafilter_le_nhds (ω.map q) (by
    rw [Ultrafilter.coe_map, le_principal_iff]
    change ∀ᶠ n in (ω : Filter ℕ), q n ∈ S
    exact Eventually.of_forall hmem)
  have ht : Tendsto q (ω : Filter ℕ) (𝓝 p) := hlim
  have hφlim (a : A) : Tendsto (fun n => φ n a) (ω : Filter ℕ) (𝓝 (p.1 a)) :=
    show Tendsto (fun n => (q n).1 a) (ω : Filter ℕ) (𝓝 (p.1 a)) from
      (WeakDual.eval_continuous a).tendsto p.1 |>.comp
        ((continuous_fst.tendsto p).comp ht)
  have hψlim (a : A) : Tendsto (fun n => ψ n a) (ω : Filter ℕ) (𝓝 (p.2 a)) :=
    show Tendsto (fun n => (q n).2 a) (ω : Filter ℕ) (𝓝 (p.2 a)) from
      (WeakDual.eval_continuous a).tendsto p.2 |>.comp
        ((continuous_snd.tendsto p).comp ht)
  have hpos₁ : FunctionalPositive (WeakDual.toStrongDual p.1) := by
    intro a ha
    refine ⟨ge_of_tendsto' (Complex.continuous_re.tendsto _ |>.comp (hφlim a))
      (fun n => (hφ n a ha).1), ?_⟩
    have hzero : Tendsto (fun n => (φ n a).im) (ω : Filter ℕ) (𝓝 0) := by
      simpa only [funext (fun n => (hφ n a ha).2)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0))
    exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp (hφlim a)) hzero
  have hpos₂ : FunctionalPositive (WeakDual.toStrongDual p.2) := by
    intro a ha
    refine ⟨ge_of_tendsto' (Complex.continuous_re.tendsto _ |>.comp (hψlim a))
      (fun n => (hψ n a ha).1), ?_⟩
    have hzero : Tendsto (fun n => (ψ n a).im) (ω : Filter ℕ) (𝓝 0) := by
      simpa only [funext (fun n => (hψ n a ha).2)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0))
    exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp (hψlim a)) hzero
  refine ⟨WeakDual.toStrongDual p.1, WeakDual.toStrongDual p.2, hpos₁, hpos₂,
    by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hp.1,
    by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hp.2, ?_⟩
  intro b hb
  have hε : Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  have hsum := ((hε.pow 2).add (Complex.continuous_re.tendsto _ |>.comp
    (hφlim (star b * b)))).add (Complex.continuous_re.tendsto _ |>.comp
    (hψlim (b * star b)))
  have hsum' := hsum.const_mul 524288
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hsum'
  exact ge_of_tendsto' hsum' (fun n => hmod n b hb)

open scoped ComplexOrder
private def functionalPositiveMap (φ : StrongDual ℂ A) (hφ : FunctionalPositive φ) :
    A →ₚ[ℂ] ℂ where
  __ := φ.toLinearMap
  monotone' := by
    intro a b hab
    have hp := hφ (b-a) (sub_nonneg.mpr hab)
    have h := Complex.nonneg_iff.mpr ⟨hp.1, hp.2.symm⟩
    change φ a ≤ φ b
    exact sub_nonneg.mp (by simpa only [map_sub] using h)

theorem quartic_state_modulus_unit (B : A →L[ℂ] StrongDual ℂ A) (hB : ‖B‖ = 1) :
    ∃ φ ψ : A →ₚ[ℂ] ℂ, ∀ b : A,
      ‖B.flip b‖^4 ≤ 524288 * ‖b‖^2 *
        ((φ (star b * b)).re + (ψ (b * star b)).re) := by
  obtain ⟨φ,ψ,hφ,hψ,_,_,h⟩ := exists_quartic_unit B hB
  refine ⟨functionalPositiveMap φ hφ, functionalPositiveMap ψ hψ, ?_⟩
  intro b
  change ‖B.flip b‖^4 ≤ 524288 * ‖b‖^2 *
    ((φ (star b * b)).re + (ψ (b * star b)).re)
  by_cases hb : b = 0
  · simp [hb]
  have hn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let t : ℂ := (‖b‖⁻¹ : ℝ)
  have htn : ‖t‖ = ‖b‖⁻¹ := by simp [t]
  have htstar : star t = t := by simp [t]
  have hb' : ‖t • b‖ ≤ 1 := by rw [norm_smul, htn, inv_mul_cancel₀ hn.ne']
  have he₁ : star (t • b) * (t • b) = (t*t) • (star b * b) := by
    simp only [star_smul, htstar, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he₂ : (t • b) * star (t • b) = (t*t) • (b * star b) := by
    simp only [star_smul, htstar, smul_mul_assoc, mul_smul_comm, smul_smul]
  have h' := h (t • b) hb'
  rw [map_smul, norm_smul, htn, mul_pow, he₁, he₂, map_smul, map_smul] at h'
  have htRe (c : ℂ) : ((t*t) • c).re = ‖b‖⁻¹^2 * c.re := by
    simp only [t, smul_eq_mul, ← Complex.ofReal_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [htRe, htRe] at h'
  have hmul := mul_le_mul_of_nonneg_left h' (show 0 ≤ ‖b‖^4 by positivity)
  field_simp [hn.ne'] at hmul
  nlinarith

theorem quartic_state_modulus (B : A →L[ℂ] StrongDual ℂ A) :
    ∃ (φ ψ : A →ₚ[ℂ] ℂ) (C : ℝ), 0 ≤ C ∧ ∀ b : A,
      ‖B.flip b‖^4 ≤ C * ‖b‖^2 *
        ((φ (star b * b)).re + (ψ (b * star b)).re) := by
  by_cases hB : B = 0
  · exact ⟨0,0,0,le_rfl, by simp [hB]⟩
  have hn : 0 < ‖B‖ := (norm_pos_iff (a := B)).mpr hB
  let t : ℂ := (‖B‖⁻¹ : ℝ)
  have htn : ‖t‖ = ‖B‖⁻¹ := by simp [t, abs_of_nonneg hn.le]
  have hBn : ‖t • B‖ = 1 := by
    let := @NormedSpace.toNormSMulClass ℂ (A →L[ℂ] StrongDual ℂ A) _ _ _
    rw [norm_smul, htn, inv_mul_cancel₀ hn.ne']
  obtain ⟨φ,ψ,h⟩ := quartic_state_modulus_unit (t • B) hBn
  refine ⟨φ,ψ,524288 * ‖B‖^4, by positivity, ?_⟩
  intro b
  have h' := h b
  rw [ContinuousLinearMap.flip_smul, smul_apply, norm_smul, htn, mul_pow] at h'
  have hm := mul_le_mul_of_nonneg_left h' (show 0 ≤ ‖B‖^4 by positivity)
  field_simp [hn.ne'] at hm
  nlinarith
end BilinearModulus
end HochschildFourPoint
end
end OAI
end

section
namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace HochschildDomination
universe u v
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PreHilbert
variable (φ ψ : M →ₚ[ℂ] ℂ)

lemma norm_def (x : PreHilbert φ ψ) :
    ‖x‖ = Real.sqrt ((φ (star (val φ ψ x) * val φ ψ x) +
      ψ (val φ ψ x * star (val φ ψ x))).re) := rfl

lemma norm_of_le (b : M) :
    ‖of φ ψ b‖ ≤ Real.sqrt (‖φ 1‖ + ‖ψ 1‖) * ‖b‖ := by
  rw [norm_def]
  refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  change (φ (star b * b)).re + (ψ (b * star b)).re ≤ _
  calc
    _ ≤ ‖φ (star b * b)‖ + ‖ψ (b * star b)‖ :=
      add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
    _ ≤ ‖φ 1‖ * ‖star b * b‖ + ‖ψ 1‖ * ‖b * star b‖ :=
      add_le_add (φ.norm_apply_le_of_nonneg _ (star_mul_self_nonneg _))
        (ψ.norm_apply_le_of_nonneg _ (mul_star_self_nonneg _))
    _ = (‖φ 1‖ + ‖ψ 1‖) * ‖b‖ ^ 2 := by
      rw [CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star]
      ring

def ofCLM : M →L[ℂ] PreHilbert φ ψ :=
  (of φ ψ).toLinearMap.mkContinuous (Real.sqrt (‖φ 1‖ + ‖ψ 1‖)) (norm_of_le φ ψ)

@[simp] lemma ofCLM_apply (b : M) : ofCLM φ ψ b = of φ ψ b := rfl

end PreHilbert

abbrev Hilbert (φ ψ : M →ₚ[ℂ] ℂ) := UniformSpace.Completion (PreHilbert φ ψ)

def beta (φ ψ : M →ₚ[ℂ] ℂ) : M →L[ℂ] Hilbert φ ψ :=
  UniformSpace.Completion.toComplL.comp (PreHilbert.ofCLM φ ψ)

variable (B : M →L[ℂ] StrongDual ℂ M) (φ ψ : M →ₚ[ℂ] ℂ)
  (C : ℝ) (hC : 0 ≤ C)
  (hdom : ∀ a b, ‖B a b‖ ≤ C * ‖a‖ * ‖PreHilbert.of φ ψ b‖)

end HochschildDomination

open scoped InnerProductSpace ComplexOrder
namespace HochschildDomination
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma beta_norm_sq (φ ψ : M →ₚ[ℂ] ℂ) (b : M) :
    ‖beta φ ψ b‖^2 = (φ (star b * b)).re + (ψ (b * star b)).re := by
  change ‖(PreHilbert.of φ ψ b : UniformSpace.Completion (PreHilbert φ ψ))‖^2 = _
  rw [UniformSpace.Completion.norm_coe, PreHilbert.norm_def]
  exact Real.sq_sqrt (add_nonneg
    (Complex.nonneg_iff.mp (φ.map_nonneg (star_mul_self_nonneg b))).1
    (Complex.nonneg_iff.mp (ψ.map_nonneg (mul_star_self_nonneg b))).1)

omit [PartialOrder M] [StarOrderedRing M] in

theorem exists_quartic_hilbert_modulus (B : M →L[ℂ] StrongDual ℂ M) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (β : M →L[ℂ] H) (C : ℝ),
      0 ≤ C ∧ ∀ b, ‖B.flip b‖^4 ≤ C * ‖b‖^2 * ‖β b‖^2 := by
  let := CStarAlgebra.spectralOrder M
  let := CStarAlgebra.spectralOrderedRing M
  have hp : ∃ (φ ψ : M →ₚ[ℂ] ℂ) (C : ℝ), 0 ≤ C ∧ ∀ b,
      ‖B.flip b‖^4 ≤ C * ‖b‖^2 *
        ((φ (star b * b)).re + (ψ (b * star b)).re) := by
    cases subsingleton_or_nontrivial M with
    | inl hs =>
      let := hs
      refine ⟨0,0,0,le_rfl,?_⟩
      intro b
      have hb : b = 0 := Subsingleton.elim _ _
      simp [hb]
    | inr hn =>
      let := hn
      exact HochschildFourPoint.quartic_state_modulus B
  obtain ⟨φ,ψ,C,hC,hdom⟩ := hp
  refine ⟨Hilbert φ ψ,inferInstance,inferInstance,inferInstance,beta φ ψ,C,hC,?_⟩
  intro b
  rw [beta_norm_sq]
  exact hdom b
end HochschildDomination
end
end OAI
end

theorem solution.{u} : type_of% @OAI.HochschildDomination.exists_quartic_hilbert_modulus.{u} := @OAI.HochschildDomination.exists_quartic_hilbert_modulus.{u}
