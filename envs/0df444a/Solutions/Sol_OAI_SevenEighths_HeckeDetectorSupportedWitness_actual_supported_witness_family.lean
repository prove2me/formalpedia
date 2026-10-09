-- Prove2me | solution 1 for OAI.SevenEighths.HeckeDetectorSupportedWitness.actual_supported_witness_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:29:55.083442+00:00
-- url     : https://prove2.me/submissions/3357afc2-c473-4c72-ae35-eff305fe984a

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorDyadicActual_simultaneous_upper
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorFrequency_dyadic_frequency_bound
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorLower_exists_dyadic_zero_witness
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_one_le_re

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector
namespace OAI

namespace SevenEighths.Detector

theorem simultaneous_saturation {U δ r m ε A B : ℝ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprod : U ^ (δ * (r + m) - ε) ≤ A * B)
    (hupperA : A ≤ U ^ (δ * r + ε))
    (hupperB : B ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ A ∧ U ^ (δ * m - 2 * ε) ≤ B := by
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hBcoarse : B ≤ U ^ (δ * m + ε) := by
    apply hupperB.trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le
      (by have h := mul_le_mul_of_nonneg_left (min_le_left m (1 - m)) hδ0; linarith)
  have hpupper : A * B ≤ U ^ (δ * r + ε + (δ * min m (1 - m) + ε)) := by
    rw [Real.rpow_add hU0]
    exact mul_le_mul hupperA hupperB hB (Real.rpow_nonneg hU0.le _)
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp (hprod.trans hpupper)
  have hlength : m ≤ 1 / 2 + 75 * ε := by
    by_cases hm : m ≤ 1 / 2
    · linarith
    · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
      rw [hmin] at hexp
      have hm0 : 0 ≤ m - 1 / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hδ hm0
      nlinarith
  have hlowerA : U ^ (δ * r - 2 * ε) ≤ A := by
    have hp : U ^ (δ * r - 2 * ε) * U ^ (δ * m + ε) ≤
        A * U ^ (δ * m + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := mul_le_mul_of_nonneg_left hBcoarse hA
    have hpos := Real.rpow_pos_of_pos hU0 (δ * m + ε)
    nlinarith
  have hlowerB : U ^ (δ * m - 2 * ε) ≤ B := by
    have hp : U ^ (δ * m - 2 * ε) * U ^ (δ * r + ε) ≤
        B * U ^ (δ * r + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hupperA hB
    have hpos := Real.rpow_pos_of_pos hU0 (δ * r + ε)
    nlinarith
  exact ⟨hlength, hlowerA, hlowerB⟩

end SevenEighths.Detector

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology
namespace SevenEighths.HeckeDetectorZeros
open HeckeFamily

variable {ι : Type*} [Fintype ι]

theorem zeroMaximum_mem (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    zeroMaximum χ hχ T ∈ realParts χ hχ T := Finset.max'_mem _ _

theorem maximum_attained (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ)
    (hmax : (51/100 : ℝ) < zeroMaximum χ hχ T) :
    ∃ i s, LFunction (χ i) s = 0 ∧ |s.im| ≤ T ∧ s.re = zeroMaximum χ hχ T := by
  have hm := zeroMaximum_mem χ hχ T
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩, hs, heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_familyZeros χ hχ T i s).mp hs
    exact ⟨i,s,hz.2.2.2,hz.2.2.1,heq⟩

end SevenEighths.HeckeDetectorZeros

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicLossBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem indexed_height_bound (i I : ℕ) (hi : i≤I) (T : ℝ) (hT : 0≤T) :
    (3+(3*i+2 : ℕ)*T)^4≤(3*(I : ℝ)+5)^4*(1+T)^4 := by
  have hi' : (i : ℝ)≤I := by exact_mod_cast hi
  have hlin : 3+(3*i+2 : ℕ)*T≤(3*(I : ℝ)+5)*(1+T) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hi' hT,Nat.cast_nonneg (α:=ℝ) I]
  calc
    _ ≤ ((3*(I : ℝ)+5)*(1+T))^4 := pow_le_pow_left₀ (by positivity) hlin 4
    _ = _ := mul_pow _ _ _

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma norm_phase (x D : ℝ) (hx : 0<x) (hD : 0<D) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-s)*FourierBridge.logPhase t (Real.log (x/D)) =
      (D : ℂ)^(-s)*((x/D : ℝ) : ℂ)^(-HeckeDyadic.shift s.re (2*Real.pi*t-s.im)) := by
  have hxD : 0<x/D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold FourierBridge.logPhase HeckeDyadic.shift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s=(s.re : ℂ)+(s.im : ℂ)*I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring

lemma normalization (D : ℝ) (hD : 0<D) (s : ℂ) :
    (D : ℂ)^((1/2 : ℂ)-s)*(D : ℂ)^(-(1/2 : ℂ))=(D : ℂ)^(-s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 1
  ring

lemma polynomial_eq_finite (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

theorem phase_sum_eq_polynomial (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (s : ℂ) (t : ℝ) (S : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    (∑ J∈S, coefficient χ inverse J*(J.absNorm : ℂ)^(-s)*
      W ((J.absNorm : ℝ)/D)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ inverse W D s.re (2*Real.pi*t-s.im) := by
  rw [polynomial_eq_finite χ inverse W D s.re (2*Real.pi*t-s.im) S hcover,
    ← mul_assoc, normalization D hD s, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hnorm : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS J hJ))
  have hp := norm_phase (J.absNorm : ℝ) D hnorm hD s t
  simp only [Complex.ofReal_natCast] at hp
  calc
    _ = coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
        ((J.absNorm : ℂ)^(-s)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) := by ring
    _ = _ := by rw [hp]; ring

lemma inverseProfile_at_norm (V W : ℝ→ℂ) (Dstar D x : ℝ) (hD : 0<D) :
    inverseProfile V W Dstar D (x/D)=V (x/Dstar)*W (x/D) := by
  unfold inverseProfile
  congr 2
  field_simp

lemma weighted_eq (χ : Character) (s : ℂ) (J : Ideal O) (hJ : J≠0) :
    IdealEuler.weighted (idealCoeff χ) s J=idealCoeff χ J*(J.absNorm : ℂ)^(-s) := by
  simp only [IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight, if_neg hJ]

theorem plain_phase_eq (χ : Character) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (plainCoefficient χ W D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ false W D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ false W D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [plainCoefficient, weighted_eq χ s J (hS J hJ)]
  rfl

theorem inverse_phase_eq (χ : Character) (V W : ℝ→ℂ) (Dstar D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (inverseCoefficient χ V W Dstar D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*
        polynomial χ true (inverseProfile V W Dstar D) D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ true (inverseProfile V W Dstar D) D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [inverseCoefficient, weighted_eq χ s J (hS J hJ), inverseProfile_at_norm V W Dstar D _ hD]
  simp only [coefficient, ite_true]
  ring

lemma normalization_norm (D : ℝ) (hD : 0<D) (s : ℂ) :
    ‖(D : ℂ)^((1/2 : ℂ)-s)‖=D^(1/2-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  congr 1
  simp

theorem pair_phase_norm (χ : Character) (V W₁ W₂ : ℝ→ℂ) (Dstar D N : ℝ)
    (hD : 0<D) (hN : 0<N) (s : ℂ) (t : ℝ) (S R : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0) (hR : ∀ J∈R, J≠0)
    (hcoverS : ∀ J : Ideal O, J≠0 → inverseProfile V W₁ Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (hcoverR : ∀ J : Ideal O, J≠0 → W₂ ((J.absNorm : ℝ)/N)≠0 → J∈R) :
    ‖phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
        (fun J => Real.log ((J.absNorm : ℝ)/D)) t‖ *
      ‖phasePolynomial R (plainCoefficient χ W₂ N s)
        (fun J => Real.log ((J.absNorm : ℝ)/N)) t‖ =
      D^(1/2-s.re)*N^(1/2-s.re)*
        (‖polynomial χ true (inverseProfile V W₁ Dstar D) D s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false W₂ N s.re (2*Real.pi*t-s.im)‖) := by
  rw [inverse_phase_eq χ V W₁ Dstar D hD s t S hS hcoverS,
    plain_phase_eq χ W₂ N hN s t R hR hcoverR,
    norm_mul, norm_mul, normalization_norm D hD s, normalization_norm N hN s]
  ring

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDetectorFinite HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma fourierSet_nonzero (U : ℝ) (J : Ideal O) (hJ : J∈fourierSet U) : J≠0 := by
  have hn := (mem_idealsUpTo.mp hJ).1
  exact Ideal.absNorm_eq_zero_iff.not.mp (by omega)

lemma annular_covered (U D : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : W ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hr : (J.absNorm : ℝ)/D<2 := lt_of_not_ge (fun hn => hw (hW _ hn))
  have hn : (J.absNorm : ℝ)≤16*U := by
    have hh := (div_lt_iff₀ hD).mp hr
    linarith
  exact_mod_cast hn.trans (Nat.le_ceil (16*U))

lemma inverse_annular_covered (U D Dstar : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (V W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply annular_covered U D hD hDU W hW J hJ
  exact (mul_ne_zero_iff.mp hw).2

lemma scales_le_eight_terminal (U : ℝ) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U) :
    (2 : ℝ)^j≤8*U ∧ (2 : ℝ)^k≤8*U := by
  have hj : 1≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hk : 1≤(2 : ℝ)^k := one_le_pow₀ (by norm_num)
  constructor
  · exact (le_mul_of_one_le_right (by positivity) hk).trans hprod.le
  · exact (le_mul_of_one_le_left (by positivity) hj).trans hprod.le

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesCutoffs
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma cutoff_norm_le (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
  exact QuadraticInitialBound.sieveBump.le_one

lemma annular_log_bound (x : ℝ) (hx : 0 ≤ x)
    (hactive : DyadicTransfer.annularCutoff cutoff x ≠ 0) : |Real.log x| ≤ Real.log 2 := by
  have hh := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
    (by simpa using hactive)
  norm_num at hh
  have hx0 : 0 < x := by linarith
  have hlo := Real.log_le_log (by norm_num : 0 < (2 : ℝ)⁻¹)
    (show (2 : ℝ)⁻¹ ≤ x by linarith)
  rw [Real.log_inv] at hlo
  exact abs_le.mpr ⟨hlo,Real.log_le_log hx0 hh.2.le⟩

theorem exists_product_log_cutoff :
    ∃ Ω : ℝ → ℂ, HasCompactSupport Ω ∧ ContDiff ℝ ∞ Ω ∧
      tsupport Ω ⊆ Set.Icc (-(2*Real.log 2+1)) (2*Real.log 2+1) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        DyadicTransfer.annularCutoff cutoff x ≠ 0 → DyadicTransfer.annularCutoff cutoff y ≠ 0 →
        Ω (Real.log x+Real.log y) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨Ω,hc,hs,hone,hsupp,hzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (2*Real.log 2) (by positivity)
  refine ⟨Ω,hc,hs,hsupp,?_⟩
  intro x y hx hy hax hay
  apply hone
  have hb1 := annular_log_bound x hx hax
  have hb2 := annular_log_bound y hy hay
  exact (abs_add_le _ _).trans (by linarith)

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFrequencyTail
namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.HeckeDetectorFrequency

lemma logb_square_div_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun U : ℝ => (Real.logb 2 U)^2/U^a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have h' := h.const_mul ((Real.log 2)^2)⁻¹
  convert (preTransparency := .instances) h' using 1
  · ext U
    rw [Real.rpow_two,Real.logb]
    ring
  · ring_nf

theorem exists_frequency_tail_order (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ C : ℝ, ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n) ≤ 1/4 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (43/τ)
  have he : 0 < τ*(n : ℝ)-42 := by
    have hh := (div_lt_iff₀ hτ).mp hn
    nlinarith
  refine ⟨n,?_⟩
  intro C
  have ht := (logb_square_div_rpow_tendsto (τ*(n : ℝ)-42) he).const_mul (625*67108864*C)
  have ht' : Tendsto
      (fun U : ℝ => (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n))
      atTop (𝓝 0) := by
    apply (show Tendsto (fun U : ℝ => (625*67108864*C)*
      ((Real.logb 2 U)^2/U^(τ*(n : ℝ)-42))) atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    rw [Real.rpow_sub hU,Real.rpow_mul_natCast hU.le,
      show (42 : ℝ)=((42 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    field_simp
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht').2 (1/4) (by norm_num))
  exact ⟨U₀,fun U hU hU1 => (hU₀ U hU).le⟩

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCommonFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier HeckeDetectorLower
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorPartition
local notation "O" => HeckeFamily.O

theorem exists_common_frequency_witness (R θ τ : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hτ : 0 < τ) :
    ∃ C U₀ : ℝ, 0 < C ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ χ : Character, χ.residue ≠ 1 → ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖ ≤ U^τ ∧
            1 ≤ C*(Real.logb 2 U)^2*‖phaseProduct χ D U ρ j k t‖ ∧
            (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨Ω,hΩc,hΩ,hwindow,hΩone⟩ := exists_product_log_cutoff
  obtain ⟨n,hn⟩ := exists_frequency_tail_order τ hτ
  have hL : 0 ≤ 2*Real.log 2+1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  obtain ⟨C₀,Cn,hC₀,hCn,hfreq⟩ := dyadic_frequency_bound Ω hΩc hΩ
    (2*Real.log 2+1) hL hwindow hΩone n
  obtain ⟨UF,hUF⟩ := hn Cn
  obtain ⟨UL,hUL⟩ := exists_dyadic_zero_witness R θ hR hθ hθ'
  refine ⟨2500*C₀,max 2 (max UF UL),by positivity,?_⟩
  intro U hU χ hχ D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  obtain ⟨j,hj,k,hk,hblock,hsupport⟩ :=
    hUL U ((le_max_right UF UL).trans ((le_max_right 2 _).trans hU))
      χ hχ cutoff cutoff cutoff_norm_le cutoff_norm_le cutoff_one cutoff_zero cutoff_one cutoff_zero
      D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨t,ht,hb⟩ := hfreq U D (U^τ) hU1 (by linarith) (by positivity) χ ρ (by linarith) j k
  have htail := hUF U ((le_max_left UF UL).trans ((le_max_right 2 _).trans hU)) hU1
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 625*(Real.logb 2 U)^2 by positivity)
  refine ⟨j,hj,k,hk,t,ht,?_,hsupport⟩
  change ‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖ at hb
  change (625*(Real.logb 2 U)^2)*‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (625*(Real.logb 2 U)^2)*((67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖) at hb'
  nlinarith

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicCutoff
namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

lemma positiveAnnular_eq (x : ℝ) (hx : 0≤x) :
    positiveAnnular x=DyadicTransfer.annularCutoff cutoff x :=
  (Classical.choose_spec exists_positive_annular).2.2 x hx

lemma positiveAnnular_zero (x : ℝ) (hx : 2≤x) : positiveAnnular x=0 := by
  rw [positiveAnnular_eq x (by linarith)]
  exact DyadicTransfer.annularCutoff_eq_zero_of_two_le cutoff cutoff_zero hx

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorNormalized
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNormalized
open HeckeFamily HeckeDyadic HeckeDetectorFourier HeckeDetectorProfiles
open HeckeDetectorDyadicBridge HeckeDetectorDyadicProfiles HeckeDetectorFrequency

lemma plainCoefficient_positive (χ : Character) (D : ℝ) (hD : 0<D) (s : ℂ) :
    plainCoefficient χ positiveAnnular D s=
      plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) D s := by
  funext J
  unfold plainCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

lemma inverseCoefficient_positive (χ : Character) (Dstar D : ℝ) (hD : 0<D) (s : ℂ) :
    inverseCoefficient χ cutoff positiveAnnular Dstar D s=
      inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s := by
  funext J
  unfold inverseCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

theorem phaseProduct_norm (χ : Character) (Dstar U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    ‖phaseProduct χ Dstar U s j k t‖ =
      ((2 : ℝ)^j)^(1/2-s.re)*((2 : ℝ)^k)^(1/2-s.re)*
        (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
            ((2 : ℝ)^j) s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) s.re (2*Real.pi*t-s.im)‖) := by
  obtain ⟨hj,hk⟩ := scales_le_eight_terminal (U^21) j k hprod
  have hDj : 0<(2 : ℝ)^j := by positivity
  have hNk : 0<(2 : ℝ)^k := by positivity
  unfold phaseProduct
  rw [norm_mul, ← inverseCoefficient_positive χ Dstar ((2 : ℝ)^j) hDj s,
    ← plainCoefficient_positive χ ((2 : ℝ)^k) hNk s]
  exact pair_phase_norm χ cutoff positiveAnnular positiveAnnular Dstar ((2 : ℝ)^j) ((2 : ℝ)^k)
    hDj hNk s t (fourierSet (U^21)) (fourierSet (U^21))
    (fourierSet_nonzero (U^21)) (fourierSet_nonzero (U^21))
    (inverse_annular_covered (U^21) ((2 : ℝ)^j) Dstar hDj hj cutoff positiveAnnular positiveAnnular_zero)
    (annular_covered (U^21) ((2 : ℝ)^k) hNk hk positiveAnnular positiveAnnular_zero)

theorem exists_normalized_product (R θ τ : ℝ) (hR : 0≤R)
    (hθ : 0≤θ) (hθ' : θ<3/4) (hτ : 0<τ) :
    ∃ C U₀ : ℝ, 0<C ∧ ∀ U : ℝ, U₀≤U →
      ∀ χ : Character, χ.residue≠1 → ∀ Dstar : ℝ, 2≤Dstar → Dstar≤U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ)≤R*U → ∀ ρ : ℂ,
      (51/100 : ℝ)≤ρ.re → LFunction χ ρ=0 → |ρ.im|≤U^θ →
      ∃ j∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖≤U^τ ∧
            1≤C*(Real.logb 2 U)^2*((2 : ℝ)^j)^(1/2-ρ.re)*((2 : ℝ)^k)^(1/2-ρ.re)*
              (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
                  ((2 : ℝ)^j) ρ.re (2*Real.pi*t-ρ.im)‖ *
               ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) ρ.re (2*Real.pi*t-ρ.im)‖) ∧
            (2 : ℝ)^j<4*Dstar ∧ Dstar/8<(2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k<8*U^21 := by
  obtain ⟨C,U₀,hC,hbound⟩ := exists_common_frequency_witness R θ τ hR hθ hθ' hτ
  refine ⟨C,U₀,hC,?_⟩
  intro U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,t,ht,hb,hd,hn,hprod⟩ := hbound U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  refine ⟨j,hj,k,hk,t,ht,?_,hd,hn,hprod⟩
  rw [phaseProduct_norm χ Dstar U ρ j k t hprod] at hb
  convert (preTransparency := .instances) hb using 1; ring

end SevenEighths.HeckeDetectorNormalized

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorSaturation
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSaturation
open HeckeDetectorFrequency

lemma logarithmic_cost_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ U : ℝ in atTop, (C*(Real.logb 2 U)^2)^2≤U^ε := by
  have ht := (logb_square_div_rpow_tendsto (ε/2) (by linarith)).pow 2
  have ht' := ht.const_mul (C ^2)
  have hbound : ∀ᶠ U : ℝ in atTop,
      C ^2*((Real.logb 2 U)^2/U^(ε/2))^2≤1 := by
    have hh : Tendsto (fun U : ℝ => C ^2*((Real.logb 2 U)^2/U^(ε/2))^2)
        atTop (𝓝 0) := by simpa using ht'
    exact (tendsto_order.mp hh).2 1 (by norm_num) |>.mono (fun _ h => h.le)
  filter_upwards [hbound,eventually_gt_atTop (0 : ℝ)] with U hb hU
  have he : (U^(ε/2))^2=U^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hU.le]
    congr 1
    norm_num
  rw [div_pow, he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU ε)).mp
    (show C ^2*((Real.logb 2 U)^2)^2/U^ε≤1 by simpa only [mul_div_assoc] using hb)
  simpa only [one_mul,mul_one,mul_pow] using hh

lemma normalized_product_lower (U r m σ a ε K A B : ℝ)
    (hU : 1<U) (hr : 0≤ r) (hm : 0≤ m) (hσ : a≤σ)
    (_hK : 0≤K) (_hA : 0≤A) (_hB : 0≤B)
    (hcost : K^2≤U^ε)
    (hprod : 1≤K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B)) :
    U^((2*a-1)*(r+m)-ε)≤A^2*B^2 := by
  have hUp : 0<U := by linarith
  have hcentral : (U^r)^(1/2-σ)*(U^m)^(1/2-σ)=U^((1/2-σ)*(r+m)) := by
    rw [← Real.rpow_mul hUp.le,← Real.rpow_mul hUp.le,← Real.rpow_add hUp]
    congr 1
    ring
  have hp : 1≤K*U^((1/2-σ)*(r+m))*(A*B) := by
    calc
      1 ≤ K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B) := hprod
      _ = _ := by rw [←hcentral]; ring
  have hsq : 1≤(K*U^((1/2-σ)*(r+m))*(A*B))^2 := by nlinarith
  have he : (U^((1/2-σ)*(r+m)))^2=U^((1-2*σ)*(r+m)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,he,mul_pow] at hsq
  let q := (2*a-1)*(r+m)-ε
  let L := K^2*U^((1-2*σ)*(r+m))
  have hLq : L*U^q≤1 := by
    calc
      _ ≤ U^ε*U^((1-2*σ)*(r+m))*U^q := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
        exact mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hUp.le _)
      _ = U^(ε+(1-2*σ)*(r+m)+q) := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]
      _ ≤ U^0 := Real.rpow_le_rpow_of_exponent_le hU.le (by
        dsimp [q]
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (add_nonneg hr hm)])
      _ = 1 := Real.rpow_zero _
  calc
    U^q = U^q*1 := by ring
    _ ≤ U^q*(L*(A^2*B^2)) := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hUp.le _)
    _ = (L*U^q)*(A^2*B^2) := by ring
    _ ≤ 1*(A^2*B^2) := mul_le_mul_of_nonneg_right hLq (by positivity)
    _ = _ := by ring

open HeckeFamily HeckeDyadic HeckeDetectorDyadicActual HeckeDetectorDyadicProfiles HeckeDetectorProfiles

theorem actual_saturation (R dmax τ ε e κ η Clower : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε/2) (hClower : 0≤Clower) :
    ∃ U₀ : ℝ, ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      U₀≤Z^d → 1<Z^d →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤ r → r≤R → 0≤ m → m≤R → (Z^d)^r≤4*Dstar →
        a≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        let M := polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq
        let S := polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq
        1≤Clower*(Real.logb 2 (Z^d))^2*((Z^d)^r)^(1/2-σ)*((Z^d)^m)^(1/2-σ)*(‖M‖*‖S‖) →
        m≤1/2+75*ε ∧ (Z^d)^((2*a-1)*r-2*ε)≤‖M‖^2 ∧
          (Z^d)^((2*a-1)*m-2*ε)≤‖S‖^2 := by
  obtain ⟨Cu,hCu,hupper⟩ := simultaneous_upper R dmax τ (ε/2) e κ η
    hR hdmax hτ (by linarith) he he' hκ hκ' hη hbudget
  have hev := (logarithmic_cost_eventually Clower ε hε).and
    (constant_absorbed_eventually Cu (ε/2) (by linarith))
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨U₀,?_⟩
  intro Z d hZ hd hd' hT hlarge hU ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight M S hprod
  have hσlo : 51/100≤σ := ha.trans hσ
  obtain ⟨hcost,hconst⟩ := hU₀ (Z^d) hlarge
  obtain ⟨hMu,hSu⟩ := hupper Z d hZ hd hd' hT χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσlo hσ' hfreq hheight
  have hp := normalized_product_lower (Z^d) r m σ a ε
    (Clower*(Real.logb 2 (Z^d))^2) ‖M‖ ‖S‖ hU hr hm hσ
    (mul_nonneg hClower (sq_nonneg _)) (norm_nonneg _) (norm_nonneg _) hcost hprod
  have hbound (x : ℝ) : Cu*(Z^d)^(x+ε/2)≤(Z^d)^(x+ε) := by
    calc
      _ ≤ (Z^d)^(ε/2)*(Z^d)^(x+ε/2) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z^d)]; congr 1; ring
  exact Detector.simultaneous_saturation hU (by linarith) hε.le (sq_nonneg _) (sq_nonneg _)
    hp (hMu.trans (hbound _)) (hSu.trans (hbound _))

end SevenEighths.HeckeDetectorSaturation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_power_allowance (C p dmin α : ℝ) (hα : 0≤α) (hgap : p<dmin*α) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → C*Z^p≤(Z^d)^α := by
  have hh := constant_absorbed_eventually C (dmin*α-p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd
  have hZp : 0<Z := by linarith
  calc
    _ ≤ Z^(dmin*α-p)*Z^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*α) := by rw [←Real.rpow_add hZp]; congr 1; ring
    _ ≤ Z^(d*α) := Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hα)
    _ = _ := Real.rpow_mul hZp.le _ _

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

lemma uniform_zero_height (dmin τ : ℝ) (I : ℕ) (hgap : τ<dmin/2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3*i : ℕ)*Z^τ≤(Z^d)^(1/2 : ℝ) := by
  have hh := uniform_power_allowance (3*I : ℕ) τ dmin (1/2) (by norm_num) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hn : (3*i : ℕ)≤3*I := by omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.rpow_nonneg (by linarith) _)).trans (hZ d hd)

lemma uniform_height_budget (dmin τ η : ℝ) (I : ℕ) (hτ : 0≤τ)
    (hη : 0≤η) (hgap : 4*τ<dmin*η) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η := by
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^4*16) (4*τ) dmin η hη hgap
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hT : 1≤Z^τ := Real.one_le_rpow hZ1 hτ
  have hp : (1+Z^τ)^4≤16*Z^(4*τ) := by
    calc
      _ ≤ (2*Z^τ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        have he : (Z^τ)^4=Z^(4*τ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤Z)]
          congr 1
          norm_num
          ring
        rw [mul_pow,he]
        norm_num
  calc
    _ ≤ (3*(I : ℝ)+5)^4*(1+Z^τ)^4 := indexed_height_bound i I hi (Z^τ) (by linarith)
    _ ≤ (3*(I : ℝ)+5)^4*(16*Z^(4*τ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((3*(I : ℝ)+5)^4*16)*Z^(4*τ) := by ring
    _ ≤ _ := hZ d hd

lemma uniform_fourier_allowance (dmax τ : ℝ) (hdmax : 0<dmax) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, 0≤d → d≤dmax →
      2*Real.pi*(Z^d)^(τ/(2*dmax))≤Z^τ/2 := by
  have hh := constant_absorbed_eventually (4*Real.pi) (τ/2) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd hd'
  have hZp : 0<Z := by linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^(τ/2) := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hm := mul_le_mul_of_nonneg_right hd' (show 0≤τ/(2*dmax) by positivity)
    have he : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rwa [he] at hm
  have he : Z^(τ/2)*Z^(τ/2)=Z^τ := by rw [←Real.rpow_add hZp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le (τ/2))
  rw [he] at hh
  have hpi := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  nlinarith

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicLengths
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDyadicGeometry

lemma log_scale_bounds (U x : ℝ) (hU : 8≤U) (hx : 1≤x) (hxU : x≤8*U^21) :
    0≤Real.logb U x ∧ Real.logb U x≤22 ∧ U^(Real.logb U x)=x := by
  have hUp : 0<U := by linarith
  have hU1 : 1<U := by linarith
  have hxp : 0<x := by linarith
  have he := Real.rpow_logb hUp hU1.ne' hxp
  refine ⟨Real.logb_nonneg hU1 hx,?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hU1).mp
  rw [he,show (22 : ℝ)=((22 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  calc
    x ≤ 8*U^21 := hxU
    _ ≤ U*U^21 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = U^22 := by ring

lemma dyadic_scale_bounds (U : ℝ) (hU : 8≤U) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    0≤Real.logb U ((2 : ℝ)^j) ∧ Real.logb U ((2 : ℝ)^j)≤22 ∧
      0≤Real.logb U ((2 : ℝ)^k) ∧ Real.logb U ((2 : ℝ)^k)≤22 ∧
      U^(Real.logb U ((2 : ℝ)^j))=(2 : ℝ)^j ∧
      U^(Real.logb U ((2 : ℝ)^k))=(2 : ℝ)^k := by
  obtain ⟨hj,hk⟩ := HeckeDetectorDyadicBridge.scales_le_eight_terminal (U^21) j k hprod
  obtain ⟨hr,hr',he⟩ := log_scale_bounds U ((2 : ℝ)^j) hU (one_le_pow₀ (by norm_num)) hj
  obtain ⟨hm,hm',he'⟩ := log_scale_bounds U ((2 : ℝ)^k) hU (one_le_pow₀ (by norm_num)) hk
  exact ⟨hr,hr',hm,hm',he,he'⟩

lemma support_exponents (U t r m ε : ℝ) (hU : 1<U) (hcost : 8≤U^ε)
    (hleft : U^r<4*U^t) (hright : U^t/8<U^r*U^m) :
    r≤t+ε ∧ t-ε≤ r+m := by
  have hUp : 0<U := by linarith
  constructor
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^r ≤ 4*U^t := hleft.le
      _ ≤ U^ε*U^t := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hUp.le _)
      _ = U^(t+ε) := by rw [←Real.rpow_add hUp]; congr 1; ring
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^(t-ε) = U^t/U^ε := Real.rpow_sub hUp _ _
      _ ≤ U^t/8 := div_le_div_of_nonneg_left (Real.rpow_nonneg hUp.le _) (by norm_num) hcost
      _ ≤ U^r*U^m := hright.le
      _ = U^(r+m) := (Real.rpow_add hUp _ _).symm

lemma truncation_scale (U t : ℝ) (hU : 2≤U) (ht : 1≤t) (ht' : t≤3/2) :
    2≤U^t ∧ U^t≤U^(3/2 : ℝ) := by
  have hU1 : 1≤U := by linarith
  constructor
  · apply hU.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1 ht
  · exact Real.rpow_le_rpow_of_exponent_le hU1 ht'

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneousSupport
namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneousSupport
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤ r ∧ r≤tstar+ε ∧ 0≤ m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤ m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,
    (by linarith [hsupport.2]),hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤ r ∧ r≤tstar+ε ∧ 0≤ m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤ m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneousSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

theorem actual_supported_witness_family_oai (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSimultaneousSupport.from_actual_maximum dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  have hw (u : Row) : Nonempty (SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i) := by
    obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hprod,hM,hS⟩ :=
      hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha' (hnext u) (hcurrent u) (hQ u) tstar ht ht'
    exact ⟨⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
      nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩,hprod⟩⟩
  exact ⟨fun u => Classical.choice (hw u)⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.HeckeDetectorSupportedWitness.actual_supported_witness_family_oai.{u_1, u_2} := @OAI.SevenEighths.HeckeDetectorSupportedWitness.actual_supported_witness_family_oai.{u_1, u_2}
