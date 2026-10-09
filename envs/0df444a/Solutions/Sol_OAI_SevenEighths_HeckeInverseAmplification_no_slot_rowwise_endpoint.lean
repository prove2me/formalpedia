-- Prove2me | solution 1 for OAI.SevenEighths.HeckeInverseAmplification.no_slot_rowwise_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:23:11.289361+00:00
-- url     : https://prove2.me/submissions/88c15850-9f35-41e5-8464-7bdf2402d3f1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_HeckeInverseAmplification_averaged_energy
import Theorems.Thm_OAI_SevenEighths_HeckeRayPrimes_quotientClassCoeff_ratio_tendsto
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]

end ShortDraftHeckeBridge

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

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

theorem rowwise_energy_two {ι : Type*} (rows : Finset ι)
    (F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ)
    (hcont : ∀ j k i, i∈rows → Continuous (Function.uncurry (F j k i)))
    (hdx : ∀ k i, i∈rows → ∀ x y,
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x)
    (hdy : ∀ j i, i∈rows → ∀ x y,
      HasDerivAt (F j 0 i x) (F j 1 i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (px py : ι→ℝ)
    (hpx : ∀ i∈rows, px i∈Icc a b) (hpy : ∀ i∈rows, py i∈Icc c d)
    (henergy : ∀ j k x, x∈Icc a b → ∀ y, y∈Icc c d →
      ∑ i∈rows, ‖F j k i x y‖^2≤E) :
    ∑ i∈rows, ‖F 0 0 i (px i) (py i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  have cx (j k : Fin 2) (i : ι) (hi : i∈rows) (y : ℝ) :
      Continuous (fun x => F j k i x y) :=
    (hcont j k i hi).comp (continuous_id.prodMk continuous_const)
  have cy (j k : Fin 2) (i : ι) (hi : i∈rows) (x : ℝ) :
      Continuous (F j k i x) :=
    (hcont j k i hi).comp (continuous_const.prodMk continuous_id)
  have he (j : Fin 2) (x : ℝ) (hx : x∈Icc a b) :
      ∑ i∈rows, ‖F j 0 i x (py i)‖^2≤(1+2*(d-c))*E :=
    rowwise_energy rows (fun i => F j 0 i x) (fun i => F j 1 i x)
      (fun i hi => cy j 0 i hi x) (fun i hi => cy j 1 i hi x)
      (fun i hi y => hdy j i hi x y) c d E hcd py hpy
      (fun y hy => henergy j 0 x hx y hy) (fun y hy => henergy j 1 x hx y hy)
  exact rowwise_energy rows (fun i x => F 0 0 i x (py i))
    (fun i x => F 1 0 i x (py i))
    (fun i hi => cx 0 0 i hi (py i)) (fun i hi => cx 1 0 i hi (py i))
    (fun i hi x => hdx 0 i hi x (py i)) a b ((1+2*(d-c))*E) hab px hpx
    (he 0) (he 1)

end SevenEighths.HeckeDetectorRowwise

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwise

theorem chain_rowwise {ι : Type*} (rows : Finset ι) (M : ℕ→ι→ℝ→ℝ→ℂ)
    (cm : ∀ n i, n≤2 → Continuous (Function.uncurry (M n i)))
    (dx : ∀ n i x y, n≤1 → HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x)
    (dy : ∀ n i x y, n≤1 → HasDerivAt (M n i x) (I*M (n+1) i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ n, n≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖M n i x y‖^2≤E) :
    ∑ i∈rows, ‖M 0 i (σ i) (freq i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ := fun j k i x y =>
    if j=0 then (if k=0 then M 0 i x y else I*M 1 i x y)
    else (if k=0 then -M 1 i x y else -(I*M 2 i x y))
  have cF (j k : Fin 2) (i : ι) (hi : i∈rows) : Continuous (Function.uncurry (F j k i)) := by
    have c0 := cm 0 i (by norm_num)
    have c1 := cm 1 i (by norm_num)
    have c2 := cm 2 i (by norm_num)
    fin_cases j <;> fin_cases k
    · simpa [F] using c0
    · convert (preTransparency := .instances) c1.const_mul I using 1
      ext p
      simp [F]
      rfl
    · convert (preTransparency := .instances) c1.neg using 1
      ext p
      simp [F]
      rfl
    · convert (preTransparency := .instances) (c2.const_mul I).neg using 1
      ext p
      simp [F]
      rfl
  have dFx (k : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x := by
    fin_cases k
    · simpa [F] using dx 0 i x y (by norm_num)
    · simpa [F] using (dx 1 i x y (by norm_num)).const_mul I
  have dFy (j : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    fin_cases j
    · simpa [F] using dy 0 i x y (by norm_num)
    · convert (preTransparency := .instances) (dy 1 i x y (by norm_num)).neg using 1
      · ext t
        simp [F]
      · simp [F]
  have eF (j k : Fin 2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖F j k i x y‖^2≤E := by
    fin_cases j <;> fin_cases k
    · simpa [F] using henergy 0 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 1 (by norm_num) x hx y hy
    · simpa [F] using henergy 1 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 2 (by norm_num) x hx y hy
  simpa only [F,ite_true] using
    rowwise_energy_two rows F cF dFx dFy a b c d E hab hcd σ freq hσ hf eF

end SevenEighths.HeckeDetectorRowwise

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePolynomial
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

theorem logProfile_cover (W : ℝ→ℂ) (D : ℝ) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    ∀ J : Ideal O, J≠0 → logProfile W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
  intro J hJ hw
  exact hc J hJ (fun hz => hw (by simp [logProfile,hz]))

lemma power_sigma_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift u freq))
      (-(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
  have hd := (((hasDerivAt_id (σ : ℂ)).neg).add_const ((freq : ℂ)*I)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert (preTransparency := .instances) hh using 1
  · ext u
    congr 1
    simp only [HeckeDyadic.shift,neg_sub,Pi.neg_apply,id_eq]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [Pi.neg_apply,id_eq]
    ring

lemma power_freq_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) freq := by
  have hd := (((hasDerivAt_id (freq : ℂ)).mul_const I).const_add (-(σ : ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert (preTransparency := .instances) hh using 1
  · ext u
    congr 1
    simp [HeckeDyadic.shift]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [id_eq]
    ring

theorem polynomial_sigma_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D u freq)
      (-polynomial χ inv (logProfile W) D σ freq) σ := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift u freq))
      (-coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,neg_zero] using hasDerivAt_const σ (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (preTransparency := .instances) (power_sigma_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (preTransparency := .instances) (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem polynomial_freq_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D σ u)
      (I*polynomial χ inv (logProfile W) D σ freq) freq := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq))) freq := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,mul_zero] using hasDerivAt_const freq (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (preTransparency := .instances) (power_freq_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (preTransparency := .instances) (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,←Finset.mul_sum]
  ring

theorem polynomial_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    Continuous (fun p : ℝ×ℝ => polynomial χ inv W D p.1 p.2) := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro J hJ
  by_cases hz : J=0
  · subst J
    simp only [coefficient_zero,zero_mul]
    exact continuous_const
  have hn : 0<(J.absNorm : ℝ)/D := div_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
  unfold HeckeDyadic.shift
  fun_prop

end SevenEighths.HeckeDetectorRowwisePolynomial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseMarked
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwiseMarked
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

theorem marked_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (inv : Bool) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (h0 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv W D x y*P i‖^2≤E)
    (h1 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile W) D x y*P i‖^2≤E)
    (h2 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile (logProfile W)) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) inv W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) inv ((logProfile^[n]) W) D x y*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    interval_cases n
    all_goals
      dsimp [M,Function.uncurry]
      apply Continuous.mul_const
    · exact polynomial_continuous (χ i) inv W D hD S hc
    · exact polynomial_continuous (χ i) inv (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) inv (logProfile (logProfile W)) D hD S hc2
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤E := by
    interval_cases n
    · simpa [M] using h0 x hx y hy
    · simpa [M] using h1 x hx y hy
    · simpa [M] using h2 x hx y hy
  exact chain_rowwise rows M cm dx dy a b c d E hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwiseMarked

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace W1

theorem differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

end W1
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Wiener
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

attribute [fun_prop] Real.continuous_fourierChar

attribute [fun_prop] measurable_coe_nnreal_ennreal

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

theorem cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

end nabla

theorem BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

local instance instCoeForallRealForallComplex_solutions_rc569f8_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
theorem vonMangoldt_cheby : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(Λ k : ℂ)‖) n ≤ C * n) := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealMangoldt
namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, if_pos (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, if_pos hI]
    apply Real.log_nonneg
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

theorem isPrimePow_absNorm {I : Ideal O} (hI : IsPrimePow I) :
    IsPrimePow (Ideal.absNorm I) := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [map_pow, hnorm, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨p, n * k, hp, mul_pos hn hk, rfl⟩

theorem value_eq_zero_of_norm_not_primePow {I : Ideal O}
    (hI : ¬IsPrimePow (Ideal.absNorm I)) : value I = 0 := by
  exact if_neg (fun h => hI (isPrimePow_absNorm h))

theorem prime_mem_primesOver_of_dvd_norm {P : Ideal O} (hP : Prime P)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm P) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hd
  have heq : P = Q := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero |>.eq_of_le
    hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  subst Q
  exact ⟨Ideal.isPrime_of_prime hP, ⟨hQu.symm⟩⟩

theorem primeBase_mem_primesOver {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {I : Ideal O} (hI : IsPrimePow I) (hn : Ideal.absNorm I = p ^ k) :
    primeBase I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨hP, l, hl, heq⟩ := primeBase_spec hI
  apply prime_mem_primesOver_of_dvd_norm hP hp
  apply hp.dvd_of_dvd_pow
  have hnorm := congrArg Ideal.absNorm heq
  rw [map_pow, hn] at hnorm
  rw [hnorm]
  exact dvd_pow_self _ hk.ne'

theorem primeBase_injective_on_norm {I J : Ideal O} (hI : IsPrimePow I)
    (hJ : IsPrimePow J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hbase : primeBase I = primeBase J) : I = J := by
  obtain ⟨hP, k, hk, hPk⟩ := primeBase_spec hI
  obtain ⟨_, l, hl, hPl⟩ := primeBase_spec hJ
  rw [← hbase] at hPl
  have hkl : k = l := by
    apply Nat.pow_right_injective (SmoothMobiusCorrection.prime_norm_two_le ⟨_, hP⟩)
    have hnI : Ideal.absNorm (primeBase I) ^ k = Ideal.absNorm I := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPk
    have hnJ : Ideal.absNorm (primeBase I) ^ l = Ideal.absNorm J := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPl
    exact hnI.trans (hn.trans hnJ.symm)
  exact hPk.symm.trans ((congrArg (primeBase I ^ ·) hkl).trans hPl)

theorem coeff_nonneg (w : Ideal O → ℝ) (hw : ∀ I, 0 ≤ w I) (n : ℕ) :
    0 ≤ coeff w n :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (value_nonneg I))

theorem coeff_le_unweighted (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ coeff (fun _ => 1) n := by
  apply Finset.sum_le_sum
  intro I hI
  exact mul_le_mul_of_nonneg_right (hw I) (value_nonneg I)

theorem coeff_eq_sum_primePowers (n : ℕ) :
    coeff (fun _ => 1) n =
      ∑ I ∈ (normFiber n).filter IsPrimePow, Real.log (Ideal.absNorm (primeBase I)) := by
  simp only [coeff, one_mul, value, Finset.sum_filter]

theorem coeff_eq_zero_of_not_primePow {n : ℕ} (hn : ¬IsPrimePow n)
    (w : Ideal O → ℝ) : coeff w n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  rw [value_eq_zero_of_norm_not_primePow (by simpa only [(mem_normFiber n I).mp hI] using hn),
    mul_zero]

theorem primesOver_card (p : ℕ) [Fact p.Prime] :
    (primesOver p).card = ((Ideal.span {(p : ℤ)}).primesOver O).ncard := by
  exact (Set.ncard_eq_toFinset_card _).symm

theorem primesOver_log_sum_le (p : ℕ) [hp : Fact p.Prime] :
    ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  by_cases h1 : p % 3 = 1
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_split hp.out h1 P]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.split_count_of_mod_one hp.out h1]
    norm_num
  by_cases h2 : p % 3 = 2
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = 2 * Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_inert hp.out h2 P, Nat.cast_pow, Real.log_pow]
      norm_num
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.inert_count_of_mod_two hp.out h2]
    norm_num
  have h3 : p = 3 := by
    have h0 : p % 3 = 0 := by have := Nat.mod_lt p (by decide : 0 < 3); omega
    have h := (Nat.dvd_prime hp.out).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  subst p
  have hv (P : Ideal O) (hP : P ∈ primesOver 3) :
      Real.log (Ideal.absNorm P) = Real.log 3 := by
    have hPP := (mem_primesOver 3 P).mp hP
    let : P.IsPrime := hPP.1
    let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPP.2
    rw [ShortDraftHeckeBridge.absNorm_ramified P]
    norm_num
  rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card]
  norm_num only [Nat.cast_ofNat]
  rw [ShortDraftHeckeBridge.ramified_count]
  norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem coeff_prime_pow_le (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    coeff (fun _ => 1) (p ^ k) ≤ 2 * Real.log p := by
  rw [coeff_eq_sum_primePowers]
  let S := (normFiber (p ^ k)).filter IsPrimePow
  have hS (I : Ideal O) (hI : I ∈ S) : IsPrimePow I ∧ Ideal.absNorm I = p ^ k :=
    ⟨(Finset.mem_filter.mp hI).2, (mem_normFiber _ I).mp (Finset.mem_filter.mp hI).1⟩
  have hinj : Set.InjOn primeBase (↑S : Set (Ideal O)) := by
    intro I hI J hJ heq
    exact primeBase_injective_on_norm (hS I hI).1 (hS J hJ).1
      ((hS I hI).2.trans (hS J hJ).2.symm) heq
  have hsub : S.image primeBase ⊆ primesOver p := by
    intro P hP
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hP
    exact (mem_primesOver p _).mpr (primeBase_mem_primesOver hp.out hk (hS I hI).1 (hS I hI).2)
  calc
    _ = ∑ P ∈ S.image primeBase, Real.log (Ideal.absNorm P) := (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro P hP _
      have hPP := (mem_primesOver p P).mp hP
      have hprime : Prime P := Ideal.prime_of_mem_primesOver
        (by simpa using (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)) hPP
      exact Real.log_nonneg (by exact_mod_cast
        (SmoothMobiusCorrection.prime_norm_two_le ⟨P, hprime⟩).trans' (by decide : 1 ≤ 2))
    _ ≤ _ := primesOver_log_sum_le p

theorem coeff_le_two_vonMangoldt (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ 2 * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    exact (coeff_le_unweighted w hw _).trans (coeff_prime_pow_le p hk)
  · rw [coeff_eq_zero_of_not_primePow hn, vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

theorem coeff_chebyshev (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(coeff w n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨2 * C, fun N => ?_⟩
  calc
    _ ≤ 2 * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
        using coeff_le_two_vonMangoldt w hw1 n
    _ ≤ 2 * (C * N) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

theorem classCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ classCoeff C n :=
  coeff_nonneg _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_le_two_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n ≤ 2 * vonMangoldt n :=
  coeff_le_two_vonMangoldt _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(classCoeff C n : ℂ)‖) N ≤ B * N :=
  coeff_chebyshev _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

end

end SevenEighths.IdealMangoldt

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayOrthogonality
namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

theorem ray_card_pos (H : Subgroup Rˣ) : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

end FiniteMonoid

end
end SevenEighths.RayOrthogonality

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass
namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun N n => if n < N then f n / N else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    apply (tendsto_const_div_atTop_nhds_zero_nat (f n)).congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [F, hN]
  have hbound : ∀ N n, ‖F N n‖ ≤ f n / n := by
    intro N n
    by_cases hn : n = 0
    · subst n
      simp [F, hzero]
    by_cases hN : n < N
    · simp only [F, if_pos hN, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hf n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hf n)
        (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)
        (show (n : ℝ) ≤ N by exact_mod_cast hN.le)
    · simp only [F, if_neg hN, norm_zero]
      exact div_nonneg (hf n) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbound)
  have heq (N : ℕ) : (∑' n, F N n) = cumsum f N / N := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp [F, hn])]
    rw [cumsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, Finset.mem_range.mp hn]
  simpa only [heq, tsum_zero] using h

end SevenEighths.PNT

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass
namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

theorem prime_of_isPrimePow_of_norm_prime {I : Ideal O}
    (hI : IsPrimePow I) (hn : (Ideal.absNorm I).Prime) : Prime I := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  rw [map_pow] at hn
  rw [hn.eq_one_of_pow, pow_one]
  exact hP

theorem value_eq_zero_of_nonprime_of_norm_prime {I : Ideal O}
    (hI : ¬Prime I) (hn : (Ideal.absNorm I).Prime) : value I = 0 := by
  apply if_neg
  exact fun hpow => hI (prime_of_isPrimePow_of_norm_prime hpow hn)

theorem primeClassCoeff_eq_sum_log (C : Set (Ideal O)) (n : ℕ) :
    primeClassCoeff C n =
      ∑ P ∈ (normFiber n).filter (fun P => P ∈ C ∧ Prime P), Real.log (Ideal.absNorm P) := by
  unfold primeClassCoeff classCoeff coeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I ∈ C ∧ Prime I
  · simp [h, value_prime h.2]
  · simp only [Set.mem_ofPred_eq, h, ite_false, zero_mul]

theorem primeClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ primeClassCoeff C n :=
  classCoeff_nonneg _ n

theorem higherClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ higherClassCoeff C n :=
  classCoeff_nonneg _ n

theorem classCoeff_eq_prime_add_higher (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n = primeClassCoeff C n + higherClassCoeff C n := by
  unfold primeClassCoeff higherClassCoeff classCoeff coeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hC : I ∈ C <;> by_cases hP : Prime I <;> simp [hC, hP]

@[simp] theorem higherClassCoeff_zero (C : Set (Ideal O)) : higherClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

@[simp] theorem primeClassCoeff_zero (C : Set (Ideal O)) : primeClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

theorem higherClassCoeff_eq_zero_of_prime (C : Set (Ideal O)) {n : ℕ} (hn : n.Prime) :
    higherClassCoeff C n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  simp only [Set.mem_ofPred_eq]
  split_ifs with h
  · rw [value_eq_zero_of_nonprime_of_norm_prime h.2
      (by simpa only [(mem_normFiber n I).mp hI] using hn), mul_zero]
  · exact zero_mul _

theorem higherClassCoeff_le_nonprime_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    higherClassCoeff C n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  by_cases hn : n.Prime
  · rw [higherClassCoeff_eq_zero_of_prime C hn, if_pos hn, mul_zero]
  · rw [if_neg hn]
    exact classCoeff_le_two_vonMangoldt _ n

theorem summable_nonprime_vonMangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [vonMangoldt.residueClass, Subsingleton.elim (α := ZMod 1) _ 0,
    Set.ofPred_true, Set.indicator_univ] using h

theorem higherClassCoeff_summable_div (C : Set (Ideal O)) :
    Summable (fun n : ℕ => higherClassCoeff C n / n) := by
  apply (summable_nonprime_vonMangoldt_div.mul_left 2).of_nonneg_of_le
  · intro n
    exact div_nonneg (higherClassCoeff_nonneg C n) (Nat.cast_nonneg n)
  · intro n
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (higherClassCoeff_le_nonprime_vonMangoldt C n)
      (Nat.cast_nonneg n)

theorem higherClassCoeff_ratio_tendsto_zero (C : Set (Ideal O)) :
    Tendsto (fun N : ℕ => cumsum (higherClassCoeff C) N / N) atTop (𝓝 0) :=
  cumsum_div_tendsto_zero_of_summable_div (higherClassCoeff_nonneg C)
    (higherClassCoeff_zero C) (higherClassCoeff_summable_div C)

theorem primeClassCoeff_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => cumsum (primeClassCoeff C) N / N) atTop (𝓝 A) := by
  have h' := h.sub (higherClassCoeff_ratio_tendsto_zero C)
  have heq (N : ℕ) :
      cumsum (classCoeff C) N / N - cumsum (higherClassCoeff C) N / N =
        cumsum (primeClassCoeff C) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [classCoeff_eq_prime_add_higher, add_sub_cancel_right]
  simpa only [heq, sub_zero] using h'

theorem primeLogMass_eq_cumsum (C : Set (Ideal O)) (N : ℕ) :
    primeLogMass C N = cumsum (primeClassCoeff C) N := by
  have hmap : ∀ P ∈ primeIdealsBelow C N, Ideal.absNorm P ∈ Finset.range N := by
    intro P hP
    exact Finset.mem_range.mpr ((mem_primeIdealsBelow C N P).mp hP).2.2
  rw [primeLogMass, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold cumsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_primeIdealsBelow, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_range.mp hn⟩, heq⟩
  · intro P hP
    rfl

end

end SevenEighths.PNT.IdealPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayQuotient
namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

theorem classNumber_pos : 0 < classNumber M H := ray_card_pos H

include hH

variable [IsDomain A] [IsPrincipalIdealRing A]

end
end SevenEighths.RayQuotient

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

theorem cumulative_ratio_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => cumulative f t / t) atTop (𝓝 A) := by
  have ht : Tendsto (fun t : ℝ => ⌊t⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) tendsto_nat_floor_atTop
  have hr : Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ) / t) atTop (𝓝 1) := by
    convert (preTransparency := .instances) (tendsto_nat_floor_div_atTop (R := ℝ)).add
      (show Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) by simpa only [one_div] using tendsto_inv_atTop_zero) using 1 <;> simp [add_div]
  convert (preTransparency := .instances) (h.comp ht).mul hr using 1
  · ext t
    simp only [Function.comp_def, cumulative]
    field_simp
  · simp

theorem scaledCumulative_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => scaledCumulative f x y) atTop (𝓝 (A * y)) := by
  have ht : Tendsto (fun x : ℝ => x * y) atTop atTop := tendsto_id.atTop_mul_const hy
  apply ((cumulative_ratio_tendsto h).comp ht).mul_const y |>.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold scaledCumulative
  dsimp only [Function.comp_def]
  field_simp

theorem cumulative_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (t : ℝ) :
    0 ≤ cumulative f t := cumsum_nonneg hf _

theorem scaledCumulative_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    {x y b : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hyb : y ≤ b) :
    ‖scaledCumulative f x y‖ ≤ C * (b + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [scaledCumulative, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (cumulative_nonneg hf _) hx0.le)]
  calc
    cumulative f (x * y) / x ≤ (C * (⌊x * y⌋₊ + 1 : ℕ)) / x := by
      exact div_le_div_of_nonneg_right (hbound _) hx0.le
    _ ≤ (C * (x * y + 1)) / x := by
      gcongr
      push_cast
      linarith [Nat.floor_le (mul_nonneg hx0.le hy)]
    _ ≤ C * (b + 1) := by
      rw [div_le_iff₀ hx0]
      nlinarith [mul_le_mul_of_nonneg_left hyb hx0.le,
        mul_nonneg hC (sub_nonneg.mpr hx)]

theorem measurable_cumulative (f : ℕ → ℝ) : Measurable (cumulative f) :=
  (measurable_of_countable (cumsum f)).comp (measurable_id.nat_floor.add_const 1)

theorem measurable_scaledCumulative (f : ℕ → ℝ) (x : ℝ) :
    Measurable (scaledCumulative f x) :=
  ((measurable_cumulative f).comp (measurable_const.mul measurable_id)).div_const x

theorem annularSum_div_eq_integral (f : ℕ → ℝ) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    annularSum f φ a b x / x =
      -(∫ y in a..b, deriv φ y * scaledCumulative f x y) := by
  let g : ℝ → ℝ := fun t => φ (t / x)
  have hg (t : ℝ) : HasDerivAt g (deriv φ (t / x) / x) t := by
    convert (preTransparency := .instances) (hφ (t / x)).hasDerivAt.comp t ((hasDerivAt_id t).div_const x) using 1 <;>
      simp only [g, Function.comp_def, div_eq_mul_inv, id_eq, one_mul]
  have hgc : Continuous (deriv g) := by
    have heq : deriv g = fun t => deriv φ (t / x) / x := funext (fun t => (hg t).deriv)
    rw [heq]
    exact (hφ'.comp (continuous_id.div_const x)).div_const x
  have h := sum_mul_eq_sub_sub_integral_mul f (a := x * a) (b := x * b)
    (mul_nonneg hx.le ha) (mul_le_mul_of_nonneg_left hab hx.le)
    (fun t _ => (hg t).differentiableAt) hgc.integrableOn_Icc
  have hcum (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) = cumulative f t := by
    simp only [cumulative, cumsum, Nat.range_succ_eq_Icc_zero]
  simp_rw [hcum, (hg _).deriv] at h
  have hga : g (x * a) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφa]
  have hgb : g (x * b) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφb]
  rw [hga, hgb, zero_mul, zero_mul, sub_zero, zero_sub,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le)] at h
  have hs : annularSum f φ a b x =
      -(∫ t in x * a..x * b, (deriv φ (t / x) / x) * cumulative f t) := by
    rw [← h]
    unfold annularSum g
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hs, neg_div]
  congr 1
  have hi := intervalIntegral.integral_comp_mul_left
    (fun t => (deriv φ (t / x) / x) * cumulative f t) hx.ne' (a := a) (b := b)
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [mul_div_cancel_left₀ _ hx.ne', scaledCumulative]
  ring

theorem integral_scaledCumulative_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun x : ℝ => ∫ y in a..b, g y * scaledCumulative f x y) atTop
      (𝓝 (∫ y in a..b, g y * (A * y))) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖ * (C * (b + 1)))
  · exact Eventually.of_forall (fun x =>
      (hg.measurable.mul (measurable_scaledCumulative f x)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (scaledCumulative_bound hf hC hbound hx (ha.le.trans hy.1.le) hy.2) (norm_nonneg _)
  · exact (hg.norm.mul_const _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (scaledCumulative_tendsto hmass (ha.trans hy.1)).const_mul (g y)

theorem annularSum_div_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => annularSum f φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (integral_scaledCumulative_tendsto hf hC hbound hmass ha hab (deriv φ) hφ').neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ => (1 : ℝ)) (v := φ) (v' := deriv φ)
    (fun y _ => hasDerivAt_id y) (fun y _ => (hφ y).hasDerivAt)
    (continuous_const.intervalIntegrable a b) (hφ'.intervalIntegrable a b)
  have heq : -(∫ y in a..b, deriv φ y * (A * y)) = A * ∫ y in a..b, φ y := by
    have hfun : (fun y => deriv φ y * (A * y)) = fun y => A * (y * deriv φ y) := by
      ext y
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hibp, hφa, hφb]
    simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (annularSum_div_eq_integral f φ hφ hφ' ha.le hab hx hφa hφb).symm

theorem primeLogAnnularSum_eq (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) :
    primeLogAnnularSum C φ a b x = annularSum (primeClassCoeff C) φ a b x := by
  have hmap : ∀ P ∈ annularPrimeIdeals C a b x,
      Ideal.absNorm P ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊ := by
    intro P hP
    exact Finset.mem_Ioc.mpr ((mem_annularPrimeIdeals C a b x P).mp hP).2.2
  rw [primeLogAnnularSum, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold annularSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log, Finset.sum_mul]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_annularPrimeIdeals, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_Ioc.mp hn⟩, heq⟩
  · intro P hP
    rw [(mem_normFiber n P).mp (Finset.mem_filter.mp hP).1]

theorem primeClassCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N := by
  obtain ⟨B, hB⟩ := classCoeff_chebyshev {I | I ∈ C ∧ Prime I}
  have hbound (N : ℕ) : cumsum (primeClassCoeff C) N ≤ B * N := by
    convert (preTransparency := .instances) hB N using 1
    congr 1
    funext n
    exact (Complex.norm_of_nonneg (primeClassCoeff_nonneg C n)).symm
  refine ⟨B, ?_, hbound⟩
  have h := (cumsum_nonneg (primeClassCoeff_nonneg C) 1).trans (hbound 1)
  simpa only [Nat.cast_one, mul_one, Pi.zero_apply] using h

theorem primeLogAnnularSum_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => primeLogAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  simpa only [primeLogAnnularSum_eq] using annularSum_div_tendsto
    (primeClassCoeff_nonneg C) hB hbound (primeClassCoeff_ratio_tendsto C hmass)
    φ hφ hφ' ha hab hφa hφb

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

theorem ratio_mem_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    (Ideal.absNorm P : ℝ) / x ∈ Set.Icc a b := by
  obtain ⟨hl, hu⟩ := norm_bounds_of_mem_annularPrimeIdeals ha hab hx hP
  exact ⟨(le_div_iff₀ hx).mpr (by nlinarith), (div_le_iff₀ hx).mpr (by nlinarith)⟩

theorem log_norm_difference_bound {a b x : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hx : 0 < x) {n : ℕ} (hn : (n : ℝ) / x ∈ Set.Icc a b) :
    |Real.log x - Real.log n| ≤ |Real.log a| + |Real.log b| := by
  have hn0 : 0 < (n : ℝ) := by
    have h := (le_div_iff₀ hx).mp hn.1
    exact (mul_pos ha hx).trans_le h
  have hl := Real.log_le_log ha hn.1
  have hu := Real.log_le_log (ha.trans_le hn.1) hn.2
  rw [Real.log_div hn0.ne' hx.ne'] at hl hu
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b), abs_nonneg (Real.log a),
    abs_nonneg (Real.log b)]

theorem annularPrime_card_div_bound (C : Set (Ideal O)) {B a b x : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ((annularPrimeIdeals C a b x).card : ℝ) / x ≤ B * (b + 1) / Real.log (x * a) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 < Real.log (x * a) := Real.log_pos hxa
  have hlower : Real.log (x * a) * (annularPrimeIdeals C a b x).card ≤
      ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro P hP
    exact Real.log_le_log (mul_pos hx0 ha)
      (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx0 hP).1.le
  have hupper : (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) ≤
      cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) := by
    rw [← primeLogMass_eq_cumsum, primeLogMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro P hP _
    rw [← value_prime ((mem_primeIdealsBelow C _ P).mp hP).2.1]
    exact value_nonneg P
  have hnorm := scaledCumulative_bound (primeClassCoeff_nonneg C) hB hbound hx
    (ha.le.trans hab) (le_refl b)
  have hcum : cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x ≤ B * (b + 1) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, scaledCumulative, cumulative] using hnorm)
  apply (le_div_iff₀ hlog).mpr
  calc
    ((annularPrimeIdeals C a b x).card : ℝ) / x * Real.log (x * a) =
        (Real.log (x * a) * (annularPrimeIdeals C a b x).card) / x := by ring
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) / x :=
      div_le_div_of_nonneg_right hlower hx0.le
    _ ≤ cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x :=
      div_le_div_of_nonneg_right hupper hx0.le
    _ ≤ _ := hcum

theorem primeAnnularSum_log_error_bound (C : Set (Ideal O)) (φ : ℝ → ℝ)
    {B M a b x : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (hM : 0 ≤ M) (hφ : ∀ y ∈ Set.Icc a b, |φ y| ≤ M)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ‖Real.log x * primeAnnularSum C φ a b x / x - primeLogAnnularSum C φ a b x / x‖ ≤
      ((|Real.log a| + |Real.log b|) * M) * (B * (b + 1) / Real.log (x * a)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : Real.log x * primeAnnularSum C φ a b x - primeLogAnnularSum C φ a b x =
      ∑ P ∈ annularPrimeIdeals C a b x,
        (Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x) := by
    simp only [primeAnnularSum, primeLogAnnularSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sub_mul]
  rw [← sub_div, heq, norm_div, Real.norm_of_nonneg hx0.le]
  calc
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x,
        ‖(Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x)‖) / x :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hx0.le
    _ ≤ (∑ _P ∈ annularPrimeIdeals C a b x, (|Real.log a| + |Real.log b|) * M) / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hratio := ratio_mem_of_mem_annularPrimeIdeals ha.le hab hx0 hP
      exact mul_le_mul (log_norm_difference_bound ha hab hx0 hratio) (hφ _ hratio)
        (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((|Real.log a| + |Real.log b|) * M) * ((annularPrimeIdeals C a b x).card / x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (annularPrime_card_div_bound C hB hbound ha hab hx hxa)
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hM)

theorem primeAnnularSum_log_error_tendsto (C : Set (Ideal O)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x -
      primeLogAnnularSum C φ a b x / x) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  obtain ⟨M, hMbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMbound a ⟨le_rfl, hab⟩)
  have hup : Tendsto (fun x : ℝ => ((|Real.log a| + |Real.log b|) * M) *
      (B * (b + 1) / Real.log (x * a))) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_mul_const ha))
    convert (preTransparency := .instances) (hi.const_mul (B * (b + 1))).const_mul ((|Real.log a| + |Real.log b|) * M)
      using 1 <;> simp only [div_eq_mul_inv, mul_zero, Function.comp_def, id_eq]
  apply squeeze_zero_norm' _ hup
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.atTop_mul_const ha).eventually_gt_atTop 1] with x hx hxa
  exact primeAnnularSum_log_error_bound C φ hB hbound hM
    (fun y hy => by simpa only [Real.norm_eq_abs] using hMbound y hy) ha hab hx hxa

theorem primeAnnularSum_log_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (primeAnnularSum_log_error_tendsto C φ hφ.continuous ha hab).add
    (primeLogAnnularSum_div_tendsto C hmass φ hφ hφ' ha hab hφa hφb)
  simpa only [sub_add_cancel, zero_add] using h

theorem contDiff_powerWeight (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Ioo a b) (r : ℝ) :
    ContDiff ℝ ∞ (fun y => W y * y ^ r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ha] with y hy
    have hWy : W y = 0 := Function.notMem_support.mp (by
      intro h
      exact (not_lt_of_ge (hsupp h).1.le) hy)
    simp only [hWy, zero_mul]
  · exact hW.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hy)

theorem weightedPrimeAnnularSum_normalization (C : Set (Ideal O)) (W : ℝ → ℝ)
    (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x =
      Real.log x * primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x / x := by
  have heq : primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x =
      weightedPrimeAnnularSum C W a b x / x ^ (-5 / 6 : ℝ) := by
    unfold primeAnnularSum weightedPrimeAnnularSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp only
    rw [Real.div_rpow (Nat.cast_nonneg _) hx.le]
    ring
  have hp : x ^ (-5 / 6 : ℝ) * x = x ^ (1 / 6 : ℝ) := by
    calc
      _ = x ^ (-5 / 6 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-5 / 6 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  rw [heq, mul_div_assoc, div_div, hp]
  ring

theorem weightedPrimeAnnularSum_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  let φ : ℝ → ℝ := fun y => W y * y ^ (-5 / 6 : ℝ)
  have hφ : ContDiff ℝ ∞ φ := contDiff_powerWeight W hW ha hsupp _
  have hWa : W a = 0 := Function.notMem_support.mp (fun h => (hsupp h).1.false)
  have hWb : W b = 0 := Function.notMem_support.mp (fun h => (hsupp h).2.false)
  have hφa : φ a = 0 := by simp only [φ, hWa, zero_mul]
  have hφb : φ b = 0 := by simp only [φ, hWb, zero_mul]
  have hint : (∫ y in a..b, φ y) = ∫ y, φ y := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hWy : W y = 0 := Function.notMem_support.mp
      (fun h => hy ⟨(hsupp h).1, (hsupp h).2.le⟩)
    simp only [φ, hWy, zero_mul]
  have h := primeAnnularSum_log_div_tendsto C hmass φ (hφ.differentiable (by simp))
    (hφ.continuous_deriv (by simp)) ha hab hφa hφb
  rw [hint] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (weightedPrimeAnnularSum_normalization C W a b hx).symm

theorem exists_positive_support_annulus (W : ℝ → ℝ) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ Function.support W ⊆ Set.Ioo a b := by
  by_cases hne : (tsupport W).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hM, hmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    have hmM : m ≤ M := hmin hM
    refine ⟨m / 2, M + 1, by positivity, by linarith, ?_⟩
    intro y hy
    have hyt : y ∈ tsupport W := subset_closure hy
    have hl : m ≤ y := hmin hyt
    have hu : y ≤ M := hmax hyt
    exact ⟨by linarith, by linarith⟩
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, subset_closure hy⟩).elim

theorem mem_annularPrimeIdeals_of_weight_ne_zero {C : Set (Ideal O)} {W : ℝ → ℝ}
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x)
    {P : Ideal O} (hC : P ∈ C) (hP : Prime P) (hW : W (Ideal.absNorm P / x) ≠ 0) :
    P ∈ annularPrimeIdeals C a b x := by
  have hy := hsupp hW
  apply (mem_annularPrimeIdeals C a b x P).mpr
  refine ⟨hC, hP, ?_, ?_⟩
  · apply (Nat.floor_lt (mul_nonneg hx.le ha.le)).mpr
    have h := (lt_div_iff₀ hx).mp hy.1
    nlinarith
  · apply (Nat.le_floor_iff (mul_nonneg hx.le (ha.le.trans hab))).mpr
    have h := (div_lt_iff₀ hx).mp hy.2
    nlinarith

theorem primeWeightTerm_support_subset (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    Function.support (primeWeightTerm C W x) ⊆ (annularPrimeIdeals C a b x : Set (Ideal O)) := by
  intro P hP
  change primeWeightTerm C W x P ≠ 0 at hP
  unfold primeWeightTerm at hP
  split_ifs at hP with h
  · exact mem_annularPrimeIdeals_of_weight_ne_zero ha hab hsupp hx h.1 h.2
      (left_ne_zero_of_mul hP)
  · exact (hP rfl).elim

theorem weightedPrimeSum_eq_annular (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSum C W x = weightedPrimeAnnularSum C W a b x := by
  rw [weightedPrimeSum, finsum_eq_finsetSum_of_support_subset _
    (primeWeightTerm_support_subset C W ha hab hsupp hx)]
  apply Finset.sum_congr rfl
  intro P hP
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  simp only [primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem weightedPrimeSum_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSum C W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  apply (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab.le hsupp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [weightedPrimeSum_eq_annular C W ha hab.le hsupp hx]

theorem finite_prime_weights_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, ∀ P ∈ S, primeWeightTerm C W x P = 0 := by
  have hz : ∀ᶠ y in 𝓝 (0 : ℝ), W y = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => (show (0 : ℝ) < 0 from hp h).false)
  rw [eventually_all_finset]
  intro P hP
  have ht : Tendsto (fun x : ℝ => (Ideal.absNorm P : ℝ) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (Ideal.absNorm P : ℝ)
  filter_upwards [ht hz] with x hx
  change W (Ideal.absNorm P / x) = 0 at hx
  simp only [primeWeightTerm, hx, zero_mul, ite_self]

theorem fixed_prime_deletion_eventually_eq (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    weightedPrimeSumDeleted C S W =ᶠ[atTop] weightedPrimeSum C W := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  unfold weightedPrimeSumDeleted weightedPrimeSum
  congr 1
  ext P
  by_cases hP : P ∈ S
  · simp only [hP, ite_true, hx P hP]
  · simp only [hP, ite_false]

theorem weightedPrimeSumDeleted_tendsto (C : Set (Ideal O)) (S : Finset (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  apply (weightedPrimeSum_tendsto C hmass W hW hc hp).congr'
  filter_upwards [fixed_prime_deletion_eventually_eq C S W hp] with x hx
  rw [hx]

theorem weightedPrimeSumDeleted_eq_annular (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x =
      ∑ P ∈ annularPrimeIdeals C a b x \ S,
        W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) := by
  have hsub : Function.support (fun P => if P ∈ S then 0 else primeWeightTerm C W x P) ⊆
      (↑(annularPrimeIdeals C a b x \ S) : Set (Ideal O)) := by
    intro P hP
    change (if P ∈ S then 0 else primeWeightTerm C W x P) ≠ 0 at hP
    by_cases hPS : P ∈ S
    · simp only [hPS, ite_true, ne_self_iff_false] at hP
    · simp only [hPS, ite_false] at hP
      exact Finset.mem_sdiff.mpr ⟨primeWeightTerm_support_subset C W ha hab hsupp hx hP, hPS⟩
  rw [weightedPrimeSumDeleted, finsum_eq_finsetSum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro P hP
  have hS := (Finset.mem_sdiff.mp hP).2
  have h := (mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1
  simp only [hS, ite_false, primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem powerWeight_integral_pos (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    0 < ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  have hφ := contDiff_powerWeight W hW ha hsupp (-5 / 6)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, W y ≠ 0 := by
    by_contra h
    push Not at h
    exact hWne (funext h)
  have hy0 : 0 < y := hp (subset_closure hy)
  apply hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
  · intro z
    by_cases hz : W z = 0
    · simp only [hz, zero_mul, Pi.zero_apply, le_refl]
    · have hz0 : 0 < z := hp (subset_closure hz)
      exact mul_nonneg (hW0 z) (Real.rpow_nonneg hz0.le _)
  · exact mul_ne_zero hy (Real.rpow_pos_of_pos hy0 _).ne'

theorem weightedPrimeSumDeleted_eventually_lower_bound (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1 / 6 : ℝ) / Real.log x ≤ weightedPrimeSumDeleted C S W x := by
  let L : ℝ := A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ)
  have hL : 0 < L := mul_pos hA (powerWeight_integral_pos W hW hc hp hW0 hWne)
  refine ⟨L / 2, half_pos hL, ?_⟩
  have ht := weightedPrimeSumDeleted_tendsto C S hmass W hW hc hp
  have he := ht (Ioi_mem_nhds (half_lt_self hL))
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  change L / 2 < Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x at hx
  have hxp : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have hmul := (le_div_iff₀ hxp).mp (show L / 2 ≤
      (Real.log x * weightedPrimeSumDeleted C S W x) / x ^ (1 / 6 : ℝ) by
    convert (preTransparency := .instances) hx.le using 1; ring)
  nlinarith

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayPrimeNormalizer
namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace SevenEighths.RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

theorem eventually_lower_bound (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1/6 : ℝ) / Real.log x ≤ normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_lower_bound _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

end SevenEighths.RayPrimeNormalizer

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimePool
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open Filter
namespace SevenEighths.CenteredMomentPrimePool
open HeckeFamily PNT.AnnularPrimeMass

theorem annular_weighted_card_bound (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (a b B x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hW : ∀ y, W y ≤ B) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x ≤
      ((annularPrimeIdeals C a b x \ S).card : ℝ) * (B * a^(-5/6 : ℝ)) * x^(-5/6 : ℝ) := by
  rw [weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  calc
    _ ≤ ∑ _P ∈ annularPrimeIdeals C a b x \ S, B*(a*x)^(-5/6 : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hn := (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx (Finset.mem_sdiff.mp hP).1).1
      apply mul_le_mul (hW _) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB
      exact Real.rpow_le_rpow_of_nonpos (mul_pos ha hx) (by nlinarith) (by norm_num)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,Real.mul_rpow ha.le hx.le]
      ring

section FixedRay
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

local instance instFiniteQuotientOIdeal_solutions_rc569f8_1 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem eventually_primePool_card (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hbound : ∀ y, W y ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c*x/Real.log x ≤ (primePool M H S a b x).card := by
  obtain ⟨c,hcpos,hlower⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  let D : ℝ := B*a^(-5/6 : ℝ)
  have hD : 0 < D := mul_pos hB (Real.rpow_pos_of_pos ha _)
  refine ⟨c/D,div_pos hcpos hD,?_⟩
  filter_upwards [hlower,eventually_gt_atTop (1 : ℝ)] with x hlow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hu := annular_weighted_card_bound (RayQuotient.identityClass M H) S W a b B x
    ha hab hB.le hsupp hbound hx0
  change weightedPrimeSumDeleted _ S W x ≤ (primePool M H S a b x).card * D * x^(-5/6 : ℝ) at hu
  change c*x^(1/6 : ℝ)/Real.log x ≤ weightedPrimeSumDeleted _ S W x at hlow
  have hpower : x*x^(-5/6 : ℝ) = x^(1/6 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(-5/6 : ℝ) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+(-5/6)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hmul : (c*x/Real.log x)*x^(-5/6 : ℝ) ≤
      ((primePool M H S a b x).card * D)*x^(-5/6 : ℝ) := by
    calc
      _ = c*(x*x^(-5/6 : ℝ))/Real.log x := by ring
      _ = _ := by rw [hpower]
      _ ≤ _ := hlow.trans hu
  have hcancel := le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hx0 (-5/6 : ℝ))
  convert (preTransparency := .instances) (div_le_iff₀ hD).mpr hcancel using 1 ; ring

end FixedRay

end SevenEighths.CenteredMomentPrimePool

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPrimePool
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem typedPrimePool_card (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) :
    (typedPrimePool M H S a b x).card=
      (CenteredMomentPrimePool.primePool M H S a b x).card := by
  rw [typedPrimePool,Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro P hP
  exact ((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp
    (Finset.mem_sdiff.mp hP).1).2.1

theorem typedPrimePool_norm (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) (ha : 0≤a) (hab : a≤b) (hx : 0<x)
    (P : PrimeIdeal) (hP : P∈typedPrimePool M H S a b x) :
    (P.val.absNorm : ℝ)≤x*b := by
  have hh := Finset.mem_subtype.mp hP
  exact (PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp hh).1).2

theorem eventually_fixed_ray_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb D U E : ℝ),
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      0<D → (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawScaleEnergy data W U D (x*b) E →
      RawScaleEnergy data (scaleProfile W) U D (x*b) E →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2)≤
        4*(1+2*Real.log (x*b))*E*Real.log x/(c*x) := by
  obtain ⟨c,hc,hcard⟩ := CenteredMomentPrimePool.eventually_primePool_card M H hH S
    φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB
  have hb : 0<b := ha.trans_le hab
  refine ⟨c,hc,?_⟩
  filter_upwards [hcard,eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (1/b)] with x hcard hx hxB
  intro data rows W wa wb D U E hwa hwb hWs hW hD hrows hraw0 hraw1
  have hx0 : 0<x := zero_lt_one.trans hx
  have hxblog : 1≤x*b := (div_le_iff₀ hb).mp hxB
  have hlog : 0<Real.log x := Real.log_pos hx
  have hc' : c*x/Real.log x≤((typedPrimePool M H S a b x).card : ℝ) := by
    rw [typedPrimePool_card]
    exact hcard
  have havg := averaged_energy data rows (typedPrimePool M H S a b x) W wa wb hwa hwb
    hWs hW D U (x*b) E hD hxblog hrows
    (fun P hP => typedPrimePool_norm M H S a b x ha.le hab hx0 P hP) hraw0 hraw1
  have hsum : 0≤∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := (mul_le_mul_of_nonneg_right hc' hsum).trans havg
  apply (le_div_iff₀ (mul_pos hc hx0)).mpr
  calc
    _ = (c*x/Real.log x*(∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2))*Real.log x := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh hlog.le

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget
namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

theorem amplificationPower_nonneg (c r : ℝ) : 0≤amplificationPower c r := le_max_left _ _

theorem amplificationPower_upper (c r R : ℝ) (hc : c≤1) (hr : 0≤ r)
    (hrR : r≤R) : amplificationPower c r≤R/3 := by
  apply max_le (by linarith)
  have hh := mul_le_mul_of_nonneg_right hc hr
  nlinarith

theorem amplified_exponent (c r : ℝ) :
    1+5*amplificationPower c r=max 1 ((1+5*(1+c)*r)/6) := by
  unfold amplificationPower
  by_cases h : 0≤((1+c)*r-1)/6
  · rw [max_eq_right h,max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by linarith)]
    ring

theorem amplified_exponent_le (c r R : ℝ) (hc : 0≤ c) (hrR : r≤R)
    (hR : 0≤R) : 1+5*amplificationPower c r≤ sourceExponent r+5*c*R/6 := by
  rw [amplified_exponent]
  apply max_le
  · have hh := le_max_left 1 ((1+5*r)/6)
    unfold sourceExponent
    nlinarith [mul_nonneg hc hR]
  · have hh := le_max_right 1 ((1+5*r)/6)
    have hh' := mul_le_mul_of_nonneg_left hrR hc
    unfold sourceExponent
    nlinarith

theorem exists_amplification_budget (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧
      ∀ r : ℝ, 0≤ r → r≤R →
      1+5*amplificationPower c r+κ*(1+6*amplificationPower c r+r)≤
        sourceExponent r+ε/2 := by
  let c := min 1 (ε/(4*(R+1)))
  let κ := ε/(4*(1+3*R))
  have hc : 0<c := lt_min zero_lt_one (div_pos hε (by positivity))
  have hκ : 0<κ := div_pos hε (by positivity)
  have hc1 : c≤1 := min_le_left _ _
  have hcb : c*(4*(R+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hκb : κ*(4*(1+3*R))=ε := by dsimp [κ]; field_simp
  refine ⟨c,κ,hc,hc1,hκ,?_⟩
  intro r hr hrR
  have hp := amplificationPower_upper c r R hc1 hr hrR
  have he := amplified_exponent_le c r R hc.le hrR hR
  have hraw : κ*(1+6*amplificationPower c r+r)≤κ*(1+3*R) := by
    apply mul_le_mul_of_nonneg_left _ hκ.le
    linarith
  nlinarith

theorem logarithmic_cost_eventually (A b P η : ℝ) (hA : 1≤A)
    (hbA : 1≤b*A) (hP : 0≤P) (hη : 0<η) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ U : ℝ in atTop, ∀ p : ℝ, 0≤p → p≤P →
      (1+2*Real.log (b*(A*U^p)))*Real.log (A*U^p)≤K*U^η := by
  let K := (1+2*Real.log (b*A)+2*P)*(Real.log A+P)
  have hLA : 0≤Real.log A := Real.log_nonneg hA
  have hLB : 0≤Real.log (b*A) := Real.log_nonneg hbA
  have hK : 0≤K := mul_nonneg (by positivity) (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with U hlog hLU hU
  intro p hp hpP
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hpow : 0<U^p := Real.rpow_pos_of_pos hUp _
  have hx : 1≤A*U^p := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hU hp)
  have hlogx : Real.log (A*U^p)=Real.log A+p*Real.log U := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hA)) hpow.ne',Real.log_rpow hUp]
  have hlogbx : Real.log (b*(A*U^p))=Real.log (b*A)+p*Real.log U := by
    rw [show b*(A*U^p)=b*A*U^p by ring,
      Real.log_mul (ne_of_gt (zero_lt_one.trans_le hbA)) hpow.ne',Real.log_rpow hUp]
  have hfirst : 1+2*Real.log (b*(A*U^p))≤(1+2*Real.log (b*A)+2*P)*Real.log U := by
    rw [hlogbx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLB]
  have hsecond : Real.log (A*U^p)≤(Real.log A+P)*Real.log U := by
    rw [hlogx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLA]
  have hsq : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  calc
    _ ≤ ((1+2*Real.log (b*A)+2*P)*Real.log U)*((Real.log A+P)*Real.log U) :=
      mul_le_mul hfirst hsecond (Real.log_nonneg hx) (by positivity)
    _ = K*(Real.log U)^2 := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPowers
namespace OAI

noncomputable section
namespace SevenEighths.HeckeInverseAmplification

theorem amplified_norm_power (U A b p : ℝ) (hU : 0<U) :
    U*(b*(A*U^p))^6=(b*A)^6*U^(1+6*p) := by
  have h6 : (U^p)^6=U^(6*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    norm_num
    ring
  calc
    _ = (b*A)^6*(U^(1 : ℝ)*U^(6*p)) := by
      rw [show b*(A*U^p)=(b*A)*U^p by ring,mul_pow,h6,Real.rpow_one]
      ring
    _ = _ := by rw [←Real.rpow_add hU]

theorem amplified_energy_power (U A b p r κ : ℝ) (hU : 0<U) :
    (U*(b*(A*U^p))^6)*((U*(b*(A*U^p))^6)*U^r)^κ/(A*U^p)=
      ((b*A)^6*((b*A)^6)^κ/A)*U^(1+5*p+κ*(1+6*p+r)) := by
  rw [amplified_norm_power U A b p hU]
  have hHD : ((b*A)^6*U^(1+6*p))*U^r=(b*A)^6*U^(1+6*p+r) := by
    rw [mul_assoc,←Real.rpow_add hU]
  rw [hHD,Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
    ←Real.rpow_mul hU.le]
  calc
    _ = ((b*A)^6*((b*A)^6)^κ/A)*
        ((U^(1+6*p)*U^((1+6*p+r)*κ))/U^p) := by ring
    _ = ((b*A)^6*((b*A)^6)^κ/A)*U^((1+6*p)+(1+6*p+r)*κ-p) := by
      rw [←Real.rpow_add hU,←Real.rpow_sub hU]
    _ = _ := by congr 2; ring

theorem fixed_multiplier_lower (U A p : ℝ) (hU : 1≤U) (hA : 0≤A) (hp : 0≤p) :
    A≤A*U^p := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hU hp) hA

theorem amplified_norm_dominates (U A b c r : ℝ) (hU : 1≤U) (hbA : 1≤b*A) :
    (U^r)^(1+c)≤U*(b*(A*U^(amplificationPower c r)))^6 := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  rw [amplified_norm_power U A b _ hUp,←Real.rpow_mul hUp.le]
  have he : r*(1+c)≤1+6*amplificationPower c r := by
    have hh := le_max_right 0 (((1+c)*r-1)/6)
    unfold amplificationPower
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hU he
  have hconst : (1 : ℝ)≤(b*A)^6 := one_le_pow₀ hbA
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hUp.le _) hconst)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRaw
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem RawMoment.scaleEnergy {data : RowData} {W : ℝ→ℂ} {c κ C : ℝ}
    (hraw : RawMoment data W c κ C) (hc : 0≤ c) (hκ : 0≤κ) (hC : 0≤C)
    (U D V : ℝ) (hD : 1≤D) (hH : 1≤U*V^6) (hHD : D^(1+c)≤U*V^6) :
    RawScaleEnergy data W U D V (C*(U*V^6)*((U*V^6)*D)^κ) := by
  intro rows hrows l hl
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hHp : 0<U*V^6 := zero_lt_one.trans_le hH
  have hexp : Real.exp l≤D := by
    rw [←Real.exp_log hDp]
    exact Real.exp_le_exp.mpr hl.2
  have hp : (Real.exp l)^(1+c)≤U*V^6 :=
    (Real.rpow_le_rpow (Real.exp_pos l).le hexp (by linarith)).trans hHD
  have hh := hraw (U*V^6) (Real.exp l) hH (Real.exp_pos l) hp rows hrows
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hHp.le)
  apply Real.rpow_le_rpow (by positivity) _ hκ
  exact mul_le_mul_of_nonneg_left (max_le hD hexp) hHp.le

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEndpoint
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem no_slot_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C : ℝ),
      0≤ r → r≤R → 0≤C →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawMoment data W c κ C → RawMoment data (scaleProfile W) c κ C →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) 0 0‖^2)≤
        C*K*U^(sourceExponent r+ε) := by
  obtain ⟨c,κ,hc,hc1,hκ,hbudget⟩ := exists_amplification_budget R ε hR hε
  obtain ⟨d,hd,havg⟩ := eventually_fixed_ray_amplification M H hH S φ hφ hφc hφp
    hφ0 hφne a b B ha hab hB hφs hφB
  obtain ⟨x0,hx0⟩ := eventually_atTop.mp havg
  let A := max 1 (max x0 (1/b))
  have hb : 0<b := ha.trans_le hab
  have hA : 1≤A := le_max_left _ _
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hAx0 : x0≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hbA : 1≤b*A := by
    have hh : 1/b≤A := (le_max_right _ _).trans (le_max_right _ _)
    have hh' := (div_le_iff₀ hb).mp hh
    nlinarith
  obtain ⟨Klog,hKlog,hlog⟩ := logarithmic_cost_eventually A b (R/3) (ε/2)
    hA hbA (by positivity) (by positivity)
  let F := (b*A)^6*((b*A)^6)^κ/A
  let K := (4/d)*F*Klog
  have hF : 0≤F := by dsimp [F]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with U hlog hU
  intro r data rows W wa wb C hr hrR hC hwa hwb hWs hW hrows hraw0 hraw1
  let p := amplificationPower c r
  let x := A*U^p
  let D := U^r
  let V := b*x
  let N := U*V^6
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hp : 0≤p := amplificationPower_nonneg c r
  have hpR : p≤R/3 := amplificationPower_upper c r R hc1 hr hrR
  have hxA : A≤x := fixed_multiplier_lower U A p hU hAp.le hp
  have hV : 1≤V := by
    change 1≤b*(A*U^p)
    rw [←mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hbA (Real.one_le_rpow hU hp)
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hN : 1≤N := one_le_mul_of_one_le_of_one_le hU (one_le_pow₀ hV)
  have hDN : D^(1+c)≤N := amplified_norm_dominates U A b c r hU hbA
  have hxb : x*b=V := mul_comm x b
  have hav := hx0 x (hAx0.trans hxA) data rows W wa wb D U
    (C*N*(N*D)^κ) hwa hwb hWs hW hDp hrows
    (by rw [hxb]; exact hraw0.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
    (by rw [hxb]; exact hraw1.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
  have hlog' := hlog p hp hpR
  have hnorm : N*(N*D)^κ/x=F*U^(1+5*p+κ*(1+6*p+r)) :=
    amplified_energy_power U A b p r κ hUp
  have hexp := hbudget r hr hrR
  have hpow : U^(1+5*p+κ*(1+6*p+r)+ε/2)≤U^(sourceExponent r+ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by dsimp [p]; linarith)
  calc
    _ ≤ 4*(1+2*Real.log (x*b))*(C*N*(N*D)^κ)*Real.log x/(d*x) := hav
    _ = C*(4/d)*(N*(N*D)^κ/x)*((1+2*Real.log (b*x))*Real.log x) := by
      rw [mul_comm x b]
      ring
    _ = (C*(4/d)*F)*((1+2*Real.log (b*x))*Real.log x)*
        U^(1+5*p+κ*(1+6*p+r)) := by rw [hnorm]; ring
    _ ≤ (C*(4/d)*F)*(Klog*U^(ε/2))*U^(1+5*p+κ*(1+6*p+r)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
      exact mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = C*K*U^(1+5*p+κ*(1+6*p+r)+ε/2) := by
      rw [Real.rpow_add hUp (1+5*p+κ*(1+6*p+r)) (ε/2)]
      dsimp [K]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hK)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRowwise
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwisePolynomial

theorem no_slot_rowwise_endpoint_oai
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C T : ℝ) (σ freq : FreeRow→ℝ),
      0≤ r → r≤R → 0≤C → 0≤T →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc 0 1) → (∀ u∈rows, freq u∈Icc (-T) T) →
      (∀ n : ℕ, n≤2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-T) T,
        RawMoment data (twistProfile (logTest W n) s t) c κ C ∧
        RawMoment data (scaleProfile (twistProfile (logTest W n) s t)) c κ C) →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) (σ u) (freq u)‖^2)≤
        12*(1+T)*(C*K*U^(sourceExponent r+ε)) := by
  obtain ⟨c,κ,K,hc,hc1,hκ,hK,he⟩ := no_slot_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a b B ha hab hB hφs hφB R ε hR hε
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he,eventually_ge_atTop (1 : ℝ)] with U he hU
  intro r data rows W wa wb C T σ freq hr hrR hC hT hwa hwb hWs hW hrows hσ hf hraw
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have henergy (n : ℕ) (hn : n≤2) (s : ℝ) (hs : s∈Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t∈Icc (-T) T) :
      ∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true (logTest W n) (U^r) s t‖^2≤
        C*K*U^(sourceExponent r+ε) := by
    have hlW := (logTest_support W n).trans hWs
    have htW := (twistProfile_support (logTest W n) s t).trans hlW
    have hlS := logTest_smooth W n wa wb hwa hWs hW
    have htS := twistProfile_smooth (logTest W n) s t wa wb hwa hlW hlS
    have hh := he r data rows (twistProfile (logTest W n) s t) wa wb C hr hrR hC
      hwa hwb htW htS hrows (hraw n hn s hs t ht).1 (hraw n hn s hs t ht).2
    simpa only [polynomial_twistProfile] using hh
  let Q := scaleSupport (Real.log (U^r)) wb
  have hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/(U^r))≠0 → J∈Q := by
    simpa only [Real.exp_log hD] using scaleSupport_cover W wa wb (Real.log (U^r))
      (Real.log (U^r)) hwb hWs (le_refl _)
  have hh := HeckeDetectorRowwiseMarked.marked_rowwise rows
    (fun u : FreeRow => data.character ⟨u.val,u.property.1⟩) true W (U^r) hD Q hcover
    (fun _ => 1) 0 1 (-T) T (C*K*U^(sourceExponent r+ε)) (by norm_num) (by linarith)
    σ freq hσ hf
    (by simpa only [mul_one,logTest] using henergy 0 (by omega))
    (by simpa only [mul_one,logTest] using henergy 1 (by omega))
    (by simpa only [mul_one,logTest] using henergy 2 (by omega))
  simp only [mul_one] at hh
  refine hh.trans ?_
  have hE : 0≤C*K*U^(sourceExponent r+ε) := by positivity
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeInverseAmplification.no_slot_rowwise_endpoint_oai := @OAI.SevenEighths.HeckeInverseAmplification.no_slot_rowwise_endpoint_oai
