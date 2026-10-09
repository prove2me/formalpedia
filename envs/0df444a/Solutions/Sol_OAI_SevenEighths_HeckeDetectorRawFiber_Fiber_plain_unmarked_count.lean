-- Prove2me | solution 1 for OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.plain_unmarked_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:06:18.170755+00:00
-- url     : https://prove2.me/submissions/ec977a84-f02c-4f91-8bc9-a4e980e5e126

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem Witness.frequency_bound {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) :
    |w.frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T := by
  have hnu : |w.nu|≤allowance := by simpa only [Real.norm_eq_abs] using w.nu_bound
  have hh := abs_sub_le (2*Real.pi*w.nu) 0 w.zero.im
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hnu (by positivity)) w.zero_height)

theorem Witness.real_part_upper {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : w.zero.re≤1 := by
  by_contra hn
  exact LFunction_ne_zero_of_one_lt_re (χ w.label) (lt_of_not_ge hn) w.zero_eq

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes
namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end SevenEighths.HeckeDetectorFiberSpikes

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

end SevenEighths.HeckeDetectorRowCount

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePlain
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePlain
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

lemma norm_sum_sq_le (u v : ℂ) : ‖u+v‖^2≤2*(‖u‖^2+‖v‖^2) := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v,sq_nonneg (‖u‖-‖v‖)]

theorem plain_squared_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (hE : 0≤E)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ j k : ℕ, j+k≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) false ((logProfile^[j]) W) D x y*
        polynomial (χ i) false ((logProfile^[k]) W) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) false W D (σ i) (freq i)*
      polynomial (χ i) false W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*(16*E)) := by
  let Q (n : ℕ) (i : ι) (x y : ℝ) := polynomial (χ i) false ((logProfile^[n]) W) D x y
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    if n=0 then Q 0 i x y*Q 0 i x y*P i
    else if n=1 then 2*Q 0 i x y*Q 1 i x y*P i
    else 2*(Q 1 i x y*Q 1 i x y+Q 0 i x y*Q 2 i x y)*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cq (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (Q n i)) := by
    interval_cases n
    · exact polynomial_continuous (χ i) false W D hD S hc
    · exact polynomial_continuous (χ i) false (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) false (logProfile (logProfile W)) D hD S hc2
  have qx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => Q n i u y) (-Q (n+1) i x y) x := by
    interval_cases n
    · exact polynomial_sigma_deriv (χ i) false W D x y hD S hc
    · exact polynomial_sigma_deriv (χ i) false (logProfile W) D x y hD S hc1
  have qy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (Q n i x) (I*Q (n+1) i x y) y := by
    interval_cases n
    · exact polynomial_freq_deriv (χ i) false W D x y hD S hc
    · exact polynomial_freq_deriv (χ i) false (logProfile W) D x y hD S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    have c0 := cq 0 i (by norm_num)
    have c1 := cq 1 i (by norm_num)
    have c2 := cq 2 i (by norm_num)
    change Continuous (fun p : ℝ×ℝ => M n i p.1 p.2)
    change Continuous (fun p : ℝ×ℝ => Q 0 i p.1 p.2) at c0
    change Continuous (fun p : ℝ×ℝ => Q 1 i p.1 p.2) at c1
    change Continuous (fun p : ℝ×ℝ => Q 2 i p.1 p.2) at c2
    interval_cases n <;> dsimp [M] <;> fun_prop
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · convert (preTransparency := .instances) ((qx 0 i x y (by norm_num)).mul (qx 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (preTransparency := .instances) (((qx 0 i x y (by norm_num)).mul (qx 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · convert (preTransparency := .instances) ((qy 0 i x y (by norm_num)).mul (qy 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (preTransparency := .instances) (((qy 0 i x y (by norm_num)).mul (qy 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤16*E := by
    have e00 := henergy 0 0 (by norm_num) x hx y hy
    have e01 := henergy 0 1 (by norm_num) x hx y hy
    have e11 := henergy 1 1 (by norm_num) x hx y hy
    have e02 := henergy 0 2 (by norm_num) x hx y hy
    change ∑ i∈rows, ‖Q 0 i x y*Q 0 i x y*P i‖^2≤E at e00
    change ∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2≤E at e01
    change ∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2≤E at e11
    change ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2≤E at e02
    interval_cases n
    · simpa only [M,ite_true] using e00.trans (show E≤16*E by linarith)
    · have heq : (∑ i∈rows, ‖M 1 i x y‖^2)=4*∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hm : M 1 i x y=2*(Q 0 i x y*Q 1 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
      rw [heq]
      linarith
    · have hh : (∑ i∈rows, ‖M 2 i x y‖^2)≤
          8*((∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2)+
          ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2) := by
        rw [←Finset.sum_add_distrib,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hm : M 2 i x y=2*(Q 1 i x y*Q 1 i x y*P i+Q 0 i x y*Q 2 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
        have hh := norm_sum_sq_le (Q 1 i x y*Q 1 i x y*P i) (Q 0 i x y*Q 2 i x y*P i)
        simp only [norm_mul] at hh
        nlinarith
      linarith
  simpa only [M,ite_true,Q,Function.iterate_zero,id_eq] using
    chain_rowwise rows M cm dx dy a b c d (16*E) hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwisePlain

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorFiberEnergy
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRowwisePolynomial

theorem plain_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) W) D s t*
        polynomial (χ u label) false ((logProfile^[k]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) false W D (w u).zero.re (w u).frequency*
      polynomial (χ u label) false W D (w u).zero.re (w u).frequency*P u‖^2≤
      192*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwisePlain.plain_squared_rowwise rows (fun u => χ u label) W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) hE (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf hraw
  refine hb.trans ?_
  nlinarith

end SevenEighths.HeckeDetectorFiberEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotPlainCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNoSlotPlainCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial

theorem no_slot_plain_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (εm C height : ℝ) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq‖^2≤
          C*U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))-
        2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)+4*ε+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(max 1 (2*m)+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU ha
    witness label J K hlabel hJ hK
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i ha
    witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(max 1 (2*m)+εm))
    (fun _ => 1) hDp (by norm_num) positiveAnnular_support hE height hheight hfreq
    (by simpa only [mul_one] using hraw)
  simp only [mul_one] at he
  have hs (u : Row) (hu : u∈rows) : U^(2*((2*a-1)*m-2*ε))≤
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2 := by
    rw [show 2*((2*a-1)*m-2*ε)=((2*a-1)*m-2*ε)+((2*a-1)*m-2*ε) by ring,
      Real.rpow_add hUp,norm_mul,mul_pow]
    exact mul_le_mul (hsp u hu).2.2.2 (hsp u hu).2.2.2
      (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2≤
      (192*(1+height)*C)*U^(max 1 (2*m)+εm) := by convert (preTransparency := .instances) he using 1; ring
  have hh := HeckeDetectorRowCount.card_of_energy rows _ U (2*((2*a-1)*m-2*ε))
    (max 1 (2*m)+εm) (192*(1+height)*C) hUp hs he'
  convert (preTransparency := .instances) hh using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotPlainCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount HeckeDetectorNoSlotPlainCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.plain_unmarked_count_oai (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 0≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  exact no_slot_plain_count F.rows F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    εm C height hC hh hf moments.plain_unmarked

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.plain_unmarked_count_oai.{u_1, u_2} := @OAI.SevenEighths.HeckeDetectorRawFiber.Fiber.plain_unmarked_count_oai.{u_1, u_2}
