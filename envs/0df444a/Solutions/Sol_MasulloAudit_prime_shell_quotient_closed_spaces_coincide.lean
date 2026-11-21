-- Prove2me | solution 1 for MasulloAudit.prime_shell_quotient_closed_spaces_coincide
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:19:56.945731+00:00
-- url     : https://prove2.me/submissions/c4c47a4a-cae0-4ccf-92d8-662214a64e12

import Definitions.Def_Masullo_RationalQuotientShell
import Theorems.Thm_MasulloRH_rational_idele_class_spherical_coordinates
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_MasulloAudit_rational_prime_orbital_images_after_cutoff

open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform ENNReal
open MasulloAudit.RationalQuotientShell
namespace MasulloAudit.ShellDecay
noncomputable section

-- Rational theta decay and scaled Poisson summation from the accepted
-- MasulloRH.rational_theta_test_factorization proof.
private def latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

def thetaNat (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℕ, f (((n:ℝ)+1)*x)

private lemma thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => thetaTerm_bound f 2 n hx)

private lemma thetaNat_bound (f : 𝓢(ℝ,ℂ)) (k : ℕ) (hk : 1 < k) {x : ℝ} (hx : 0 < x) :
    ‖thetaNat f x‖ ≤ (((SchwartzMap.seminorm ℝ k 0) f) * ∑' n, latticeWeight k n) * (x^k)⁻¹ := by
  apply (norm_tsum_le_tsum_norm ((thetaNat_summable f x hx).norm)).trans
  apply (Summable.tsum_le_tsum (fun n => thetaTerm_bound f k n hx) (thetaNat_summable f x hx).norm
    ((summable_latticeWeight k hk).mul_left _)).trans_eq
  rw [tsum_mul_left]; ring

lemma thetaNat_continuousOn (f : 𝓢(ℝ,ℂ)) : ContinuousOn (thetaNat f) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have hu : Summable (fun n : ℕ => (SchwartzMap.seminorm ℝ 2 0 f) * ((x/2)^2)⁻¹ * latticeWeight 2 n) :=
    (summable_latticeWeight 2 (by norm_num)).mul_left _
  have hc : ContinuousOn (thetaNat f) (Ioi (x/2)) := by
    apply continuousOn_tsum (fun n => (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn) hu
    intro n y hy
    have hx' : 0 < x/2 := by positivity
    have hy' : x/2 < y := hy
    apply (thetaTerm_bound f 2 n (lt_trans hx' hy')).trans
    gcongr
    dsimp [latticeWeight]; positivity
  exact ((hc.continuousAt (isOpen_Ioi.mem_nhds (show x/2 < x by linarith)))).continuousWithinAt

def reflectS (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

def theta (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℤ, f ((n:ℝ)*x)

lemma theta_split (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    theta f x = thetaNat (f + reflectS f) x := by
  have h₁ := thetaNat_summable f x hx
  have h₂ := thetaNat_summable (reflectS f) x hx
  have hpos : Summable (fun n : ℕ => f ((((n:ℤ)+1 : ℤ) : ℝ)*x)) := by simpa using h₁
  have hneg : Summable (fun n : ℕ => f (((-((n:ℤ)+1) : ℤ) : ℝ)*x)) := by
    apply h₂.congr
    intro n
    change f (-(((n:ℝ)+1)*x)) = _
    push_cast; congr 1; ring
  have hsum := tsum_of_add_one_of_neg_add_one (f:=fun n : ℤ => f ((n:ℝ)*x)) hpos hneg
  change (∑' n : ℤ, f ((n:ℝ)*x)) = _
  rw [hsum]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, zero_mul, hf, add_zero]
  change _ = ∑' n : ℕ, (f (((n:ℝ)+1)*x) + f (-(((n:ℝ)+1)*x)))
  rw [h₁.tsum_add (g:=fun n : ℕ => f (-(((n:ℝ)+1)*x))) h₂]
  simp only [neg_mul]

/-- Uniform positive-scale decay of the Schwartz lattice sum in every integral order above one. -/
theorem thetaSchwartz_bound (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * (x^k)⁻¹ := by
  refine ⟨(SchwartzMap.seminorm ℝ k 0) (f+reflectS f) * ∑' n, latticeWeight k n, ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n; dsimp [latticeWeight]; positivity
  · intro x hx
    change ‖theta f x‖ ≤ _
    rw [theta_split f hf hx]
    exact thetaNat_bound _ k hk hx



open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false


theorem theta_poisson_scaled (f : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, f ((n:ℝ)*a)) =
    (a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)*a⁻¹) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (a*x) := rfl
  have hscale (ξ : ℝ) : (𝓕 g) ξ = (a⁻¹:ℝ) • (𝓕 f) (ξ*a⁻¹) := by
    change 𝓕 (⇑g) ξ = (a⁻¹:ℝ) • 𝓕 (⇑f) (ξ*a⁻¹)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    let F (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*(ξ*a⁻¹)) * Complex.I) • f x
    calc
      _ = ∫ x : ℝ, F (a*x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [F]
          rw [hg]
          congr 3
          field_simp
      _ = _ := by
        have h := Measure.integral_comp_mul_left F a
        simpa only [abs_of_pos (inv_pos.mpr ha)] using h
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, hg, hscale, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  rw [← tsum_const_smul'']
  simpa [mul_comm a] using h
private theorem exp_bound (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hi : (∫ x : ℝ, g x)=0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ, ‖theta g (Real.exp t)‖ ≤ c * Real.exp (-2*|t|) := by
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0 = 0 := by
    change 𝓕 (⇑g) 0=0
    simpa [Real.fourier_real_eq_integral_exp_smul] using hi
  obtain ⟨a,ha,hA⟩ := thetaSchwartz_bound g h0 2 (by decide)
  obtain ⟨b,hb,hB⟩ := thetaSchwartz_bound (𝓕 g) hF 3 (by decide)
  refine ⟨max a b,ha.trans (le_max_left _ _),fun t => ?_⟩
  by_cases ht : 0≤t
  · rw [abs_of_nonneg ht]
    apply (hA _ (Real.exp_pos _)).trans
    rw [←Real.exp_nat_mul,←Real.exp_neg]
    push_cast
    rw [show -(2*t) = -2*t by ring];gcongr;exact le_max_left _ _
  · rw [abs_of_neg (lt_of_not_ge ht),theta,theta_poisson_scaled g (Real.exp_pos _),norm_smul,
      Real.norm_of_nonneg (inv_pos.mpr (Real.exp_pos _)).le]
    apply (mul_le_mul_of_nonneg_left (hB _ (inv_pos.mpr (Real.exp_pos t))) (inv_pos.mpr (Real.exp_pos t)).le).trans
    rw [←Real.exp_neg,←Real.exp_nat_mul,←Real.exp_neg]
    calc
      _ = b * Real.exp (-2 * -t) := by
        rw [mul_left_comm,←Real.exp_add];congr 2;push_cast;ring
      _ ≤ _ := by gcongr;exact le_max_right _ _

private theorem env_integrable : Integrable (fun t : ℝ => Real.exp (-2*|t|)) := by
  rw [←integrableOn_univ, ←Iic_union_Ioi (a:=(0:ℝ)),integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic (a:=(2:ℝ)) (by norm_num) 0).congr_fun _ measurableSet_Iic
    intro x hx;change Real.exp (2*x)=Real.exp (-2*|x|);rw [abs_of_nonpos (show x≤0 from hx)];congr 1;ring
  · apply (integrableOn_exp_mul_Ioi (a:=(-2:ℝ)) (by norm_num) 0).congr_fun _ measurableSet_Ioi
    intro x hx;change Real.exp (-2*x)=Real.exp (-2*|x|);rw [abs_of_pos (show 0<x from hx)]

theorem profile_mem (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hi : (∫ x : ℝ,g x)=0) :
    MemLp (fun t => theta g (Real.exp t)) 2 realMeasure := by
  have hm : Measurable (fun t => theta g (Real.exp t)) :=
    Measurable.tsum (fun n : ℤ => g.continuous.measurable.comp ((measurable_const.mul Real.continuous_exp.measurable) : Measurable (fun t : ℝ => (n:ℝ)*Real.exp t)))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  rw [realMeasure,integrable_withDensity_iff_integrable_smul' (f:=weight) (by unfold weight;fun_prop) (ae_of_all _ fun t => ENNReal.ofReal_lt_top)]
  obtain ⟨c,hc,hB⟩ := exp_bound g h0 hi
  apply (env_integrable.const_mul (2*c^2)).mono'
  · apply Measurable.aestronglyMeasurable
    exact ((ENNReal.measurable_toReal.comp (show Measurable weight by unfold weight;fun_prop)).smul (hm.norm.pow_const 2))
  · apply ae_of_all; intro t
    rw [weight,ENNReal.toReal_ofReal (by positivity),smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hle : 1+t^2 ≤ 2*Real.exp (2*|t|) := by
      have habs := Real.add_one_le_exp |t|
      have hone : 1≤Real.exp |t| := Real.one_le_exp (abs_nonneg t)
      have hs := sq_le_sq' (by linarith [abs_nonneg t] : -(Real.exp |t|)≤|t|) (by linarith : |t|≤Real.exp |t|)
      rw [sq_abs] at hs
      rw [show Real.exp (2*|t|)=Real.exp |t|^2 by simpa using Real.exp_nat_mul |t| 2];nlinarith
    calc
      _ ≤ (2*Real.exp (2*|t|))*(c*Real.exp (-2*|t|))^2 := by gcongr;exact hB t
      _ = _ := by
        rw [mul_pow,show Real.exp (-2*|t|)^2=Real.exp (2*(-2*|t|)) by simpa using (Real.exp_nat_mul (-2*|t|) 2).symm]
        calc
          _ = (2*c^2)*(Real.exp (2*|t|)*Real.exp (2*(-2*|t|))) := by ring
          _ = _ := by rw [←Real.exp_add,show 2*|t|+2*(-2*|t|) = -2*|t| by ring]

end
end MasulloAudit.ShellDecay

open Set Filter MeasureTheory NumberField IsDedekindDomain
open MasulloRH.RationalFinite MasulloRH.RationalClass
open MasulloAudit.RationalSphericalCutoff MasulloAudit.RationalQuotientShell
open scoped Topology SchwartzMap ENNReal
namespace MasulloAudit.ShellGeometry
noncomputable section
abbrev Chart := Multiplicative ℝ × K ≃ₜ* C
def Coordinates (e : Chart) : Prop :=
  ∀ s : Multiplicative ℝ, ∀ u : K, ∃ x : I,
    (x:Ad) = ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) (Real.exp s.toAdd)), (u.val:A)) ∧
    classOf x = e (s,u) ∧ logNorm (classOf x) = s.toAdd

private theorem ratio_const {e : Chart} (he : Coordinates e) (s : Multiplicative ℝ) (v : K) :
    logNorm (e (s,v))=s.toAdd := by
  obtain ⟨x,_,hx,ht⟩ := he s v
  simpa only [←hx] using ht
private theorem rep_exists {e : Chart} (he : Coordinates e) (y : C) :
    ∃ x : I, classOf x=y ∧ Representative (logNorm y) x := by
  obtain ⟨⟨s,u⟩,rfl⟩ := e.surjective y
  obtain ⟨x,hx,hc,ht⟩ := he s u
  refine ⟨x,hc,?_,?_,?_⟩
  · rw [hx];exact u.property.1
  · let pr : Ad →* A := MonoidHom.snd _ _
    have heq : Units.map pr x = u.val := Units.ext (congrArg Prod.snd hx)
    have hi := congrArg (fun v : Aˣ => (↑v⁻¹ : A)) heq
    change (↑x⁻¹ : Ad).2 ∈ integers
    change (↑(Units.map pr x)⁻¹ : A) ∈ integers
    rw [hi];exact u.property.2
  · rw [←hc,ht];unfold realComponent;rw [hx];simp
private theorem log_unit {e : Chart} (he : Coordinates e)
    (hu : ∀ u : K, finiteUnit u=e (1,u)) (y : C) (v : K) :
    logNorm (y*finiteUnit v)=logNorm y := by
  obtain ⟨⟨s,u⟩,rfl⟩ := e.surjective y
  rw [hu,←map_mul,show (s,u)*(1,v)=(s,u*v) by simp,ratio_const he,ratio_const he]

theorem average_eq {e : Chart} (he : Coordinates e) (hu : ∀ u : K, finiteUnit u=e (1,u))
    [MeasurableSpace K] (κ : Measure K) [IsProbabilityMeasure κ]
    {F : Ad → ℂ} (hF : F 0=0) {w : ℂ} (y : C)
    (hs : ∀ x : I, Representative (logNorm y) x →
      HasSum (fun q : ℚˣ => F (algebraMap ℚ Ad (q:ℚ)*(x:Ad))) w) :
    sphericalTheta κ F y=w := by
  have horb (v : K) : orbitTheta F (y*finiteUnit v)=w := by
    obtain ⟨x,hc,hx⟩ := rep_exists he (y*finiteUnit v)
    rw [log_unit he hu] at hx
    rw [←hc]
    change (∑' q : ℚ,F ((x:Ad)*algebraMap ℚ Ad q)) = w
    apply HasSum.tsum_eq
    apply (Units.val_injective.hasSum_iff _).mp
    · simpa only [Function.comp_def,mul_comm (x:Ad)] using hs x hx
    · intro q hq
      have hz : q=0 := by
        by_contra hn;exact hq ⟨Units.mk0 q hn,rfl⟩
      simp [hz,hF]
  simp [sphericalTheta,horb]

theorem finite_real : IsFiniteMeasureOnCompacts realMeasure := by
  constructor
  intro U hU
  obtain ⟨b,hb⟩ := hU.exists_bound_of_continuousOn (f:=fun t : ℝ => 1+t^2) (by fun_prop)
  rw [realMeasure,withDensity_apply _ hU.measurableSet]
  apply lt_of_le_of_lt (b:=∫⁻ _ in U, ENNReal.ofReal b)
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with t ht
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hb t ht))
  · rw [lintegral_const,Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU.measure_lt_top

theorem weighted_preserving [MeasurableSpace C] {ν : Measure C}
    (h : MeasurePreserving logNorm ν volume) : MeasurePreserving logNorm (classMeasure ν) realMeasure := by
  refine ⟨h.measurable,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply h.measurable hs,realMeasure,classMeasure,withDensity_apply _ hs,
    withDensity_apply _ (h.measurable hs)]
  exact h.setLIntegral_comp_preimage hs (by unfold weight;fun_prop)

end
end MasulloAudit.ShellGeometry

open MeasureTheory Set Filter NumberField IsDedekindDomain
open MasulloRH.RationalFinite MasulloRH.RationalClass
open MasulloAudit.RationalQuotientShell MasulloAudit.RationalSphericalCutoff
open MasulloAudit.ShellGeometry
open scoped ENNReal InnerProductSpace SchwartzMap
noncomputable section
local instance : SecondCountableTopology Ad := AdeleRing.secondCountableTopology ℚ
local instance : SecondCountableTopology (InfiniteAdeleRing ℚ × A) := AdeleRing.secondCountableTopology ℚ
local instance : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  (isEmbedding_prodMkLeft (0:A)).secondCountableTopology
local instance : SecondCountableTopology A :=
  (isEmbedding_prodMkRight (0:InfiniteAdeleRing ℚ)).secondCountableTopology
local instance : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _
local instance : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩
local instance : MeasurableSpace A := borel _
local instance : BorelSpace A := ⟨rfl⟩
local instance : MeasurableSpace Ad := inferInstanceAs (MeasurableSpace (InfiniteAdeleRing ℚ × A))
local instance : BorelSpace Ad := inferInstanceAs (BorelSpace (InfiniteAdeleRing ℚ × A))

private theorem closed_shell [MeasurableSpace K] [MeasurableSpace C]
    {κ : Measure K} [IsProbabilityMeasure κ] {ν : Measure C}
    (hn : MeasurePreserving logNorm (classMeasure ν) realMeasure)
    {e : Chart} (he : Coordinates e) (hu : ∀ u : K, finiteUnit u=e (1,u))
    (profile : ∀ F, Admissible F → ∃ h : ℝ → ℂ, MemLp h 2 realMeasure ∧
      ∀ z : C,sphericalTheta κ F z=h (logNorm z))
    (p : Nat.Primes) (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (ha : s ⊆ Ici a)
    (B : Set (Ad → ℂ)) (hpB : primeSources p ⊆ B) (hBA : B ⊆ {F | Admissible F}) :
    let J := Lp.compMeasurePreservingₗᵢ (E:=ℂ) (p:=2) ℂ logNorm hn
    closure (testImage κ ν s B) = J '' supported realMeasure s := by
  classical
  let J := Lp.compMeasurePreservingₗᵢ (E:=ℂ) (p:=2) ℂ logNorm hn
  change closure _=J '' _
  have hpull (w : Lp ℂ 2 realMeasure) : (J w : C → ℂ) =ᵐ[classMeasure ν] w ∘ logNorm :=
    Lp.coeFn_compMeasurePreserving w hn
  haveI : IsFiniteMeasureOnCompacts realMeasure := finite_real
  have hd := (MasulloAudit.rational_prime_orbital_images_after_cutoff p realMeasure a s hs ha).2.2.1
  have hc : IsClosed (supported realMeasure s) := hd ▸ isClosed_closure
  apply le_antisymm
  · apply closure_minimal _ (J.isometry.isClosedEmbedding.isClosedMap _ hc)
    rintro v ⟨F,hF,hmem,hv⟩
    obtain ⟨g,hg,heq⟩ := profile F (hBA hF)
    have hg' := hg.indicator hs
    let w := hg'.toLp (s.indicator g)
    have hw : (w : ℝ → ℂ) =ᵐ[realMeasure] s.indicator g := hg'.coeFn_toLp
    refine ⟨w,?_,Lp.ext ?_⟩
    · filter_upwards [hw] with t ht h
      rw [ht,indicator_of_notMem h]
    · filter_upwards [hpull w,hn.quasiMeasurePreserving.ae hw,hv] with z hz hf hv'
      change J w z=v z
      rw [hz,hv'];change w (logNorm z)=_
      rw [hf]
      by_cases h : logNorm z∈s
      · simpa only [indicator_of_mem h,indicator_of_mem (show z∈logNorm ⁻¹' s from h)] using (heq z).symm
      · rw [indicator_of_notMem h,indicator_of_notMem (show z∉logNorm ⁻¹' s from h)]
  · rw [←hd]
    apply (image_closure_subset_closure_image J.continuous).trans
    apply closure_mono
    rintro _ ⟨w,⟨F,hF,hrep⟩,rfl⟩
    have hAdm := hBA (hpB hF)
    obtain ⟨g,hg,heq⟩ := profile F hAdm
    refine ⟨F,hpB hF,?_,?_⟩
    · have hco : sphericalTheta κ F=g ∘ logNorm := funext heq
      rw [hco];exact hg.comp_measurePreserving hn
    · filter_upwards [hpull w,hn.quasiMeasurePreserving.ae hrep] with z hz h
      rw [hz];change w (logNorm z)=_
      by_cases hzs : logNorm z∈s
      · rw [indicator_of_mem (show z∈logNorm ⁻¹' s from hzs)]
        exact (average_eq he hu κ hAdm.2.1 z (h.2 hzs)).symm
      · rw [indicator_of_notMem (show z∉logNorm ⁻¹' s from hzs)]
        exact h.1 hzs

theorem solution [MeasurableSpace K] [BorelSpace K] [MeasurableSpace C] [BorelSpace C] :
    ∃ κ : Measure K, κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
    ∃ ν : Measure C, ν.IsHaarMeasure ∧ MeasurePreserving logNorm ν volume ∧
    ∃ J : Lp ℂ 2 realMeasure →ₗᵢ[ℂ] Lp ℂ 2 (classMeasure ν),
      (∀ w, (J w : C → ℂ) =ᵐ[classMeasure ν] fun z => w (logNorm z)) ∧
      (∀ F, Admissible F → MemLp (sphericalTheta κ F) 2 (classMeasure ν)) ∧
      ∀ (p : Nat.Primes) (a : ℝ) (s : Set ℝ), MeasurableSet s → s ⊆ Ici a →
        (∀ B : Set (Ad → ℂ), primeSources p ⊆ B → B ⊆ {F | Admissible F} →
          closure (testImage κ ν s B) = J '' supported realMeasure s) ∧
        closure (testImage κ ν s (primeSources p)) = closure (testImage κ ν s {F | Admissible F}) ∧
        ∀ v ∈ closure (testImage κ ν s {F | Admissible F}),
          (∀ u ∈ closure (testImage κ ν s (primeSources p)), inner ℂ u v=0) → v=0 := by
  let μ : Measure Ad := Measure.addHaar
  haveI hμ : μ.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  obtain ⟨_,_,⟨κ,hκ,hprob⟩,e,he,hu,hmeasure⟩ := MasulloRH.rational_idele_class_spherical_coordinates μ
  letI : κ.IsHaarMeasure := hκ
  letI : IsProbabilityMeasure κ := hprob
  obtain ⟨ν,hν,_,hn,_,_,image_eq,_⟩ := hmeasure κ
  have hw := weighted_preserving hn
  let J := Lp.compMeasurePreservingₗᵢ (E:=ℂ) (p:=2) ℂ logNorm hw
  refine ⟨κ,hκ,hprob,ν,hν,hn,J,fun w => Lp.coeFn_compMeasurePreserving w hw,?_,?_⟩
  all_goals
    have profile (F : Ad → ℂ) (hF : Admissible F) :
        ∃ h : ℝ → ℂ, MemLp h 2 realMeasure ∧ ∀ z,sphericalTheta κ F z=h (logNorm z) := by
      have hl : sphericalTheta κ F ∈ {φ : C → ℂ | ∃ f ∈ AdelicFourier.schwartzBruhat ℚ,
          f 0=0 ∧ (∫ x, f x ∂μ)=0 ∧ φ=sphericalTheta κ f} := ⟨F,hF.1,hF.2.1,@hF.2.2 μ hμ,rfl⟩
      rw [image_eq] at hl
      obtain ⟨g,h0,hi,hg⟩ := hl
      exact ⟨_,MasulloAudit.ShellDecay.profile_mem g h0 hi,hg⟩
  · intro F hF
    obtain ⟨g,hg,heq⟩ := profile F hF
    rw [show sphericalTheta κ F=g ∘ logNorm from funext heq]
    exact hg.comp_measurePreserving hw
  · intro p a s hs ha
    have h := closed_shell hw he hu profile p a s hs ha
    have inc : primeSources p ⊆ {F | Admissible F} := fun F hF => hF.1
    have eq := (h _ Subset.rfl inc).trans (h _ inc Subset.rfl).symm
    refine ⟨h,eq,fun v hv horth => ?_⟩
    rw [←eq] at hv
    exact inner_self_eq_zero.mp (horth v hv)
