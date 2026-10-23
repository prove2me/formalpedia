-- Prove2me | solution 1 for JHolomorphic.exists_holomorphic_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:54:36.908793+00:00
-- url     : https://prove2.me/submissions/ee68bff8-0909-4141-833e-c966f5cd78a6

import Theorems.Thm_JHolomorphic_exists_local_weak_solution
import Theorems.Thm_JHolomorphic_ae_eq_differentiableOn_of_weak_dbar_eq_zero
import Mathlib


set_option linter.all false

namespace HFDev

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Ring hom `ℂ → End_ℝ E`, `a + b i ↦ a + b J`. -/
noncomputable def cHom (J : E →L[ℝ] E) (hJ : J.comp J = -ContinuousLinearMap.id ℝ E) :
    ℂ →+* Module.End ℝ E where
  toFun c := c.re • LinearMap.id + c.im • (J : E →ₗ[ℝ] E)
  map_one' := by simp; rfl
  map_mul' a b := by
    have h2 : (J : E →ₗ[ℝ] E) * (J : E →ₗ[ℝ] E) = -LinearMap.id := by
      ext x; have := congrArg (fun T => T x) hJ; simpa using this
    simp only [Complex.mul_re, Complex.mul_im]
    ext x
    have hx : J (J x) = -x := by have := congrArg (fun T => T x) hJ; simpa using this
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe, Module.End.mul_apply, map_add, map_smul, hx]
    module
  map_zero' := by simp
  map_add' a b := by ext x; simp [add_smul]; abel

lemma exists_cframe (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (J : E →L[ℝ] E)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ E) :
    ∃ Ψ0 : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E, ∀ w, Ψ0 (Complex.I • w) = J (Ψ0 w) := by
  letI : Module ℂ E := Module.compHom E (cHom J hJ)
  have hsm : ∀ (c : ℂ) (x : E), c • x = c.re • x + c.im • J x := fun c x => rfl
  haveI : IsScalarTower ℝ ℂ E := ⟨fun r c x => by
    rw [hsm, hsm (c) x]; simp [smul_add, smul_smul, Complex.smul_re, Complex.smul_im]⟩
  haveI : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  have hfr : Module.finrank ℂ E = n := by
    have := Module.finrank_mul_finrank ℝ ℂ E
    rw [Complex.finrank_real_complex, hn] at this; omega
  have hfr' : Module.finrank ℂ E = Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := by simp [hfr]
  let L : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] E := LinearEquiv.ofFinrankEq _ _ hfr'.symm
  let Lr : EuclideanSpace ℂ (Fin n) ≃ₗ[ℝ] E := L.restrictScalars ℝ
  refine ⟨Lr.toContinuousLinearEquiv, fun w => ?_⟩
  show L (Complex.I • w) = J (L w)
  rw [map_smul, hsm]; simp

end HFDev


set_option linter.all false

namespace HFDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Weak `W^{1,1}_loc`-type package on an open set. -/
def WP (U : Set ℂ) (u us ut : ℂ → V) : Prop :=
  ContinuousOn u U ∧ (∀ K ⊆ U, IsCompact K → IntegrableOn us K) ∧
    (∀ K ⊆ U, IsCompact K → IntegrableOn ut K) ∧ JHolomorphic.HasWeakPartialsOn U u us ut

/-- test-function data -/
structure IsTest (U : Set ℂ) (φ : ℂ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  cpt : HasCompactSupport φ
  sub : tsupport φ ⊆ U

lemma int_cont {U : Set ℂ} {a : ℂ → ℝ} {f : ℂ → V} {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) (ha : ContinuousOn a U) (hz : ∀ z ∉ K, a z = 0) (hf : ContinuousOn f U) :
    Integrable (fun z => a z • f z) := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := K) ?_ (fun z hz' => by simp [hz z hz'])
  exact ((ha.mono hKU).smul (hf.mono hKU)).integrableOn_compact hK

lemma int_us {U : Set ℂ} {a : ℂ → ℝ} {f : ℂ → V} {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) (ha : ContinuousOn a U) (hz : ∀ z ∉ K, a z = 0)
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K) :
    Integrable (fun z => a z • f z) := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := K) ?_ (fun z hz' => by simp [hz z hz'])
  exact (hf K hKU hK).continuousOn_smul (ha.mono hKU) hK

lemma IsTest.cont {U : Set ℂ} {φ : ℂ → ℝ} (h : IsTest U φ) : Continuous φ := h.smooth.continuous

lemma IsTest.zero {U : Set ℂ} {φ : ℂ → ℝ} (h : IsTest U φ) : ∀ z ∉ tsupport φ, φ z = 0 :=
  fun z hz => image_eq_zero_of_notMem_tsupport hz

lemma IsTest.dzero {U : Set ℂ} {φ : ℂ → ℝ} (h : IsTest U φ) (v : ℂ) :
    ∀ z ∉ tsupport φ, fderiv ℝ φ z v = 0 := by
  intro z hz
  have : fderiv ℝ φ z = 0 := by
    by_contra hne; exact hz (support_fderiv_subset ℝ hne)
  simp [this]

lemma IsTest.dcont {U : Set ℂ} {φ : ℂ → ℝ} (h : IsTest U φ) (v : ℂ) :
    Continuous (fun z => fderiv ℝ φ z v) :=
  ((h.smooth.continuous_fderiv (by simp))).clm_apply continuous_const

lemma WP.int_d {U : Set ℂ} {u us ut : ℂ → V} (hw : WP U u us ut) {φ : ℂ → ℝ} (hφ : IsTest U φ)
    (v : ℂ) : Integrable (fun z => fderiv ℝ φ z v • u z) :=
  int_cont hφ.cpt hφ.sub (hφ.dcont v).continuousOn (hφ.dzero v) hw.1

lemma WP.int_s {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → V} (hw : WP U u us ut) {φ : ℂ → ℝ}
    (hφ : IsTest U φ) : Integrable (fun z => φ z • us z) :=
  int_us hφ.cpt hφ.sub hφ.cont.continuousOn hφ.zero hw.2.1

lemma WP.int_t {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → V} (hw : WP U u us ut) {φ : ℂ → ℝ}
    (hφ : IsTest U φ) : Integrable (fun z => φ z • ut z) :=
  int_us hφ.cpt hφ.sub hφ.cont.continuousOn hφ.zero hw.2.2.1

lemma WP.weak {U : Set ℂ} {u us ut : ℂ → V} (hw : WP U u us ut) {φ : ℂ → ℝ} (hφ : IsTest U φ) :
    (∫ z, fderiv ℝ φ z 1 • u z = -∫ z, φ z • us z) ∧
      (∫ z, fderiv ℝ φ z Complex.I • u z = -∫ z, φ z • ut z) :=
  hw.2.2.2 φ hφ.smooth hφ.cpt hφ.sub

lemma WP.of_test {U : Set ℂ} {u us ut : ℂ → V} (h1 : ContinuousOn u U)
    (h2 : ∀ K ⊆ U, IsCompact K → IntegrableOn us K)
    (h3 : ∀ K ⊆ U, IsCompact K → IntegrableOn ut K)
    (h : ∀ φ, IsTest U φ → (∫ z, fderiv ℝ φ z 1 • u z = -∫ z, φ z • us z) ∧
      (∫ z, fderiv ℝ φ z Complex.I • u z = -∫ z, φ z • ut z)) : WP U u us ut :=
  ⟨h1, h2, h3, fun φ a b c => h φ ⟨a, b, c⟩⟩

lemma WP.clm {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → V} (hw : WP U u us ut) (L : V →L[ℝ] W) :
    WP U (fun z => L (u z)) (fun z => L (us z)) (fun z => L (ut z)) := by
  refine WP.of_test (L.continuous.comp_continuousOn hw.1)
    (fun K h1 h2 => L.integrable_comp (hw.2.1 K h1 h2))
    (fun K h1 h2 => L.integrable_comp (hw.2.2.1 K h1 h2)) fun φ hφ => ?_
  have e : ∀ (a : ℂ → ℝ) (f : ℂ → V), Integrable (fun z => a z • f z) →
      ∫ z, a z • L (f z) = L (∫ z, a z • f z) := by
    intro a f hf
    rw [← L.integral_comp_comm hf]; simp
  obtain ⟨h1, h2⟩ := hw.weak hφ
  refine ⟨?_, ?_⟩
  · rw [e _ _ (hw.int_d hφ 1), e _ _ (hw.int_s hU hφ), h1, map_neg]
  · rw [e _ _ (hw.int_d hφ _), e _ _ (hw.int_t hU hφ), h2, map_neg]

lemma WP.add {U : Set ℂ} (hU : IsOpen U) {u us ut v vs vt : ℂ → V} (hu : WP U u us ut)
    (hv : WP U v vs vt) :
    WP U (fun z => u z + v z) (fun z => us z + vs z) (fun z => ut z + vt z) := by
  refine WP.of_test (hu.1.add hv.1) (fun K h1 h2 => (hu.2.1 K h1 h2).add (hv.2.1 K h1 h2))
    (fun K h1 h2 => (hu.2.2.1 K h1 h2).add (hv.2.2.1 K h1 h2)) fun φ hφ => ?_
  obtain ⟨a1, a2⟩ := hu.weak hφ
  obtain ⟨b1, b2⟩ := hv.weak hφ
  simp only [smul_add]
  refine ⟨?_, ?_⟩
  · rw [integral_add (hu.int_d hφ 1) (hv.int_d hφ 1), integral_add (hu.int_s hU hφ) (hv.int_s hU hφ),
      a1, b1, neg_add]
  · rw [integral_add (hu.int_d hφ _) (hv.int_d hφ _), integral_add (hu.int_t hU hφ) (hv.int_t hU hφ),
      a2, b2, neg_add]

lemma WP.zero (U : Set ℂ) : WP U (fun _ => (0 : V)) (fun _ => 0) (fun _ => 0) :=
  WP.of_test continuousOn_const (fun _ _ _ => integrableOn_zero) (fun _ _ _ => integrableOn_zero)
    fun φ _ => by simp

lemma WP.sum {U : Set ℂ} (hU : IsOpen U) {ι : Type*} (s : Finset ι) {u us ut : ι → ℂ → V}
    (h : ∀ i ∈ s, WP U (u i) (us i) (ut i)) :
    WP U (fun z => ∑ i ∈ s, u i z) (fun z => ∑ i ∈ s, us i z) (fun z => ∑ i ∈ s, ut i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WP.zero (V := V) U
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add hU (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma WP.congr {U : Set ℂ} {u us ut us' ut' : ℂ → V} (hw : WP U u us ut) (h1 : us = us')
    (h2 : ut = ut') : WP U u us' ut' := h1 ▸ h2 ▸ hw

/-- product of a test function with a function smooth on `U` is a test function -/
lemma IsTest.mul {U : Set ℂ} (hU : IsOpen U) {φ c : ℂ → ℝ} (hφ : IsTest U φ)
    (hc : ContDiffOn ℝ ∞ c U) : IsTest U (fun z => φ z * c z) := by
  have hts : tsupport (fun z => φ z * c z) ⊆ tsupport φ :=
    tsupport_mul_subset_left
  refine ⟨?_, hφ.cpt.mul_right, hts.trans hφ.sub⟩
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hφ.smooth.contDiffAt.mul (hc.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport φ := fun h => hz (hφ.sub h)
    rw [notMem_tsupport_iff_eventuallyEq] at hz'
    refine contDiffAt_const (c := (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hz'] with w hw
    simp [hw]

lemma IsTest.fderiv_mul {U : Set ℂ} (hU : IsOpen U) {φ c : ℂ → ℝ} (hφ : IsTest U φ)
    (hc : ContDiffOn ℝ ∞ c U) (v : ℂ) (z : ℂ) :
    fderiv ℝ (fun z => φ z * c z) z v = fderiv ℝ φ z v * c z + φ z * fderiv ℝ c z v := by
  by_cases hz : z ∈ U
  · have hcd : DifferentiableAt ℝ c z :=
      (hc.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    rw [fderiv_fun_mul (hφ.smooth.differentiable (by simp) z) hcd]
    simp; ring
  · have hz' : z ∉ tsupport φ := fun h => hz (hφ.sub h)
    have h0 : z ∉ tsupport (fun z => φ z * c z) := fun h => hz' (tsupport_mul_subset_left h)
    rw [(hφ.mul hU hc).dzero v z h0, hφ.dzero v z hz', hφ.zero z hz']
    simp

lemma WP.smul {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → V} (hw : WP U u us ut) {c : ℂ → ℝ}
    (hc : ContDiffOn ℝ ∞ c U) :
    WP U (fun z => c z • u z) (fun z => fderiv ℝ c z 1 • u z + c z • us z)
      (fun z => fderiv ℝ c z Complex.I • u z + c z • ut z) := by
  have hcc : ContinuousOn c U := hc.continuousOn
  have hdc : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ c z v) U := fun v =>
    ((hc.continuousOn_fderiv_of_isOpen hU (by simp))).clm_apply continuousOn_const
  have hloc : ∀ (v : ℂ) (f : ℂ → V), (∀ K ⊆ U, IsCompact K → IntegrableOn f K) →
      ∀ K ⊆ U, IsCompact K → IntegrableOn (fun z => fderiv ℝ c z v • u z + c z • f z) K := by
    intro v f hf K hKU hK
    exact (((hdc v).mono hKU).smul (hw.1.mono hKU)).integrableOn_compact hK |>.add
      ((hf K hKU hK).continuousOn_smul (hcc.mono hKU) hK)
  refine WP.of_test (hcc.smul hw.1) (hloc 1 us hw.2.1) (hloc _ ut hw.2.2.1) fun φ hφ => ?_
  have hψ := hφ.mul hU hc
  obtain ⟨a1, a2⟩ := hw.weak hψ
  have key : ∀ (v : ℂ) (f : ℂ → V), (∀ K ⊆ U, IsCompact K → IntegrableOn f K) →
      (∫ z, fderiv ℝ (fun z => φ z * c z) z v • u z = -∫ z, (φ z * c z) • f z) →
      ∫ z, fderiv ℝ φ z v • (c z • u z) = -∫ z, φ z • (fderiv ℝ c z v • u z + c z • f z) := by
    intro v f hf h
    have i1 : Integrable (fun z => fderiv ℝ (fun z => φ z * c z) z v • u z) := hw.int_d hψ v
    have i2 : Integrable (fun z => (φ z * fderiv ℝ c z v) • u z) :=
      int_cont hφ.cpt hφ.sub (hφ.cont.continuousOn.mul (hdc v))
        (fun z hz => by simp [hφ.zero z hz]) hw.1
    have i3 : Integrable (fun z => (φ z * c z) • f z) :=
      int_us hφ.cpt hφ.sub (hφ.cont.continuousOn.mul hcc) (fun z hz => by simp [hφ.zero z hz]) hf
    have e1 : (fun z => fderiv ℝ φ z v • (c z • u z)) =
        fun z => fderiv ℝ (fun z => φ z * c z) z v • u z - (φ z * fderiv ℝ c z v) • u z := by
      funext z; rw [hφ.fderiv_mul hU hc v z, smul_smul, ← sub_smul]; congr 1; ring
    have e2 : (fun z => φ z • (fderiv ℝ c z v • u z + c z • f z)) =
        fun z => (φ z * fderiv ℝ c z v) • u z + (φ z * c z) • f z := by
      funext z; rw [smul_add, smul_smul, smul_smul]
    rw [e1, e2, integral_sub i1 i2, integral_add i2 i3, h]; abel
  exact ⟨key 1 us hw.2.1 a1, key _ ut hw.2.2.1 a2⟩

lemma WP.congr' {U : Set ℂ} {u us ut u' us' ut' : ℂ → V} (hw : WP U u us ut) (h0 : EqOn u u' U)
    (h1 : EqOn us us' U) (h2 : EqOn ut ut' U) : WP U u' us' ut' := by
  refine WP.of_test (hw.1.congr h0.symm) (fun K hK hc => (hw.2.1 K hK hc).congr_fun (h1.mono hK)
    hc.measurableSet) (fun K hK hc => (hw.2.2.1 K hK hc).congr_fun (h2.mono hK)
    hc.measurableSet) fun φ hφ => ?_
  obtain ⟨a1, a2⟩ := hw.weak hφ
  have e : ∀ (a : ℂ → ℝ) (f f' : ℂ → V), (∀ z ∉ tsupport φ, a z = 0) → EqOn f f' U →
      (fun z => a z • f' z) = fun z => a z • f z := by
    intro a f f' ha hf; funext z
    by_cases hz : z ∈ U
    · rw [hf hz]
    · rw [ha z (fun h => hz (hφ.sub h))]; simp
  rw [e _ _ _ (hφ.dzero 1) h0, e _ _ _ (hφ.dzero _) h0, e _ _ _ hφ.zero h1, e _ _ _ hφ.zero h2]
  exact ⟨a1, a2⟩

abbrev Cn (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- multiplication by `i` -/
noncomputable def Li (n : ℕ) : Cn n →L[ℝ] Cn n := ContinuousLinearMap.lsmul ℝ ℂ Complex.I

@[simp] lemma Li_apply (n : ℕ) (v : Cn n) : Li n v = Complex.I • v := rfl

lemma WP.csmul {n : ℕ} {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → Cn n} (hw : WP U u us ut)
    {c : ℂ → ℂ} (hc : ContDiffOn ℝ ∞ c U) :
    WP U (fun z => c z • u z) (fun z => fderiv ℝ c z 1 • u z + c z • us z)
      (fun z => fderiv ℝ c z Complex.I • u z + c z • ut z) := by
  have hre : ContDiffOn ℝ ∞ (fun z => (c z).re) U := Complex.reCLM.contDiff.comp_contDiffOn hc
  have him : ContDiffOn ℝ ∞ (fun z => (c z).im) U := Complex.imCLM.contDiff.comp_contDiffOn hc
  have h := (hw.smul hU hre).add hU ((hw.clm hU (Li n)).smul hU him)
  have hd : ∀ z ∈ U, ∀ v : ℂ, fderiv ℝ (fun z => (c z).re) z v = (fderiv ℝ c z v).re ∧
      fderiv ℝ (fun z => (c z).im) z v = (fderiv ℝ c z v).im := by
    intro z hz v
    have hcd : DifferentiableAt ℝ c z := (hc.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    refine ⟨?_, ?_⟩
    · rw [show (fun z => (c z).re) = Complex.reCLM ∘ c from rfl,
        (Complex.reCLM.hasFDerivAt.comp z hcd.hasFDerivAt).fderiv]; simp
    · rw [show (fun z => (c z).im) = Complex.imCLM ∘ c from rfl,
        (Complex.imCLM.hasFDerivAt.comp z hcd.hasFDerivAt).fderiv]; simp
  have ce : ∀ (a : ℂ) (x : Cn n), a • x = a.re • x + a.im • (Complex.I • x) := by
    intro a x
    conv_lhs => rw [← Complex.re_add_im a]
    rw [add_smul, mul_comm, mul_smul]; norm_cast
    congr 1; exact smul_comm _ _ _
  refine h.congr' (fun z _ => (ce _ _).symm) (fun z hz => ?_) (fun z hz => ?_)
  · simp only [Li_apply, (hd z hz 1).1, (hd z hz 1).2, ce (fderiv ℝ c z 1), ce (c z), smul_add]; abel
  · simp only [Li_apply, (hd z hz _).1, (hd z hz _).2, ce (fderiv ℝ c z _), ce (c z), smul_add]; abel

lemma WP.weak_dbar {n : ℕ} {U : Set ℂ} (hU : IsOpen U) {F Fs Ft : ℂ → Cn n} (hw : WP U F Fs Ft)
    (h0 : ∀ᵐ z ∂(volume.restrict U), Fs z + Complex.I • Ft z = 0) (φ : ℂ → ℝ)
    (hφ : IsTest U φ) :
    ∫ z, (fderiv ℝ φ z 1 • F z + fderiv ℝ φ z Complex.I • (Complex.I • F z)) = 0 := by
  obtain ⟨a1, a2⟩ := hw.weak hφ
  have i1 := hw.int_d hφ 1
  have i2 := hw.int_d hφ Complex.I
  have i3 := hw.int_s hU hφ
  have i4 := hw.int_t hU hφ
  have e : (fun z => fderiv ℝ φ z Complex.I • (Complex.I • F z)) =
      fun z => Complex.I • (fderiv ℝ φ z Complex.I • F z) := by
    funext z; rw [smul_comm]
  have hz : ∫ z, φ z • (Fs z + Complex.I • Ft z) = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [ae_restrict_iff' hU.measurableSet] at h0
    filter_upwards [h0] with z hz
    by_cases hzU : z ∈ U
    · rw [hz hzU, smul_zero]; rfl
    · rw [hφ.zero z (fun h => hzU (hφ.sub h)), zero_smul]; rfl
  have e2 : (fun z => φ z • (Fs z + Complex.I • Ft z)) =
      fun z => φ z • Fs z + Complex.I • (φ z • Ft z) := by
    funext z; rw [smul_add, smul_comm]
  have i5 : Integrable (fun z => Complex.I • (φ z • Ft z)) := i4.smul Complex.I
  have i6 : Integrable (fun z => Complex.I • (fderiv ℝ φ z Complex.I • F z)) := i2.smul Complex.I
  rw [e2, integral_add i3 i5, integral_smul] at hz
  rw [integral_add i1 (by rw [e]; exact i6), e, integral_smul, a1, a2]
  rw [smul_neg, ← neg_add, hz, neg_zero]

end HFDev


set_option linter.all false

namespace HFDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

lemma weyl_ball {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (F : ℂ → Cn n) (hF : ContinuousOn F (closedBall 0 ρ))
    (hweak : ∀ φ : ℂ → ℝ, IsTest (ball 0 ρ) φ →
      ∫ z, (fderiv ℝ φ z 1 • F z + fderiv ℝ φ z Complex.I • (Complex.I • F z)) = 0) :
    ∃ f : ℂ → Cn n, DifferentiableOn ℂ f (ball 0 ρ) ∧ EqOn F f (ball 0 ρ) := by
  set u : ℂ → Cn n := fun z => F (ρ • z) with hu
  have hmaps : ∀ z ∈ closedBall (0:ℂ) 1, ρ • z ∈ closedBall (0:ℂ) ρ := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at hz ⊢
    nlinarith
  have hmaps' : ∀ z ∈ ball (0:ℂ) 1, ρ • z ∈ ball (0:ℂ) ρ := by
    intro z hz
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at hz ⊢
    nlinarith
  have huc : ContinuousOn u (closedBall 0 1) :=
    hF.comp (continuous_const_smul ρ).continuousOn hmaps
  have hui : IntegrableOn u (ball 0 1) :=
    (huc.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  have hρ' : ρ⁻¹ ≠ 0 := inv_ne_zero hρ.ne'
  have hW : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      ∫ z, (fderiv ℝ φ z 1 • u z + fderiv ℝ φ z Complex.I • (Complex.I • u z)) = 0 := by
    intro φ hφs hφc hφt
    set ψ : ℂ → ℝ := fun w => φ (ρ⁻¹ • w) with hψ
    have hψs : ContDiff ℝ ∞ ψ := hφs.comp (contDiff_const_smul _)
    have hψt : tsupport ψ ⊆ ball 0 ρ := by
      have hsub : tsupport ψ ⊆ (fun w : ℂ => ρ⁻¹ • w) ⁻¹' tsupport φ := by
        refine closure_minimal ?_ ((isClosed_tsupport φ).preimage (continuous_const_smul _))
        intro w hw; exact subset_tsupport _ hw
      intro w hw
      have := hφt (hsub hw)
      simp only [mem_preimage, mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hρ] at this ⊢
      rwa [inv_mul_lt_iff₀ hρ, mul_one] at this
    have hψT : IsTest (ball 0 ρ) ψ := ⟨hψs, hφc.comp_smul hρ', hψt⟩
    have hdψ : ∀ w v : ℂ, fderiv ℝ ψ w v = ρ⁻¹ * fderiv ℝ φ (ρ⁻¹ • w) v := by
      intro w v
      have hd : HasFDerivAt ψ ((fderiv ℝ φ (ρ⁻¹ • w)).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ ℂ)) w :=
        (hφs.differentiable (by simp) _).hasFDerivAt.comp w
          ((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_smul ρ⁻¹)
      rw [hd.fderiv]; simp [map_smul]
    have h0 := hweak ψ hψT
    set G : ℂ → Cn n := fun w =>
      fderiv ℝ φ (ρ⁻¹ • w) 1 • F w + fderiv ℝ φ (ρ⁻¹ • w) Complex.I • (Complex.I • F w) with hG
    have e1 : (fun z => fderiv ℝ φ z 1 • u z + fderiv ℝ φ z Complex.I • (Complex.I • u z)) =
        fun z => G (ρ • z) := by
      funext z; simp only [hG, hu, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    have e2 : G = fun w => ρ • (fderiv ℝ ψ w 1 • F w + fderiv ℝ ψ w Complex.I • (Complex.I • F w)) := by
      funext w; simp only [hG, hdψ, smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
    rw [e1, Measure.integral_comp_smul, e2, integral_smul, h0, smul_zero, smul_zero]

  obtain ⟨v, hv, hae⟩ := JHolomorphic.ae_eq_differentiableOn_of_weak_dbar_eq_zero n u hui hW
  · have heq : EqOn u v (ball 0 1) :=
      Measure.eqOn_open_of_ae_eq hae isOpen_ball (huc.mono ball_subset_closedBall) hv.continuousOn
    refine ⟨fun w => v ((ρ⁻¹ : ℂ) * w), ?_, fun w hw => ?_⟩
    · refine hv.comp (differentiableOn_const _ |>.mul differentiableOn_id) fun w hw => ?_
      simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, norm_inv, Real.norm_eq_abs,
        abs_of_pos hρ] at hw ⊢
      rw [inv_mul_lt_iff₀ hρ]; simpa using hw
    · have hw' : ρ⁻¹ • w ∈ ball (0:ℂ) 1 := by
        simp only [mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hρ] at hw ⊢
        rw [inv_mul_lt_iff₀ hρ]; simpa using hw
      have := heq hw'
      simp only [hu, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] at this
      rw [this, Complex.real_smul]; push_cast; rfl

end HFDev


set_option linter.all false

namespace HFDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma frame_data (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (Jbar A : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (hA : ContDiffOn ℝ ∞ A (ball 0 1)) (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) + A z (h z) = 0) :
    ∃ r > (0:ℝ), r < 1 ∧ ∃ (Ψ : ℂ → Cn n →L[ℝ] E) (g : ℂ → Cn n) (K : ℝ),
      (∀ z ∈ ball (0:ℂ) r, ∃ e : Cn n ≃L[ℝ] E, (e : Cn n →L[ℝ] E) = Ψ z) ∧
      ContinuousOn Ψ (ball 0 r) ∧
      (∀ z ∈ ball (0:ℂ) r, ∀ w, Ψ z (Complex.I • w) = Jbar z (Ψ z w)) ∧
      ContDiffOn ℝ ∞ g (ball 0 r) ∧
      (∀ z ∈ ball (0:ℂ) r, h z = Ψ z (g z)) ∧
      (∀ z ∈ ball (0:ℂ) r, ‖fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I‖ ≤ K * ‖g z‖) := by
  have h0 : (0:ℂ) ∈ ball (0:ℂ) 1 := mem_ball_self one_pos
  obtain ⟨Ψ0, hΨ0⟩ := exists_cframe n hn (Jbar 0) (hJbar2 0 h0)
  have JJ : ∀ z ∈ ball (0:ℂ) 1, ∀ x, Jbar z (Jbar z x) = -x := by
    intro z hz x; have := congrArg (fun T => T x) (hJbar2 z hz); simpa using this
  set P0 : Cn n →L[ℝ] E := (Ψ0 : Cn n →L[ℝ] E) with hP0
  set Ψ : ℂ → Cn n →L[ℝ] E := fun z => (1/2 : ℝ) • (P0 - (Jbar z).comp (P0.comp (Li n))) with hΨ
  have hΨapp : ∀ z w, Ψ z w = (1/2:ℝ) • (Ψ0 w - Jbar z (Ψ0 (Complex.I • w))) := by
    intro z w; simp [hΨ, hP0]
  have hΨ00 : Ψ 0 = P0 := by
    ext w
    rw [hΨapp, hΨ0, JJ 0 h0]; simp [hP0]; module
  have hcx : ∀ z ∈ ball (0:ℂ) 1, ∀ w, Ψ z (Complex.I • w) = Jbar z (Ψ z w) := by
    intro z hz w
    rw [hΨapp, hΨapp, smul_smul, Complex.I_mul_I, neg_one_smul, Ψ0.map_neg, (Jbar z).map_smul,
      (Jbar z).map_sub, JJ z hz, (Jbar z).map_neg]
    module
  have hΨs : ContDiffOn ℝ ∞ Ψ (ball 0 1) :=
    (contDiffOn_const.sub (hJbar.clm_comp contDiffOn_const)).const_smul _
  -- invertibility near 0
  have hopen := ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Cn n) (F := E)
  have hcont0 : ContinuousAt Ψ 0 := (hΨs.contDiffAt (isOpen_ball.mem_nhds h0)).continuousAt
  have hmem : Ψ ⁻¹' (range ((↑) : (Cn n ≃L[ℝ] E) → Cn n →L[ℝ] E)) ∈ 𝓝 (0:ℂ) :=
    hcont0.preimage_mem_nhds (hopen.mem_nhds ⟨Ψ0, hΨ00.symm⟩)
  obtain ⟨r0, hr0, hr0s⟩ := Metric.mem_nhds_iff.1 hmem
  set r1 := min r0 (1/2) with hr1
  have hr1p : 0 < r1 := lt_min hr0 (by norm_num)
  have hr1b : ball (0:ℂ) r1 ⊆ ball 0 1 := ball_subset_ball (by rw [hr1]; linarith [min_le_right r0 (1/2:ℝ)])
  have hiso : ∀ z ∈ ball (0:ℂ) r1, ∃ e : Cn n ≃L[ℝ] E, (e : Cn n →L[ℝ] E) = Ψ z := by
    intro z hz
    obtain ⟨e, he⟩ := hr0s (ball_subset_ball (min_le_left _ _) hz)
    exact ⟨e, he⟩
  set Ψi : ℂ → E →L[ℝ] Cn n := fun z => (Ψ z).inverse with hΨi
  have hΨiat : ∀ z ∈ ball (0:ℂ) r1, ContDiffAt ℝ ∞ Ψi z := by
    intro z hz
    obtain ⟨e, he⟩ := hiso z hz
    have h1 : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (Ψ z) := he ▸ contDiffAt_map_inverse e
    exact h1.comp z (hΨs.contDiffAt (isOpen_ball.mem_nhds (hr1b hz)))
  have hΨΨi : ∀ z ∈ ball (0:ℂ) r1, ∀ x, Ψ z (Ψi z x) = x := by
    intro z hz x; obtain ⟨e, he⟩ := hiso z hz
    simp only [hΨi, ← he, ContinuousLinearMap.inverse_equiv]; simp
  have hΨiΨ : ∀ z ∈ ball (0:ℂ) r1, ∀ x, Ψi z (Ψ z x) = x := by
    intro z hz x; obtain ⟨e, he⟩ := hiso z hz
    simp only [hΨi, ← he, ContinuousLinearMap.inverse_equiv]; simp
  set g : ℂ → Cn n := fun z => Ψi z (h z) with hg
  have hgat : ∀ z ∈ ball (0:ℂ) r1, ContDiffAt ℝ ∞ g z := fun z hz =>
    (hΨiat z hz).clm_apply (hh.contDiffAt (isOpen_ball.mem_nhds (hr1b hz)))
  have hgs : ContDiffOn ℝ ∞ g (ball 0 r1) := fun z hz => (hgat z hz).contDiffWithinAt
  have hhg : ∀ z ∈ ball (0:ℂ) r1, h z = Ψ z (g z) := fun z hz => (hΨΨi z hz _).symm
  -- the matrix `M`
  set M : ℂ → Cn n →L[ℝ] Cn n := fun z => -((Ψi z).comp (fderiv ℝ Ψ z 1 +
    (Jbar z).comp (fderiv ℝ Ψ z Complex.I) + (A z).comp (Ψ z))) with hM
  have hdg : ∀ z ∈ ball (0:ℂ) r1,
      fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I = M z (g z) := by
    intro z hz
    have hz1 := hr1b hz
    have hgd : HasFDerivAt g (fderiv ℝ g z) z :=
      ((hgat z hz).differentiableAt (by simp)).hasFDerivAt
    have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ z) z :=
      ((hΨs.contDiffAt (isOpen_ball.mem_nhds hz1)).differentiableAt (by simp)).hasFDerivAt
    have H := hΨd.clm_apply hgd
    have hev : h =ᶠ[𝓝 z] fun y => Ψ y (g y) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy using hhg y hy
    have hD := (H.congr_of_eventuallyEq hev).fderiv
    have e0 := heq z hz1
    rw [hD, hhg z hz] at e0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.flip_apply] at e0
    have key : Ψ z (fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I) = Ψ z (M z (g z)) := by
      rw [map_add, hcx z hz1, hM]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.add_apply, map_neg, hΨΨi z hz]
      rw [map_add] at e0
      rw [eq_neg_iff_add_eq_zero, ← e0]; abel
    have := congrArg (Ψi z) key
    rwa [hΨiΨ z hz, hΨiΨ z hz] at this
  -- bound for `M`
  have hMc : ContinuousOn M (ball 0 r1) := by
    have hfd : ContinuousOn (fderiv ℝ Ψ) (ball 0 1) :=
      hΨs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
    have hΨic : ContinuousOn Ψi (ball 0 r1) := fun z hz => (hΨiat z hz).continuousAt.continuousWithinAt
    refine ContinuousOn.neg (hΨic.clm_comp ?_)
    refine ((hfd.mono hr1b).clm_apply continuousOn_const).add
      ((hJbar.continuousOn.mono hr1b).clm_comp ((hfd.mono hr1b).clm_apply continuousOn_const)) |>.add
      ((hA.continuousOn.mono hr1b).clm_comp (hΨs.continuousOn.mono hr1b))
  have hsub : closedBall (0:ℂ) (r1/2) ⊆ ball 0 r1 := closedBall_subset_ball (by linarith)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0:ℂ) (r1/2)).exists_bound_of_continuousOn (hMc.mono hsub)
  refine ⟨r1/2, by linarith, by linarith [min_le_right r0 (1/2:ℝ)], Ψ, g, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z hz => hiso z (ball_subset_ball (by linarith) hz)
  · exact hΨs.continuousOn.mono ((ball_subset_ball (by linarith)).trans hr1b)
  · exact fun z hz => hcx z (hr1b (ball_subset_ball (by linarith) hz))
  · exact hgs.mono (ball_subset_ball (by linarith))
  · exact fun z hz => hhg z (ball_subset_ball (by linarith) hz)
  · intro z hz
    rw [hdg z (ball_subset_ball (by linarith) hz)]
    exact ((M z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hK z (ball_subset_closedBall hz)) (norm_nonneg _))

end HFDev


set_option linter.all false

namespace HFDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ComplexConjugate

noncomputable def cjL (n : ℕ) : Cn n ≃ₗᵢ[ℝ] Cn n :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => Complex.conjLIE)

@[simp] lemma cjL_apply (n : ℕ) (x : Cn n) (j : Fin n) : (cjL n x) j = conj (x j) := by simp [cjL]

lemma inner_cjL (n : ℕ) (x y : Cn n) : inner ℂ (cjL n x) y = ∑ j, x j * y j := by
  simp [cjL, PiLp.inner_apply, mul_comm]

/-- `P i k v = v_k e_i` -/
noncomputable def Pm {n : ℕ} (i k : Fin n) : Cn n →L[ℝ] Cn n :=
  ((EuclideanSpace.proj k : Cn n →L[ℂ] ℂ).smulRight (EuclideanSpace.single i (1:ℂ))).restrictScalars ℝ

@[simp] lemma Pm_apply {n : ℕ} (i k : Fin n) (v : Cn n) :
    Pm i k v = v k • EuclideanSpace.single i (1:ℂ) := by simp [Pm]

lemma Pm_I {n : ℕ} (i k : Fin n) (v : Cn n) : Pm i k (Complex.I • v) = Complex.I • Pm i k v := by
  simp [smul_smul]

lemma coord_contDiffOn {n : ℕ} {U : Set ℂ} {g : ℂ → Cn n} (hg : ContDiffOn ℝ ∞ g U) (k : Fin n) :
    ContDiffOn ℝ ∞ (fun z => g z k) U :=
  ((EuclideanSpace.proj k : Cn n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hg

lemma coord_fderiv {n : ℕ} {g : ℂ → Cn n} {z : ℂ} (hg : DifferentiableAt ℝ g z) (k : Fin n) (v : ℂ) :
    fderiv ℝ (fun z => g z k) z v = (fderiv ℝ g z v) k := by
  have := (((EuclideanSpace.proj k : Cn n →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt).comp z
    hg.hasFDerivAt
  rw [show (fun z => g z k) = ((EuclideanSpace.proj k : Cn n →L[ℂ] ℂ).restrictScalars ℝ) ∘ g
    from rfl, this.fderiv]
  simp

lemma coord_continuousOn {n : ℕ} {U : Set ℂ} {g : ℂ → Cn n} (hg : ContinuousOn g U) (k : Fin n) :
    ContinuousOn (fun z => g z k) U :=
  (EuclideanSpace.proj k : Cn n →L[ℂ] ℂ).continuous.comp_continuousOn hg

end HFDev


set_option linter.all false

namespace HFDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ComplexConjugate

theorem main_hf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar A : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (hA : ContDiffOn ℝ ∞ A (ball 0 1)) (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) + A z (h z) = 0) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z) ∧
          ∀ w, Φ z (Complex.I • w) = Jbar z (Φ z w)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, h z = Φ z (f z) := by
  obtain ⟨r, hr, hr1, Ψ, g, K, hiso, hΨc, hcx, hgs, hhg, hK⟩ :=
    frame_data n hn Jbar A hJbar hJbar2 hA h hh heq
  have hgc : ContinuousOn g (ball 0 r) := hgs.continuousOn
  have hgd : ∀ z ∈ ball (0:ℂ) r, DifferentiableAt ℝ g z := fun z hz =>
    (hgs.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  set a : ℂ → Cn n := fun z => fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I with ha
  have hac : ContinuousOn a (ball 0 r) := by
    have hfd : ContinuousOn (fderiv ℝ g) (ball 0 r) :=
      hgs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
    exact (hfd.clm_apply continuousOn_const).add
      ((hfd.clm_apply continuousOn_const).const_smul Complex.I)
  set S : Set ℂ := ball 0 r ∩ g ⁻¹' {0}ᶜ with hS
  have hSo : IsOpen S := hgc.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  set Bf : ℂ → Cn n →L[ℝ] Cn n := fun z =>
    ((innerSL ℂ (cjL n ((‖g z‖ ^ 2)⁻¹ • a z))).smulRight (cjL n (g z))).restrictScalars ℝ with hBf
  have hBfapp : ∀ z v, Bf z v = ((‖g z‖ ^ 2)⁻¹ * ∑ j, a z j * v j : ℂ) • cjL n (g z) := by
    intro z v
    simp only [hBf, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, map_smul]
    rw [show ((‖g z‖ ^ 2)⁻¹ : ℝ) • cjL n (a z) = (((‖g z‖ ^ 2)⁻¹ : ℝ) : ℂ) • cjL n (a z) from
      (Complex.coe_smul _ _).symm, inner_smul_left, inner_cjL]
    simp
  have hKa : ∀ z ∈ ball (0:ℂ) r, ‖a z‖ ≤ K * ‖g z‖ := hK
  set K' := max K 0 with hK'
  have hBfb : ∀ z ∈ S, ‖Bf z‖ ≤ K' := by
    intro z hz
    have hg0 : g z ≠ 0 := hz.2
    have hgn : 0 < ‖g z‖ := norm_pos_iff.2 hg0
    simp only [hBf, ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_smulRight_apply,
      innerSL_apply_norm, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    calc (‖g z‖ ^ 2)⁻¹ * ‖a z‖ * ‖g z‖ ≤ (‖g z‖ ^ 2)⁻¹ * (K * ‖g z‖) * ‖g z‖ := by
          gcongr; exact hKa z hz.1
      _ = K := by field_simp
      _ ≤ K' := le_max_left _ _
  set B : ℂ → Cn n →L[ℝ] Cn n := S.indicator Bf with hB
  have hBb : ∀ z, ‖B z‖ ≤ K' := by
    intro z
    by_cases hz : z ∈ S
    · rw [hB, indicator_of_mem hz]; exact hBfb z hz
    · rw [hB, indicator_of_notMem hz, norm_zero]; exact le_max_right _ _
  have hBfc : ContinuousOn Bf S := by
    refine (continuousOn_clm_apply (𝕜 := ℝ) (E := Cn n) (F := Cn n)).2 fun v => ?_
    simp only [hBfapp]
    have hgS : ContinuousOn g S := hgc.mono inter_subset_left
    have haS : ContinuousOn a S := hac.mono inter_subset_left
    refine ContinuousOn.smul (M := ℂ) ?_ ((cjL n).continuous.comp_continuousOn hgS)
    refine ContinuousOn.mul ?_ (continuousOn_finset_sum _ fun j _ =>
      (coord_continuousOn haS j).mul continuousOn_const)
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.inv₀ ((continuous_norm.comp_continuousOn hgS).pow 2) fun z hz => ?_
    exact pow_ne_zero _ (norm_ne_zero_iff.2 hz.2)
  have hBm : AEStronglyMeasurable B volume :=
    (aestronglyMeasurable_indicator_iff hSo.measurableSet).2 (hBfc.aestronglyMeasurable hSo.measurableSet)
  haveI : IsFiniteMeasure (volume.restrict (ball (0:ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hBmem : MemLp B (ENNReal.ofReal 3) (volume.restrict (ball 0 1)) :=
    MemLp.of_bound hBm.restrict K' (Eventually.of_forall hBb)
  have hθ := fun i : Fin n => JHolomorphic.exists_local_weak_solution n 3 (by norm_num) B hBmem
    (EuclideanSpace.single i 1)
  obtain ⟨ε, hεall, hεpos, hεr⟩ := ((Filter.eventually_all.2 hθ).and (Ioo_mem_nhdsGT hr)).exists
  choose θ hθc hθ0 θs θt hθw hθm hθsm hθtm hθeq using hεall
  have hεb : ball (0:ℂ) ε ⊆ ball 0 r := ball_subset_ball hεr.le
  haveI : IsFiniteMeasure (volume.restrict (ball (0:ℂ) ε)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hint : ∀ {f : ℂ → Cn n}, MemLp f (ENNReal.ofReal 3) (volume.restrict (ball 0 ε)) →
      ∀ K ⊆ ball (0:ℂ) ε, IsCompact K → IntegrableOn f K := fun {f} hf K hK _ =>
    (show IntegrableOn f (ball (0:ℂ) ε) volume from
      hf.integrable (by rw [ENNReal.one_le_ofReal]; norm_num)).mono_set hK
  have hWθ : ∀ i, WP (ball 0 ε) (θ i) (θs i) (θt i) := fun i =>
    ⟨hθc i, hint (hθsm i), hint (hθtm i), hθw i⟩
  have hgε : ContDiffOn ℝ ∞ g (ball 0 ε) := hgs.mono hεb
  have hterm : ∀ i k, WP (ball 0 ε) (fun z => g z k • Pm i k (θ i z))
      (fun z => fderiv ℝ g z 1 k • Pm i k (θ i z) + g z k • Pm i k (θs i z))
      (fun z => fderiv ℝ g z Complex.I k • Pm i k (θ i z) + g z k • Pm i k (θt i z)) := by
    intro i k
    refine (((hWθ i).clm isOpen_ball (Pm i k)).csmul isOpen_ball (coord_contDiffOn hgε k)).congr'
      (fun _ _ => rfl) (fun z hz => ?_) (fun z hz => ?_)
    · simp only [coord_fderiv (hgd z (hεb hz))]
    · simp only [coord_fderiv (hgd z (hεb hz))]
  have hFw := WP.sum isOpen_ball Finset.univ
    (u := fun i z => ∑ k, g z k • Pm i k (θ i z))
    (us := fun i z => ∑ k, (fderiv ℝ g z 1 k • Pm i k (θ i z) + g z k • Pm i k (θs i z)))
    (ut := fun i z => ∑ k, (fderiv ℝ g z Complex.I k • Pm i k (θ i z) + g z k • Pm i k (θt i z)))
    (fun i _ => WP.sum isOpen_ball Finset.univ (fun k _ => hterm i k))
  have hgsq : ∀ x : Cn n, ∑ k, x k * conj (x k) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [EuclideanSpace.norm_sq_eq]; push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hae : ∀ᵐ z ∂(volume.restrict (ball (0:ℂ) ε)),
      (∑ i, ∑ k, (fderiv ℝ g z 1 k • Pm i k (θ i z) + g z k • Pm i k (θs i z))) +
      Complex.I • (∑ i, ∑ k, (fderiv ℝ g z Complex.I k • Pm i k (θ i z) +
        g z k • Pm i k (θt i z))) = 0 := by
    filter_upwards [ae_all_iff.2 hθeq, self_mem_ae_restrict measurableSet_ball] with z hz hzb
    have e1 : ∀ i k, (fderiv ℝ g z 1 k • Pm i k (θ i z) + g z k • Pm i k (θs i z)) +
        Complex.I • (fderiv ℝ g z Complex.I k • Pm i k (θ i z) + g z k • Pm i k (θt i z)) =
        (a z k * θ i z k - g z k * (B z (θ i z)) k) • EuclideanSpace.single i (1:ℂ) := by
      intro i k
      have h1 : θs i z = -B z (θ i z) - Complex.I • θt i z := by
        rw [← sub_eq_zero, ← hz i]; abel
      have h2 : a z k = fderiv ℝ g z 1 k + Complex.I * fderiv ℝ g z Complex.I k := by simp [ha]
      rw [h1, h2]
      simp only [Pm_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      module
    simp only [Finset.smul_sum, ← Finset.sum_add_distrib, e1, ← Finset.sum_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    suffices hs : ∑ k, (a z k * θ i z k - g z k * (B z (θ i z)) k) = 0 by rw [hs, zero_smul]
    by_cases hzS : z ∈ S
    · rw [hB, indicator_of_mem hzS, hBfapp]
      simp only [PiLp.smul_apply, cjL_apply, smul_eq_mul, Finset.sum_sub_distrib]
      have hg0 : ‖g z‖ ≠ 0 := norm_ne_zero_iff.2 hzS.2
      simp_rw [mul_left_comm (g z _), ← Finset.mul_sum]
      rw [hgsq (g z)]
      have h3 : ((‖g z‖ ^ 2)⁻¹ : ℝ) * (‖g z‖ ^ 2) = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hg0)
      have hc : (((‖g z‖ ^ 2)⁻¹ : ℝ) : ℂ) * (((‖g z‖ ^ 2) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, h3, Complex.ofReal_one]
      linear_combination (-(∑ j, a z j * θ i z j)) * hc
    · have hg0 : g z = 0 := by
        by_contra hne; exact hzS ⟨hεb hzb, hne⟩
      have ha0 : a z = 0 := by
        have := hKa z (hεb hzb); rw [hg0, norm_zero, mul_zero] at this
        exact norm_le_zero_iff.1 this
      simp [hg0, ha0]
  set F : ℂ → Cn n := fun z => ∑ i, ∑ k, g z k • Pm i k (θ i z) with hF
  have hweak : ∀ φ : ℂ → ℝ, IsTest (ball 0 (ε/2)) φ →
      ∫ z, (fderiv ℝ φ z 1 • F z + fderiv ℝ φ z Complex.I • (Complex.I • F z)) = 0 :=
    fun φ hφ => hFw.weak_dbar isOpen_ball hae φ
      ⟨hφ.smooth, hφ.cpt, hφ.sub.trans (ball_subset_ball (by linarith))⟩
  have hFc : ContinuousOn F (closedBall 0 (ε/2)) := hFw.1.mono (closedBall_subset_ball (by linarith))
  obtain ⟨f, hfd, hFf⟩ := weyl_ball (by linarith : (0:ℝ) < ε/2) F hFc hweak
  set Θ : ℂ → Cn n →L[ℝ] Cn n := fun z => ∑ i, ∑ k, (θ i z k) • Pm i k with hΘ
  have hΘapp : ∀ z w, Θ z w = ∑ i, ∑ k, θ i z k • Pm i k w := by
    intro z w; simp [hΘ, ContinuousLinearMap.sum_apply]
  have hFΘ : ∀ z, F z = Θ z (g z) := by
    intro z; rw [hΘapp]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Pm_apply, smul_smul, mul_comm]
  have hΘ0 : Θ 0 = ContinuousLinearMap.id ℝ (Cn n) := by
    ext w j
    rw [hΘapp]; simp [hθ0, EuclideanSpace.single_apply, Pi.single_apply]
  have hΘc : ContinuousOn Θ (ball 0 ε) :=
    continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun k _ =>
      (coord_continuousOn (hθc i) k).smul continuousOn_const
  have hΘI : ∀ z w, Θ z (Complex.I • w) = Complex.I • Θ z w := by
    intro z w; rw [hΘapp, hΘapp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pm_I, smul_comm]
  have hmem : Θ ⁻¹' (range ((↑) : (Cn n ≃L[ℝ] Cn n) → Cn n →L[ℝ] Cn n)) ∈ 𝓝 (0:ℂ) :=
    (hΘc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hεpos))).preimage_mem_nhds
      ((ContinuousLinearEquiv.isOpen).mem_nhds ⟨ContinuousLinearEquiv.refl ℝ (Cn n), by rw [hΘ0]; rfl⟩)
  obtain ⟨r3, hr3, hr3s⟩ := Metric.mem_nhds_iff.1 hmem
  set δ := min r3 (ε/2) / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; exact half_pos (lt_min hr3 (by linarith))
  have hδ1 : δ < r3 := by rw [hδ]; linarith [min_le_left r3 (ε/2)]
  have hδ2 : δ < ε/2 := by rw [hδ]; linarith [min_le_right r3 (ε/2)]
  have hsub : ∀ z ∈ closedBall (0:ℂ) δ, z ∈ ball (0:ℂ) r3 ∧ z ∈ ball (0:ℂ) ε ∧ z ∈ ball (0:ℂ) r :=
    fun z hz => ⟨closedBall_subset_ball hδ1 hz, closedBall_subset_ball (by linarith) hz,
      closedBall_subset_ball (by linarith) hz⟩
  set Θi : ℂ → Cn n →L[ℝ] Cn n := fun z => (Θ z).inverse with hΘi
  set Φ : ℂ → Cn n →L[ℝ] E := fun z => (Ψ z).comp (Θi z) with hΦ
  have hΘe : ∀ z ∈ closedBall (0:ℂ) δ, ∃ e : Cn n ≃L[ℝ] Cn n, (e : Cn n →L[ℝ] Cn n) = Θ z ∧
      Θi z = (e.symm : Cn n →L[ℝ] Cn n) := by
    intro z hz
    obtain ⟨e, he⟩ := hr3s (hsub z hz).1
    exact ⟨e, he, by simp only [hΘi, ← he, ContinuousLinearMap.inverse_equiv]⟩
  refine ⟨δ, hδp, Φ, f, ?_, ?_, hfd.mono (ball_subset_ball hδ2.le), ?_⟩
  · intro z hz
    obtain ⟨e, he, -⟩ := hΘe z hz
    have c0 : ContinuousAt ContinuousLinearMap.inverse (Θ z) :=
      (he ▸ (contDiffAt_map_inverse (n := ∞) e) : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (Θ z)).continuousAt
    have c1 : ContinuousAt Θi z := c0.comp (hΘc.continuousAt (isOpen_ball.mem_nhds (hsub z hz).2.1))
    exact ((hΨc.continuousAt (isOpen_ball.mem_nhds (hsub z hz).2.2)).clm_comp c1).continuousWithinAt
  · intro z hz
    obtain ⟨e, he, hei⟩ := hΘe z hz
    obtain ⟨e1, he1⟩ := hiso z (hsub z hz).2.2
    have hΦe : Φ z = ((e.symm.trans e1 : Cn n ≃L[ℝ] E) : Cn n →L[ℝ] E) := by
      ext w; simp [hΦ, hei, ← he1]
    refine ⟨by rw [hΦe]; exact (e.symm.trans e1).bijective, fun w => ?_⟩
    have hsI : e.symm (Complex.I • w) = Complex.I • e.symm w := by
      apply e.injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      have := hΘI z (e.symm w)
      rw [← he] at this
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at this
      exact this.symm
    simp only [hΦ, ContinuousLinearMap.coe_comp', Function.comp_apply, hei,
      ContinuousLinearEquiv.coe_coe, hsI]
    exact hcx z (hsub z hz).2.2 _
  · intro z hz
    have hz' : z ∈ closedBall (0:ℂ) δ := ball_subset_closedBall hz
    obtain ⟨e, he, hei⟩ := hΘe z hz'
    have hz2 : z ∈ ball (0:ℂ) (ε/2) := ball_subset_ball hδ2.le hz
    rw [hhg z (hsub z hz').2.2]
    simp only [hΦ, ContinuousLinearMap.coe_comp', Function.comp_apply, hei]
    rw [← hFf hz2, hFΘ, ← he]
    simp

end HFDev


open JHolomorphic MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar A : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (hA : ContDiffOn ℝ ∞ A (ball 0 1)) (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) + A z (h z) = 0) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z) ∧
          ∀ w, Φ z (Complex.I • w) = Jbar z (Φ z w)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, h z = Φ z (f z) :=
  HFDev.main_hf n hn Jbar A hJbar hJbar2 hA h hh heq
