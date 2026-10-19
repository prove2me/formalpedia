-- Prove2me | solution 1 for HunterPDE.Parabolic.hilbert_triple_continuity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T17:51:40.678716+00:00
-- url     : https://prove2.me/submissions/78175478-3f25-409b-8f40-3eecf85d4f78

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_HilbertTriple

/-! Hunter, Theorem 6.41 (Lions-Magenes): `u ∈ L²(0,T;𝒱)`, `u_t ∈ L²(0,T;𝒱')` ⇒ `u ∈ C([0,T];ℋ)`.
Proof without mollifiers: the Steklov averages `B_h(t) = h⁻¹ ∫_t^{t+h} u` are continuous in `𝒱`,
their `𝒱'`-images are `C¹` with derivative the Steklov average of `u_t` (scalar du Bois-Reymond),
so `‖B_h - B_k‖²_ℋ` satisfies an exact energy identity; averaging gives a uniform bound by
`L²` norms, and Steklov averages converge in `L²` (continuity of translation).  Hence the `B_h`
are uniformly Cauchy in `C([a,b];ℋ)` on the windows `[0,2T/3]` (forward, `h > 0`) and
`[T/3,T]` (backward, `h < 0`); the limits glue to a continuous representative.  The weak
derivative formulas reuse the integration-by-parts lemmas (section IBPc), and the `L^∞` bound
follows from the energy identity by averaging. -/

set_option autoImplicit false

section Q0ca_A
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace IBPc
open HunterPDE.Parabolic

/-! ## Weak derivative of a primitive, and the du Bois-Reymond lemma -/

/-- Weak derivative of an absolutely continuous function, against a test function on `(0,T)`. -/
lemma weak_deriv_of_ac {T : ℝ} (hT : 0 ≤ T) {y y' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval y 0 T)
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt y (y' t) t) (φ : ℝ → ℝ)
    (hφ : IsTestFunctionOn T φ) :
    ∫ t in Ioo 0 T, deriv φ t * y t = -∫ t in Ioo 0 T, φ t * y' t := by
  obtain ⟨hφs, -, hφt⟩ := hφ
  have hφac : AbsolutelyContinuousOnInterval φ 0 T :=
    (hφs.contDiffOn.of_le (by simp)).absolutelyContinuousOnInterval
  have key := hac.integral_mul_deriv_eq_deriv_mul hφac
  have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp at this)
  have hTT : φ T = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp at this)
  rw [h0, hTT] at key
  simp only [mul_zero, sub_zero] at key
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at key
  have hcongr : ∫ t in Ioo 0 T, deriv y t * φ t = ∫ t in Ioo 0 T, φ t * y' t := by
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hd] with t ht htI
    rw [(ht htI).deriv, mul_comm]
  rw [← hcongr]
  simp_rw [mul_comm (deriv φ _) (y _)]
  rw [key]
  ring

/-- The weak derivative of the primitive `y0 + ∫₀ᵗ g` is `g`. -/
lemma primitive_weak_deriv {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo 0 T))
    (y0 : ℝ) (φ : ℝ → ℝ) (hφ : IsTestFunctionOn T φ) :
    ∫ t in Ioo 0 T, deriv φ t * (y0 + ∫ s in (0:ℝ)..t, g s) = -∫ t in Ioo 0 T, φ t * g t := by
  have hu : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT.le
  have hgI : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hg
  have hZac : AbsolutelyContinuousOnInterval (fun t => ∫ s in (0:ℝ)..t, g s) 0 T :=
    hgI.absolutelyContinuousOnInterval_intervalIntegral (by simp [hu, hT.le])
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => y0) 0 T :=
    ((LipschitzWith.const (α := ℝ) y0).lipschitzOnWith (s := uIcc (0:ℝ) T)).absolutelyContinuousOnInterval
  have hac : AbsolutelyContinuousOnInterval (fun t => y0 + ∫ s in (0:ℝ)..t, g s) 0 T :=
    hconst.add hZac
  refine weak_deriv_of_ac hT.le hac ?_ φ hφ
  have h1 := hgI.ae_hasDerivAt_integral
  filter_upwards [h1] with t ht htT
  have htI : t ∈ uIcc 0 T := by rw [hu]; exact Ioo_subset_Icc_self htT
  have h0 : (0:ℝ) ∈ uIcc 0 T := by simp [hu, hT.le]
  exact (ht htI 0 h0).const_add y0

lemma test_zero_off {T : ℝ} {φ : ℝ → ℝ} (hφ : IsTestFunctionOn T φ) {t : ℝ} (ht : t ∉ Ioo 0 T) :
    φ t = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => ht (hφ.2.2 h))

lemma exists_Icc_of_compact {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : IsCompact S) (hST : S ⊆ Ioo 0 T) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < T ∧ S ⊆ Icc a b := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨T / 3, 2 * T / 3, by positivity, by linarith, by linarith, empty_subset _⟩
  · have ha : sInf S ∈ S := hS.sInf_mem hne
    have hb : sSup S ∈ S := hS.sSup_mem hne
    exact ⟨sInf S, sSup S, (hST ha).1, csInf_le hS.bddBelow hb, (hST hb).2,
      fun x hx => ⟨csInf_le hS.bddBelow hx, le_csSup hS.bddAbove hx⟩⟩

lemma primitive_test {T : ℝ} (hT : 0 < T) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) (hsupp : ∀ t, t ∉ Icc a b → χ t = 0)
    (hint : ∫ t, χ t = 0) :
    IsTestFunctionOn T (fun t => ∫ s in (0:ℝ)..t, χ s) ∧
      deriv (fun t => ∫ s in (0:ℝ)..t, χ s) = χ := by
  have hderiv : ∀ x, HasDerivAt (fun t => ∫ s in (0:ℝ)..t, χ s) (χ x) x := fun x =>
    (hχ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd : deriv (fun t => ∫ s in (0:ℝ)..t, χ s) = χ := funext fun x => (hderiv x).deriv
  have hz : ∀ t, t ∉ Icc a b → ∫ s in (0:ℝ)..t, χ s = 0 := by
    intro t ht
    rcases lt_or_ge t a with hta | hta
    · have : ∀ s ∈ uIcc (0:ℝ) t, χ s = 0 := by
        intro s hs
        apply hsupp
        intro hsI
        have : s ≤ max 0 t := hs.2
        have := max_lt ha hta
        linarith [hsI.1]
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) this]
      simp
    · have htb : b < t := by
        by_contra hh
        exact ht ⟨hta, not_lt.mp hh⟩
      have h0t : 0 ≤ t := by linarith
      have hcompl : ∀ x, x ∉ Ioc 0 t → χ x = 0 := by
        intro x hx
        apply hsupp
        intro hxI
        exact hx ⟨ha.trans_le hxI.1, hxI.2.trans htb.le⟩
      rw [intervalIntegral.integral_of_le h0t, setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
      exact hint
  refine ⟨⟨?_, ?_, ?_⟩, hd⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by rw [hd]; exact hχ⟩
  · exact HasCompactSupport.intro isCompact_Icc hz
  · have : tsupport (fun t => ∫ s in (0:ℝ)..t, χ s) ⊆ Icc a b :=
      closure_minimal (fun t ht => by_contra fun h => ht (hz t h)) isClosed_Icc
    exact this.trans fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

lemma exists_unit_test {T : ℝ} (hT : 0 < T) :
    ∃ φ0 : ℝ → ℝ, IsTestFunctionOn T φ0 ∧ ∫ t, φ0 t = 1 := by
  let b : ContDiffBump (T / 2 : ℝ) := ⟨T / 8, T / 4, by positivity, by linarith⟩
  have hI : 0 < ∫ t, b t := b.integral_pos
  refine ⟨fun t => (∫ s, b s)⁻¹ * b t, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul b.contDiff
  · exact b.hasCompactSupport.mul_left
  · have h1 : tsupport (fun t => (∫ s, b s)⁻¹ * b t) ⊆ tsupport b :=
      closure_mono (Function.support_mul_subset_right (fun _ => (∫ s, b s)⁻¹) b)
    refine h1.trans ?_
    rw [b.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    have : b.rOut = T / 4 := rfl
    rw [this] at hx
    constructor <;> linarith [hx.1, hx.2]
  · simp only
    rw [integral_const_mul, inv_mul_cancel₀ hI.ne']

lemma test_mul_int {T : ℝ} {φ : ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) : IntegrableOn (fun t => φ t * f t) (Ioo 0 T) := by
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφs
  exact Integrable.bdd_mul hf hφc.aestronglyMeasurable (Filter.Eventually.of_forall hC)

lemma dbr_core {T : ℝ} (hT : 0 < T) {k : ℝ → ℝ} (hk : IntegrableOn k (Ioo 0 T))
    (h : ∀ φ, IsTestFunctionOn T φ → ∫ t in Ioo 0 T, deriv φ t * k t = 0) :
    ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), k t = C := by
  obtain ⟨φ0, hφ0, hφ0I⟩ := exists_unit_test hT
  obtain ⟨C, hC⟩ : ∃ C, C = ∫ t in Ioo 0 T, φ0 t * k t := ⟨_, rfl⟩
  refine ⟨C, ?_⟩
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), t ∈ Ioo 0 T := ae_restrict_mem measurableSet_Ioo
  have hloc : LocallyIntegrableOn (fun t => k t - C) (Ioo 0 T) (volume.restrict (Ioo 0 T)) := by
    have : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) := isFiniteMeasure_restrict.2 (by simp)
    exact (hk.sub (integrable_const C)).locallyIntegrable.locallyIntegrableOn _
  have hz := (isOpen_Ioo).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [hz, hmem] with t ht1 ht2
    have := ht1 ht2
    linarith
  · intro g hgs hgc hgt
    have hgT : IsTestFunctionOn T g := ⟨hgs, hgc, hgt⟩
    -- the primitive of `g - (∫ g) φ0`
    obtain ⟨a, b, ha, hab, hb, hsub⟩ := exists_Icc_of_compact hT (hgc.isCompact.union hφ0.2.1.isCompact)
      (union_subset hgt hφ0.2.2)
    have hgi : Integrable g := hgs.continuous.integrable_of_hasCompactSupport hgc
    have hφi : Integrable φ0 := hφ0.1.continuous.integrable_of_hasCompactSupport hφ0.2.1
    obtain ⟨I, hI⟩ : ∃ I, I = ∫ t, g t := ⟨_, rfl⟩
    have hχs : ∀ t, t ∉ Icc a b → g t - I * φ0 t = 0 := by
      intro t ht
      have h1 : t ∉ tsupport g := fun h' => ht (hsub (Or.inl h'))
      have h2 : t ∉ tsupport φ0 := fun h' => ht (hsub (Or.inr h'))
      rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
      ring
    have hχint : ∫ t, (g t - I * φ0 t) = 0 := by
      rw [integral_sub hgi (hφi.const_mul I), integral_const_mul, hφ0I, ← hI]
      ring
    obtain ⟨hX, hXd⟩ := primitive_test hT (χ := fun t => g t - I * φ0 t)
      (hgs.sub (contDiff_const.mul hφ0.1)) ha hab hb hχs hχint
    have hkey := h _ hX
    rw [hXd] at hkey
    have e1 : IntegrableOn (fun t => g t * k t) (Ioo 0 T) := test_mul_int hgs.continuous hgc hk
    have e2 : IntegrableOn (fun t => φ0 t * k t) (Ioo 0 T) :=
      test_mul_int hφ0.1.continuous hφ0.2.1 hk
    have e3 : ∫ t in Ioo 0 T, (g t - I * φ0 t) * k t =
        (∫ t in Ioo 0 T, g t * k t) - I * ∫ t in Ioo 0 T, φ0 t * k t := by
      rw [← integral_const_mul, ← integral_sub e1 (e2.const_mul I)]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      ring
    rw [e3] at hkey
    have e4 : ∫ t in Ioo 0 T, g t = I := by
      rw [hI]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
        test_zero_off hgT ht
    have e5 : ∫ x, g x • (k x - C) ∂(volume.restrict (Ioo 0 T)) =
        (∫ t in Ioo 0 T, g t * k t) - C * ∫ t in Ioo 0 T, g t := by
      have hg1 : IntegrableOn g (Ioo 0 T) := hgi.integrableOn
      rw [← integral_const_mul, ← integral_sub e1 (hg1.const_mul C)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [smul_eq_mul]
      ring
    rw [e5, e4]
    rw [← hC] at hkey
    linarith

theorem dbr_scalar {T : ℝ} (hT : 0 < T) {h w : ℝ → ℝ} (hh : IntegrableOn h (Ioo 0 T))
    (hw : IntegrableOn w (Ioo 0 T))
    (hweak : ∀ φ, IsTestFunctionOn T φ →
      ∫ t in Ioo 0 T, deriv φ t * h t = -∫ t in Ioo 0 T, φ t * w t) :
    ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), h t = C + ∫ s in (0:ℝ)..t, w s := by
  have hwI : IntervalIntegrable w volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hw
  have hYc : ContinuousOn (fun t => ∫ s in (0:ℝ)..t, w s) (Icc 0 T) := by
    have hI : IntegrableOn w (uIcc 0 T) := by
      rw [uIcc_of_le hT.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hw)
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
    rwa [uIcc_of_le hT.le] at this
  have hYi : IntegrableOn (fun t => ∫ s in (0:ℝ)..t, w s) (Ioo 0 T) :=
    (hYc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  obtain ⟨C, hC⟩ := dbr_core hT (k := fun t => h t - ∫ s in (0:ℝ)..t, w s) (hh.sub hYi) (by
    intro φ hφ
    have hd : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
    have hdc : HasCompactSupport (deriv φ) := hφ.2.1.deriv
    have e1 := test_mul_int hd hdc hh
    have e2 := test_mul_int hd hdc hYi
    have e3 := primitive_weak_deriv hT hw 0 φ hφ
    simp only [zero_add] at e3
    have e4 : ∫ t in Ioo 0 T, deriv φ t * (h t - ∫ s in (0:ℝ)..t, w s) =
        (∫ t in Ioo 0 T, deriv φ t * h t) - ∫ t in Ioo 0 T, deriv φ t * ∫ s in (0:ℝ)..t, w s := by
      rw [← integral_sub e1 e2]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      ring
    rw [e4, e3, hweak φ hφ]
    ring)
  refine ⟨C, ?_⟩
  filter_upwards [hC] with t ht
  linarith



/-- A continuous function on `[0,T]` with weak derivative `w ∈ L¹` satisfies the fundamental theorem of calculus. -/
theorem ftc_of_weak {T : ℝ} (hT : 0 < T) {h w : ℝ → ℝ} (hhc : ContinuousOn h (Icc 0 T))
    (hw : IntegrableOn w (Ioo 0 T))
    (hweak : ∀ φ, IsTestFunctionOn T φ →
      ∫ t in Ioo 0 T, deriv φ t * h t = -∫ t in Ioo 0 T, φ t * w t) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, h t - h s = ∫ r in s..t, w r := by
  have hhI : IntegrableOn h (Ioo 0 T) := (hhc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  obtain ⟨C, hC⟩ := dbr_scalar hT hhI hw hweak
  have hI : IntegrableOn w (uIcc 0 T) := by
    rw [uIcc_of_le hT.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hw)
  have hYc : ContinuousOn (fun t => ∫ s in (0:ℝ)..t, w s) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
    rwa [uIcc_of_le hT.le] at this
  have hEq : EqOn h (fun t => C + ∫ s in (0:ℝ)..t, w s) (Icc 0 T) := by
    have h1 : EqOn h (fun t => C + ∫ s in (0:ℝ)..t, w s) (Ioo 0 T) :=
      Measure.eqOn_open_of_ae_eq hC isOpen_Ioo (hhc.mono Ioo_subset_Icc_self)
        ((continuousOn_const.add hYc).mono Ioo_subset_Icc_self)
    exact h1.of_subset_closure hhc (continuousOn_const.add hYc) Ioo_subset_Icc_self
      (by rw [closure_Ioo hT.ne])
  intro s hs t ht
  have hsI : IntervalIntegrable w volume 0 s := by
    refine (hI.mono_set ?_).intervalIntegrable
    rw [uIcc_of_le hT.le]; intro x hx
    rw [uIcc_of_le hs.1] at hx; exact ⟨hx.1, hx.2.trans hs.2⟩
  have htI : IntervalIntegrable w volume 0 t := by
    refine (hI.mono_set ?_).intervalIntegrable
    rw [uIcc_of_le hT.le]; intro x hx
    rw [uIcc_of_le ht.1] at hx; exact ⟨hx.1, hx.2.trans ht.2⟩
  rw [hEq ht, hEq hs, ← intervalIntegral.integral_interval_sub_left htI hsI]
  ring

end IBPc
end Q0ca_A

section Q0ca_B
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace IBPc

lemma eLpNorm_shift {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f volume) (ρ : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun t => f (t + ρ)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume ρ)

lemma memLp_shift {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (ρ : ℝ) : MemLp (fun t => f (t + ρ)) p volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume ρ)

/-- Translation is continuous in `L²` for compactly supported continuous functions. -/
lemma trans_small_cs {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} (hgs : HasCompactSupport g)
    (hgc : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ρ in 𝓝 (0:ℝ), eLpNorm (fun t => g (t + ρ) - g t) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R0, hR0⟩ := hgs.isCompact.isBounded.subset_closedBall (0:ℝ)
  set R : ℝ := |R0| + 1 with hR
  have hRpos : 0 < R := by positivity
  have hsub : tsupport g ⊆ Icc (-R) R := by
    intro x hx
    have := hR0 hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have h1 : R0 ≤ |R0| := le_abs_self _
    have h2 : -|R0| ≤ R0 := neg_abs_le _
    have := abs_le.1 this
    constructor <;> linarith [this.1, this.2]
  have hK : (volume (Icc (-(R+1)) (R+1))) = ENNReal.ofReal (2 * R + 2) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hsqpos : 0 < Real.sqrt (2 * R + 2) := Real.sqrt_pos.2 (by positivity)
  set η : ℝ := ε / Real.sqrt (2 * R + 2) with hη
  have hηpos : 0 < η := div_pos hε hsqpos
  have huc := hgs.uniformContinuous_of_continuous hgc
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc η hηpos
  have hev : ∀ᶠ ρ in 𝓝 (0:ℝ), |ρ| < min δ 1 := by
    have : Metric.ball (0:ℝ) (min δ 1) ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds _ (lt_min hδ one_pos)
    filter_upwards [this] with ρ hρ
    simpa [Real.dist_eq] using hρ
  filter_upwards [hev] with ρ hρ
  have hρδ : |ρ| < δ := lt_of_lt_of_le hρ (min_le_left _ _)
  have hρ1 : |ρ| < 1 := lt_of_lt_of_le hρ (min_le_right _ _)
  have hsupp : Function.support (fun t => g (t + ρ) - g t) ⊆ Icc (-(R+1)) (R+1) := by
    intro t ht
    by_contra hnot
    apply ht
    simp only
    have h1 : g t = 0 := by
      by_contra h
      have : t ∈ tsupport g := subset_tsupport _ h
      have := hsub this
      apply hnot
      constructor <;> linarith [this.1, this.2]
    have h2 : g (t + ρ) = 0 := by
      by_contra h
      have : t + ρ ∈ tsupport g := subset_tsupport _ h
      have h3 := hsub this
      have h4 := abs_lt.1 hρ1
      apply hnot
      constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
    rw [h1, h2, sub_zero]
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  have hbd : ∀ᵐ t ∂(volume.restrict (Icc (-(R+1)) (R+1))), ‖g (t + ρ) - g t‖ ≤ η := by
    refine Filter.Eventually.of_forall fun t => ?_
    have := hδ' (a := t + ρ) (b := t) (by rw [Real.dist_eq]; simpa using hρδ)
    rw [dist_eq_norm] at this
    exact this.le
  refine (eLpNorm_le_of_ae_bound hbd).trans ?_
  rw [Measure.restrict_apply_univ, hK]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [show (2:ℝ)⁻¹ = (2:ℝ)⁻¹ from rfl]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [show (2:ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact (by rw [hη]; field_simp : Real.sqrt (2 * R + 2) * η = ε).le

/-- Continuity of translation in `L²(ℝ; E)`. -/
lemma trans_small {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E}
    (hF : MemLp F 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ρ in 𝓝 (0:ℝ), eLpNorm (fun t => F (t + ρ) - F t) 2 volume ≤ ENNReal.ofReal ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, hgs, hgF, hgc, hgm⟩ := hF.exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_pos.2 hε3).ne'
  filter_upwards [trans_small_cs hgs hgc hε3] with ρ hρ
  have e1 : (fun t => F (t + ρ) - F t) =
      fun t => ((F - g) (t + ρ)) + (g (t + ρ) - g t) + (g - F) t := by
    funext t; simp only [Pi.sub_apply]; abel
  have hFg : MemLp (F - g) 2 volume := hF.sub hgm
  have hgF' : MemLp (g - F) 2 volume := hgm.sub hF
  have m1 : MemLp (fun t => (F - g) (t + ρ)) 2 volume := memLp_shift hFg ρ
  have m2 : MemLp (fun t => g (t + ρ) - g t) 2 volume := (memLp_shift hgm ρ).sub hgm
  have n1 : eLpNorm (fun t => (F - g) (t + ρ)) 2 volume ≤ ENNReal.ofReal (ε / 3) := by
    rw [eLpNorm_shift hFg.1 ρ]; exact hgF
  have n3 : eLpNorm (g - F) 2 volume ≤ ENNReal.ofReal (ε / 3) := by
    rw [← eLpNorm_neg]; simpa using hgF
  rw [e1]
  calc eLpNorm (fun t => ((F - g) (t + ρ)) + (g (t + ρ) - g t) + (g - F) t) 2 volume
      ≤ eLpNorm (fun t => ((F - g) (t + ρ)) + (g (t + ρ) - g t)) 2 volume + eLpNorm (g - F) 2 volume :=
        eLpNorm_add_le (m1.1.add m2.1) hgF'.1 (by norm_num)
    _ ≤ (eLpNorm (fun t => (F - g) (t + ρ)) 2 volume + eLpNorm (fun t => g (t + ρ) - g t) 2 volume)
          + eLpNorm (g - F) 2 volume := by
        gcongr; exact eLpNorm_add_le m1.1 m2.1 (by norm_num)
    _ ≤ (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) + ENNReal.ofReal (ε / 3) := by gcongr
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε3.le hε3.le, ← ENNReal.ofReal_add (by positivity) hε3.le]
        congr 1; ring

end IBPc
end Q0ca_B

section Q0ca_C
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace IBPc

section key

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma pair_eLpNorm_le {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : AEStronglyMeasurable X volume)
    (hY : AEStronglyMeasurable Y volume) :
    eLpNorm (fun t => X t (Y t)) 1 volume ≤ eLpNorm X 2 volume * eLpNorm Y 2 volume := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) hX hY
    (fun (f : StrongDual ℝ W) (w : W) => f w) 1
    (ae_of_all _ fun t => by
      have := (X t).le_opNorm (Y t)
      simpa [one_mul] using this)
  simpa using this

lemma pair_aesm {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : AEStronglyMeasurable X volume)
    (hY : AEStronglyMeasurable Y volume) : AEStronglyMeasurable (fun t => X t (Y t)) volume :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hX.prodMk hY)

lemma pair_integrable {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 volume)
    (hY : MemLp Y 2 volume) : Integrable (fun t => X t (Y t)) volume := by
  rw [← memLp_one_iff_integrable]
  refine ⟨pair_aesm hX.1 hY.1, ?_⟩
  exact lt_of_le_of_lt (pair_eLpNorm_le hX.1 hY.1) (ENNReal.mul_lt_top hX.2 hY.2)

lemma pair_abs_le {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 volume)
    (hY : MemLp Y 2 volume) :
    ∫ t, |X t (Y t)| ≤ (eLpNorm X 2 volume).toReal * (eLpNorm Y 2 volume).toReal := by
  have h1 : ∫ t, |X t (Y t)| = (eLpNorm (fun t => X t (Y t)) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm (pair_aesm hX.1 hY.1)]
    simp [Real.norm_eq_abs]
  rw [h1, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hX.2.ne hY.2.ne) (pair_eLpNorm_le hX.1 hY.1)

lemma wpair_le {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 volume)
    (hY : MemLp Y 2 volume) {ψ : ℝ → ℝ} {M : ℝ} (hψ : ∀ t, |ψ t| ≤ M) (hψm : Measurable ψ) :
    |∫ t, ψ t * X t (Y t)| ≤ M * ((eLpNorm X 2 volume).toReal * (eLpNorm Y 2 volume).toReal) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hψ 0)
  have hi := pair_integrable hX hY
  have hi' : Integrable (fun t => |X t (Y t)|) volume := hi.abs
  calc |∫ t, ψ t * X t (Y t)| ≤ ∫ t, |ψ t * X t (Y t)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, M * |X t (Y t)| := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) (hi'.const_mul M)
          (ae_of_all _ fun t => ?_)
        show |ψ t * X t (Y t)| ≤ M * |X t (Y t)|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hψ t) (abs_nonneg _)
    _ = M * ∫ t, |X t (Y t)| := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (pair_abs_le hX hY) hM

/-- The shifted pairing integral. -/
noncomputable def Phi (X : ℝ → StrongDual ℝ W) (Y : ℝ → W) (ψ : ℝ → ℝ) (ρ δ : ℝ) : ℝ :=
  ∫ t, ψ t * X (t + ρ) (Y (t + δ))

lemma Phi_diff {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 volume)
    (hY : MemLp Y 2 volume) {ψ : ℝ → ℝ} {M : ℝ} (hψ : ∀ t, |ψ t| ≤ M) (hψm : Measurable ψ)
    (ρ δ : ℝ) :
    |Phi X Y ψ ρ δ - Phi X Y ψ 0 0| ≤
      M * ((eLpNorm (fun t => X (t + ρ) - X t) 2 volume).toReal * (eLpNorm Y 2 volume).toReal
        + (eLpNorm X 2 volume).toReal * (eLpNorm (fun t => Y (t + δ) - Y t) 2 volume).toReal) := by
  have hXρ : MemLp (fun t => X (t + ρ) - X t) 2 volume := (memLp_shift hX ρ).sub hX
  have hYδ : MemLp (fun t => Y (t + δ)) 2 volume := memLp_shift hY δ
  have hYd : MemLp (fun t => Y (t + δ) - Y t) 2 volume := hYδ.sub hY
  have e1 := wpair_le hXρ hYδ hψ hψm
  have e2 := wpair_le hX hYd hψ hψm
  have hnY : (eLpNorm (fun t => Y (t + δ)) 2 volume) = eLpNorm Y 2 volume := eLpNorm_shift hY.1 δ 2
  rw [hnY] at e1
  have i1 : Integrable (fun t => ψ t * X (t + ρ) (Y (t + δ))) volume := by
    have := (pair_integrable (memLp_shift hX ρ) hYδ)
    obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖ψ t‖ ≤ C := ⟨M, fun t => by simpa using hψ t⟩
    exact this.bdd_mul hψm.aestronglyMeasurable (ae_of_all _ hC)
  have i0 : Integrable (fun t => ψ t * X t (Y t)) volume := by
    have := (pair_integrable hX hY)
    exact this.bdd_mul hψm.aestronglyMeasurable (ae_of_all _ fun t => by simpa using hψ t)
  have iA : Integrable (fun t => ψ t * (X (t + ρ) - X t) (Y (t + δ))) volume :=
    (pair_integrable hXρ hYδ).bdd_mul hψm.aestronglyMeasurable (ae_of_all _ fun t => by simpa using hψ t)
  have iB : Integrable (fun t => ψ t * X t (Y (t + δ) - Y t)) volume :=
    (pair_integrable hX hYd).bdd_mul hψm.aestronglyMeasurable (ae_of_all _ fun t => by simpa using hψ t)
  have hsplit : Phi X Y ψ ρ δ - Phi X Y ψ 0 0 =
      (∫ t, ψ t * (X (t + ρ) - X t) (Y (t + δ))) + ∫ t, ψ t * X t (Y (t + δ) - Y t) := by
    unfold Phi
    rw [← integral_sub i1 (by simpa using i0), ← integral_add iA iB]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [add_zero, ContinuousLinearMap.coe_sub', Pi.sub_apply, map_sub]
    ring
  rw [hsplit]
  calc |(∫ t, ψ t * (X (t + ρ) - X t) (Y (t + δ))) + ∫ t, ψ t * X t (Y (t + δ) - Y t)|
      ≤ |∫ t, ψ t * (X (t + ρ) - X t) (Y (t + δ))| + |∫ t, ψ t * X t (Y (t + δ) - Y t)| :=
        abs_add_le _ _
    _ ≤ _ := by
        have := add_le_add e1 e2
        linarith

end key

end IBPc
end Q0ca_C

section Q0ca_C2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace IBPc

section key2

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma wpair_abs_le {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 volume)
    (hY : MemLp Y 2 volume) {ψ : ℝ → ℝ} {M : ℝ} (hψ : ∀ t, |ψ t| ≤ M) :
    ∫ t, |ψ t * X t (Y t)| ≤ M * ((eLpNorm X 2 volume).toReal * (eLpNorm Y 2 volume).toReal) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hψ 0)
  have hi' : Integrable (fun t => |X t (Y t)|) volume := (pair_integrable hX hY).abs
  calc ∫ t, |ψ t * X t (Y t)| ≤ ∫ t, M * |X t (Y t)| := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) (hi'.const_mul M)
          (ae_of_all _ fun t => ?_)
        show |ψ t * X t (Y t)| ≤ M * |X t (Y t)|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hψ t) (abs_nonneg _)
    _ = M * ∫ t, |X t (Y t)| := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (pair_abs_le hX hY) hM

lemma fubini_eq {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hXm : StronglyMeasurable X)
    (hYm : StronglyMeasurable Y) (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) {ψ : ℝ → ℝ}
    {M : ℝ} (hψ : ∀ t, |ψ t| ≤ M) (hψc : Continuous ψ) {h : ℝ} (hh : 0 < h) (δ : ℝ) :
    IntervalIntegrable (fun ρ => Phi X Y ψ ρ δ) volume 0 h ∧
    Integrable (fun t => ψ t * ((1 / h) * ∫ r in t..t + h, X r (Y (t + δ)))) volume ∧
    ∫ t, ψ t * ((1 / h) * ∫ r in t..t + h, X r (Y (t + δ))) =
      (1 / h) * ∫ ρ in (0:ℝ)..h, Phi X Y ψ ρ δ := by
  set F : ℝ → ℝ → ℝ := fun t ρ => ψ t * X (t + ρ) (Y (t + δ)) with hF
  have hmeas : StronglyMeasurable (Function.uncurry F) := by
    have h1 : StronglyMeasurable (fun p : ℝ × ℝ => X (p.1 + p.2)) :=
      hXm.comp_measurable (measurable_fst.add measurable_snd)
    have h2 : StronglyMeasurable (fun p : ℝ × ℝ => Y (p.1 + δ)) :=
      hYm.comp_measurable (measurable_fst.add_const δ)
    have h3 : StronglyMeasurable (fun p : ℝ × ℝ => ψ p.1) := (hψc.comp continuous_fst).stronglyMeasurable
    exact h3.mul ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (h1.prodMk h2))
  set ν : Measure ℝ := volume.restrict (Ioc 0 h) with hν
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, Measure.restrict_apply_univ]; simp
  have hint : Integrable (Function.uncurry F) (volume.prod ν) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun ρ => ?_, ?_⟩
    · have := pair_integrable (memLp_shift hX ρ) (memLp_shift hY δ)
      exact this.bdd_mul hψc.aestronglyMeasurable (ae_of_all _ fun t => by simpa using hψ t)
    · refine Integrable.mono' (integrable_const (M * ((eLpNorm X 2 volume).toReal *
        (eLpNorm Y 2 volume).toReal))) ?_ (ae_of_all _ fun ρ => ?_)
      · have h0 : AEStronglyMeasurable (fun p => ‖Function.uncurry F p‖) (volume.prod ν) :=
          hmeas.norm.aestronglyMeasurable
        have := h0.prod_swap
        exact AEStronglyMeasurable.integral_prod_right' (μ := ν) (ν := volume) this
      · have hb := wpair_abs_le (memLp_shift hX ρ) (memLp_shift hY δ) hψ
        rw [eLpNorm_shift hX.1, eLpNorm_shift hY.1] at hb
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
        simpa [hF, Function.uncurry, Real.norm_eq_abs] using hb
  have hIntI : IntervalIntegrable (fun ρ => Phi X Y ψ ρ δ) volume 0 h := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
    exact hint.integral_prod_right
  have step1 : ∀ t, ψ t * ((1 / h) * ∫ r in t..t + h, X r (Y (t + δ))) =
      (1 / h) * ∫ ρ in (0:ℝ)..h, F t ρ := by
    intro t
    have := intervalIntegral.integral_comp_add_left (a := 0) (b := h)
      (fun r => X r (Y (t + δ))) t
    simp only [add_zero] at this
    rw [← this]
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    ring
  have step2 : ∀ t, ∫ ρ in (0:ℝ)..h, F t ρ = ∫ ρ in Ioc 0 h, F t ρ := fun t =>
    intervalIntegral.integral_of_le hh.le
  have hIntT : Integrable (fun t => ψ t * ((1 / h) * ∫ r in t..t + h, X r (Y (t + δ)))) volume := by
    have h1 := (hint.integral_prod_left).const_mul (1 / h)
    refine h1.congr (ae_of_all _ fun t => ?_)
    show (1 / h) * ∫ y, Function.uncurry F (t, y) ∂ν = _
    show _ = ψ t * ((1 / h) * ∫ r in t..t + h, X r (Y (t + δ)))
    rw [step1 t, step2 t]
    rfl
  refine ⟨hIntI, hIntT, ?_⟩
  simp_rw [step1]
  rw [integral_const_mul]
  congr 1
  simp_rw [step2]
  rw [integral_integral_swap hint, intervalIntegral.integral_of_le hh.le]
  rfl

theorem key {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hXm : StronglyMeasurable X)
    (hYm : StronglyMeasurable Y) (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) {ψ : ℝ → ℝ}
    {M : ℝ} (hψ : ∀ t, |ψ t| ≤ M) (hψc : Continuous ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h0 > 0, ∀ h : ℝ, 0 < h → h < h0 → ∀ δ ∈ Icc 0 h,
      |(∫ t, ψ t * ((1 / h) * ∫ r in t..t + h, X r (Y (t + δ)))) - ∫ t, ψ t * X t (Y t)| ≤ ε := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hψ 0)
  set a : ℝ := (eLpNorm X 2 volume).toReal with ha
  set b : ℝ := (eLpNorm Y 2 volume).toReal with hb
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hη1 : 0 < ε / (2 * (M * b + 1)) := by positivity
  have hη2 : 0 < ε / (2 * (M * a + 1)) := by positivity
  have e1 := trans_small hX hη1
  have e2 := trans_small hY hη2
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨δ0, hδ0, fun h hh hhδ δ hδ => ?_⟩
  obtain ⟨hI, -, hEq⟩ := fubini_eq hXm hYm hX hY hψ hψc hh δ
  rw [hEq]
  have hbound : ∀ ρ ∈ Icc 0 h, |Phi X Y ψ ρ δ - Phi X Y ψ 0 0| ≤ ε := by
    intro ρ hρ
    have hρδ : dist ρ 0 < δ0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hρ.1]; linarith [hρ.2]
    have hδδ : dist δ 0 < δ0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ.1]; linarith [hδ.2]
    have p1 := (hδ0' hρδ).1
    have p2 := (hδ0' hδδ).2
    have q1 : (eLpNorm (fun t => X (t + ρ) - X t) 2 volume).toReal ≤ ε / (2 * (M * b + 1)) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top p1
      rwa [ENNReal.toReal_ofReal hη1.le] at this
    have q2 : (eLpNorm (fun t => Y (t + δ) - Y t) 2 volume).toReal ≤ ε / (2 * (M * a + 1)) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top p2
      rwa [ENNReal.toReal_ofReal hη2.le] at this
    refine (Phi_diff hX hY hψ hψc.measurable ρ δ).trans ?_
    have r1 : M * ((eLpNorm (fun t => X (t + ρ) - X t) 2 volume).toReal * b) ≤ ε / 2 := by
      calc M * ((eLpNorm (fun t => X (t + ρ) - X t) 2 volume).toReal * b)
          ≤ M * (ε / (2 * (M * b + 1)) * b) := by gcongr
        _ = ε / 2 * ((M * b) / (M * b + 1)) := by field_simp
        _ ≤ ε / 2 * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; linarith
        _ = ε / 2 := by ring
    have r2 : M * (a * (eLpNorm (fun t => Y (t + δ) - Y t) 2 volume).toReal) ≤ ε / 2 := by
      calc M * (a * (eLpNorm (fun t => Y (t + δ) - Y t) 2 volume).toReal)
          ≤ M * (a * (ε / (2 * (M * a + 1)))) := by gcongr
        _ = ε / 2 * ((M * a) / (M * a + 1)) := by field_simp
        _ ≤ ε / 2 * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; linarith
        _ = ε / 2 := by ring
    nlinarith [r1, r2]
  have h00 : Phi X Y ψ 0 0 = ∫ t, ψ t * X t (Y t) := by simp [Phi]
  rw [← h00]
  have hconst : (1 / h) * ∫ ρ in (0:ℝ)..h, Phi X Y ψ 0 0 = Phi X Y ψ 0 0 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
  have hsub : (1 / h) * (∫ ρ in (0:ℝ)..h, Phi X Y ψ ρ δ) - Phi X Y ψ 0 0 =
      (1 / h) * ∫ ρ in (0:ℝ)..h, (Phi X Y ψ ρ δ - Phi X Y ψ 0 0) := by
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const, mul_sub, hconst]
  rw [hsub, abs_mul, abs_of_pos (by positivity : 0 < 1 / h)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
    (f := fun ρ => Phi X Y ψ ρ δ - Phi X Y ψ 0 0) (C := ε) (fun ρ hρ => by
      rw [uIoc_of_le hh.le] at hρ
      simpa [Real.norm_eq_abs] using hbound ρ ⟨hρ.1.le, hρ.2⟩)
  rw [Real.norm_eq_abs] at this
  calc 1 / h * |∫ ρ in (0:ℝ)..h, (Phi X Y ψ ρ δ - Phi X Y ψ 0 0)| ≤ 1 / h * (ε * |h - 0|) :=
        by gcongr
    _ = ε := by rw [sub_zero, abs_of_pos hh]; field_simp

end key2

end IBPc
end Q0ca_C2

section Q0ca_D1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open HunterPDE.Parabolic

namespace IBPc

section D1

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma smul_integrable_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ}
    {f : ℝ → E} (hf : Integrable f μ) {g : ℝ → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun t => g t • f t) μ := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgs
  exact hf.smul_of_top_right (memLp_top_of_bound hg.aestronglyMeasurable C (ae_of_all _ hC))

lemma scalar_weak (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hdu : HasWeakTimeDeriv HT.toDualV T u ut)
    {uc : ℝ → H} (huc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc t = HT.toH (u t)) (w : V) :
    ∀ φ, IsTestFunctionOn T φ →
      ∫ t in Ioo 0 T, deriv φ t * inner ℝ (uc t) (HT.toH w) = -∫ t in Ioo 0 T, φ t * ut t w := by
  intro φ hφ
  have : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have hu1 : Integrable u (volume.restrict (Ioo 0 T)) := hu.integrable one_le_two
  have hut1 : Integrable ut (volume.restrict (Ioo 0 T)) := hut.integrable one_le_two
  have hd : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hds : HasCompactSupport (deriv φ) := hφ.2.1.deriv
  have i1 : Integrable (fun t => deriv φ t • HT.toDualV (u t)) (volume.restrict (Ioo 0 T)) :=
    smul_integrable_test (HT.toDualV.integrable_comp hu1) hd hds
  have i2 : Integrable (fun t => φ t • ut t) (volume.restrict (Ioo 0 T)) :=
    smul_integrable_test hut1 hφ.1.continuous hφ.2.1
  have e := congrArg (ContinuousLinearMap.apply ℝ ℝ w) (hdu φ hφ)
  rw [← ContinuousLinearMap.integral_comp_comm _ i1, map_neg,
    ← ContinuousLinearMap.integral_comp_comm _ i2] at e
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at e
  have hconv : ∫ t in Ioo 0 T, deriv φ t * inner ℝ (uc t) (HT.toH w) =
      ∫ t in Ioo 0 T, deriv φ t * (HT.toDualV (u t)) w := by
    refine integral_congr_ae ?_
    filter_upwards [huc] with t ht
    rw [ht]
    simp [HilbertTriple.toDualV, HT.pairing]
  rw [hconv]
  exact e

lemma uc_increment (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hdu : HasWeakTimeDeriv HT.toDualV T u ut)
    {uc : ℝ → H} (hucc : ContinuousOn uc (Icc 0 T))
    (huc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc t = HT.toH (u t)) (w : V) :
    ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
      inner ℝ (uc t) (HT.toH w) - inner ℝ (uc s) (HT.toH w) = ∫ r in s..t, ut r w := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have hw : IntegrableOn (fun t => ut t w) (Ioo 0 T) :=
    (ContinuousLinearMap.apply ℝ ℝ w).integrable_comp (hut.integrable one_le_two)
  exact ftc_of_weak hT (hucc.inner continuousOn_const) hw (scalar_weak HT hT hu hut hdu huc w)

end D1

end IBPc
end Q0ca_D1

section Q0ca_D2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace IBPc

/-- Difference quotients of a test function, integrated against a continuous function. -/
lemma dq_tendsto {ψ φ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hφ : Continuous φ) :
    Tendsto (fun h : ℝ => ∫ t, ((ψ t - ψ (t - h)) / h) * φ t) (𝓝[>] 0)
      (𝓝 (∫ t, deriv ψ t * φ t)) := by
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  obtain ⟨M, hM⟩ := hd.bounded_above_of_compact_support hψs.deriv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R0, hR0⟩ := hψs.isCompact.isBounded.subset_closedBall (0:ℝ)
  set R : ℝ := |R0| + 1 with hR
  have hsub : tsupport ψ ⊆ Icc (-R) R := by
    intro x hx
    have := hR0 hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have h1 : R0 ≤ |R0| := le_abs_self _
    have h2 : -|R0| ≤ R0 := neg_abs_le _
    have := abs_le.1 this
    constructor <;> linarith [this.1, this.2]
  set K : Set ℝ := Icc (-R) (R + 1) with hK
  set bound : ℝ → ℝ := K.indicator (fun t => M * |φ t|) with hbound
  have hbi : Integrable bound volume := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    exact (continuous_const.mul hφ.abs).integrableOn_Icc
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbi ?_
  · refine Filter.Eventually.of_forall fun h => ?_
    exact ((((hψ.continuous).sub (hψ.continuous.comp (continuous_id.sub continuous_const))).div_const
      h).mul hφ).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with h hh
    refine ae_of_all _ fun t => ?_
    by_cases htK : t ∈ K
    · rw [hbound, indicator_of_mem htK, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hh.1]
      have hmvt : ‖ψ t - ψ (t - h)‖ ≤ M * ‖t - (t - h)‖ := by
        refine Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := ψ) (x := t - h) (y := t)
          (fun x _ => hdiff x) (fun x _ => hM x) convex_univ (mem_univ _) (mem_univ _)
      have : ‖t - (t - h)‖ = h := by
        rw [sub_sub_cancel, Real.norm_eq_abs, abs_of_pos hh.1]
      rw [this, Real.norm_eq_abs] at hmvt
      calc |ψ t - ψ (t - h)| / h * |φ t| ≤ M * |φ t| := by
            gcongr
            rw [div_le_iff₀ hh.1]; linarith
        _ = _ := rfl
    · have h1 : ψ t = 0 := by
        by_contra hne
        have := hsub (subset_tsupport _ hne)
        exact htK ⟨this.1, by linarith [this.2]⟩
      have h2 : ψ (t - h) = 0 := by
        by_contra hne
        have := hsub (subset_tsupport _ hne)
        exact htK ⟨by linarith [this.1, hh.1], by linarith [this.2, hh.2]⟩
      rw [hbound, indicator_of_notMem htK, h1, h2]
      simp
  · refine ae_of_all _ fun t => ?_
    have hdt : HasDerivAt ψ (deriv ψ t) t := (hdiff t).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hdt
    have hg : Tendsto (fun h : ℝ => t - h) (𝓝[>] 0) (𝓝[≠] t) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun h : ℝ => t - h) (𝓝 0) (𝓝 (t - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        rw [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [mem_compl_iff, mem_singleton_iff]
        intro hx
        have : (0:ℝ) < h := hh
        linarith
    have := (hdt.comp hg).mul_const (φ t)
    refine this.congr fun h => ?_
    simp only [Function.comp, slope_def_field]
    rw [show t - h - t = -h by ring, show ψ (t - h) - ψ t = -(ψ t - ψ (t - h)) by ring]
    rw [neg_div_neg_eq]


lemma dq_identity {ψ φ : ℝ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hφc : Continuous φ) {h : ℝ} (hh : 0 < h) :
    ∫ t, ((ψ t - ψ (t - h)) / h) * φ t = -∫ t, ψ t * ((φ (t + h) - φ t) / h) := by
  have i1 : Integrable (fun t => ψ t * φ t) volume :=
    (hψc.mul hφc).integrable_of_hasCompactSupport hψs.mul_right
  have i2 : Integrable (fun t => ψ t * φ (t + h)) volume :=
    (hψc.mul (hφc.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hψs.mul_right
  have i3 : Integrable (fun t => ψ (t - h) * φ t) volume :=
    ((hψc.comp (continuous_id.sub continuous_const)).mul hφc).integrable_of_hasCompactSupport
      ((hψs.comp_homeomorph (Homeomorph.subRight h)).mul_right)
  have e3 : ∫ t, ψ (t - h) * φ t = ∫ t, ψ t * φ (t + h) := by
    have := integral_add_right_eq_self (μ := volume) (fun t => ψ (t - h) * φ t) h
    simp only [add_sub_cancel_right] at this
    exact this.symm
  have l1 : ∫ t, ((ψ t - ψ (t - h)) / h) * φ t =
      (1 / h) * ((∫ t, ψ t * φ t) - ∫ t, ψ (t - h) * φ t) := by
    rw [← integral_sub i1 i3, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    field_simp
  have l2 : ∫ t, ψ t * ((φ (t + h) - φ t) / h) =
      (1 / h) * ((∫ t, ψ t * φ (t + h)) - ∫ t, ψ t * φ t) := by
    rw [← integral_sub i2 i1, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    field_simp
  rw [l1, l2, e3]
  ring

end IBPc
end Q0ca_D2

section Q0ca_D3a
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open HunterPDE.Parabolic

namespace IBPc

section D3a

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma split_alg (a1 a0 b1 b0 wv wu : H) (h1 : a0 = wu) (h2 : b1 = wv) :
    inner ℝ a1 b1 - inner ℝ a0 b0 =
      (inner ℝ a1 wv - inner ℝ a0 wv) + (inner ℝ b1 wu - inner ℝ b0 wu) := by
  subst h1 h2
  rw [real_inner_comm b0 a0, real_inner_comm b1 a0]
  ring

lemma ae_shift_mem {T h : ℝ} {P : ℝ → Prop} (hP : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), P s) :
    ∀ᵐ t, t + h ∈ Ioo 0 T → P (t + h) := by
  have hae : ∀ᵐ s, s ∈ Ioo 0 T → P s := (ae_restrict_iff' measurableSet_Ioo).1 hP
  exact (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hae

theorem claimA (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T)
    {u v : ℝ → V} {ut vt : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hv : MemLp v 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hvt : MemLp vt 2 (volume.restrict (Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (hdv : HasWeakTimeDeriv HT.toDualV T v vt)
    {uc vc : ℝ → H} (hucc : Continuous uc) (hvcc : Continuous vc)
    (huc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc t = HT.toH (u t))
    (hvc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), vc t = HT.toH (v t))
    {X1 X2 : ℝ → StrongDual ℝ V} {Y1 Y2 : ℝ → V}
    (hX1 : ∀ r ∈ Ioo 0 T, X1 r = ut r) (hY1 : ∀ r ∈ Ioo 0 T, Y1 r = v r)
    (hX2 : ∀ r ∈ Ioo 0 T, X2 r = vt r) (hY2 : ∀ r ∈ Ioo 0 T, Y2 r = u r)
    (sX1 : StronglyMeasurable X1) (sY1 : StronglyMeasurable Y1)
    (sX2 : StronglyMeasurable X2) (sY2 : StronglyMeasurable Y2)
    (mX1 : MemLp X1 2 volume) (mY1 : MemLp Y1 2 volume)
    (mX2 : MemLp X2 2 volume) (mY2 : MemLp Y2 2 volume)
    {ψ : ℝ → ℝ} {M : ℝ} (hM' : ∀ t, |ψ t| ≤ M) (hψc : Continuous ψ)
    {a b c : ℝ} (ha : 0 < a) (hb : b < T) (hca : c ≤ a) (hcb : c ≤ T - b)
    (hsub : tsupport ψ ⊆ Icc a b) {h : ℝ} (hh : 0 < h) (hhc : h < c) :
    ∫ t, ψ t * ((inner ℝ (uc (t + h)) (vc (t + h)) - inner ℝ (uc t) (vc t)) / h) =
      (∫ t, ψ t * ((1 / h) * ∫ r in t..t + h, X1 r (Y1 (t + h)))) +
      ∫ t, ψ t * ((1 / h) * ∫ r in t..t + h, X2 r (Y2 (t + 0))) := by
  obtain ⟨-, hi1, -⟩ := fubini_eq sX1 sY1 mX1 mY1 hM' hψc hh h
  obtain ⟨-, hi2, -⟩ := fubini_eq sX2 sY2 mX2 mY2 hM' hψc hh 0
  rw [← integral_add hi1 hi2]
  have hae1 : ∀ᵐ t, t ∈ Ioo 0 T → uc t = HT.toH (u t) :=
    (ae_restrict_iff' measurableSet_Ioo).1 huc
  have hae2' : ∀ᵐ t, t + h ∈ Ioo 0 T → vc (t + h) = HT.toH (v (t + h)) := ae_shift_mem hvc
  refine integral_congr_ae ?_
  filter_upwards [hae1, hae2'] with t h1 h2
  by_cases hψ0 : ψ t = 0
  · simp [hψ0]
  have htI : t ∈ Icc a b := hsub (subset_tsupport _ hψ0)
  have ht0 : t ∈ Ioo 0 T := ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have hth : t + h ∈ Ioo 0 T := ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have hIt : t ∈ Icc (0:ℝ) T := Ioo_subset_Icc_self ht0
  have hIth : t + h ∈ Icc (0:ℝ) T := Ioo_subset_Icc_self hth
  have e1 := uc_increment HT hT hu hut hdu hucc.continuousOn huc (v (t + h)) t hIt (t + h) hIth
  have e2 := uc_increment HT hT hv hvt hdv hvcc.continuousOn hvc (u t) t hIt (t + h) hIth
  have k1 : ∫ r in t..t + h, X1 r (Y1 (t + h)) = ∫ r in t..t + h, ut r (v (t + h)) := by
    rw [hY1 _ hth]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (by linarith)] at hr
    have hr' : r ∈ Ioo 0 T := ⟨by linarith [htI.1, hr.1], by linarith [hr.2, hth.2]⟩
    show X1 r (v (t + h)) = ut r (v (t + h))
    rw [hX1 r hr']
  have k2 : ∫ r in t..t + h, X2 r (Y2 (t + 0)) = ∫ r in t..t + h, vt r (u t) := by
    rw [add_zero, hY2 _ ht0]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (by linarith)] at hr
    have hr' : r ∈ Ioo 0 T := ⟨by linarith [htI.1, hr.1], by linarith [hr.2, hth.2]⟩
    show X2 r (u t) = vt r (u t)
    rw [hX2 r hr']
  rw [k1, k2, ← e1, ← e2]
  have hdiff := split_alg (uc (t + h)) (uc t) (vc (t + h)) (vc t) (HT.toH (v (t + h)))
    (HT.toH (u t)) (h1 ht0) (h2 hth)
  rw [hdiff]
  field_simp

end D3a

end IBPc
end Q0ca_D3a

section Q0ca_D3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open HunterPDE.Parabolic

namespace IBPc

section D3

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma memLp_ind_normed {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → E} (hf : StronglyMeasurable f) {p : ENNReal} (h : MemLp f p (volume.restrict s)) :
    MemLp (s.indicator f) p volume := by
  refine ⟨(hf.indicator hs).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact h.2

theorem weak_product (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T)
    {u v : ℝ → V} {ut vt : ℝ → StrongDual ℝ V}
    (hum : StronglyMeasurable u) (hvm : StronglyMeasurable v)
    (hutm : StronglyMeasurable ut) (hvtm : StronglyMeasurable vt)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hv : MemLp v 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hvt : MemLp vt 2 (volume.restrict (Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (hdv : HasWeakTimeDeriv HT.toDualV T v vt)
    {uc vc : ℝ → H} (hucc : Continuous uc) (hvcc : Continuous vc)
    (huc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc t = HT.toH (u t))
    (hvc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), vc t = HT.toH (v t))
    {ψ : ℝ → ℝ} (hψ : IsTestFunctionOn T ψ) :
    ∫ t in Ioo 0 T, deriv ψ t * inner ℝ (uc t) (vc t) =
      -∫ t in Ioo 0 T, ψ t * (ut t (v t) + vt t (u t)) := by
  obtain ⟨hψd, hψs, hψt⟩ := hψ
  have hψc : Continuous ψ := hψd.continuous
  obtain ⟨a, b, ha, hab, hb, hsub⟩ := exists_Icc_of_compact hT hψs.isCompact hψt
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψs
  have hM' : ∀ t, |ψ t| ≤ M := fun t => by simpa using hM t
  -- zero extensions
  obtain ⟨X1, hX1⟩ : ∃ X1 : ℝ → StrongDual ℝ V, X1 = (Ioo (0:ℝ) T).indicator ut := ⟨_, rfl⟩
  obtain ⟨Y1, hY1⟩ : ∃ Y1 : ℝ → V, Y1 = (Ioo (0:ℝ) T).indicator v := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ X2 : ℝ → StrongDual ℝ V, X2 = (Ioo (0:ℝ) T).indicator vt := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y2 : ℝ → V, Y2 = (Ioo (0:ℝ) T).indicator u := ⟨_, rfl⟩
  have mX1 : MemLp X1 2 volume := by
    rw [hX1]; exact memLp_ind_normed (E := StrongDual ℝ V) measurableSet_Ioo hutm hut
  have mY1 : MemLp Y1 2 volume := by
    rw [hY1]; exact memLp_ind_normed (E := V) measurableSet_Ioo hvm hv
  have mX2 : MemLp X2 2 volume := by
    rw [hX2]; exact memLp_ind_normed (E := StrongDual ℝ V) measurableSet_Ioo hvtm hvt
  have mY2 : MemLp Y2 2 volume := by
    rw [hY2]; exact memLp_ind_normed (E := V) measurableSet_Ioo hum hu
  have sX1 : StronglyMeasurable X1 := by rw [hX1]; exact hutm.indicator measurableSet_Ioo
  have sY1 : StronglyMeasurable Y1 := by rw [hY1]; exact hvm.indicator measurableSet_Ioo
  have sX2 : StronglyMeasurable X2 := by rw [hX2]; exact hvtm.indicator measurableSet_Ioo
  have sY2 : StronglyMeasurable Y2 := by rw [hY2]; exact hum.indicator measurableSet_Ioo
  have eX1 : ∀ r ∈ Ioo (0:ℝ) T, X1 r = ut r := fun r hr => by rw [hX1]; exact indicator_of_mem hr _
  have eY1 : ∀ r ∈ Ioo (0:ℝ) T, Y1 r = v r := fun r hr => by rw [hY1]; exact indicator_of_mem hr _
  have eX2 : ∀ r ∈ Ioo (0:ℝ) T, X2 r = vt r := fun r hr => by rw [hX2]; exact indicator_of_mem hr _
  have eY2 : ∀ r ∈ Ioo (0:ℝ) T, Y2 r = u r := fun r hr => by rw [hY2]; exact indicator_of_mem hr _
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun t => inner ℝ (uc t) (vc t) := ⟨_, rfl⟩
  have hφc : Continuous φ := by rw [hφ]; exact hucc.inner hvcc
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min a (T - b) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact lt_min ha (by linarith)
  have hca : c ≤ a := by rw [hc]; exact min_le_left _ _
  have hcb : c ≤ T - b := by rw [hc]; exact min_le_right _ _
  obtain ⟨I1, hI1⟩ : ∃ I1 : ℝ, I1 = ∫ t, ψ t * X1 t (Y1 t) := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I2 : ℝ, I2 = ∫ t, ψ t * X2 t (Y2 t) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℝ, S = fun h => ∫ t, ψ t * ((φ (t + h) - φ t) / h) := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ Q1 : ℝ → ℝ, Q1 = fun h =>
      ∫ t, ψ t * ((1 / h) * ∫ r in t..t + h, X1 r (Y1 (t + h))) := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : ℝ → ℝ, Q2 = fun h =>
      ∫ t, ψ t * ((1 / h) * ∫ r in t..t + h, X2 r (Y2 (t + 0))) := ⟨_, rfl⟩
  -- Claim A
  have hA : ∀ h : ℝ, 0 < h → h < c → S h = Q1 h + Q2 h := by
    intro h hh hhc
    rw [hS, hQ1, hQ2]
    simp only [hφ]
    exact claimA HT hT hu hv hut hvt hdu hdv hucc hvcc huc hvc eX1 eY1 eX2 eY2 sX1 sY1 sX2 sY2
      mX1 mY1 mX2 mY2 hM' hψc ha hb hca hcb hsub hh hhc
  -- Claim B
  have hB : Tendsto S (𝓝[>] 0) (𝓝 (I1 + I2)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨h1, hh1, k1⟩ := key sX1 sY1 mX1 mY1 hM' hψc (ε := ε / 3) (by positivity)
    obtain ⟨h2, hh2, k2⟩ := key sX2 sY2 mX2 mY2 hM' hψc (ε := ε / 3) (by positivity)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hcpos (lt_min hh1 hh2))] with h hh
    have hc' : h < c := lt_of_lt_of_le hh.2 (min_le_left _ _)
    have hh1' : h < h1 := lt_of_lt_of_le hh.2 ((min_le_right _ _).trans (min_le_left _ _))
    have hh2' : h < h2 := lt_of_lt_of_le hh.2 ((min_le_right _ _).trans (min_le_right _ _))
    rw [Real.dist_eq, hA h hh.1 hc']
    have q1 := k1 h hh.1 hh1' h ⟨hh.1.le, le_rfl⟩
    have q2 := k2 h hh.1 hh2' 0 ⟨le_rfl, hh.1.le⟩
    have key2 : ∀ a b c d : ℝ, |a - c| ≤ ε / 3 → |b - d| ≤ ε / 3 → |a + b - (c + d)| < ε :=
      fun a b c d h1 h2 => by
        rw [abs_le] at h1 h2
        exact abs_lt.2 ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
    rw [hQ1, hQ2, hI1, hI2]
    exact key2 _ _ _ _ q1 q2
  -- Claim C
  have hC : ∀ h : ℝ, 0 < h → ∫ t, ((ψ t - ψ (t - h)) / h) * φ t = - S h := by
    intro h hh
    rw [hS]
    exact dq_identity hψc hψs hφc hh
  -- Combine
  have hD := dq_tendsto hψd hψs hφc
  have hE : Tendsto (fun h => - S h) (𝓝[>] 0) (𝓝 (-(I1 + I2))) := hB.neg
  have hD' : Tendsto (fun h => - S h) (𝓝[>] 0) (𝓝 (∫ t, deriv ψ t * φ t)) := by
    refine hD.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hC h hh
  have hEq : ∫ t, deriv ψ t * φ t = -(I1 + I2) := tendsto_nhds_unique hD' hE
  -- conversions
  have hlhs : ∫ t in Ioo 0 T, deriv ψ t * φ t = ∫ t, deriv ψ t * φ t := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    have : deriv ψ t = 0 := by
      by_contra hne
      exact ht (hψt (support_deriv_subset (Function.mem_support.2 hne)))
    simp [this]
  have iA : Integrable (fun t => ψ t * X1 t (Y1 t)) volume :=
    (pair_integrable mX1 mY1).bdd_mul hψc.aestronglyMeasurable
      (ae_of_all _ fun t => by simpa using hM' t)
  have iB : Integrable (fun t => ψ t * X2 t (Y2 t)) volume :=
    (pair_integrable mX2 mY2).bdd_mul hψc.aestronglyMeasurable
      (ae_of_all _ fun t => by simpa using hM' t)
  have hrhs : ∫ t in Ioo 0 T, ψ t * (ut t (v t) + vt t (u t)) = I1 + I2 := by
    have s1 : ∫ t in Ioo 0 T, ψ t * (ut t (v t) + vt t (u t)) =
        ∫ t in Ioo 0 T, (ψ t * X1 t (Y1 t) + ψ t * X2 t (Y2 t)) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      simp only [eX1 t ht, eY1 t ht, eX2 t ht, eY2 t ht]
      ring
    rw [s1, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_add iA iB, hI1, hI2]
    intro t ht
    have : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hψt h))
    simp [this]
  rw [hrhs]
  have : ∫ t in Ioo 0 T, deriv ψ t * inner ℝ (uc t) (vc t) = ∫ t in Ioo 0 T, deriv ψ t * φ t := by
    rw [hφ]
  rw [this, hlhs]
  exact hEq

end D3

end IBPc
end Q0ca_D3

section Q0ca_D4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open HunterPDE.Parabolic

namespace IBPc

section D4

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma pair_integrable_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {μ : Measure ℝ}
    {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun t => X t (Y t)) μ := by
  rw [← memLp_one_iff_integrable]
  refine ⟨(continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hX.1.prodMk hY.1), ?_⟩
  have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) hX.1 hY.1
    (fun (f : StrongDual ℝ W) (w : W) => f w) 1
    (ae_of_all _ fun t => by
      have := (X t).le_opNorm (Y t)
      simpa [one_mul] using this)
  simp only [ENNReal.coe_one, one_mul] at this
  exact lt_of_le_of_lt this (ENNReal.mul_lt_top hX.2 hY.2)

theorem ibp_core (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T)
    {u v : ℝ → V} {ut vt : ℝ → StrongDual ℝ V}
    (hum : StronglyMeasurable u) (hvm : StronglyMeasurable v)
    (hutm : StronglyMeasurable ut) (hvtm : StronglyMeasurable vt)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hv : MemLp v 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hvt : MemLp vt 2 (volume.restrict (Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (hdv : HasWeakTimeDeriv HT.toDualV T v vt)
    {uc vc : ℝ → H} (hucc : Continuous uc) (hvcc : Continuous vc)
    (huc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc t = HT.toH (u t))
    (hvc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), vc t = HT.toH (v t)) :
    ∫ t in Ioo 0 T, ut t (v t) =
      inner ℝ (uc T) (vc T) - inner ℝ (uc 0) (vc 0) - ∫ t in Ioo 0 T, vt t (u t) := by
  have i1 : IntegrableOn (fun t => ut t (v t)) (Ioo 0 T) := pair_integrable_gen hut hv
  have i2 : IntegrableOn (fun t => vt t (u t)) (Ioo 0 T) := pair_integrable_gen hvt hu
  have hφc : Continuous (fun t => inner ℝ (uc t) (vc t)) := hucc.inner hvcc
  have := ftc_of_weak hT hφc.continuousOn (i1.add i2) (fun ψ hψ =>
    weak_product HT hT hum hvm hutm hvtm hu hv hut hvt hdu hdv hucc hvcc huc hvc hψ)
    0 ⟨le_rfl, hT.le⟩ T ⟨hT.le, le_rfl⟩
  rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo] at this
  simp only [Pi.add_apply] at this
  rw [integral_add i1 i2] at this
  linarith

end D4

end IBPc
end Q0ca_D4

section Qf92_S
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HTC

section S

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Steklov average. -/
noncomputable def stek (F : ℝ → E) (h t : ℝ) : E := h⁻¹ • ∫ r in t..t + h, F r

lemma stek_sub {F : ℝ → E} (hFi : Integrable F volume) {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    stek F h t - F t = ∫ θ in (0:ℝ)..1, (F (t + θ * h) - F t) := by
  have hi0 : Integrable (fun θ => F (h * θ + t)) volume :=
    (hFi.comp_add_right t).comp_mul_left' hh
  have hi : IntervalIntegrable (fun θ => F (t + θ * h)) volume 0 1 := by
    have e : (fun θ => F (t + θ * h)) = fun θ => F (h * θ + t) := by
      funext θ; congr 1; ring
    rw [e]; exact hi0.intervalIntegrable
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
  have e : ∫ θ in (0:ℝ)..1, F (t + θ * h) = h⁻¹ • ∫ r in t..t + h, F r := by
    have := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) F hh t
    simp only [mul_zero, zero_add, mul_one] at this
    rw [add_comm h t] at this
    rw [← this]
    congr 1; funext θ; congr 1; ring
  rw [e, intervalIntegral.integral_const, sub_zero, one_smul]
  rfl

lemma avg_eLpNorm_le {g : ℝ → ℝ → E} (hg : StronglyMeasurable (Function.uncurry g))
    {M : ℝ≥0∞} (hb : ∀ θ ∈ Ioc (0:ℝ) 1, eLpNorm (g θ) 2 volume ≤ M) :
    eLpNorm (fun t => ∫ θ in Ioc (0:ℝ) 1, g θ t) 2 volume ≤ M := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0:ℝ) 1)) := ⟨by simp⟩
  have hpt : ∀ t, ‖∫ θ in Ioc (0:ℝ) 1, g θ t‖ₑ ^ (2:ℝ) ≤
      ∫⁻ θ in Ioc (0:ℝ) 1, ‖g θ t‖ₑ ^ (2:ℝ) := by
    intro t
    have hm : AEStronglyMeasurable (fun θ => g θ t) (volume.restrict (Ioc (0:ℝ) 1)) :=
      (hg.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have h1 := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc (0:ℝ) 1))
      (fun θ => g θ t)
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := volume.restrict (Ioc (0:ℝ) 1))
      (p := 1) (q := 2) (by norm_num) hm
    rw [eLpNorm_one_eq_lintegral_enorm,
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at h2
    simp only [ENNReal.toReal_ofNat] at h2
    calc ‖∫ θ in Ioc (0:ℝ) 1, g θ t‖ₑ ^ (2:ℝ)
        ≤ ((∫⁻ θ in Ioc (0:ℝ) 1, ‖g θ t‖ₑ ^ (2:ℝ)) ^ (1 / (2:ℝ))) ^ (2:ℝ) := by
          gcongr; exact h1.trans h2
      _ = _ := by rw [← ENNReal.rpow_mul]; norm_num
  have hmeas : AEMeasurable (Function.uncurry fun (t θ : ℝ) => ‖g θ t‖ₑ ^ (2:ℝ))
      (volume.prod (volume.restrict (Ioc (0:ℝ) 1))) :=
    ((hg.comp_measurable measurable_swap).enorm.pow_const (2:ℝ)).aemeasurable
  have hsw := lintegral_lintegral_swap hmeas
  have hθ : ∀ θ ∈ Ioc (0:ℝ) 1, ∫⁻ t, ‖g θ t‖ₑ ^ (2:ℝ) ≤ M ^ (2:ℝ) := by
    intro θ hθ
    have := hb θ hθ
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at this
    simp only [ENNReal.toReal_ofNat] at this
    calc ∫⁻ t, ‖g θ t‖ₑ ^ (2:ℝ) = ((∫⁻ t, ‖g θ t‖ₑ ^ (2:ℝ)) ^ (1 / (2:ℝ))) ^ (2:ℝ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ M ^ (2:ℝ) := by gcongr
  have htot : ∫⁻ t, ‖∫ θ in Ioc (0:ℝ) 1, g θ t‖ₑ ^ (2:ℝ) ≤ M ^ (2:ℝ) := by
    calc ∫⁻ t, ‖∫ θ in Ioc (0:ℝ) 1, g θ t‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ t, ∫⁻ θ in Ioc (0:ℝ) 1, ‖g θ t‖ₑ ^ (2:ℝ) := lintegral_mono fun t => hpt t
      _ = ∫⁻ θ in Ioc (0:ℝ) 1, ∫⁻ t, ‖g θ t‖ₑ ^ (2:ℝ) := hsw
      _ ≤ ∫⁻ θ in Ioc (0:ℝ) 1, M ^ (2:ℝ) := setLIntegral_mono' measurableSet_Ioc hθ
      _ = M ^ (2:ℝ) := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ t, ‖∫ θ in Ioc (0:ℝ) 1, g θ t‖ₑ ^ (2:ℝ)) ^ (1 / (2:ℝ))
      ≤ (M ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by gcongr
    _ = M := by rw [← ENNReal.rpow_mul]; norm_num

/-- Steklov averages converge in `L²(ℝ; E)`. -/
theorem stek_tendsto {F : ℝ → E} (hF : MemLp F 2 volume) (hFm : StronglyMeasurable F)
    (hFi : Integrable F volume) :
    Tendsto (fun h => eLpNorm (fun t => stek F h t - F t) 2 volume) (𝓝[≠] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => hεt ▸ le_top
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  have hts := IBPc.trans_small hF hε'
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hts
  have hev1 : ∀ᶠ h in 𝓝[≠] (0:ℝ), h ∈ Metric.ball (0:ℝ) δ :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hδ)
  have hev2 : ∀ᶠ h in 𝓝[≠] (0:ℝ), h ≠ 0 := self_mem_nhdsWithin
  filter_upwards [hev1, hev2] with h hb hh0
  have e : (fun t => stek F h t - F t) = fun t => ∫ θ in Ioc (0:ℝ) 1, (F (t + θ * h) - F t) := by
    funext t; rw [stek_sub hFi hh0 t, intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  refine (avg_eLpNorm_le (g := fun θ t => F (t + θ * h) - F t) ?_ ?_).trans
    (ENNReal.ofReal_toReal hεt).le
  · exact ((hFm.comp_measurable (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 + p.1 * h)).sub
      (hFm.comp_measurable measurable_snd) :)
  · intro θ hθ
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right] at hb
    rw [dist_zero_right, norm_mul]
    calc ‖θ‖ * ‖h‖ ≤ 1 * ‖h‖ := by
          gcongr; rw [Real.norm_eq_abs, abs_of_pos hθ.1]; exact hθ.2
      _ < δ := by simpa using hb

end S

end HTC
end Qf92_S

section Qf92_D
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Interval
open HunterPDE.Parabolic

namespace HTC

section D

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma toDualV_apply (HT : HilbertTriple V H) (x y : V) :
    HT.toDualV x y = inner ℝ (HT.toH x) (HT.toH y) := by
  simp [HilbertTriple.toDualV, HT.pairing]

lemma toDualV_symm (HT : HilbertTriple V H) (x y : V) : HT.toDualV x y = HT.toDualV y x := by
  rw [toDualV_apply, toDualV_apply, real_inner_comm]

lemma toDualV_self (HT : HilbertTriple V H) (x : V) : HT.toDualV x x = ‖HT.toH x‖ ^ 2 := by
  rw [toDualV_apply, real_inner_self_eq_norm_sq]

/-- Derivative of the squared `ℋ`-norm along a `𝒱`-valued curve whose `𝒱'`-image is
differentiable (uses the symmetry of the pairing). -/
lemma sq_hasDerivAt (HT : HilbertTriple V H) {B : ℝ → V} {A' : StrongDual ℝ V} {t : ℝ}
    (hB : ContinuousAt B t) (hA : HasDerivAt (fun s => HT.toDualV (B s)) A' t) :
    HasDerivAt (fun s => ‖HT.toH (B s)‖ ^ 2) (2 * A' (B t)) t := by
  rw [hasDerivAt_iff_tendsto_slope] at hA ⊢
  have hBB : Tendsto (fun s => B s + B t) (𝓝[≠] t) (𝓝 (B t + B t)) :=
    ((hB.add continuousAt_const).tendsto).mono_left nhdsWithin_le_nhds
  have hlim := ((continuous_fst.clm_apply continuous_snd).tendsto (A', B t + B t)).comp
    (hA.prodMk_nhds hBB)
  have e2 : A' (B t + B t) = 2 * A' (B t) := by rw [map_add]; ring
  simp only [e2] at hlim
  refine hlim.congr' (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, slope_def_module, ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, map_add, map_add, ← toDualV_self HT (B s),
    ← toDualV_self HT (B t), toDualV_symm HT (B s) (B t)]
  ring

lemma ftc_window {a b : ℝ} {f g : ℝ → ℝ} (hfc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) (hg : IntegrableOn g (Ioo a b)) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, f t - f s = ∫ r in s..t, g r := by
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → f t - f s = ∫ r in s..t, g r := by
    intro s hs t ht hst
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hfc.mono hsub)
      (fun x hx => hd x ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩) ?_).symm
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hst]
    exact hg.mono_set (Ioo_subset_Ioo hs.1 ht.2)
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [intervalIntegral.integral_symm, ← key t ht s hs hts]; ring

lemma sup_bound {a b : ℝ} (hab : a < b) {F g : ℝ → ℝ} (hFc : ContinuousOn F (Icc a b))
    (hg : IntegrableOn g (Ioo a b))
    (hftc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F t - F s = ∫ r in s..t, g r) :
    ∀ t ∈ Icc a b, F t ≤ (b - a)⁻¹ * (∫ s in Ioo a b, F s) + ∫ r in Ioo a b, |g r| := by
  intro t ht
  have hgc : IntegrableOn g (Ioc a b) := (integrableOn_Ioc_iff_integrableOn_Ioo).2 hg
  have hI : ∀ s ∈ Icc a b, F t ≤ F s + ∫ r in Ioo a b, |g r| := by
    intro s hs
    have e := hftc s hs t ht
    have h1 : ‖∫ r in s..t, g r‖ ≤ ∫ r in Ι s t, ‖g r‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    have hsub : Ι s t ⊆ Ioc a b := by
      intro x hx
      rcases (mem_uIoc.1 hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hs.1.trans_lt h1, h2.trans ht.2⟩
      · exact ⟨ht.1.trans_lt h1, h2.trans hs.2⟩
    have h2 : ∫ r in Ι s t, ‖g r‖ ≤ ∫ r in Ioc a b, ‖g r‖ :=
      setIntegral_mono_set hgc.norm (ae_of_all _ fun r => norm_nonneg _) hsub.eventuallyLE
    have h3 : ∫ r in Ioc a b, ‖g r‖ = ∫ r in Ioo a b, |g r| := by
      rw [integral_Ioc_eq_integral_Ioo]; rfl
    have h4 := le_abs_self (∫ r in s..t, g r)
    rw [Real.norm_eq_abs] at h1
    linarith
  have hFi : IntegrableOn F (Ioo a b) := (hFc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hmono : ∫ s in Ioo a b, F t ≤ ∫ s in Ioo a b, (F s + ∫ r in Ioo a b, |g r|) :=
    setIntegral_mono_on (integrableOn_const (by simp)) (hFi.add (integrableOn_const (by simp)))
      measurableSet_Ioo (fun s hs => hI s (Ioo_subset_Icc_self hs))
  rw [setIntegral_const, integral_add hFi (integrableOn_const (by simp)), setIntegral_const,
    Real.volume_real_Ioo_of_le hab.le, smul_eq_mul, smul_eq_mul] at hmono
  have hba : 0 < b - a := by linarith
  have e : F t = (b - a)⁻¹ * ((b - a) * F t) := by field_simp
  rw [e]
  calc (b - a)⁻¹ * ((b - a) * F t)
      ≤ (b - a)⁻¹ * ((∫ s in Ioo a b, F s) + (b - a) * ∫ r in Ioo a b, |g r|) :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hba.le)
    _ = _ := by field_simp

lemma weak_indicator {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {ι : X →L[ℝ] Y} {T : ℝ}
    {u : ℝ → X} {w : ℝ → Y} (h : HasWeakTimeDeriv ι T u w) :
    HasWeakTimeDeriv ι T ((Ioo 0 T).indicator u) ((Ioo 0 T).indicator w) := by
  intro φ hφ
  have e1 : ∫ t in Ioo 0 T, deriv φ t • ι ((Ioo 0 T).indicator u t) =
      ∫ t in Ioo 0 T, deriv φ t • ι (u t) :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [indicator_of_mem ht]
  have e2 : ∫ t in Ioo 0 T, φ t • (Ioo 0 T).indicator w t = ∫ t in Ioo 0 T, φ t • w t :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [indicator_of_mem ht]
  rw [e1, e2]; exact h φ hφ

lemma dual_const (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (huti : Integrable ut volume)
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (v : V) :
    ∃ c : ℝ, ∀ᵐ r ∂(volume.restrict (Ioc 0 T)),
      HT.toDualV (u r) v = c + (∫ s in (0:ℝ)..r, ut s) v := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have hu1 : Integrable u (volume.restrict (Ioo 0 T)) := hu.integrable one_le_two
  have hut1 : Integrable ut (volume.restrict (Ioo 0 T)) := hut.integrable one_le_two
  have hw : IntegrableOn (fun s => ut s v) (Ioo 0 T) :=
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hut1
  have hh : IntegrableOn (fun r => HT.toDualV (u r) v) (Ioo 0 T) :=
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp (HT.toDualV.integrable_comp hu1)
  have hweak : ∀ φ, IsTestFunctionOn T φ →
      ∫ t in Ioo 0 T, deriv φ t * HT.toDualV (u t) v = -∫ t in Ioo 0 T, φ t * ut t v := by
    intro φ hφ
    have := IBPc.scalar_weak HT hT hu hut hdu (uc := fun t => HT.toH (u t))
      (ae_of_all _ fun _ => rfl) v φ hφ
    simpa [toDualV_apply] using this
  obtain ⟨C, hC⟩ := IBPc.dbr_scalar hT hh hw hweak
  refine ⟨C, ?_⟩
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  filter_upwards [hC] with r hr
  rw [hr]
  congr 1
  exact (ContinuousLinearMap.apply ℝ ℝ v).intervalIntegral_comp_comm huti.intervalIntegrable

lemma uIoc_sub_Ioc {T τ h : ℝ} (hτ : uIcc τ (τ + h) ⊆ Icc 0 T) : Ι τ (τ + h) ⊆ Ioc 0 T := by
  intro x hx
  have h0 := hτ left_mem_uIcc
  have h1 := hτ right_mem_uIcc
  have hx' := hτ (uIoc_subset_uIcc hx)
  refine ⟨?_, hx'.2⟩
  rcases (mem_uIoc.1 hx) with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · exact h0.1.trans_lt a1
  · exact h1.1.trans_lt a1

lemma dual_window (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hui : Integrable u volume)
    (huti : Integrable ut volume)
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (h : ℝ) :
    ∀ t t', uIcc t (t + h) ⊆ Icc 0 T → uIcc t' (t' + h) ⊆ Icc 0 T →
      HT.toDualV (∫ r in t..t + h, u r) - ∫ r in t..t + h, (∫ s in (0:ℝ)..r, ut s) =
      HT.toDualV (∫ r in t'..t' + h, u r) - ∫ r in t'..t' + h, (∫ s in (0:ℝ)..r, ut s) := by
  intro t t' ht ht'
  have hGc : Continuous (fun r => ∫ s in (0:ℝ)..r, ut s) :=
    intervalIntegral.continuous_primitive (fun a b => huti.intervalIntegrable) 0
  have hval : ∀ v : V, ∃ c : ℝ, ∀ τ, uIcc τ (τ + h) ⊆ Icc 0 T →
      (HT.toDualV (∫ r in τ..τ + h, u r) - ∫ r in τ..τ + h, (∫ s in (0:ℝ)..r, ut s)) v =
        h * c := by
    intro v
    obtain ⟨c, hc⟩ := dual_const HT hT hu hut huti hdu v
    refine ⟨c, fun τ hτ => ?_⟩
    have hc' : ∀ᵐ r, r ∈ Ioc 0 T → HT.toDualV (u r) v = c + (∫ s in (0:ℝ)..r, ut s) v :=
      (ae_restrict_iff' measurableSet_Ioc).1 hc
    have ev : ∀ (f : ℝ → StrongDual ℝ V) (a b : ℝ), IntervalIntegrable f volume a b →
        (∫ x in a..b, f x) v = ∫ x in a..b, f x v := fun f a b hf =>
      ((ContinuousLinearMap.apply ℝ ℝ v).intervalIntegral_comp_comm hf).symm
    rw [ContinuousLinearMap.sub_apply,
      ← HT.toDualV.intervalIntegral_comp_comm hui.intervalIntegrable,
      ev _ _ _ (HT.toDualV.integrable_comp hui).intervalIntegrable,
      ev _ _ _ (hGc.intervalIntegrable _ _)]
    have i1 : IntervalIntegrable (fun x => HT.toDualV (u x) v) volume τ (τ + h) :=
      ((ContinuousLinearMap.apply ℝ ℝ v).integrable_comp
        (HT.toDualV.integrable_comp hui)).intervalIntegrable
    have i2 : IntervalIntegrable (fun x => (∫ s in (0:ℝ)..x, ut s) v) volume τ (τ + h) :=
      (((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hGc).intervalIntegrable _ _)
    rw [← intervalIntegral.integral_sub i1 i2]
    have e : ∫ r in τ..τ + h, (HT.toDualV (u r) v - (∫ s in (0:ℝ)..r, ut s) v) =
        ∫ r in τ..τ + h, c := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hc'] with r hr hrI
      rw [hr (uIoc_sub_Ioc hτ hrI)]
      ring
    rw [e, intervalIntegral.integral_const, smul_eq_mul]
    ring
  ext v
  obtain ⟨c, hc⟩ := hval v
  rw [hc t ht, hc t' ht']

/-- The `𝒱'`-image of a Steklov average is differentiable, with derivative the Steklov average
of `u_t`. -/
lemma stekD_hasDerivAt (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hu : MemLp u 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hui : Integrable u volume)
    (huti : Integrable ut volume)
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (h : ℝ) {a b : ℝ}
    (hadm : ∀ t ∈ Icc a b, uIcc t (t + h) ⊆ Icc 0 T) :
    ∀ t ∈ Ioo a b, HasDerivAt (fun s => HT.toDualV (h⁻¹ • ∫ r in s..s + h, u r))
      (h⁻¹ • ∫ r in t..t + h, ut r) t := by
  intro t ht
  obtain ⟨G, hG⟩ : ∃ G : ℝ → StrongDual ℝ V, G = fun r => ∫ s in (0:ℝ)..r, ut s := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hG]; exact intervalIntegral.continuous_primitive (fun a b => huti.intervalIntegrable) 0
  have hP : ∀ x, HasDerivAt (fun y => ∫ r in (0:ℝ)..y, G r) (G x) x := fun x =>
    (hGc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hJ : HasDerivAt (fun s => ∫ r in s..s + h, G r) (G (t + h) - G t) t := by
    have e : (fun s => ∫ r in s..s + h, G r) =
        fun s => (∫ r in (0:ℝ)..s + h, G r) - ∫ r in (0:ℝ)..s, G r := by
      funext s
      rw [intervalIntegral.integral_interval_sub_left (hGc.intervalIntegrable _ _)
        (hGc.intervalIntegrable _ _)]
    rw [e]
    exact ((hP (t + h)).comp_add_const t h).sub (hP t)
  have hGd : G (t + h) - G t = ∫ r in t..t + h, ut r := by
    rw [hG]
    exact intervalIntegral.integral_interval_sub_left huti.intervalIntegrable
      huti.intervalIntegrable
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hev : (fun s => HT.toDualV (h⁻¹ • ∫ r in s..s + h, u r)) =ᶠ[𝓝 t]
      fun s => h⁻¹ • ((HT.toDualV (∫ r in t..t + h, u r) - ∫ r in t..t + h, G r) +
        ∫ r in s..s + h, G r) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    have dw := dual_window HT hT hu hut hui huti hdu h s t (hadm s hs) (hadm t htI)
    rw [← hG] at dw
    rw [map_smul, ← dw]
    abel_nf
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  rw [← hGd]
  exact (hJ.const_add _).const_smul h⁻¹

lemma stek_continuous {u : ℝ → V} (hui : Integrable u volume) (h : ℝ) :
    Continuous (fun s => h⁻¹ • ∫ r in s..s + h, u r) := by
  have hPc : Continuous (fun y => ∫ r in (0:ℝ)..y, u r) :=
    intervalIntegral.continuous_primitive (fun a b => hui.intervalIntegrable) 0
  have e : (fun s => h⁻¹ • ∫ r in s..s + h, u r) =
      fun s => h⁻¹ • ((∫ r in (0:ℝ)..s + h, u r) - ∫ r in (0:ℝ)..s, u r) := by
    funext s
    rw [intervalIntegral.integral_interval_sub_left hui.intervalIntegrable
      hui.intervalIntegrable]
  rw [e]
  exact ((hPc.comp (continuous_id.add continuous_const)).sub hPc).const_smul _

end D

end HTC
end Qf92_D

section Qf92_C
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Interval
open HunterPDE.Parabolic

namespace HTC

section C

lemma cont_memLp {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (Ioo a b)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) := isFiniteMeasure_restrict.2 (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hm : AEStronglyMeasurable f (volume.restrict (Ioo a b)) :=
    (hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  refine (memLp_top_of_bound hm C ?_).mono_exponent le_top
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

lemma int_sq {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} {f : ℝ → E}
    (hf : MemLp f 2 μ) : ∫ t, ‖f t‖ ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h0 : 0 ≤ ∫ t, ‖f t‖ ^ (2:ℝ) ∂μ := integral_nonneg fun t => by positivity
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

lemma int_ind_normed {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → E} (h : Integrable f (volume.restrict s)) : Integrable (s.indicator f) volume :=
  (integrable_indicator_iff hs).2 h

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma pair_abs_le_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {μ : Measure ℝ}
    {X : ℝ → StrongDual ℝ W} {Y : ℝ → W} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ t, |X t (Y t)| ∂μ ≤ (eLpNorm X 2 μ).toReal * (eLpNorm Y 2 μ).toReal := by
  have hm : AEStronglyMeasurable (fun t => X t (Y t)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hX.1.prodMk hY.1)
  have hle := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) hX.1 hY.1
    (fun (f : StrongDual ℝ W) (w : W) => f w) 1
    (ae_of_all _ fun t => by
      have := (X t).le_opNorm (Y t)
      simpa [one_mul] using this)
  simp only [ENNReal.coe_one, one_mul] at hle
  have h1 : ∫ t, |X t (Y t)| ∂μ = (eLpNorm (fun t => X t (Y t)) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hm]
    simp [Real.norm_eq_abs]
  rw [h1, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hX.2.ne hY.2.ne) hle

/-- The uniform energy bound on a window for a `𝒱`-valued curve whose `𝒱'`-image is `C¹`. -/
lemma cauchy_est (HT : HilbertTriple V H) {a b : ℝ} (hab : a < b) {B : ℝ → V}
    {R : ℝ → StrongDual ℝ V} (hBc : ContinuousOn B (Icc a b))
    (hR : MemLp R 2 (volume.restrict (Ioo a b)))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt (fun s => HT.toDualV (B s)) (R t) t) :
    ∀ t ∈ Icc a b, ‖HT.toH (B t)‖ ^ 2 ≤
      ‖HT.toH‖ ^ 2 / (b - a) * (eLpNorm B 2 (volume.restrict (Ioo a b))).toReal ^ 2 +
      2 * ((eLpNorm R 2 (volume.restrict (Ioo a b))).toReal *
        (eLpNorm B 2 (volume.restrict (Ioo a b))).toReal) := by
  intro t ht
  have hB2 := cont_memLp hBc 2
  have hFc : ContinuousOn (fun s => ‖HT.toH (B s)‖ ^ 2) (Icc a b) :=
    ((HT.toH.continuous.comp_continuousOn hBc).norm).pow 2
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (fun s => ‖HT.toH (B s)‖ ^ 2)
      (2 * R x (B x)) x := fun x hx =>
    sq_hasDerivAt HT (hBc.continuousAt (Icc_mem_nhds hx.1 hx.2)) (hd x hx)
  have hgi : IntegrableOn (fun r => 2 * R r (B r)) (Ioo a b) :=
    (IBPc.pair_integrable_gen hR hB2).const_mul 2
  have hsb := sup_bound hab hFc hgi (ftc_window hFc hderiv hgi) t ht
  have hba : 0 < b - a := by linarith
  have hB2c : ContinuousOn (fun s => ‖HT.toH‖ ^ 2 * ‖B s‖ ^ 2) (Icc a b) :=
    continuousOn_const.mul (hBc.norm.pow 2)
  have b1 : ∫ s in Ioo a b, ‖HT.toH (B s)‖ ^ 2 ≤
      ‖HT.toH‖ ^ 2 * (eLpNorm B 2 (volume.restrict (Ioo a b))).toReal ^ 2 := by
    calc ∫ s in Ioo a b, ‖HT.toH (B s)‖ ^ 2
        ≤ ∫ s in Ioo a b, ‖HT.toH‖ ^ 2 * ‖B s‖ ^ 2 := by
          refine setIntegral_mono_on ((hFc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
            ((hB2c.integrableOn_Icc).mono_set Ioo_subset_Icc_self) measurableSet_Ioo
            (fun s _ => ?_)
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (HT.toH.le_opNorm _) 2
      _ = ‖HT.toH‖ ^ 2 * ∫ s in Ioo a b, ‖B s‖ ^ 2 := integral_const_mul _ _
      _ = _ := by rw [int_sq hB2]
  have b2 : ∫ r in Ioo a b, |2 * R r (B r)| ≤
      2 * ((eLpNorm R 2 (volume.restrict (Ioo a b))).toReal *
        (eLpNorm B 2 (volume.restrict (Ioo a b))).toReal) := by
    have e : ∫ r in Ioo a b, |2 * R r (B r)| = 2 * ∫ r in Ioo a b, |R r (B r)| := by
      rw [← integral_const_mul]
      congr 1; funext r; rw [abs_mul, abs_two]
    rw [e]
    exact mul_le_mul_of_nonneg_left (pair_abs_le_gen hR hB2) (by norm_num)
  have e3 : ‖HT.toH‖ ^ 2 / (b - a) * (eLpNorm B 2 (volume.restrict (Ioo a b))).toReal ^ 2 =
      (b - a)⁻¹ * (‖HT.toH‖ ^ 2 * (eLpNorm B 2 (volume.restrict (Ioo a b))).toReal ^ 2) := by
    ring
  rw [e3]
  calc ‖HT.toH (B t)‖ ^ 2 ≤ _ := hsb
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left b1 (inv_nonneg.2 hba.le)) b2

end C

end HTC
end Qf92_C

section Qf92_W
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Interval
open HunterPDE.Parabolic

namespace HTC

section W

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma eLpNorm_pair_le {E : Type*} [NormedAddCommGroup E] {f g u0 : ℝ → E}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hu : AEStronglyMeasurable u0 volume) (s : Set ℝ) :
    eLpNorm (fun t => f t - g t) 2 (volume.restrict s) ≤
      eLpNorm (fun t => f t - u0 t) 2 volume + eLpNorm (fun t => g t - u0 t) 2 volume := by
  have e : (fun t => f t - g t) = (fun t => f t - u0 t) - (fun t => g t - u0 t) := by
    funext t; simp
  rw [e]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
  exact eLpNorm_sub_le (hf.sub hu) (hg.sub hu) (by norm_num)

lemma memLp_ind {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → E} (hf : StronglyMeasurable f) {p : ℝ≥0∞} (h : MemLp f p (volume.restrict s)) :
    MemLp (s.indicator f) p volume := by
  refine ⟨(hf.indicator hs).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact h.2

lemma stek_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : ℝ → E} (hui : Integrable u volume) (h : ℝ) : Continuous (stek u h) := by
  have hPc : Continuous (fun y => ∫ r in (0:ℝ)..y, u r) :=
    intervalIntegral.continuous_primitive (fun a b => hui.intervalIntegrable) 0
  have e : stek u h = fun s => h⁻¹ • ((∫ r in (0:ℝ)..s + h, u r) - ∫ r in (0:ℝ)..s, u r) := by
    funext s
    rw [stek, intervalIntegral.integral_interval_sub_left hui.intervalIntegrable
      hui.intervalIntegrable]
  rw [e]
  exact ((hPc.comp (continuous_id.add continuous_const)).sub hPc).const_smul _

lemma small_bound {K A R δ ε x : ℝ} (hK : 0 ≤ K) (hA0 : 0 ≤ A) (hR0 : 0 ≤ R)
    (hA : A ≤ 2 * δ) (hR : R ≤ 2 * δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδε : (8 * K + 17) * δ ≤ ε ^ 2) (hε : 0 < ε) (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ K * A ^ 2 + 2 * (R * A)) : x < ε := by
  have h1 : K * A ^ 2 ≤ K * (2 * δ) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA 2) hK
  have h2 : R * A ≤ (2 * δ) * (2 * δ) := mul_le_mul hR hA hA0 (by linarith)
  have h3 : δ ^ 2 ≤ δ := by nlinarith
  have h4 : x ^ 2 < ε ^ 2 := by nlinarith
  by_contra hc
  have hc' := not_lt.1 hc
  nlinarith

/-- Continuity on a window `[a, b]` from Steklov averages with steps `hn n → 0`. -/
theorem window (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hum : StronglyMeasurable u) (hutm : StronglyMeasurable ut)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hut : MemLp ut 2 (volume.restrict (Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) {a b : ℝ} (hab : a < b)
    (hn : ℕ → ℝ) (hn0 : ∀ n, hn n ≠ 0) (hlim : Tendsto hn atTop (𝓝 0))
    (hadm : ∀ n, ∀ t ∈ Icc a b, uIcc t (t + hn n) ⊆ Icc 0 T) :
    ∃ w : ℝ → H, ContinuousOn w (Icc a b) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), w t = HT.toH (u t) := by
  have hfin : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (by simp)
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℝ → V, u0 = (Ioo 0 T).indicator u := ⟨_, rfl⟩
  obtain ⟨ut0, hut0⟩ : ∃ ut0 : ℝ → StrongDual ℝ V, ut0 = (Ioo 0 T).indicator ut := ⟨_, rfl⟩
  have hu0m : StronglyMeasurable u0 := by rw [hu0]; exact hum.indicator measurableSet_Ioo
  have hut0m : StronglyMeasurable ut0 := by rw [hut0]; exact hutm.indicator measurableSet_Ioo
  have hu0L : MemLp u0 2 volume := by
    rw [hu0]; exact memLp_ind measurableSet_Ioo hum hu
  have hut0L : MemLp ut0 2 volume := by
    rw [hut0]; exact memLp_ind (E := StrongDual ℝ V) measurableSet_Ioo hutm hut
  have hu0i : Integrable u0 volume := by
    rw [hu0]; exact int_ind_normed measurableSet_Ioo (hu.integrable one_le_two)
  have hut0i : Integrable ut0 volume := by
    rw [hut0]
    exact int_ind_normed (E := StrongDual ℝ V) measurableSet_Ioo (hut.integrable one_le_two)
  have hu0R : MemLp u0 2 (volume.restrict (Ioo 0 T)) := hu0L.restrict _
  have hut0R : MemLp ut0 2 (volume.restrict (Ioo 0 T)) := hut0L.restrict _
  have hdu0 : HasWeakTimeDeriv HT.toDualV T u0 ut0 := by
    rw [hu0, hut0]; exact weak_indicator hdu
  have hab0 : Ioo a b ⊆ Ioo 0 T := by
    intro t ht
    have h1 := hadm 0 a ⟨le_rfl, hab.le⟩ left_mem_uIcc
    have h2 := hadm 0 b ⟨hab.le, le_rfl⟩ left_mem_uIcc
    exact ⟨h1.1.trans_lt ht.1, ht.2.trans_le h2.2⟩
  have hlim' : Tendsto hn atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hn0⟩
  have hα : Tendsto (fun n => eLpNorm (fun t => stek u0 (hn n) t - u0 t) 2 volume) atTop
      (𝓝 0) := (stek_tendsto hu0L hu0m hu0i).comp hlim'
  have hβ : Tendsto (fun n => eLpNorm (fun t => stek ut0 (hn n) t - ut0 t) 2 volume) atTop
      (𝓝 0) := (stek_tendsto hut0L hut0m hut0i).comp hlim'
  have hBc : ∀ n, Continuous (stek u0 (hn n)) := fun n => stek_cont hu0i (hn n)
  have hRc : ∀ n, Continuous (stek ut0 (hn n)) := fun n => stek_cont hut0i (hn n)
  have hBd : ∀ n, ∀ t ∈ Ioo a b, HasDerivAt (fun s => HT.toDualV (stek u0 (hn n) s))
      (stek ut0 (hn n) t) t := fun n =>
    stekD_hasDerivAt HT hT hu0R hut0R hu0i hut0i hdu0 (hn n) (hadm n)
  have hest : ∀ n m, ∀ t ∈ Icc a b,
      ‖HT.toH (stek u0 (hn n) t) - HT.toH (stek u0 (hn m) t)‖ ^ 2 ≤
      ‖HT.toH‖ ^ 2 / (b - a) * (eLpNorm (fun s => stek u0 (hn n) s - stek u0 (hn m) s) 2
        (volume.restrict (Ioo a b))).toReal ^ 2 +
      2 * ((eLpNorm (fun s => stek ut0 (hn n) s - stek ut0 (hn m) s) 2
        (volume.restrict (Ioo a b))).toReal *
        (eLpNorm (fun s => stek u0 (hn n) s - stek u0 (hn m) s) 2
          (volume.restrict (Ioo a b))).toReal) := by
    intro n m t ht
    rw [← map_sub]
    refine cauchy_est HT hab (B := fun s => stek u0 (hn n) s - stek u0 (hn m) s)
      (R := fun s => stek ut0 (hn n) s - stek ut0 (hn m) s)
      ((hBc n).sub (hBc m)).continuousOn (cont_memLp ((hRc n).sub (hRc m)).continuousOn 2)
      (fun x hx => ?_) t ht
    have := (hBd n x hx).sub (hBd m x hx)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [map_sub, Pi.sub_apply]
  have hUC : UniformCauchySeqOn (fun n t => HT.toH (stek u0 (hn n) t)) atTop (Icc a b) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hK : 0 ≤ ‖HT.toH‖ ^ 2 / (b - a) := div_nonneg (by positivity) (by linarith)
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (ε ^ 2 / (8 * (‖HT.toH‖ ^ 2 / (b - a)) + 17)) :=
      ⟨_, rfl⟩
    have hden : 0 < 8 * (‖HT.toH‖ ^ 2 / (b - a)) + 17 := by linarith
    have hδ0 : 0 < δ := by rw [hδ]; exact lt_min one_pos (div_pos (by positivity) hden)
    have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
    have hδε : (8 * (‖HT.toH‖ ^ 2 / (b - a)) + 17) * δ ≤ ε ^ 2 := by
      have : δ ≤ ε ^ 2 / (8 * (‖HT.toH‖ ^ 2 / (b - a)) + 17) := by rw [hδ]; exact min_le_right _ _
      rw [le_div_iff₀ hden] at this; linarith
    have e1 := (ENNReal.tendsto_nhds_zero.1 hα) (ENNReal.ofReal δ) (by simpa using hδ0)
    have e2 := (ENNReal.tendsto_nhds_zero.1 hβ) (ENNReal.ofReal δ) (by simpa using hδ0)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (e1.and e2)
    refine ⟨N, fun m hm n hn' t ht => ?_⟩
    rw [dist_eq_norm]
    have hsum : ∀ {x y : ℝ≥0∞}, x ≤ ENNReal.ofReal δ → y ≤ ENNReal.ofReal δ →
        x + y ≤ ENNReal.ofReal (2 * δ) := fun hx hy => by
      rw [two_mul, ENNReal.ofReal_add hδ0.le hδ0.le]; exact add_le_add hx hy
    have hA : (eLpNorm (fun s => stek u0 (hn m) s - stek u0 (hn n) s) 2
        (volume.restrict (Ioo a b))).toReal ≤ 2 * δ :=
      ENNReal.toReal_le_of_le_ofReal (by linarith)
        ((eLpNorm_pair_le (hBc m).aestronglyMeasurable (hBc n).aestronglyMeasurable
          hu0m.aestronglyMeasurable _).trans (hsum (hN m hm).1 (hN n hn').1))
    have hR : (eLpNorm (fun s => stek ut0 (hn m) s - stek ut0 (hn n) s) 2
        (volume.restrict (Ioo a b))).toReal ≤ 2 * δ :=
      ENNReal.toReal_le_of_le_ofReal (by linarith)
        ((eLpNorm_pair_le (hRc m).aestronglyMeasurable (hRc n).aestronglyMeasurable
          hut0m.aestronglyMeasurable _).trans (hsum (hN m hm).2 (hN n hn').2))
    exact small_bound hK ENNReal.toReal_nonneg ENNReal.toReal_nonneg hA hR hδ0 hδ1 hδε hε
      (norm_nonneg _) (hest m n t ht)
  obtain ⟨w, hw⟩ : ∃ w : ℝ → H,
      w = fun t => limUnder atTop (fun n => HT.toH (stek u0 (hn n) t)) := ⟨_, rfl⟩
  have hpt : ∀ t ∈ Icc a b, Tendsto (fun n => HT.toH (stek u0 (hn n) t)) atTop (𝓝 (w t)) :=
    fun t ht => by rw [hw]; exact (hUC.cauchySeq ht).tendsto_limUnder
  have hTU : TendstoUniformlyOn (fun n t => HT.toH (stek u0 (hn n) t)) w atTop (Icc a b) :=
    hUC.tendstoUniformlyOn_of_tendsto hpt
  have hwc : ContinuousOn w (Icc a b) :=
    hTU.continuousOn (Frequently.of_forall fun n =>
      (HT.toH.continuous.comp (hBc n)).continuousOn)
  refine ⟨w, hwc, ?_⟩
  have hL2 : Tendsto (fun n => eLpNorm ((fun t => HT.toH (stek u0 (hn n) t)) -
      (fun t => HT.toH (u0 t))) 2 (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
    have hb : ∀ n, eLpNorm ((fun t => HT.toH (stek u0 (hn n) t)) - (fun t => HT.toH (u0 t))) 2
        (volume.restrict (Ioo a b)) ≤
        ‖HT.toH‖₊ * eLpNorm (fun t => stek u0 (hn n) t - u0 t) 2 volume := by
      intro n
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (ae_of_all _ fun t => ?_) 2).trans
        (le_of_eq (ENNReal.smul_def _ _))
      simp only [Pi.sub_apply, ← map_sub]
      exact HT.toH.le_opNNNorm _
    have := ENNReal.Tendsto.const_mul (a := (‖HT.toH‖₊ : ℝ≥0∞)) hα (Or.inr ENNReal.coe_ne_top)
    rw [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun n => zero_le) hb
  have hTM := tendstoInMeasure_of_tendsto_eLpNorm (two_ne_zero)
    (fun n => (HT.toH.continuous.comp (hBc n)).aestronglyMeasurable)
    (HT.toH.continuous.comp_aestronglyMeasurable hu0m.aestronglyMeasurable) hL2
  obtain ⟨ns, hns, hae⟩ := hTM.exists_seq_tendsto_ae
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t h1 h2
  have h3 := (hpt t (Ioo_subset_Icc_self h2)).comp hns.tendsto_atTop
  have e : u t = u0 t := by rw [hu0, indicator_of_mem (hab0 h2)]
  rw [e]
  exact tendsto_nhds_unique h3 h1

end W

end HTC
end Qf92_W

section Qf92_F
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Interval
open HunterPDE.Parabolic

namespace HTC

section F

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weak_congr {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {ι : X →L[ℝ] Y} {T : ℝ}
    {u u' : ℝ → X} {w w' : ℝ → Y} (h : HasWeakTimeDeriv ι T u w)
    (hu : u =ᵐ[volume.restrict (Ioo 0 T)] u') (hw : w =ᵐ[volume.restrict (Ioo 0 T)] w') :
    HasWeakTimeDeriv ι T u' w' := by
  intro φ hφ
  have e1 : ∫ t in Ioo 0 T, deriv φ t • ι (u' t) = ∫ t in Ioo 0 T, deriv φ t • ι (u t) :=
    integral_congr_ae (by filter_upwards [hu] with t ht; rw [ht])
  have e2 : ∫ t in Ioo 0 T, φ t • w' t = ∫ t in Ioo 0 T, φ t • w t :=
    integral_congr_ae (by filter_upwards [hw] with t ht; rw [ht])
  rw [e1, e2]; exact h φ hφ

lemma glue {T : ℝ} (hT : 0 < T) {f g : ℝ → H} (hf : ContinuousOn f (Icc 0 (2 * T / 3)))
    (hg : ContinuousOn g (Icc (T / 3) T))
    (hfg : ∀ᵐ t ∂(volume.restrict (Ioo (T / 3) (2 * T / 3))), f t = g t) :
    ∃ w : ℝ → H, ContinuousOn w (Icc 0 T) ∧ EqOn w f (Icc 0 (2 * T / 3)) ∧
      EqOn w g (Icc (T / 3) T) := by
  have s1 : Icc (T / 3) (2 * T / 3) ⊆ Icc 0 (2 * T / 3) := Icc_subset_Icc (by positivity) le_rfl
  have s2 : Icc (T / 3) (2 * T / 3) ⊆ Icc (T / 3) T := Icc_subset_Icc le_rfl (by linarith)
  have hEo : EqOn f g (Ioo (T / 3) (2 * T / 3)) :=
    Measure.eqOn_open_of_ae_eq hfg isOpen_Ioo (hf.mono (Ioo_subset_Icc_self.trans s1))
      (hg.mono (Ioo_subset_Icc_self.trans s2))
  have hE : EqOn f g (Icc (T / 3) (2 * T / 3)) :=
    hEo.of_subset_closure (hf.mono s1) (hg.mono s2) Ioo_subset_Icc_self
      (by rw [closure_Ioo (by linarith : T / 3 ≠ 2 * T / 3)])
  have hw1 : EqOn (fun t => if t < T / 2 then f t else g t) f (Icc 0 (2 * T / 3)) := by
    intro t ht
    by_cases h : t < T / 2
    · simp [h]
    · simp only [h, if_false]
      exact (hE ⟨by linarith [not_lt.1 h], ht.2⟩).symm
  have hw2 : EqOn (fun t => if t < T / 2 then f t else g t) g (Icc (T / 3) T) := by
    intro t ht
    by_cases h : t < T / 2
    · simp only [h, if_true]
      exact hE ⟨ht.1, by linarith⟩
    · simp [h]
  refine ⟨fun t => if t < T / 2 then f t else g t, ?_, hw1, hw2⟩
  intro t ht
  by_cases h : t < 2 * T / 3
  · have hc : ContinuousWithinAt (fun t => if t < T / 2 then f t else g t)
        (Icc 0 (2 * T / 3)) t :=
      (hf t ⟨ht.1, h.le⟩).congr (fun x hx => hw1 hx) (hw1 ⟨ht.1, h.le⟩)
    exact hc.mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (2 * T / 3), isOpen_Iio, h, fun x hx => ⟨hx.2.1, hx.1.le⟩⟩)
  · have h' : T / 3 < t := by linarith [not_lt.1 h]
    have hc : ContinuousWithinAt (fun t => if t < T / 2 then f t else g t)
        (Icc (T / 3) T) t :=
      (hg t ⟨h'.le, ht.2⟩).congr (fun x hx => hw2 hx) (hw2 ⟨h'.le, ht.2⟩)
    exact hc.mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi (T / 3), isOpen_Ioi, h', fun x hx => ⟨hx.1.le, hx.2.2⟩⟩)

theorem core (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {ut : ℝ → StrongDual ℝ V} (hum : StronglyMeasurable u) (hutm : StronglyMeasurable ut)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hut : MemLp ut 2 (volume.restrict (Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) :
    ∃ w : ℝ → H, ContinuousOn w (Icc 0 T) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), w t = HT.toH (u t) := by
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hT3 : 0 < T / 3 := by positivity
  have hl1 : Tendsto (fun n : ℕ => T / 3 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using hseq.const_mul (T / 3)
  have hl2 : Tendsto (fun n : ℕ => -(T / 3 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa using hl1.neg
  obtain ⟨f, hfc, hfa⟩ := window HT hT hum hutm hu hut hdu (a := 0) (b := 2 * T / 3)
    (by positivity) (fun n => T / 3 * (1 / ((n : ℝ) + 1)))
    (fun n => (mul_pos hT3 (hpos n)).ne') hl1
    (fun n t ht => by
      have h0 := hpos n
      have h1 := hle1 n
      have hh : T / 3 * (1 / ((n : ℝ) + 1)) ≤ T / 3 := by nlinarith
      have hh0 : 0 < T / 3 * (1 / ((n : ℝ) + 1)) := mul_pos hT3 h0
      rw [uIcc_of_le (by linarith)]
      exact Icc_subset_Icc ht.1 (by linarith [ht.2]))
  obtain ⟨g, hgc, hga⟩ := window HT hT hum hutm hu hut hdu (a := T / 3) (b := T)
    (by linarith) (fun n => -(T / 3 * (1 / ((n : ℝ) + 1))))
    (fun n => neg_ne_zero.2 (mul_pos hT3 (hpos n)).ne') hl2
    (fun n t ht => by
      have h0 := hpos n
      have h1 := hle1 n
      have hh : T / 3 * (1 / ((n : ℝ) + 1)) ≤ T / 3 := by nlinarith
      have hh0 : 0 < T / 3 * (1 / ((n : ℝ) + 1)) := mul_pos hT3 h0
      rw [uIcc_of_ge (by linarith)]
      exact Icc_subset_Icc (by linarith [ht.1]) ht.2)
  have hfg : ∀ᵐ t ∂(volume.restrict (Ioo (T / 3) (2 * T / 3))), f t = g t := by
    have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (T / 3) (2 * T / 3))), f t = HT.toH (u t) :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (by positivity) le_rfl) hfa
    have h2 : ∀ᵐ t ∂(volume.restrict (Ioo (T / 3) (2 * T / 3))), g t = HT.toH (u t) :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl (by linarith)) hga
    filter_upwards [h1, h2] with t a1 a2
    rw [a1, a2]
  obtain ⟨w, hwc, hw1, hw2⟩ := glue hT hfc hgc hfg
  refine ⟨w, hwc, ?_⟩
  have hU : Ioo 0 T = Ioo 0 (2 * T / 3) ∪ Ioo (T / 3) T := by
    ext t
    simp only [mem_Ioo, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : t < 2 * T / 3
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨by linarith [not_lt.1 h], h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  rw [hU, ae_restrict_union_iff]
  constructor
  · filter_upwards [hfa, ae_restrict_mem measurableSet_Ioo] with t a1 a2
    rw [hw1 (Ioo_subset_Icc_self a2), a1]
  · filter_upwards [hga, ae_restrict_mem measurableSet_Ioo] with t a1 a2
    rw [hw2 (Ioo_subset_Icc_self a2), a1]

lemma const_bound {k x A B y : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ x * (k ^ 2 * A ^ 2) + 2 * (B * A)) :
    y ≤ (k * (x + 1) + 1) * (A + B) := by
  have hC : 0 ≤ k * (x + 1) + 1 := by positivity
  have h1 : x ≤ (x + 1) ^ 2 := by nlinarith
  have h2 : k ^ 2 * x ≤ (k * (x + 1)) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : x * (k ^ 2 * A ^ 2) ≤ (k * (x + 1)) ^ 2 * (A + B) ^ 2 := by
    have : A ^ 2 ≤ (A + B) ^ 2 := by nlinarith
    calc x * (k ^ 2 * A ^ 2) = (k ^ 2 * x) * A ^ 2 := by ring
      _ ≤ (k * (x + 1)) ^ 2 * (A + B) ^ 2 :=
        mul_le_mul h2 this (by positivity) (by positivity)
  have h4 : 2 * (B * A) ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
  have h5 : y ^ 2 ≤ ((k * (x + 1) + 1) * (A + B)) ^ 2 := by
    have : (k * (x + 1)) ^ 2 * (A + B) ^ 2 + (A + B) ^ 2 ≤
        ((k * (x + 1) + 1) * (A + B)) ^ 2 := by
      have hkx : 0 ≤ k * (x + 1) := by positivity
      nlinarith [sq_nonneg (A + B)]
    linarith
  have hz : 0 ≤ (k * (x + 1) + 1) * (A + B) := by positivity
  by_contra hc
  have hc' := not_le.1 hc
  nlinarith

theorem main (HT : HilbertTriple V H) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ≥0, ∀ (u : ℝ → V) (ut : ℝ → StrongDual ℝ V),
      MemLp u 2 (volume.restrict (Set.Ioo 0 T)) →
      MemLp ut 2 (volume.restrict (Set.Ioo 0 T)) →
      HasWeakTimeDeriv HT.toDualV T u ut →
      ∃ ũ : ℝ → H, ContinuousOn ũ (Set.Icc 0 T) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), ũ t = HT.toH (u t)) ∧
        (∀ v : V, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
          (fun t => inner ℝ (ũ t) (HT.toH v)) (fun t => ut t v)) ∧
        HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
          (fun t => ‖ũ t‖ ^ 2) (fun t => 2 * ut t (u t)) ∧
        eLpNorm ũ ∞ (volume.restrict (Set.Ioo 0 T)) ≤
          (C : ℝ≥0∞) * (eLpNorm u 2 (volume.restrict (Set.Ioo 0 T)) +
            eLpNorm ut 2 (volume.restrict (Set.Ioo 0 T))) := by
  refine ⟨Real.toNNReal (‖HT.toH‖ * (T⁻¹ + 1) + 1), fun u ut hu hut hdu => ?_⟩
  have hfin : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (by simp)
  obtain ⟨u', hu'm, hu'e⟩ : ∃ u' : ℝ → V, StronglyMeasurable u' ∧
      u =ᵐ[volume.restrict (Ioo 0 T)] u' := ⟨_, hu.1.stronglyMeasurable_mk, hu.1.ae_eq_mk⟩
  obtain ⟨ut', hut'm, hut'e⟩ : ∃ ut' : ℝ → StrongDual ℝ V, StronglyMeasurable ut' ∧
      ut =ᵐ[volume.restrict (Ioo 0 T)] ut' := ⟨_, hut.1.stronglyMeasurable_mk, hut.1.ae_eq_mk⟩
  have hu' : MemLp u' 2 (volume.restrict (Ioo 0 T)) := hu.ae_eq hu'e
  have hut' : MemLp ut' 2 (volume.restrict (Ioo 0 T)) := hut.ae_eq hut'e
  have hdu' : HasWeakTimeDeriv HT.toDualV T u' ut' := weak_congr hdu hu'e hut'e
  obtain ⟨w, hwc, hwa'⟩ := core HT hT hu'm hut'm hu' hut' hdu'
  have hwa : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), w t = HT.toH (u t) := by
    filter_upwards [hwa', hu'e] with t a1 a2
    rw [a1, a2]
  have h1 : ∀ v : V, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
      (fun t => inner ℝ (w t) (HT.toH v)) (fun t => ut t v) := by
    intro v φ hφ
    have := IBPc.scalar_weak HT hT hu hut hdu hwa v φ hφ
    simpa only [ContinuousLinearMap.id_apply, smul_eq_mul] using this
  obtain ⟨cl, hcl⟩ : ∃ cl : ℝ → ℝ, cl = fun t => min (max t 0) T := ⟨_, rfl⟩
  have hclc : Continuous cl := by
    rw [hcl]; exact (continuous_id.max continuous_const).min continuous_const
  have hclmem : ∀ t, cl t ∈ Icc (0:ℝ) T := fun t => by
    rw [hcl]
    exact ⟨le_min (le_max_right _ _) hT.le, min_le_right _ _⟩
  have hclid : ∀ t ∈ Icc (0:ℝ) T, cl t = t := fun t ht => by
    rw [hcl]
    simp only
    rw [max_eq_left ht.1, min_eq_left ht.2]
  have hwcc : Continuous (fun t => w (cl t)) := hwc.comp_continuous hclc hclmem
  have hwc' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), w (cl t) = HT.toH (u' t) := by
    filter_upwards [hwa', ae_restrict_mem measurableSet_Ioo] with t a1 a3
    rw [hclid t (Ioo_subset_Icc_self a3), a1]
  have h2' : HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T (fun t => ‖w t‖ ^ 2)
      (fun t => 2 * ut' t (u' t)) := by
    intro ψ hψ
    have := IBPc.weak_product HT hT hu'm hu'm hut'm hut'm hu' hu' hut' hut' hdu' hdu'
      hwcc hwcc hwc' hwc' hψ
    have e1 : ∫ t in Ioo 0 T, deriv ψ t • (ContinuousLinearMap.id ℝ ℝ) (‖w t‖ ^ 2) =
        ∫ t in Ioo 0 T, deriv ψ t * inner ℝ (w (cl t)) (w (cl t)) :=
      setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        simp only [ContinuousLinearMap.id_apply, smul_eq_mul]
        rw [hclid t (Ioo_subset_Icc_self ht), real_inner_self_eq_norm_sq]
    have e2 : ∫ t in Ioo 0 T, ψ t • (2 * ut' t (u' t)) =
        ∫ t in Ioo 0 T, ψ t * (ut' t (u' t) + ut' t (u' t)) :=
      integral_congr_ae (ae_of_all _ fun t => by simp only [smul_eq_mul]; ring)
    rw [e1, e2]; exact this
  have h2 : HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T (fun t => ‖w t‖ ^ 2)
      (fun t => 2 * ut t (u t)) :=
    weak_congr h2' (ae_of_all _ fun _ => rfl)
      (by filter_upwards [hu'e, hut'e] with t a1 a2; rw [a1, a2])
  refine ⟨w, hwc, hwa, h1, h2, ?_⟩
  -- the L^∞ bound
  have hFc : ContinuousOn (fun t => ‖w t‖ ^ 2) (Icc 0 T) := hwc.norm.pow 2
  have hgi : IntegrableOn (fun t => 2 * ut t (u t)) (Ioo 0 T) :=
    (IBPc.pair_integrable_gen hut hu).const_mul 2
  have hftc := IBPc.ftc_of_weak hT hFc hgi (fun φ hφ => by
    simpa only [ContinuousLinearMap.id_apply, smul_eq_mul] using h2 φ hφ)
  have hsb := sup_bound hT hFc hgi hftc
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (eLpNorm u 2 (volume.restrict (Ioo 0 T))).toReal := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (eLpNorm ut 2 (volume.restrict (Ioo 0 T))).toReal := ⟨_, rfl⟩
  have hint : ∫ s in Ioo 0 T, ‖w s‖ ^ 2 ≤ ‖HT.toH‖ ^ 2 * A ^ 2 := by
    have hi2 : Integrable (fun s => ‖HT.toH‖ ^ 2 * ‖u s‖ ^ 2) (volume.restrict (Ioo 0 T)) :=
      ((memLp_two_iff_integrable_sq_norm hu.1).1 hu).const_mul _
    calc ∫ s in Ioo 0 T, ‖w s‖ ^ 2 = ∫ s in Ioo 0 T, ‖HT.toH (u s)‖ ^ 2 :=
          integral_congr_ae (by filter_upwards [hwa] with t ht; rw [ht])
      _ ≤ ∫ s in Ioo 0 T, ‖HT.toH‖ ^ 2 * ‖u s‖ ^ 2 := by
          refine integral_mono_of_nonneg (ae_of_all _ fun s => by positivity) hi2
            (ae_of_all _ fun s => ?_)
          show ‖HT.toH (u s)‖ ^ 2 ≤ ‖HT.toH‖ ^ 2 * ‖u s‖ ^ 2
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (HT.toH.le_opNorm _) 2
      _ = ‖HT.toH‖ ^ 2 * ∫ s in Ioo 0 T, ‖u s‖ ^ 2 := integral_const_mul _ _
      _ = _ := by rw [int_sq hu, hA]
  have hpair : ∫ r in Ioo 0 T, |2 * ut r (u r)| ≤ 2 * (B * A) := by
    have e : ∫ r in Ioo 0 T, |2 * ut r (u r)| = 2 * ∫ r in Ioo 0 T, |ut r (u r)| := by
      rw [← integral_const_mul]
      congr 1; funext r; rw [abs_mul, abs_two]
    rw [e, hA, hB]
    exact mul_le_mul_of_nonneg_left (pair_abs_le_gen hut hu) (by norm_num)
  have hpt : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ (‖HT.toH‖ * (T⁻¹ + 1) + 1) * (A + B) := by
    intro t ht
    have h := hsb t ht
    rw [sub_zero] at h
    refine const_bound (norm_nonneg _) (inv_nonneg.2 hT.le) (by rw [hA]; exact ENNReal.toReal_nonneg)
      (by rw [hB]; exact ENNReal.toReal_nonneg) (norm_nonneg _) ?_
    calc ‖w t‖ ^ 2 ≤ T⁻¹ * (∫ s in Ioo 0 T, ‖w s‖ ^ 2) + ∫ r in Ioo 0 T, |2 * ut r (u r)| := h
      _ ≤ T⁻¹ * (‖HT.toH‖ ^ 2 * A ^ 2) + 2 * (B * A) :=
        add_le_add (mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hT.le)) hpair
  have hC0 : 0 ≤ ‖HT.toH‖ * (T⁻¹ + 1) + 1 := by positivity
  rw [eLpNorm_exponent_top]
  refine (eLpNormEssSup_le_of_ae_bound (C := (‖HT.toH‖ * (T⁻¹ + 1) + 1) * (A + B)) ?_).trans
    (le_of_eq ?_)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hpt t (Ioo_subset_Icc_self ht)
  · rw [ENNReal.ofReal_mul hC0, hA, hB,
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hu.2.ne, ENNReal.ofReal_toReal hut.2.ne]
    rfl

end F

end HTC
end Qf92_F

open MeasureTheory HunterPDE.Parabolic ENNReal NNReal in
theorem solution {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HT : HilbertTriple V H) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ≥0, ∀ (u : ℝ → V) (ut : ℝ → StrongDual ℝ V),
      MemLp u 2 (volume.restrict (Set.Ioo 0 T)) →
      MemLp ut 2 (volume.restrict (Set.Ioo 0 T)) →
      HasWeakTimeDeriv HT.toDualV T u ut →
      ∃ ũ : ℝ → H, ContinuousOn ũ (Set.Icc 0 T) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), ũ t = HT.toH (u t)) ∧
        (∀ v : V, HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
          (fun t => inner ℝ (ũ t) (HT.toH v)) (fun t => ut t v)) ∧
        HasWeakTimeDeriv (ContinuousLinearMap.id ℝ ℝ) T
          (fun t => ‖ũ t‖ ^ 2) (fun t => 2 * ut t (u t)) ∧
        eLpNorm ũ ∞ (volume.restrict (Set.Ioo 0 T)) ≤
          (C : ℝ≥0∞) * (eLpNorm u 2 (volume.restrict (Set.Ioo 0 T)) +
            eLpNorm ut 2 (volume.restrict (Set.Ioo 0 T))) := by
  exact HTC.main HT T hT
