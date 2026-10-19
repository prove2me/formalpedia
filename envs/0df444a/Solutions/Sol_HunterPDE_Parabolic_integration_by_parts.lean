-- Prove2me | solution 1 for HunterPDE.Parabolic.integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T12:10:30.113133+00:00
-- url     : https://prove2.me/submissions/0ba87ee6-0bde-4a09-84ca-7743d4b10576

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_HilbertTriple

/-! Integration by parts in time for a Hilbert triple (Hunter, Theorem 6.42).
Proof: after replacing the data by strongly measurable representatives and extending the continuous
representatives to `ℝ`, the scalar function `φ(t) = (uc t, vc t)_ℋ` has weak derivative
`⟨u_t, v⟩ + ⟨v_t, u⟩ ∈ L¹(0,T)`.  This is shown by testing against `ψ ∈ C_c^∞(0,T)`, writing
`φ(t+h) - φ(t)` through the increments `uc(t+h) - uc(t) = ∫_t^{t+h} u_t` (scalar du Bois-Reymond),
and passing `h → 0` with Fubini and continuity of translation in `L²`.  Then `φ` is absolutely
continuous and `φ(T) - φ(0) = ∫₀ᵀ (⟨u_t, v⟩ + ⟨v_t, u⟩)`. -/

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

section Q0ca_D5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
open HunterPDE.Parabolic

namespace IBPc

section D5

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem ibp_main (HT : HilbertTriple V H) {T : ℝ} (hT : 0 < T)
    {u v : ℝ → V} {ut vt : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T))) (hv : MemLp v 2 (volume.restrict (Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Ioo 0 T))) (hvt : MemLp vt 2 (volume.restrict (Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (hdv : HasWeakTimeDeriv HT.toDualV T v vt)
    {uc vc : ℝ → H} (hucc : ContinuousOn uc (Icc 0 T)) (hvcc : ContinuousOn vc (Icc 0 T))
    (huc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc t = HT.toH (u t))
    (hvc : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), vc t = HT.toH (v t)) :
    ∫ t in Ioo 0 T, ut t (v t) =
      inner ℝ (uc T) (vc T) - inner ℝ (uc 0) (vc 0) - ∫ t in Ioo 0 T, vt t (u t) := by
  obtain ⟨u', hu'm, hu'e⟩ : ∃ u' : ℝ → V, StronglyMeasurable u' ∧
      u =ᵐ[volume.restrict (Ioo 0 T)] u' := ⟨_, hu.1.stronglyMeasurable_mk, hu.1.ae_eq_mk⟩
  obtain ⟨v', hv'm, hv'e⟩ : ∃ v' : ℝ → V, StronglyMeasurable v' ∧
      v =ᵐ[volume.restrict (Ioo 0 T)] v' := ⟨_, hv.1.stronglyMeasurable_mk, hv.1.ae_eq_mk⟩
  obtain ⟨ut', hut'm, hut'e⟩ : ∃ ut' : ℝ → StrongDual ℝ V, StronglyMeasurable ut' ∧
      ut =ᵐ[volume.restrict (Ioo 0 T)] ut' := ⟨_, hut.1.stronglyMeasurable_mk, hut.1.ae_eq_mk⟩
  obtain ⟨vt', hvt'm, hvt'e⟩ : ∃ vt' : ℝ → StrongDual ℝ V, StronglyMeasurable vt' ∧
      vt =ᵐ[volume.restrict (Ioo 0 T)] vt' := ⟨_, hvt.1.stronglyMeasurable_mk, hvt.1.ae_eq_mk⟩
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
  have hucc' : Continuous (fun t => uc (cl t)) := hucc.comp_continuous hclc hclmem
  have hvcc' : Continuous (fun t => vc (cl t)) := hvcc.comp_continuous hclc hclmem
  have hdu' : HasWeakTimeDeriv HT.toDualV T u' ut' := by
    intro φ hφ
    have e := hdu φ hφ
    have e1 : ∫ t in Ioo 0 T, deriv φ t • HT.toDualV (u' t) =
        ∫ t in Ioo 0 T, deriv φ t • HT.toDualV (u t) :=
      integral_congr_ae (by filter_upwards [hu'e] with t ht; rw [ht])
    have e2 : ∫ t in Ioo 0 T, φ t • ut' t = ∫ t in Ioo 0 T, φ t • ut t :=
      integral_congr_ae (by filter_upwards [hut'e] with t ht; rw [ht])
    rw [e1, e2]; exact e
  have hdv' : HasWeakTimeDeriv HT.toDualV T v' vt' := by
    intro φ hφ
    have e := hdv φ hφ
    have e1 : ∫ t in Ioo 0 T, deriv φ t • HT.toDualV (v' t) =
        ∫ t in Ioo 0 T, deriv φ t • HT.toDualV (v t) :=
      integral_congr_ae (by filter_upwards [hv'e] with t ht; rw [ht])
    have e2 : ∫ t in Ioo 0 T, φ t • vt' t = ∫ t in Ioo 0 T, φ t • vt t :=
      integral_congr_ae (by filter_upwards [hvt'e] with t ht; rw [ht])
    rw [e1, e2]; exact e
  have huc' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), uc (cl t) = HT.toH (u' t) := by
    filter_upwards [huc, hu'e, ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3
    rw [hclid t (Ioo_subset_Icc_self h3), h1, h2]
  have hvc' : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), vc (cl t) = HT.toH (v' t) := by
    filter_upwards [hvc, hv'e, ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3
    rw [hclid t (Ioo_subset_Icc_self h3), h1, h2]
  have key := ibp_core HT hT hu'm hv'm hut'm hvt'm (hu.ae_eq hu'e) (hv.ae_eq hv'e)
    (hut.ae_eq hut'e) (hvt.ae_eq hvt'e) hdu' hdv' hucc' hvcc' huc' hvc'
  have eT := hclid T ⟨hT.le, le_rfl⟩
  have e0 := hclid 0 ⟨le_rfl, hT.le⟩
  rw [eT, e0] at key
  have f1 : ∫ t in Ioo 0 T, ut t (v t) = ∫ t in Ioo 0 T, ut' t (v' t) :=
    integral_congr_ae (by filter_upwards [hut'e, hv'e] with t h1 h2; rw [h1, h2])
  have f2 : ∫ t in Ioo 0 T, vt t (u t) = ∫ t in Ioo 0 T, vt' t (u' t) :=
    integral_congr_ae (by filter_upwards [hvt'e, hu'e] with t h1 h2; rw [h1, h2])
  rw [f1, f2]
  exact key

end D5

end IBPc
end Q0ca_D5

open MeasureTheory HunterPDE.Parabolic in
theorem solution {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HT : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u v : ℝ → V) (ut vt : ℝ → StrongDual ℝ V)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo 0 T)))
    (hv : MemLp v 2 (volume.restrict (Set.Ioo 0 T)))
    (hut : MemLp ut 2 (volume.restrict (Set.Ioo 0 T)))
    (hvt : MemLp vt 2 (volume.restrict (Set.Ioo 0 T)))
    (hdu : HasWeakTimeDeriv HT.toDualV T u ut) (hdv : HasWeakTimeDeriv HT.toDualV T v vt)
    (uc vc : ℝ → H) (hucc : ContinuousOn uc (Set.Icc 0 T)) (hvcc : ContinuousOn vc (Set.Icc 0 T))
    (huc : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), uc t = HT.toH (u t))
    (hvc : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)), vc t = HT.toH (v t)) :
    ∫ t in Set.Ioo 0 T, ut t (v t) =
      inner ℝ (uc T) (vc T) - inner ℝ (uc 0) (vc 0) - ∫ t in Set.Ioo 0 T, vt t (u t) := by
  exact IBPc.ibp_main HT hT hu hv hut hvt hdu hdv hucc hvcc huc hvc
