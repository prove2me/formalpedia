-- Prove2me | solution 1 for JHolomorphic.eLpNorm_diffQuot_partials_le_of_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:25:47.191332+00:00
-- url     : https://prove2.me/submissions/c8bb380d-72ac-46ec-bb4c-d4948844648f

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_clm_apply
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral
import Theorems.Thm_JHolomorphic_eLpNorm_diffQuot_le



namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Weak partial derivatives are compatible with translation. -/
theorem HasWeakPartialsOn.comp_add_right_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f fs ft : ℂ → E} (h : HasWeakPartialsOn U f fs ft) (a : ℂ) :
    HasWeakPartialsOn ((· + a) ⁻¹' U) (fun z => f (z + a)) (fun z => fs (z + a))
      (fun z => ft (z + a)) := by
  intro φ hφ hc hU
  set ψ : ℂ → ℝ := fun z => φ (z - a) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.sub contDiff_const)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subRight a)
  have hψU : tsupport ψ ⊆ U := by
    intro z hz
    have : z - a ∈ tsupport φ := by
      have := tsupport_comp_subset_preimage φ (f := fun z => z - a) (continuous_sub_right a) hz
      exact this
    simpa using hU this
  obtain ⟨h1, h2⟩ := h ψ hψs hψc hψU
  have hd : ∀ z, fderiv ℝ ψ z = fderiv ℝ φ (z - a) := fun z => fderiv_comp_sub (f := φ) a
  constructor
  · calc ∫ z, fderiv ℝ φ z 1 • f (z + a)
        = ∫ z, fderiv ℝ φ (z - a) 1 • f (z - a + a) :=
          (integral_sub_right_eq_self (fun z => fderiv ℝ φ z 1 • f (z + a)) a).symm
      _ = ∫ z, fderiv ℝ ψ z 1 • f z := by simp [hd]
      _ = -∫ z, ψ z • fs z := h1
      _ = -∫ z, φ z • fs (z + a) := by
          rw [← integral_add_right_eq_self (fun z => ψ z • fs z) a]; simp [hψ]
  · calc ∫ z, fderiv ℝ φ z Complex.I • f (z + a)
        = ∫ z, fderiv ℝ φ (z - a) Complex.I • f (z - a + a) :=
          (integral_sub_right_eq_self (fun z => fderiv ℝ φ z Complex.I • f (z + a)) a).symm
      _ = ∫ z, fderiv ℝ ψ z Complex.I • f z := by simp [hd]
      _ = -∫ z, ψ z • ft z := h2
      _ = -∫ z, φ z • ft (z + a) := by
          rw [← integral_add_right_eq_self (fun z => ψ z • ft z) a]; simp [hψ]

/-- Weak partial derivatives of `c • (f - g)`. -/
theorem HasWeakPartialsOn.smul_sub_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {f fs ft g gs gt : ℂ → E} (hf : HasWeakPartialsOn U f fs ft)
    (hg : HasWeakPartialsOn U g gs gt)
    (hfi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K ∧ IntegrableOn fs K ∧ IntegrableOn ft K)
    (hgi : ∀ K ⊆ U, IsCompact K → IntegrableOn g K ∧ IntegrableOn gs K ∧ IntegrableOn gt K)
    (c : ℝ) :
    HasWeakPartialsOn U (fun z => c • (f z - g z)) (fun z => c • (fs z - gs z))
      (fun z => c • (ft z - gt z)) := by
  intro φ hφ hc hU
  obtain ⟨hf1, hf2⟩ := hf φ hφ hc hU
  obtain ⟨hg1, hg2⟩ := hg φ hφ hc hU
  have hI : ∀ (v : ℂ) {k : ℂ → E}, (∀ K ⊆ U, IsCompact K → IntegrableOn k K) →
      Integrable (fun z => fderiv ℝ φ z v • k z) := by
    intro v k hk
    obtain ⟨h1, h2, h3⟩ := fderiv_apply_isTestFunction hφ hc hU v
    exact integrable_smul_of_integrableOn_compact hk h1.continuous.continuousOn h2 h3
  have hJ : ∀ {k : ℂ → E}, (∀ K ⊆ U, IsCompact K → IntegrableOn k K) →
      Integrable (fun z => φ z • k z) := fun hk =>
    integrable_smul_of_integrableOn_compact hk hφ.continuous.continuousOn hc hU
  have e1 : ∀ (v : ℂ) z, fderiv ℝ φ z v • (c • (f z - g z)) =
      c • (fderiv ℝ φ z v • f z - fderiv ℝ φ z v • g z) := by
    intro v z; rw [smul_comm, smul_sub]
  have e2 : ∀ z (k l : ℂ → E), φ z • (c • (k z - l z)) = c • (φ z • k z - φ z • l z) := by
    intro z k l; rw [smul_comm, smul_sub]
  constructor
  · simp_rw [e1, e2]
    rw [integral_smul, integral_smul, integral_sub (hI 1 fun K hK hKc => (hfi K hK hKc).1)
      (hI 1 fun K hK hKc => (hgi K hK hKc).1),
      integral_sub (hJ fun K hK hKc => (hfi K hK hKc).2.1)
      (hJ fun K hK hKc => (hgi K hK hKc).2.1), hf1, hg1]
    module
  · simp_rw [e1, e2]
    rw [integral_smul, integral_smul, integral_sub (hI Complex.I fun K hK hKc => (hfi K hK hKc).1)
      (hI Complex.I fun K hK hKc => (hgi K hK hKc).1),
      integral_sub (hJ fun K hK hKc => (hfi K hK hKc).2.2)
      (hJ fun K hK hKc => (hgi K hK hKc).2.2), hf2, hg2]
    module

/-- Weak partial derivatives of `β • w` for a real `C¹` function `β`. -/
theorem HasWeakPartialsOn.smul_left_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {β : ℂ → ℝ} (hβ : ContDiff ℝ 1 β)
    {w ws wt : ℂ → E} (hw : HasWeakPartialsOn U w ws wt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn w K ∧ IntegrableOn ws K ∧ IntegrableOn wt K) :
    HasWeakPartialsOn U (fun z => β z • w z) (fun z => fderiv ℝ β z 1 • w z + β z • ws z)
      (fun z => fderiv ℝ β z Complex.I • w z + β z • wt z) := by
  have hA : ContDiffOn ℝ 1 (fun z => β z • ContinuousLinearMap.id ℝ E) U :=
    (hβ.smul contDiff_const).contDiffOn
  have h := HasWeakPartialsOn.clm_apply hU hA hw hint
  have hd : ∀ z, fderiv ℝ (fun z => β z • ContinuousLinearMap.id ℝ E) z =
      (fderiv ℝ β z).smulRight (ContinuousLinearMap.id ℝ E) := fun z =>
    fderiv_smul_const (c := β) (f := ContinuousLinearMap.id ℝ E)
      ((hβ.differentiable (by norm_num)) z)
  simpa [hd] using h

/-- Translation of `L^p` membership and norm on a restricted measure. -/
theorem memLp_comp_add_right_aux {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ}
    [μ.IsAddRightInvariant] {q : ENNReal} {g : ℂ → E} {S : Set ℂ} (hS : MeasurableSet S) (a : ℂ)
    (hg : MemLp g q (μ.restrict S)) :
    MemLp (fun z => g (z + a)) q (μ.restrict ((· + a) ⁻¹' S)) ∧
      eLpNorm (fun z => g (z + a)) q (μ.restrict ((· + a) ⁻¹' S)) = eLpNorm g q (μ.restrict S) := by
  have hmp := (measurePreserving_add_right μ a).restrict_preimage hS
  exact ⟨hg.comp_measurePreserving hmp, eLpNorm_comp_measurePreserving hg.1 hmp⟩

end JHolomorphic

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff

/-- The uniform difference-quotient bound for `uₛ`, `uₜ` on a small disc (absorption step). -/
theorem diffQuot_bound_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (U : Set ℂ) (hU : IsOpen U)
    (u us ut : ℂ → E) (hu : ContinuousOn u U)
    (hw : HasWeakPartialsOn U u us ut)
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J (u z) (ut z) = 0)
    (z₀ : ℂ) (R₀ r : ℝ) (hr : 0 < r) (h3r : 3 * r ≤ R₀) (hS : closedBall z₀ R₀ ⊆ U)
    (hLpS : MemLp u (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)) ∧
      MemLp us (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)))
    (J₀ : E →L[ℝ] E) (Cf CM L ε : ℝ) (hCf0 : 0 ≤ Cf) (hCM0 : 0 ≤ CM) (hL0 : 0 ≤ L)
    (hε0 : 0 ≤ ε)
    (hCf : ∀ U : Set ℂ, IsOpen U → ∀ ξ ξs ξt : ℂ → E, Continuous ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ U → HasWeakPartialsOn U ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict U) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm ξs (ENNReal.ofReal p) (volume.restrict U) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict U) ≤
        ENNReal.ofReal Cf * eLpNorm (fun z => ξs z + J₀ (ξt z)) (ENNReal.ofReal p)
          (volume.restrict U))
    (hCM : ∀ ξ ξs ξt : ℂ → E, Continuous ξ →
      tsupport ξ ⊆ ball z₀ (2 * r) → HasWeakPartialsOn (ball z₀ (2 * r)) ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) →
      ∀ z, ‖ξ z‖ₑ ≤ ENNReal.ofReal CM *
        (eLpNorm ξs (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r)))))
    (hJε : ∀ z ∈ closedBall z₀ R₀, ‖J (u z) - J₀‖ ≤ ε)
    (hJL : ∀ z ∈ closedBall z₀ R₀, ∀ z' ∈ closedBall z₀ R₀,
      ‖J (u z) - J (u z')‖ ≤ L * ‖u z - u z'‖)
    (hsm1 : Cf * ε ≤ 1 / 4)
    (hsm2 : Cf * L * CM *
      (eLpNorm ut (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀))).toReal ≤ 1 / 4)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ closedBall z₀ (3 * r / 2))
    (hβ1 : ∀ z ∈ ball z₀ r, β z = 1) (hβb : ∀ z, ‖β z‖ ≤ 1)
    (M : ℝ) (hM : ∀ z, ‖fderiv ℝ β z‖ ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) (h : ℝ) (hh0 : h ≠ 0) (hhr : |h| < r) :
    eLpNorm (fun z => h⁻¹ • (us (z + (h : ℂ) * v) - us z)) (ENNReal.ofReal p)
        (volume.restrict (ball z₀ r)) +
      eLpNorm (fun z => h⁻¹ • (ut (z + (h : ℂ) * v) - ut z)) (ENNReal.ofReal p)
        (volume.restrict (ball z₀ r)) ≤
    ENNReal.ofReal (2 * (Cf * (M * (1 + ‖J₀‖ + ε)) *
      (eLpNorm (fun z => v.re • us z + v.im • ut z) (ENNReal.ofReal p)
        (volume.restrict (closedBall z₀ R₀))).toReal)) := by
  set P := ENNReal.ofReal p with hPdef
  have hp1 : (1 : ENNReal) ≤ P := by
    rw [hPdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  set a : ℂ := (h : ℂ) * v with ha_def
  have ha : ‖a‖ = |h| := by rw [ha_def, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
  set S := closedBall z₀ R₀ with hS_def
  set B := ball z₀ (2 * r) with hB_def
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀)
  have hBS : B ⊆ S := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hBa : B ⊆ (· + a) ⁻¹' S := by
    intro z hz
    simp only [Set.mem_preimage, hS_def, mem_closedBall]
    have h1 := mem_ball.1 hz
    have h2 : dist (z + a) z ≤ |h| := by rw [dist_eq_norm, add_sub_cancel_left, ha]
    linarith [dist_triangle (z + a) z z₀]
  have hBU : B ⊆ U := hBS.trans hS
  have hBaU : B ⊆ (· + a) ⁻¹' U := hBa.trans (Set.preimage_mono hS)
  have hmS : MeasurableSet S := isClosed_closedBall.measurableSet
  have hμBS : volume.restrict B ≤ volume.restrict S := Measure.restrict_mono hBS le_rfl
  have hμBa : volume.restrict B ≤ volume.restrict ((· + a) ⁻¹' S) :=
    Measure.restrict_mono hBa le_rfl
  have tr : ∀ {g : ℂ → E}, MemLp g P (volume.restrict S) →
      MemLp (fun z => g (z + a)) P (volume.restrict B) ∧
        eLpNorm (fun z => g (z + a)) P (volume.restrict B) ≤ eLpNorm g P (volume.restrict S) := by
    intro g hg
    obtain ⟨h1, h2⟩ := memLp_comp_add_right_aux (μ := volume) hmS a hg
    exact ⟨h1.mono_measure hμBa, (eLpNorm_mono_measure _ hμBa).trans h2.le⟩
  -- the six functions on `B`
  have m0 := hLpS.1.mono_measure hμBS
  have m1 := hLpS.2.1.mono_measure hμBS
  have m2 := hLpS.2.2.mono_measure hμBS
  have n0 := (tr hLpS.1).1
  have n1 := (tr hLpS.2.1).1
  have n2 := (tr hLpS.2.2).1
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hInt : ∀ {g : ℂ → E}, MemLp g P (volume.restrict B) →
      ∀ K ⊆ B, IsCompact K → IntegrableOn g K := fun hg K hK _ =>
    IntegrableOn.mono_set (t := B) (hg.integrable hp1) hK
  set w : ℂ → E := fun z => h⁻¹ • (u (z + a) - u z) with hw_def
  set ws : ℂ → E := fun z => h⁻¹ • (us (z + a) - us z) with hws_def
  set wt : ℂ → E := fun z => h⁻¹ • (ut (z + a) - ut z) with hwt_def
  have mw : MemLp w P (volume.restrict B) := (n0.sub m0).const_smul h⁻¹
  have mws : MemLp ws P (volume.restrict B) := (n1.sub m1).const_smul h⁻¹
  have mwt : MemLp wt P (volume.restrict B) := (n2.sub m2).const_smul h⁻¹
  have hwB : HasWeakPartialsOn B u us ut := fun φ hφ hc hs => hw φ hφ hc (hs.trans hBU)
  have hwB' : HasWeakPartialsOn B (fun z => u (z + a)) (fun z => us (z + a))
      (fun z => ut (z + a)) := fun φ hφ hc hs =>
    (hw.comp_add_right_aux a) φ hφ hc (hs.trans hBaU)
  have hW : HasWeakPartialsOn B w ws wt :=
    HasWeakPartialsOn.smul_sub_aux hwB' hwB
      (fun K hK hKc => ⟨hInt n0 K hK hKc, hInt n1 K hK hKc, hInt n2 K hK hKc⟩)
      (fun K hK hKc => ⟨hInt m0 K hK hKc, hInt m1 K hK hKc, hInt m2 K hK hKc⟩) h⁻¹
  -- the localized difference quotient `ξ = β w`
  have hβ1' : ContDiff ℝ 1 β := hβ.of_le (by exact_mod_cast le_top)
  set bs : ℂ → ℝ := fun z => fderiv ℝ β z 1 with hbs_def
  set bt : ℂ → ℝ := fun z => fderiv ℝ β z Complex.I with hbt_def
  have hdc : Continuous (fderiv ℝ β) := hβ.continuous_fderiv (by simp)
  have hbsc : Continuous bs := hdc.clm_apply continuous_const
  have hbtc : Continuous bt := hdc.clm_apply continuous_const
  have hbsM : ∀ z, ‖bs z‖ ≤ M := fun z =>
    ((fderiv ℝ β z).le_opNorm 1).trans (by simpa using hM z)
  have hbtM : ∀ z, ‖bt z‖ ≤ M := fun z =>
    ((fderiv ℝ β z).le_opNorm Complex.I).trans (by simpa using hM z)
  set ξ : ℂ → E := fun z => β z • w z with hξ_def
  set ξs : ℂ → E := fun z => bs z • w z + β z • ws z with hξs_def
  set ξt : ℂ → E := fun z => bt z • w z + β z • wt z with hξt_def
  have hX : HasWeakPartialsOn B ξ ξs ξt :=
    HasWeakPartialsOn.smul_left_aux isOpen_ball hβ1' hW
      (fun K hK hKc => ⟨hInt mw K hK hKc, hInt mws K hK hKc, hInt mwt K hK hKc⟩)
  have mξs : MemLp ξs P (volume.restrict B) := by
    refine (mw.of_le_mul (c := M) (hbsc.aestronglyMeasurable.smul mw.1)
      (ae_of_all _ fun z => ?_)).add (mws.of_le_mul (c := 1)
      (hβ.continuous.aestronglyMeasurable.smul mws.1) (ae_of_all _ fun z => ?_))
    · exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (hbsM z) (norm_nonneg _))
    · exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (hβb z) (norm_nonneg _))
  have mξt : MemLp ξt P (volume.restrict B) := by
    refine (mw.of_le_mul (c := M) (hbtc.aestronglyMeasurable.smul mw.1)
      (ae_of_all _ fun z => ?_)).add (mwt.of_le_mul (c := 1)
      (hβ.continuous.aestronglyMeasurable.smul mwt.1) (ae_of_all _ fun z => ?_))
    · exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (hbtM z) (norm_nonneg _))
    · exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (hβb z) (norm_nonneg _))
  have hβB : tsupport β ⊆ B := hβs.trans (closedBall_subset_ball (by linarith))
  have hξB : tsupport ξ ⊆ B := (tsupport_smul_subset_left _ _).trans hβB
  have hwc : ContinuousOn w B := by
    have h1 : ContinuousOn (fun z => u (z + a)) B :=
      hu.comp (continuous_add_right a).continuousOn (fun z hz => hBaU hz)
    exact (h1.sub (hu.mono hBU)).const_smul h⁻¹
  have hξc : Continuous ξ := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ B
    · exact (hβ.continuous.continuousOn.smul hwc).continuousAt (isOpen_ball.mem_nhds hz)
    · have h0 : z ∉ tsupport ξ := fun h' => hz (hξB h')
      rw [notMem_tsupport_iff_eventuallyEq] at h0
      exact continuousAt_const.congr h0.symm
  have hξK : HasCompactSupport ξ :=
    (isCompact_closedBall z₀ (3 * r / 2)).of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_smul_subset_left _ _).trans hβs)
  have hF := hCf B isOpen_ball ξ ξs ξt hξc hξK hξB hX mξs mξt
  have hMo := hCM ξ ξs ξt hξc hξB hX mξs mξt
  set X := eLpNorm ξs P (volume.restrict B) + eLpNorm ξt P (volume.restrict B) with hX_def
  have hXfin : X ≠ ⊤ := ENNReal.add_ne_top.2 ⟨mξs.2.ne, mξt.2.ne⟩
  set k := ENNReal.ofReal CM * X with hk_def
  have hk : k ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXfin
  have hξb : ∀ z, ‖ξ z‖ ≤ k.toReal := fun z => by
    have := hMo z
    rw [← ofReal_norm_eq_enorm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hk).1 this
  -- the equation at `z` and at `z + a`
  have heqB : ∀ᵐ z ∂(volume.restrict B), us z + J (u z) (ut z) = 0 :=
    heq.filter_mono (ae_mono (Measure.restrict_mono hBU le_rfl))
  have heqB' : ∀ᵐ z ∂(volume.restrict B), us (z + a) + J (u (z + a)) (ut (z + a)) = 0 := by
    have hmp := (measurePreserving_add_right (volume : Measure ℂ) a).restrict_preimage
      hU.measurableSet
    have := hmp.quasiMeasurePreserving.ae heq
    exact this.filter_mono (ae_mono (Measure.restrict_mono hBaU le_rfl))
  set K1 := M * (1 + ‖J₀‖ + ε) with hK1_def
  have hpt : ∀ᵐ z ∂(volume.restrict B), ‖ξs z + J₀ (ξt z)‖ ≤
      K1 * ‖w z‖ + ε * ‖ξt z‖ + (L * k.toReal) * ‖ut (z + a)‖ := by
    filter_upwards [heqB, heqB', ae_restrict_mem measurableSet_ball] with z e1 e2 hz
    have hzS : z ∈ S := hBS hz
    have hzaS : z + a ∈ S := hBa hz
    have hus : us z = -J (u z) (ut z) := eq_neg_of_add_eq_zero_left e1
    have hus' : us (z + a) = -J (u (z + a)) (ut (z + a)) := eq_neg_of_add_eq_zero_left e2
    have hid : ξs z + J₀ (ξt z) = bs z • w z + bt z • J₀ (w z) +
        (J₀ - J (u z)) (β z • wt z) +
        (β z * h⁻¹) • (J (u z) - J (u (z + a))) (ut (z + a)) := by
      simp only [hξs_def, hξt_def, hws_def, hwt_def, hus, hus', map_add, map_smul, map_sub,
        ContinuousLinearMap.sub_apply, smul_sub, smul_add, mul_smul, smul_neg, neg_sub]
      module
    have hwn : ‖u z - u (z + a)‖ = |h| * ‖w z‖ := by
      rw [hw_def]; simp only [norm_smul, norm_inv, Real.norm_eq_abs]
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hh0), one_mul, norm_sub_rev]
    have t1 : ‖bs z • w z‖ ≤ M * ‖w z‖ := by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hbsM z) (norm_nonneg _)
    have t2 : ‖bt z • J₀ (w z)‖ ≤ M * ‖J₀‖ * ‖w z‖ := by
      rw [norm_smul, mul_assoc]
      exact mul_le_mul (hbtM z) (J₀.le_opNorm _) (norm_nonneg _) hM0
    have hβwt : β z • wt z = ξt z - bt z • w z := by simp [hξt_def]
    have t3 : ‖(J₀ - J (u z)) (β z • wt z)‖ ≤ ε * ‖ξt z‖ + ε * M * ‖w z‖ := by
      have hn : ‖J₀ - J (u z)‖ ≤ ε := by rw [norm_sub_rev]; exact hJε z hzS
      calc ‖(J₀ - J (u z)) (β z • wt z)‖ ≤ ‖J₀ - J (u z)‖ * ‖β z • wt z‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * (‖ξt z‖ + M * ‖w z‖) := by
            refine mul_le_mul hn ?_ (norm_nonneg _) hε0
            rw [hβwt]
            refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hbtM z) (norm_nonneg _)
        _ = ε * ‖ξt z‖ + ε * M * ‖w z‖ := by ring
    have t4 : ‖(β z * h⁻¹) • (J (u z) - J (u (z + a))) (ut (z + a))‖ ≤
        L * k.toReal * ‖ut (z + a)‖ := by
      have hJ := hJL z hzS (z + a) hzaS
      have hξz : ‖β z‖ * ‖w z‖ ≤ k.toReal := by
        have := hξb z; rwa [hξ_def, norm_smul] at this
      calc ‖(β z * h⁻¹) • (J (u z) - J (u (z + a))) (ut (z + a))‖
          ≤ ‖β z * h⁻¹‖ * (‖J (u z) - J (u (z + a))‖ * ‖ut (z + a)‖) := by
            rw [norm_smul]; gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖β z * h⁻¹‖ * ((L * (|h| * ‖w z‖)) * ‖ut (z + a)‖) := by
            gcongr; rw [← hwn]; exact hJ
        _ = L * (‖β z‖ * ‖w z‖) * ‖ut (z + a)‖ := by
            simp only [norm_mul, norm_inv, Real.norm_eq_abs]
            field_simp
        _ ≤ L * k.toReal * ‖ut (z + a)‖ := by gcongr
    rw [hid]
    calc ‖bs z • w z + bt z • J₀ (w z) + (J₀ - J (u z)) (β z • wt z) +
          (β z * h⁻¹) • (J (u z) - J (u (z + a))) (ut (z + a))‖
        ≤ ‖bs z • w z‖ + ‖bt z • J₀ (w z)‖ + ‖(J₀ - J (u z)) (β z • wt z)‖ +
          ‖(β z * h⁻¹) • (J (u z) - J (u (z + a))) (ut (z + a))‖ := norm_add₄_le
      _ ≤ M * ‖w z‖ + M * ‖J₀‖ * ‖w z‖ + (ε * ‖ξt z‖ + ε * M * ‖w z‖) +
          L * k.toReal * ‖ut (z + a)‖ := by gcongr
      _ = K1 * ‖w z‖ + ε * ‖ξt z‖ + (L * k.toReal) * ‖ut (z + a)‖ := by
          rw [hK1_def]; ring
  -- `L^p` norms
  have hnorm : ∀ (c : ℝ) {g : ℂ → E}, 0 ≤ c →
      eLpNorm (fun z => c * ‖g z‖) P (volume.restrict B) ≤
        ENNReal.ofReal c * eLpNorm g P (volume.restrict B) := fun c g hc =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (norm_nonneg _))]) P
  have hK10 : 0 ≤ K1 := mul_nonneg hM0 (by positivity)
  have hLk0 : 0 ≤ L * k.toReal := mul_nonneg hL0 ENNReal.toReal_nonneg
  have hsum : eLpNorm (fun z => ξs z + J₀ (ξt z)) P (volume.restrict B) ≤
      ENNReal.ofReal K1 * eLpNorm w P (volume.restrict B) +
        ENNReal.ofReal ε * eLpNorm ξt P (volume.restrict B) +
        ENNReal.ofReal (L * k.toReal) * eLpNorm (fun z => ut (z + a)) P (volume.restrict B) := by
    refine (eLpNorm_mono_ae_real hpt).trans ?_
    have a1 := mw.1.norm.const_mul K1
    have a2 := mξt.1.norm.const_mul ε
    have a3 := n2.1.norm.const_mul (L * k.toReal)
    refine (eLpNorm_add_le (a1.add a2) a3 hp1).trans ?_
    refine add_le_add ((eLpNorm_add_le a1 a2 hp1).trans (add_le_add ?_ ?_)) ?_
    · exact hnorm K1 hK10
    · exact hnorm ε hε0
    · exact hnorm (L * k.toReal) hLk0
  -- the difference-quotient bound for `w`
  have hwG : eLpNorm w P (volume.restrict B) ≤
      eLpNorm (fun z => v.re • us z + v.im • ut z) P (volume.restrict S) := by
    have hbR : ball z₀ R₀ ⊆ U := ball_subset_closedBall.trans hS
    have hi : ∀ K ⊆ ball z₀ R₀, IsCompact K →
        IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K := by
      intro K hK _
      haveI : IsFiniteMeasure (volume.restrict S) :=
        isFiniteMeasure_restrict.2 (measure_closedBall_lt_top).ne
      have hKS : K ⊆ S := hK.trans ball_subset_closedBall
      exact ⟨IntegrableOn.mono_set (t := S) (hLpS.1.integrable hp1) hKS,
        IntegrableOn.mono_set (t := S) (hLpS.2.1.integrable hp1) hKS,
        IntegrableOn.mono_set (t := S) (hLpS.2.2.integrable hp1) hKS⟩
    have hb : ball z₀ (2 * r + |h|) ⊆ ball z₀ R₀ := ball_subset_ball (by linarith)
    have := eLpNorm_diffQuot_le P hp1 isOpen_ball
      (fun φ hφ hc hs => hw φ hφ hc (hs.trans hbR)) hi v hv z₀ (2 * r) h hh0 hb
    refine this.trans (eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl))
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hut' := (tr hLpS.2.2).2
  -- absorption, in real numbers
  set NG := eLpNorm (fun z => v.re • us z + v.im • ut z) P (volume.restrict S) with hNG
  set NT := eLpNorm ut P (volume.restrict S) with hNT
  have hNGf : NG ≠ ⊤ := ((hLpS.2.1.const_smul v.re).add (hLpS.2.2.const_smul v.im)).2.ne
  have hNTf : NT ≠ ⊤ := hLpS.2.2.2.ne
  have hmain : X ≤ ENNReal.ofReal Cf * (ENNReal.ofReal K1 * NG + ENNReal.ofReal ε * X +
      ENNReal.ofReal L * (ENNReal.ofReal CM * X) * NT) := by
    refine hF.trans ?_
    gcongr
    refine hsum.trans ?_
    rw [ENNReal.ofReal_mul hL0, ENNReal.ofReal_toReal hk]
    gcongr
    exact le_add_self
  have hXr : X.toReal ≤ Cf * (K1 * NG.toReal + ε * X.toReal +
      L * (CM * X.toReal) * NT.toReal) := by
    have := (ENNReal.toReal_le_toReal hXfin (by finiteness)).2 hmain
    generalize X = Y at this hXfin ⊢
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)] at this
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCf0, ENNReal.toReal_ofReal hK10,
      ENNReal.toReal_ofReal hε0, ENNReal.toReal_ofReal hL0, ENNReal.toReal_ofReal hCM0] using this
  have hx0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  have hg0 : 0 ≤ NG.toReal := ENNReal.toReal_nonneg
  have hXbound : X.toReal ≤ 2 * (Cf * K1 * NG.toReal) := by
    have e1 : Cf * (ε * X.toReal) ≤ 1 / 4 * X.toReal := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsm1 hx0
    have e2 : Cf * (L * (CM * X.toReal) * NT.toReal) ≤ 1 / 4 * X.toReal := by
      have : Cf * (L * (CM * X.toReal) * NT.toReal) = Cf * L * CM * NT.toReal * X.toReal := by
        ring
      rw [this]; exact mul_le_mul_of_nonneg_right hsm2 hx0
    nlinarith
  -- back to the difference quotients of `uₛ`, `uₜ` on `B(z₀, r)`
  have hrB : ball z₀ r ⊆ B := ball_subset_ball (by linarith)
  have hμrB : volume.restrict (ball z₀ r) ≤ volume.restrict B := Measure.restrict_mono hrB le_rfl
  have hd0 : ∀ z ∈ ball z₀ r, fderiv ℝ β z = 0 := by
    intro z hz
    have : β =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) fun y hy => hβ1 y hy
    rw [this.fderiv_eq]; exact fderiv_const_apply _
  have e1 : eLpNorm ws P (volume.restrict (ball z₀ r)) ≤ eLpNorm ξs P (volume.restrict B) := by
    refine le_of_eq_of_le (eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_ball
      fun z hz => ?_)) (eLpNorm_mono_measure _ hμrB)
    simp [hξs_def, hbs_def, hd0 z hz, hβ1 z hz]
  have e2 : eLpNorm wt P (volume.restrict (ball z₀ r)) ≤ eLpNorm ξt P (volume.restrict B) := by
    refine le_of_eq_of_le (eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_ball
      fun z hz => ?_)) (eLpNorm_mono_measure _ hμrB)
    simp [hξt_def, hbt_def, hd0 z hz, hβ1 z hz]
  calc eLpNorm ws P (volume.restrict (ball z₀ r)) + eLpNorm wt P (volume.restrict (ball z₀ r))
      ≤ X := add_le_add e1 e2
    _ = ENNReal.ofReal X.toReal := (ENNReal.ofReal_toReal hXfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hXbound

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (U : Set ℂ) (hU : IsOpen U)
    (u us ut : ℂ → E) (hu : ContinuousOn u U)
    (hw : HasWeakPartialsOn U u us ut)
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J (u z) (ut z) = 0)
    (z₀ : ℂ) (R₀ r : ℝ) (hr : 0 < r) (h3r : 3 * r ≤ R₀) (hS : closedBall z₀ R₀ ⊆ U)
    (hLpS : MemLp u (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)) ∧
      MemLp us (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)))
    (J₀ : E →L[ℝ] E) (Cf CM L ε : ℝ) (hCf0 : 0 ≤ Cf) (hCM0 : 0 ≤ CM) (hL0 : 0 ≤ L)
    (hε0 : 0 ≤ ε)
    (hCf : ∀ U : Set ℂ, IsOpen U → ∀ ξ ξs ξt : ℂ → E, Continuous ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ U → HasWeakPartialsOn U ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict U) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm ξs (ENNReal.ofReal p) (volume.restrict U) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict U) ≤
        ENNReal.ofReal Cf * eLpNorm (fun z => ξs z + J₀ (ξt z)) (ENNReal.ofReal p)
          (volume.restrict U))
    (hCM : ∀ ξ ξs ξt : ℂ → E, Continuous ξ →
      tsupport ξ ⊆ ball z₀ (2 * r) → HasWeakPartialsOn (ball z₀ (2 * r)) ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) →
      ∀ z, ‖ξ z‖ₑ ≤ ENNReal.ofReal CM *
        (eLpNorm ξs (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r)))))
    (hJε : ∀ z ∈ closedBall z₀ R₀, ‖J (u z) - J₀‖ ≤ ε)
    (hJL : ∀ z ∈ closedBall z₀ R₀, ∀ z' ∈ closedBall z₀ R₀,
      ‖J (u z) - J (u z')‖ ≤ L * ‖u z - u z'‖)
    (hsm1 : Cf * ε ≤ 1 / 4)
    (hsm2 : Cf * L * CM *
      (eLpNorm ut (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀))).toReal ≤ 1 / 4)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ closedBall z₀ (3 * r / 2))
    (hβ1 : ∀ z ∈ ball z₀ r, β z = 1) (hβb : ∀ z, ‖β z‖ ≤ 1)
    (M : ℝ) (hM : ∀ z, ‖fderiv ℝ β z‖ ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) (h : ℝ) (hh0 : h ≠ 0) (hhr : |h| < r) :
    eLpNorm (fun z => h⁻¹ • (us (z + (h : ℂ) * v) - us z)) (ENNReal.ofReal p)
        (volume.restrict (ball z₀ r)) +
      eLpNorm (fun z => h⁻¹ • (ut (z + (h : ℂ) * v) - ut z)) (ENNReal.ofReal p)
        (volume.restrict (ball z₀ r)) ≤
    ENNReal.ofReal (2 * (Cf * (M * (1 + ‖J₀‖ + ε)) *
      (eLpNorm (fun z => v.re • us z + v.im • ut z) (ENNReal.ofReal p)
        (volume.restrict (closedBall z₀ R₀))).toReal)) :=
  JHolomorphic.diffQuot_bound_aux p hp J U hU u us ut hu hw heq z₀ R₀ r hr h3r hS hLpS J₀ Cf CM L ε hCf0 hCM0 hL0 hε0 hCf hCM hJε hJL hsm1 hsm2 β hβ hβs hβ1 hβb M hM v hv h hh0 hhr
