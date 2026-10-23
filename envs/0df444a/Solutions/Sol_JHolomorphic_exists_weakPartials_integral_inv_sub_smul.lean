-- Prove2me | solution 1 for JHolomorphic.exists_weakPartials_integral_inv_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T09:29:13.584262+00:00
-- url     : https://prove2.me/submissions/f8e31961-0796-4bde-97dd-0aaebcd18595

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Theorems.Thm_JHolomorphic_norm_integral_inv_sub_smul_le
import Theorems.Thm_JHolomorphic_contDiff_integral_inv_sub_smul
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_integral_inv_sub_smul_le
import Theorems.Thm_JHolomorphic_tendsto_eLpNorm_normed_convolution_sub
import Theorems.Thm_JHolomorphic_eLpNorm_normed_convolution_le
import Theorems.Thm_JHolomorphic_exists_memLp_weakDeriv_of_enorm_integral_le
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Theorems.Thm_JHolomorphic_ae_eq_of_forall_integral_smul_eq
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution

/-- Hölder's inequality for `∫ φ • f` with conjugate exponents `p / (p - 1)` and `p`. -/
theorem enorm_integral_smul_le_eLpNorm_mul_eLpNorm_aux {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} (p : ℝ) (hp : 1 < p) {φ : α → ℝ}
    {f : α → E} (hφ : AEStronglyMeasurable φ μ) (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, φ x • f x ∂μ‖ₑ ≤
      eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm f (ENNReal.ofReal p) μ := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  haveI : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one, add_comm]; exact hpq.inv_add_inv_ennreal⟩
  calc ‖∫ x, φ x • f x ∂μ‖ₑ ≤ ∫⁻ x, ‖φ x • f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (φ • f) 1 μ := by rw [eLpNorm_one_eq_lintegral_enorm]; rfl
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm hf hφ

set_option maxHeartbeats 2000000 in
/-- The Cauchy transform of compactly supported `L^p` data, `p > 2`. -/
theorem exists_weakPartials_integral_inv_sub_smul_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (p R : ℝ) (hp : 2 < p) (hR : 0 < R)
    (g : ℂ → E) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hsupp : Function.support g ⊆ ball 0 R) :
    ContinuousOn (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) (ball 0 R) ∧
      ∃ ws wt : ℂ → E, HasWeakPartialsOn (ball 0 R) (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) ws wt ∧
        MemLp ws (ENNReal.ofReal p) (volume.restrict (ball 0 R)) ∧
        MemLp wt (ENNReal.ofReal p) (volume.restrict (ball 0 R)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 R)), ws z + Complex.I • wt z = (2 * Real.pi : ℂ) • g z := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hp1 : 1 < p := by linarith
  have hP1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp1
  haveI : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one, add_comm]; exact hpq.inv_add_inv_ennreal⟩
  obtain ⟨T, hTdef⟩ : ∃ T : (ℂ → E) → ℂ → E, T = fun f z => ∫ ζ, (z - ζ)⁻¹ • f ζ := ⟨_, rfl⟩
  have hTapp : ∀ f z, T f z = ∫ ζ, (z - ζ)⁻¹ • f ζ := fun f z => by rw [hTdef]
  have hTg : (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) = T g := by rw [hTdef]
  rw [hTg]
  -- mollifiers
  let ρ : ℕ → ContDiffBump (0 : ℂ) := fun k =>
    ⟨R / (2 * ((k : ℝ) + 1)), R / ((k : ℝ) + 1), by positivity, by
      apply div_lt_div_of_pos_left hR (by positivity); linarith⟩
  have hρ0 : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0) := by
    show Tendsto (fun k : ℕ => R / ((k : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hρR : ∀ k, (ρ k).rOut ≤ R := fun k => by
    show R / ((k : ℝ) + 1) ≤ R
    exact div_le_self hR.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ → ℂ → E,
      h = fun k => (ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := ⟨_, rfl⟩
  have hgli : LocallyIntegrable g volume := hg.locallyIntegrable hP1
  have hgc : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun x hx => by
      by_contra hne
      exact hx (ball_subset_closedBall (hsupp hne)))
  have hhs : ∀ k, ContDiff ℝ ∞ (h k) := fun k => by
    rw [hhdef]
    exact (ρ k).hasCompactSupport_normed.contDiff_convolution_left _ (ρ k).contDiff_normed hgli
  have hhc : ∀ k, HasCompactSupport (h k) := fun k => by
    rw [hhdef]
    exact (ρ k).hasCompactSupport_normed.convolution _ hgc
  have hhsupp : ∀ k, Function.support (h k) ⊆ ball 0 (2 * R) := by
    intro k x hx
    rw [hhdef] at hx
    have hx' : x ∈ Function.support
        ((ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ) hx'
    have ha' := mem_ball_zero_iff.1 (hsupp ha)
    rw [(ρ k).support_normed_eq] at hb
    have hb' := mem_ball_zero_iff.1 hb
    rw [mem_ball_zero_iff]
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ < R + (ρ k).rOut := add_lt_add ha' hb'
      _ ≤ 2 * R := by linarith [hρR k]
  have hhm : ∀ k, MemLp (h k) (ENNReal.ofReal p) volume := fun k =>
    (hhs k).continuous.memLp_of_hasCompactSupport (hhc k)
  have hconv : Tendsto (fun k => eLpNorm (h k - g) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    rw [hhdef]
    exact tendsto_eLpNorm_normed_convolution_sub hP1 hPtop ρ hρ0 hg
  have hle : ∀ k, eLpNorm (h k) (ENNReal.ofReal p) volume ≤ eLpNorm g (ENNReal.ofReal p) volume :=
    fun k => by rw [hhdef]; exact eLpNorm_normed_convolution_le (ρ k) hP1 hPtop hg.1
  -- constants
  obtain ⟨C1, hC1, hC1b⟩ := norm_integral_inv_sub_smul_le (E := E) p (2 * R) hp (by positivity)
  obtain ⟨M, hM, hMb⟩ := eLpNorm_fderiv_integral_inv_sub_smul_le (E := E) p R hp hR
  have hT : ∀ k, ContDiff ℝ ∞ (T (h k)) ∧ ∀ z, fderiv ℝ (T (h k)) z 1 +
      Complex.I • fderiv ℝ (T (h k)) z Complex.I = (2 * Real.pi : ℂ) • h k z := fun k => by
    rw [hTdef]; exact contDiff_integral_inv_sub_smul (h k) (hhs k) (hhc k)
  -- uniform approximation on the disc
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ,
      ε = fun k => C1 * (eLpNorm (h k - g) (ENNReal.ofReal p) volume).toReal := ⟨_, rfl⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul C1
    rw [hεdef]; simpa using this
  have hgsupp2 : Function.support g ⊆ ball 0 (2 * R) := hsupp.trans (ball_subset_ball (by linarith))
  have hunif : ∀ k, ∀ z ∈ ball (0 : ℂ) R, ‖T (h k) z - T g z‖ ≤ ε k := by
    intro k z hz
    have hz2 : z ∈ ball (0 : ℂ) (2 * R) := ball_subset_ball (by linarith) hz
    have hds : Function.support (h k - g) ⊆ ball 0 (2 * R) :=
      (Function.support_sub _ _).trans (union_subset (hhsupp k) hgsupp2)
    obtain ⟨hi1, -⟩ := hC1b (h k) (hhm k) (hhsupp k) z hz2
    obtain ⟨hi2, -⟩ := hC1b g hg hgsupp2 z hz2
    obtain ⟨-, hb⟩ := hC1b (h k - g) ((hhm k).sub hg) hds z hz2
    have : T (h k) z - T g z = ∫ ζ, (z - ζ)⁻¹ • (h k - g) ζ := by
      rw [hTapp, hTapp, ← integral_sub hi1 hi2]
      simp only [Pi.sub_apply, smul_sub]
    rw [this, hεdef]
    exact hb
  have hTgc : ContinuousOn (T g) (ball 0 R) := by
    refine TendstoUniformlyOn.continuousOn (F := fun k => T (h k)) (p := atTop) ?_
      (Frequently.of_forall fun k => (hT k).1.continuous.continuousOn)
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [(tendsto_order.1 hε).2 δ hδ] with k hk z hz
    rw [dist_eq_norm, norm_sub_rev]
    exact (hunif k z hz).trans_lt hk
  have hTgK : ∀ K ⊆ ball (0 : ℂ) R, IsCompact K → IntegrableOn (T g) K :=
    fun K hK hKc => (hTgc.mono hK).integrableOn_compact hKc
  -- convergence of the pairings
  have hL2 : ∀ ψ : ℂ → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball 0 R →
      Tendsto (fun k => ∫ z, ψ z • T (h k) z) atTop (𝓝 (∫ z, ψ z • T g z)) := by
    intro ψ hψ hψc hψs
    have hi : ∀ k, Integrable (fun z => ψ z • T (h k) z) := fun k =>
      (hψ.smul (hT k).1.continuous).integrable_of_hasCompactSupport hψc.smul_right
    have hig : Integrable (fun z => ψ z • T g z) :=
      integrable_smul_of_integrableOn_compact hTgK hψ.continuousOn hψc hψs
    have hψi : Integrable (fun z => ‖ψ z‖) := hψ.norm.integrable_of_hasCompactSupport hψc.norm
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (by simpa using hε.mul_const (∫ z, ‖ψ z‖))
    rw [← integral_sub (hi k) hig]
    calc ‖∫ z, (ψ z • T (h k) z - ψ z • T g z)‖ ≤ ∫ z, ε k * ‖ψ z‖ := by
          refine norm_integral_le_of_norm_le (hψi.const_mul _) (Eventually.of_forall fun z => ?_)
          rw [← smul_sub, norm_smul]
          by_cases hz : z ∈ ball (0 : ℂ) R
          · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hunif k z hz) (norm_nonneg _)
          · rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hψs hm))]; simp
      _ = ε k * ∫ z, ‖ψ z‖ := integral_const_mul _ _
  have hL3 : ∀ ψ : ℂ → ℝ, Continuous ψ → HasCompactSupport ψ →
      Tendsto (fun k => ∫ z, ψ z • h k z) atTop (𝓝 (∫ z, ψ z • g z)) := by
    intro ψ hψ hψc
    have hψq : MemLp ψ (ENNReal.ofReal (p / (p - 1))) volume := hψ.memLp_of_hasCompactSupport hψc
    have hi : ∀ k, Integrable (fun z => ψ z • h k z) := fun k =>
      (hψ.smul (hhs k).continuous).integrable_of_hasCompactSupport hψc.smul_right
    have hm : MemLp (ψ • g) 1 volume := MemLp.smul hg hψq
    have hig : Integrable (fun z => ψ z • g z) := memLp_one_iff_integrable.1 hm
    have hqfin : eLpNorm ψ (ENNReal.ofReal (p / (p - 1))) volume ≠ ⊤ := hψq.eLpNorm_ne_top
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (by simpa using (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv).const_mul
        (eLpNorm ψ (ENNReal.ofReal (p / (p - 1))) volume).toReal))
    rw [← integral_sub (hi k) hig]
    have hb := enorm_integral_smul_le_eLpNorm_mul_eLpNorm_aux (μ := volume) p hp1
      hψ.aestronglyMeasurable ((hhm k).1.sub hg.1)
    have heq : (fun z => ψ z • h k z - ψ z • g z) = fun z => ψ z • (h k - g) z := by
      funext z; simp [smul_sub]
    rw [heq, ← toReal_enorm, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hqfin ((hhm k).sub hg).eLpNorm_ne_top) hb
  -- integration by parts for the smooth approximants
  have hWk : ∀ k, HasWeakPartialsOn (ball 0 R) (T (h k)) (fun z => fderiv ℝ (T (h k)) z 1)
      (fun z => fderiv ℝ (T (h k)) z Complex.I) := fun k =>
    HasWeakPartialsOn.of_contDiffOn isOpen_ball
      (((hT k).1.of_le (by exact_mod_cast le_top)).contDiffOn)
  have hibp : ∀ k, ∀ v : ℂ, (v = 1 ∨ v = Complex.I) → ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      ∫ z, fderiv ℝ φ z v • T (h k) z = -∫ z, φ z • fderiv ℝ (T (h k)) z v := by
    intro k v hv φ hφ hφc hφs
    rcases hv with rfl | rfl
    · exact ((hWk k) φ hφ hφc hφs).1
    · exact ((hWk k) φ hφ hφc hφs).2
  have hDcont : ∀ k v, Continuous (fun z => fderiv ℝ (T (h k)) z v) := fun k v =>
    (((hT k).1.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (T (h k))).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  -- duality bounds
  have hdual : ∀ v : ℂ, (v = 1 ∨ v = Complex.I) → ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      ‖∫ z, fderiv ℝ φ z v • T g z‖ₑ ≤
        ENNReal.ofReal (M * (eLpNorm g (ENNReal.ofReal p) volume).toReal) *
          eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict (ball 0 R)) := by
    intro v hv φ hφ hφc hφs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hψ : Continuous (fun z => fderiv ℝ φ z v) :=
      (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hψc : HasCompactSupport (fun z => fderiv ℝ φ z v) := hφc.fderiv_apply ℝ v
    have hψs : tsupport (fun z => fderiv ℝ φ z v) ⊆ ball 0 R :=
      (tsupport_fderiv_apply_subset ℝ v).trans hφs
    have hlim := hL2 _ hψ hψc hψs
    refine le_of_tendsto' ((continuous_enorm.tendsto _).comp hlim) (fun k => ?_)
    show ‖∫ z, fderiv ℝ φ z v • T (h k) z‖ₑ ≤ _
    rw [hibp k v hv φ hφ hφc hφs, enorm_neg]
    have hφ0 : ∀ z, z ∉ ball (0 : ℂ) R → φ z • fderiv ℝ (T (h k)) z v = 0 := fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hφs hm)), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφ0]
    have hDv : eLpNorm (fun z => fderiv ℝ (T (h k)) z v) (ENNReal.ofReal p)
        (volume.restrict (ball 0 R)) ≤ ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal p) volume := by
      have hsum := (hMb (h k) (hhs k) (hhc k) (hhsupp k)).trans
        (mul_le_mul_of_nonneg_left (hle k) zero_le)
      have hTk : (fun z => ∫ ζ, (z - ζ)⁻¹ • h k ζ) = T (h k) := by rw [hTdef]
      rw [hTk] at hsum
      rcases hv with rfl | rfl
      · exact le_self_add.trans hsum
      · exact le_add_self.trans hsum
    calc _ ≤ eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict (ball 0 R)) *
          eLpNorm (fun z => fderiv ℝ (T (h k)) z v) (ENNReal.ofReal p)
            (volume.restrict (ball 0 R)) :=
          enorm_integral_smul_le_eLpNorm_mul_eLpNorm_aux p hp1
            hφ.continuous.aestronglyMeasurable (hDcont k v).aestronglyMeasurable
      _ ≤ eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict (ball 0 R)) *
          (ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal p) volume) := by gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_toReal hg.eLpNorm_ne_top]; ring
  obtain ⟨ws, hwsm, hws⟩ := exists_memLp_weakDeriv_of_enorm_integral_le p hp1 isOpen_ball hTgK 1
    (M * (eLpNorm g (ENNReal.ofReal p) volume).toReal) (hdual 1 (Or.inl rfl))
  obtain ⟨wt, hwtm, hwt⟩ := exists_memLp_weakDeriv_of_enorm_integral_le p hp1 isOpen_ball hTgK
    Complex.I (M * (eLpNorm g (ENNReal.ofReal p) volume).toReal) (hdual Complex.I (Or.inr rfl))
  refine ⟨hTgc, ws, wt, fun φ hφ hφc hφs => ⟨hws φ hφ hφc hφs, hwt φ hφ hφc hφs⟩, hwsm, hwtm, ?_⟩
  -- the equation
  have hKint : ∀ f : ℂ → E, MemLp f (ENNReal.ofReal p) (volume.restrict (ball 0 R)) →
      ∀ K ⊆ ball (0 : ℂ) R, IsCompact K → IntegrableOn f K := by
    intro f hf K hK hKc
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact (hf.mono_measure (Measure.restrict_mono hK le_rfl)).integrable hP1
  have hgK : MemLp g (ENNReal.ofReal p) (volume.restrict (ball 0 R)) := hg.restrict _
  refine ae_eq_of_forall_integral_smul_eq isOpen_ball
    (fun K hK hKc => (hKint ws hwsm K hK hKc).add ((hKint wt hwtm K hK hKc).smul Complex.I))
    (fun K hK hKc => (hKint g hgK K hK hKc).smul (2 * Real.pi : ℂ)) (fun φ hφ hφc hφs => ?_)
  have hiws : Integrable (fun z => φ z • ws z) :=
    integrable_smul_of_integrableOn_compact (hKint ws hwsm) hφ.continuous.continuousOn hφc hφs
  have hiwt : Integrable (fun z => φ z • wt z) :=
    integrable_smul_of_integrableOn_compact (hKint wt hwtm) hφ.continuous.continuousOn hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hψ : ∀ v, Continuous (fun z => fderiv ℝ φ z v) := fun v =>
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψs : ∀ v, tsupport (fun z => fderiv ℝ φ z v) ⊆ ball 0 R := fun v =>
    (tsupport_fderiv_apply_subset ℝ v).trans hφs
  have hLHS : ∫ z, φ z • (ws z + Complex.I • wt z) =
      -(∫ z, fderiv ℝ φ z 1 • T g z) + Complex.I • -(∫ z, fderiv ℝ φ z Complex.I • T g z) := by
    have h1 : (fun z => φ z • (ws z + Complex.I • wt z)) =
        fun z => φ z • ws z + Complex.I • (φ z • wt z) := by
      funext z; rw [smul_add, smul_comm (φ z) Complex.I]
    have hiwt' : Integrable (fun z => Complex.I • (φ z • wt z)) := hiwt.smul Complex.I
    rw [h1, integral_add hiws hiwt', integral_smul, hws φ hφ hφc hφs, hwt φ hφ hφc hφs, neg_neg,
      neg_neg]
  have hRHS : ∫ z, φ z • ((2 * Real.pi : ℂ) • g z) = (2 * Real.pi : ℂ) • ∫ z, φ z • g z := by
    simp_rw [smul_comm (φ _) (2 * Real.pi : ℂ)]
    exact integral_smul _ _
  rw [hLHS, hRHS]
  -- both sides are limits of the same sequence
  have hA := ((hL2 _ (hψ 1) (hφc.fderiv_apply ℝ 1) (hψs 1)).neg).add
    (((hL2 _ (hψ Complex.I) (hφc.fderiv_apply ℝ Complex.I) (hψs Complex.I)).neg).const_smul
      Complex.I)
  have hB := (hL3 φ hφ.continuous hφc).const_smul (2 * Real.pi : ℂ)
  refine tendsto_nhds_unique hA (hB.congr' (Eventually.of_forall fun k => ?_))
  show (2 * Real.pi : ℂ) • ∫ z, φ z • h k z =
    -(∫ z, fderiv ℝ φ z 1 • T (h k) z) + Complex.I • -(∫ z, fderiv ℝ φ z Complex.I • T (h k) z)
  rw [hibp k 1 (Or.inl rfl) φ hφ hφc hφs, hibp k Complex.I (Or.inr rfl) φ hφ hφc hφs, neg_neg,
    neg_neg]
  have hi1 : Integrable (fun z => φ z • fderiv ℝ (T (h k)) z 1) :=
    (hφ.continuous.smul (hDcont k 1)).integrable_of_hasCompactSupport hφc.smul_right
  have hiI : Integrable (fun z => φ z • fderiv ℝ (T (h k)) z Complex.I) :=
    (hφ.continuous.smul (hDcont k Complex.I)).integrable_of_hasCompactSupport hφc.smul_right
  have hiI' : Integrable (fun z => Complex.I • (φ z • fderiv ℝ (T (h k)) z Complex.I)) :=
    hiI.smul Complex.I
  rw [← integral_smul Complex.I (fun z => φ z • fderiv ℝ (T (h k)) z Complex.I),
    ← integral_add hi1 hiI', ← integral_smul (2 * Real.pi : ℂ) (fun z => φ z • h k z)]
  congr 1
  funext z
  rw [smul_comm Complex.I (φ z), ← smul_add, (hT k).2 z, smul_comm]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (p R : ℝ) (hp : 2 < p) (hR : 0 < R)
    (g : ℂ → E) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hsupp : Function.support g ⊆ ball 0 R) :
    ContinuousOn (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) (ball 0 R) ∧
      ∃ ws wt : ℂ → E, HasWeakPartialsOn (ball 0 R) (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) ws wt ∧
        MemLp ws (ENNReal.ofReal p) (volume.restrict (ball 0 R)) ∧
        MemLp wt (ENNReal.ofReal p) (volume.restrict (ball 0 R)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 R)), ws z + Complex.I • wt z = (2 * Real.pi : ℂ) • g z :=
  exists_weakPartials_integral_inv_sub_smul_aux p R hp hR g hg hsupp
