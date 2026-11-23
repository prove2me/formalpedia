-- Prove2me | solution 1 for GlobalTheory.PeriodicWeierstrass.exists_eq_of_sq_mul_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:00.726251+00:00
-- url     : https://prove2.me/submissions/d0e86793-7e2e-4444-85f6-eb093b140089

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsConstOfSqMulTendstoZero
import Theorems.Thm_GlobalTheory_eq_of_differentiable_of_periodic
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP
import Theorems.Thm_GlobalTheory_weierstrassP_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter PeriodPair
open scoped Topology
noncomputable section
namespace GlobalTheory
namespace PeriodicWeierstrass
variable (L : PeriodPair)
open Filter PeriodPair in
open scoped Topology in
private lemma tendsto_sq_mul_weierstrassP' (L : PeriodPair) :
    Tendsto (fun z ↦ z ^ 2 * ℘[L] z) (𝓝[≠] 0) (𝓝 1) := by
  have h0 : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
  have hA : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 :=
    L.analyticOnNhd_weierstrassPExcept 0 0 (by simp)
  have hc : Tendsto (fun z ↦ z ^ 2 * ℘[L - (0 : ℂ)] z + 1) (𝓝[≠] 0)
      (𝓝 (0 ^ 2 * ℘[L - (0:ℂ)] 0 + 1)) :=
    (((continuous_pow 2).continuousAt.mul hA.continuousAt).add continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add] at hc
  refine hc.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hz' : z ≠ 0 := hz
  have := L.weierstrassPExcept_def ⟨0, h0⟩ z
  simp only [sub_zero, div_zero, zero_pow two_ne_zero] at this
  rw [this]
  field_simp
  ring
open Filter PeriodPair in
open scoped Topology in
private lemma exists_tendsto_pow_mul_of_tendsto_pow_succ_mul_zero {h : ℂ → ℂ} (k : ℕ)
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ h z)
    (h2 : Tendsto (fun z ↦ z ^ (k + 1) * h z) (𝓝[≠] 0) (𝓝 0)) :
    ∃ r, Tendsto (fun z ↦ z ^ k * h z) (𝓝[≠] 0) (𝓝 r) := by
  set u := Function.update (fun z ↦ z ^ (k + 1) * h z) 0 0 with hu
  have hcont : ContinuousAt u 0 := by
    rw [hu, continuousAt_update_same]; exact h2
  have hdu : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ u z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hz hz0
    refine (((differentiableAt_id.pow (k + 1)).mul hz)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
    simp [hu, Function.update_of_ne (show w ≠ 0 from hw)]
  have hA : AnalyticAt ℂ u 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdu hcont
  refine ⟨deriv u 0, ?_⟩
  refine hA.differentiableAt.hasDerivAt.tendsto_slope_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  simp [hu, Function.update_of_ne ht, pow_succ]
  field_simp
open Filter PeriodPair in
open scoped Topology in
private lemma exists_const_of_periodic_of_mul_tendsto_zero (L : PeriodPair) {F : ℂ → ℂ}
    (hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ F z) (hp : ∀ z, ∀ l ∈ L.lattice, F (z + l) = F z)
    (h : Tendsto (fun z ↦ z * F z) (𝓝[≠] 0) (𝓝 0)) : ∃ k, ∀ z ∉ L.lattice, F z = k := by
  classical
  have hd0 : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z :=
    (_root_.GlobalTheory.eventually_ne_notMem_periodLattice L 0).mono fun z hz => hd z hz
  have h' : Tendsto (fun z => z * (F z - F 0)) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun z : ℂ => z * F 0) (𝓝[≠] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    simpa [mul_sub] using h.sub h0
  have ho : (fun z => F z - F 0) =o[𝓝[≠] 0] fun z => (z - 0)⁻¹ := by
    refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr (h'.congr' ?_)
    · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0) hz'
      simp [hz] at hz'
    · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      field_simp [hz]
      ring
  have hK := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd0 ho
  set K := limUnder (𝓝[≠] (0:ℂ)) F
  set G : ℂ → ℂ := fun z => if z ∈ L.lattice then K else F z with hGdef
  have hGl : ∀ l ∈ L.lattice, Tendsto G (𝓝[≠] l) (𝓝 K) := by
    intro l hl
    have hsh : Tendsto (fun w => w - l) (𝓝[≠] l) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_id.sub continuous_const).tendsto' l 0 (sub_self l)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ l)
        exact sub_ne_zero.mpr hw
    refine (hK.comp hsh).congr' ?_
    filter_upwards [_root_.GlobalTheory.eventually_ne_notMem_periodLattice L l] with w hw
    simp only [Function.comp_apply, hGdef, if_neg hw]
    rw [← hp (w - l) l hl, sub_add_cancel]
  have hdiff : Differentiable ℂ G := by
    intro z
    by_cases hz : z ∈ L.lattice
    · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_)
        |>.differentiableAt
      · filter_upwards [_root_.GlobalTheory.eventually_ne_notMem_periodLattice L z] with w hw
        refine (hd w hw).congr_of_eventuallyEq ?_
        filter_upwards [_root_.GlobalTheory.eventually_notMem_periodLattice L hw] with v hv
        simp [hGdef, hv]
      · rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
        simpa [hGdef, hz] using hGl z hz
    · refine (hd z hz).congr_of_eventuallyEq ?_
      filter_upwards [_root_.GlobalTheory.eventually_notMem_periodLattice L hz] with v hv
      simp [hGdef, hv]
  have hGp : ∀ z l, l ∈ L.lattice → G (z + l) = G z := by
    intro z l hl
    by_cases hz : z ∈ L.lattice
    · simp [hGdef, hz, add_mem hz hl]
    · have : z + l ∉ L.lattice := fun h' => hz (by simpa using sub_mem h' hl)
      simp [hGdef, hz, this, hp z l hl]
  refine ⟨K, fun z hz => ?_⟩
  have := _root_.GlobalTheory.eq_of_differentiable_of_periodic L hdiff hGp z 0
  simpa [hGdef, hz, L.lattice.zero_mem] using this
open Filter PeriodPair in
open scoped Topology in
private lemma tendsto_sq_mul_weierstrassP_sub_one_div (L : PeriodPair) :
    Tendsto (fun z ↦ (z ^ 2 * ℘[L] z - 1) / z) (𝓝[≠] 0) (𝓝 0) := by
  have h0 : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
  have hA : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 :=
    L.analyticOnNhd_weierstrassPExcept 0 0 (by simp)
  have hc : Tendsto (fun z ↦ z * ℘[L - (0 : ℂ)] z) (𝓝[≠] 0) (𝓝 (0 * ℘[L - (0:ℂ)] 0)) :=
    (continuousAt_id.mul hA.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  rw [zero_mul] at hc
  refine hc.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hz' : z ≠ 0 := hz
  have := L.weierstrassPExcept_def ⟨0, h0⟩ z
  simp only [sub_zero, div_zero, zero_pow two_ne_zero] at this
  rw [this]
  field_simp
  ring
open Filter PeriodPair in
open scoped Topology in
private lemma half_sub_half_notMem_lattice (L : PeriodPair) :
    L.ω₁ / 2 - L.ω₂ / 2 ∉ L.lattice := by
  rw [mem_lattice]
  rintro ⟨m, n, h⟩
  have := LinearIndependent.pair_iff.mp L.indep (2 * m - 1) (2 * n + 1)
    (by rw [Complex.real_smul, Complex.real_smul]; push_cast; linear_combination 2 * h)
  have h' : ((2 * m - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith [this.1]
  rw [Int.cast_eq_zero] at h'
  omega
open Filter PeriodPair in
open scoped Topology in
private lemma half_add_half_notMem_lattice (L : PeriodPair) :
    L.ω₁ / 2 + L.ω₂ / 2 ∉ L.lattice := by
  rw [mem_lattice]
  rintro ⟨m, n, h⟩
  have := LinearIndependent.pair_iff.mp L.indep (2 * m - 1) (2 * n - 1)
    (by rw [Complex.real_smul, Complex.real_smul]; push_cast; linear_combination 2 * h)
  have h' : ((2 * m - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith [this.1]
  rw [Int.cast_eq_zero] at h'
  omega
end PeriodicWeierstrass
end GlobalTheory
end
end

set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory
open GlobalTheory.PeriodicWeierstrass
variable (L : PeriodPair)
open Filter PeriodPair
open scoped Topology
namespace GlobalTheory.PeriodicWeierstrass
namespace _root_.GlobalTheory.PeriodicWeierstrass
theorem _root_.solution (L : PeriodPair) {g : ℂ → ℂ} {a : ℂ}
    (hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z) (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z)
    (h : Tendsto (fun z ↦ z ^ 2 * g z) (𝓝[≠] 0) (𝓝 a)) :
    ∃ k, ∀ z ∉ L.lattice, g z = a * ℘[L] z + k := by
  set f₀ : ℂ → ℂ := fun z => g z - a * ℘[L] z with hf₀
  have hnegmem : ∀ z, -z ∈ L.lattice ↔ z ∈ L.lattice := fun z => neg_mem_iff
  have hd₀ : ∀ z ∉ L.lattice, DifferentiableAt ℂ f₀ z := fun z hz =>
    (hd z hz).sub ((_root_.GlobalTheory.hasDerivAt_weierstrassP L hz).differentiableAt.const_mul a)
  have hp₀ : ∀ z, ∀ l ∈ L.lattice, f₀ (z + l) = f₀ z := fun z l hl => by
    simp only [hf₀, hp z l hl, L.weierstrassP_add_coe z ⟨l, hl⟩]
  have h2 : Tendsto (fun z => z ^ (1 + 1) * f₀ z) (𝓝[≠] 0) (𝓝 0) := by
    have := h.sub ((tendsto_sq_mul_weierstrassP' L).const_mul a)
    simp only [mul_one, sub_self] at this
    refine this.congr' (Eventually.of_forall fun z => ?_)
    simp only [hf₀]
    ring
  obtain ⟨r, hr⟩ := exists_tendsto_pow_mul_of_tendsto_pow_succ_mul_zero 1
    ((_root_.GlobalTheory.eventually_ne_notMem_periodLattice L 0).mono fun z hz => hd₀ z hz) h2
  simp only [pow_one] at hr
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      exact neg_ne_zero.mpr hz
  obtain ⟨k₁, hk₁⟩ := exists_const_of_periodic_of_mul_tendsto_zero L
    (F := fun z => f₀ z + f₀ (-z))
    (fun z hz => (hd₀ z hz).add
      ((hd₀ (-z) (by rwa [hnegmem])).comp z differentiableAt_id.neg))
    (fun z l hl => by
      rw [hp₀ z l hl, show -(z + l) = -z + (-l) by ring, hp₀ (-z) (-l) (neg_mem hl)])
    (by
      have := hr.sub (hr.comp hneg)
      rw [sub_self] at this
      refine this.congr' (Eventually.of_forall fun z => ?_)
      simp only [Function.comp]
      ring)
  set f : ℂ → ℂ := fun z => f₀ z - k₁ / 2 with hf
  have hodd : ∀ z ∉ L.lattice, f (-z) = - f z := fun z hz => by
    have := hk₁ z hz
    simp only [hf]
    linear_combination this
  have hdf : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z := fun z hz => (hd₀ z hz).sub_const _
  have hpf : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z := fun z l hl => by
    simp only [hf, hp₀ z l hl]
  have hrf : Tendsto (fun z => z * f z) (𝓝[≠] 0) (𝓝 r) := by
    have h0 : Tendsto (fun z : ℂ => z * (k₁ / 2)) (𝓝[≠] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    have := hr.sub h0
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun z => ?_)
    simp only [hf]
    ring
  have hq : Tendsto (fun z => (z * f z - r) / z) (𝓝[≠] 0) (𝓝 0) := by
    set Q := Function.update (fun z => z * f z) 0 r with hQ
    have hQc : ContinuousAt Q 0 := by
      rw [hQ, continuousAt_update_same]; exact hrf
    have hQd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ Q z := by
      filter_upwards [_root_.GlobalTheory.eventually_ne_notMem_periodLattice L 0, self_mem_nhdsWithin] with z hz hz0
      refine (differentiableAt_id.mul (hdf z hz)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
      simp [hQ, Function.update_of_ne (show w ≠ 0 from hw)]
    have hQa := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hQd hQc
    have heven : Q =ᶠ[𝓝 0] fun z => Q (-z) := by
      have hev : ∀ᶠ z in 𝓝 (0:ℂ), z ≠ 0 → z ∉ L.lattice :=
        eventually_nhdsWithin_iff.mp (_root_.GlobalTheory.eventually_ne_notMem_periodLattice L 0)
      filter_upwards [hev] with z hz
      by_cases hz0 : z = 0
      · simp [hz0]
      · simp only [hQ, Function.update_of_ne hz0, Function.update_of_ne (neg_ne_zero.mpr hz0)]
        rw [hodd z (hz hz0)]
        ring
    have hQ0 : HasDerivAt Q (deriv Q 0) (-0) := by
      rw [neg_zero]; exact hQa.differentiableAt.hasDerivAt
    have hd1 : HasDerivAt Q (deriv Q 0 * -1) 0 :=
      (hQ0.comp 0 (hasDerivAt_neg 0)).congr_of_eventuallyEq heven
    have hd2 : deriv Q 0 = 0 := by
      have := hd1.deriv
      linear_combination this / 2
    have := hQa.differentiableAt.hasDerivAt.tendsto_slope_zero
    rw [hd2] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp [hQ, Function.update_of_ne ht, div_eq_inv_mul]
  obtain ⟨k₂, hk₂⟩ := exists_const_of_periodic_of_mul_tendsto_zero L
    (F := fun z => f z ^ 2 - r ^ 2 * ℘[L] z)
    (fun z hz => ((hdf z hz).pow 2).sub
      ((_root_.GlobalTheory.hasDerivAt_weierstrassP L hz).differentiableAt.const_mul _))
    (fun z l hl => by simp only [hpf z l hl, L.weierstrassP_add_coe z ⟨l, hl⟩])
    (by
      have := (hq.mul (hrf.add (tendsto_const_nhds (x := r)))).sub
        ((tendsto_sq_mul_weierstrassP_sub_one_div L).const_mul (r ^ 2))
      simp only [zero_mul, mul_zero, sub_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      field_simp
      ring)
  have hhalf : ∀ ω ∈ L.lattice, ω / 2 ∉ L.lattice → f (ω / 2) = 0 := fun ω hω hω2 => by
    have h1 := hodd (ω / 2) hω2
    have h2 := hpf (-(ω / 2)) ω hω
    rw [show -(ω / 2) + ω = ω / 2 by ring] at h2
    rw [← h2] at h1
    linear_combination h1 / 2
  have e1 := hk₂ _ (ω₁_div_two_notMem_lattice L)
  have e2 := hk₂ _ (ω₂_div_two_notMem_lattice L)
  rw [hhalf _ L.ω₁_mem_lattice (ω₁_div_two_notMem_lattice L)] at e1
  rw [hhalf _ L.ω₂_mem_lattice (ω₂_div_two_notMem_lattice L)] at e2
  have hne : ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L (ω₁_div_two_notMem_lattice L) (ω₂_div_two_notMem_lattice L)]
    rintro (h' | h')
    · exact half_sub_half_notMem_lattice L h'
    · exact half_add_half_notMem_lattice L h'
  have hr0 : r ^ 2 = 0 := by
    have : r ^ 2 * (℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2)) = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have r0 : r = 0 := by simpa using hr0
  rw [r0] at hr
  obtain ⟨k, hk⟩ := exists_const_of_periodic_of_mul_tendsto_zero L hd₀ hp₀ hr
  refine ⟨k, fun z hz => ?_⟩
  have := hk z hz
  simp only [hf₀] at this
  linear_combination this
end _root_.GlobalTheory.PeriodicWeierstrass
end GlobalTheory.PeriodicWeierstrass
