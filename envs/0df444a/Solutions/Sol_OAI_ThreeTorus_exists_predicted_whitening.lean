-- Prove2me | solution 1 for OAI.ThreeTorus.exists_predicted_whitening
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:15:28.431048+00:00
-- url     : https://prove2.me/submissions/19efa3f6-fc75-42d6-89d0-2eb8ca733a9a

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_actual_controlled_density_prediction

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma packet_twistIter (φ : UnitAddCircle → UnitAddCircle) (n m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A (twistIter φ n x) = fourier n (m • φ x.2.1) * packet m A x := by
  change A x.2 * fourier m (x.1+n • φ x.2.1) =
    fourier n (m • φ x.2.1)*(A x.2*fourier m x.1)
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_smul]
  rw [mul_comm n m]
  ring

lemma continuous_packet {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) : Continuous (packet m A) :=
  (hA.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma integral_fourier_pair (m k : ℤ) :
    (∫ θ : UnitAddCircle, starRingEnd ℂ (fourier m θ)*fourier k θ
      ∂AddCircle.haarAddCircle) = if m = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) m k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [RCLike.inner_apply,mul_comm] using hh

/-- Exact packet orthogonality, before stationary phase or any passage limit. -/
lemma integral_packet_pair {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    ((Complex.continuous_conj.comp (continuous_packet hA)).mul
      (continuous_packet hB)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma normSq_complex (z : ℂ) : starRingEnd ℂ z*z = (‖z‖^2 : ℝ) := by
  simp only [Complex.conj_mul',Complex.ofReal_pow]

/-- Exact correlation formula for a packet under every positive or negative power. -/
lemma packet_correlation {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : Continuous B := ((fourier n).continuous.comp
    ((hφ.comp continuous_fst).const_smul m)).mul hA
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

lemma packet_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : Continuous A) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.measurable.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hA.norm.pow 2).measurable.ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Pi.pow_apply,Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

end ThreeTorus

namespace ThreeTorus

lemma measurePreserving_circleCycle :
    MeasurePreserving circleCycle tripleVolume tripleVolume := by
  exact (measurePreserving_prodAssoc AddCircle.haarAddCircle AddCircle.haarAddCircle
    AddCircle.haarAddCircle).comp Measure.measurePreserving_swap

lemma measurePreserving_fiberTranslate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {g : Ω → UnitAddCircle} (hg : Measurable g) :
    MeasurePreserving (fun p : Ω × UnitAddCircle => (p.1,p.2+g p.1))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) := by
  exact (MeasurePreserving.id μ).skew_product (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => (measurePreserving_add_right AddCircle.haarAddCircle (g x)).map_eq))

lemma measurePreserving_circleThetaShear {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (circleThetaShear H) tripleVolume tripleVolume := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_fiberTranslate (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (hH.comp measurable_fst)).comp Measure.measurePreserving_swap)

lemma measurePreserving_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H) tripleVolume tripleVolume :=
  measurePreserving_circleCycle.comp (measurePreserving_circleThetaShear hH.neg)

lemma passageChart_inverse_measurable {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    Measurable (passageChart H).symm := by
  change Measurable (fun x : TripleTorus => (x.2.2-(-H x.1),x.1,x.2.1))
  exact (measurable_snd.snd.sub (hH.comp measurable_fst).neg).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma stationaryWeight_reflect {I : Set ℝ} {J : ℝ → ℝ}
    (hinj : InjOn J I) (A : ℝ → ℂ) (s : ℝ) :
    stationaryWeight I (fun x => -J x) (fun x => conj (A x)) s =
      stationaryWeight I J A (-s) := by
  classical
  have hi : InjOn (fun x => -J x) I := fun x hx y hy he => hinj hx hy (neg_injective he)
  by_cases hs : -s ∈ J '' I
  · obtain ⟨x,hx,hxs⟩ := hs
    have hneg : -J x = s := by linarith
    have hm : s ∈ (fun x => -J x) '' I := ⟨x,hx,hneg⟩
    have h₁ : invFunOn (fun x => -J x) I s = x := by
      rw [← hneg]; exact hi.leftInvOn_invFunOn hx
    have h₂ : invFunOn J I (-s) = x := by
      rw [← hxs]; exact hinj.leftInvOn_invFunOn hx
    simp only [stationaryWeight,branchDensity,indicator_of_mem hm,
      indicator_of_mem (show -s ∈ J '' I from ⟨x,hx,hxs⟩),h₁,h₂,
      Complex.norm_conj]
    change ‖A x‖^2/|deriv (-J) x| = ‖A x‖^2/|deriv J x|
    rw [deriv.neg,abs_neg]
  · have hm : s ∉ (fun x => -J x) '' I := by
      rintro ⟨x,hx,he⟩
      exact hs ⟨x,hx,by linarith⟩
    simp only [stationaryWeight,branchDensity,indicator_of_notMem hm,indicator_of_notMem hs]

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma integral_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f : TripleTorus → ℝ) :
    (∫ x, f (passageChart H x) ∂tripleVolume) = ∫ x, f x ∂tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact (measurePreserving_passageChart hH).integral_comp e.measurableEmbedding f

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

-- The same elementary identity used in the supplied whitening proof.
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {ζ : X → Y} {w : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hw : Measurable w) :
    (μ.withDensity (w ∘ ζ)).map ζ = (μ.map ζ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hζ hs, withDensity_apply _ (hζ hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hζ hs), ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hζ]
  apply lintegral_congr
  intro x
  rfl

/-- If a coefficient's modulus is independent of its spare coordinate, its
literal packet spectral measure is the single-coordinate weighted image. -/
lemma packetSpectralMeasure_of_modulus
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) {j : ℤ}
    {B : UnitAddCircle × UnitAddCircle → ℂ} {q : UnitAddCircle → ℝ}
    (hq : Measurable q) (hB : ∀ p, ‖B p‖^2 = q p.1) :
    packetSpectralMeasure φ j B =
      (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => j • φ a) := by
  unfold packetSpectralMeasure
  have he : (fun p : UnitAddCircle × UnitAddCircle => ENNReal.ofReal (‖B p‖^2)) =
      (fun a => ENNReal.ofReal (q a)) ∘ Prod.fst := funext (fun p => congrArg _ (hB p))
  rw [he]
  change Measure.map ((fun a => j • φ a) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun a => j • φ a) from hφ.const_smul j) measurable_fst,
    map_withDensity_comp slowVolume measurable_fst hq.ennreal_ofReal]
  simp only [slowVolume,Measure.map_fst_prod,measure_univ,one_smul]

lemma packet_twisted_pair_zero {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ) {m k : ℤ}
    (hdisj : m = k → Disjoint (support A) (support B)) (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B (twistIter φ n x)
      ∂tripleVolume) = 0 := by
  let B' : UnitAddCircle × UnitAddCircle → ℂ := fun p => fourier n (k • φ p.1)*B p
  have hb' : Continuous B' :=
    ((fourier n).continuous.comp ((hφ.comp continuous_fst).const_smul k)).mul hB
  have he (x : TripleTorus) : packet k B (twistIter φ n x) = packet k B' x := by
    rw [packet_twistIter]
    dsimp [packet,B']
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hb']
  split_ifs with hmk
  · apply integral_eq_zero_of_ae
    filter_upwards [] with p
    by_cases ha : A p = 0
    · simp [ha]
    · have hb : B p = 0 := by
        by_contra hh
        exact Set.disjoint_left.mp (hdisj hmk) ha hh
      simp [B',hb]
  · rfl

/-- The spectral measure of a smooth disjoint packet list is the sum of the
literal packet pushforwards, demonstrated by every bilateral Fourier moment. -/
lemma disjoint_packet_list_correlation {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hA : ∀ i, Continuous (A i)) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (hd : ∀ i j, i ≠ j → m i = m j → Disjoint (support (A i)) (support (A j)))
    (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (∑ i, packet (m i) (A i) x)*
        (∑ i, packet (m i) (A i) (twistIter φ n x)) ∂tripleVolume) =
      ∑ i, ∫ z, fourier n z ∂packetSpectralMeasure φ (m i) (A i) := by
  classical
  have ht : Continuous (twistIter φ n) :=
    (continuous_fst.add ((hφ.comp (continuous_fst.comp continuous_snd)).const_smul n)).prodMk
      continuous_snd
  have hc (i j : ι) : Continuous (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) :=
    (Complex.continuous_conj.comp (continuous_packet (hA i))).mul
      ((continuous_packet (hA j)).comp ht)
  have hi (i j : ι) : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) tripleVolume :=
    (hc i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j),Finset.sum_eq_single i]
  · exact (packet_spectral_moment hφ (hA i) (m i) n).symm
  · intro j _ hji
    exact packet_twisted_pair_zero (hA i) (hA j) hφ (hd i j hji.symm) n
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end ThreeTorus
end
end
end
end
end
end

section

/-! Exact spectral identity for the literal retained packet vector. This closes
 the interface between the previously proved coefficient-density estimates and
 the actual Koopman correlations, without an abstract density hypothesis. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma moment_withDensity_real {p : UnitAddCircle → ℝ} (hp : Measurable p)
    (hp0 : ∀ z, 0 ≤ p z) (v : UnitAddCircle → ℂ) :
    (∫ z, v z ∂AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z))) =
      ∫ z, (p z:ℂ)*v z ∂AddCircle.haarAddCircle := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (by filter_upwards [] with z; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (hp0 z),Complex.real_smul]

end ThreeTorus
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

end ThreeTorus
end
end

section

/-! Identification of the reference stationary marginal with the actual old
packet spectrum. In particular integer carrier speeds do not change it. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma positive_circle_branch_fold
    {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x:UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (J a:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀) z)) := by
  let w := branchDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hIm := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  have hwi : Integrable w := integrable_branchDensity hIo.measurableSet hIm hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi.integrableOn
  have hwm : Measurable w := measurable_branchDensity_smooth hJ hIo hinj hd hqm
  have hmap := circle_branch_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet hIm hD hinj (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
  apply positive_density_map_of_vectorMeasure (AddCircle.measurable_mk'.comp hj) hq
    (integrable_foldCircleDensity hwm hwi) hq0
    (foldCircleDensity_nonneg (branchDensity_nonneg hq00))
  rw [← foldCircleDensity_pushforward hwm hwi,← hmap]
  exact (vectorMeasure_map_comp _ hj AddCircle.measurable_mk').symm

lemma stationaryWeight_change_branch {A : ℝ → ℂ} {J : ℝ → ℝ} {C I : Set ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : support A ⊆ I) :
    stationaryWeight C J A = stationaryWeight I J A := by
  have h := stationaryWeight_family_of_branch (Ω := Unit) hIC hi (fun _ => hs)
  funext s
  have hh := congrFun h (s,())
  exact hh

/-- The density of a literal old angular packet, not an abstract probability
model. The integer speed carrier vanishes on the temporal circle. -/
theorem oldPacket_spectralDensity_of_modulus
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ℝ → ℂ}
    {v : UnitAddCircle → ℝ} {V : ℝ → ℝ} {m c : ℤ} {o : ℝ} {C I : Set ℝ}
    (hA : Continuous A) (hA₀ : Continuous A₀)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAe : ∀ x ∈ Ioc o (o+1), A ((x:UnitAddCircle),0) = A₀ x)
    (has : support A₀ ⊆ Ioc o (o+1)) (hAs : support A₀ ⊆ I)
    (hv : Measurable v) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVe : ∀ x ∈ I, v (x:UnitAddCircle) = V x)
    (hIo : IsOpen I) (hIC : I ⊆ C) (hinj : InjOn (fun x => (m:ℝ)*V x) C)
    (hd : ∀ x ∈ I, deriv (fun x => (m:ℝ)*V x) x ≠ 0) :
    packetSpectralMeasure (fun a => ((v a-c:ℝ):UnitAddCircle)) m A =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (stationaryWeight C (fun x => (m:ℝ)*V x) A₀) z)) := by
  have hqc : Continuous (fun u : UnitAddCircle => ‖A (u,0)‖^2) :=
    ((hA.comp (continuous_id.prodMk continuous_const)).norm.pow 2)
  have hps := packetSpectralMeasure_of_modulus
    (φ := fun a => (((v a-(c:ℝ)) : ℝ):UnitAddCircle)) (j := m) (B := A)
    (q := fun u => ‖A (u,0)‖^2)
    (AddCircle.measurable_mk'.comp (hv.sub measurable_const)) hqc.measurable
    (fun p => by rw [hmod])
  rw [hps]
  have hmode (a : UnitAddCircle) : m • ((v a-c:ℝ):UnitAddCircle) = ((m:ℝ)*v a:UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    rw [mul_sub]
    have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
      rw [← Int.cast_mul]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
    rw [AddCircle.coe_sub,he,sub_zero]
  simp_rw [hmode]
  rw [stationaryWeight_change_branch hIC hinj hAs]
  apply positive_circle_branch_fold (q₀ := fun x => ‖A₀ x‖^2)
    (hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hA₀.norm.pow 2).measurable) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun x hx => by rw [hAe x hx])
    (by intro x hx; apply has; intro hz; apply hx; simp [hz])
    (by intro x hx; apply hAs; intro hz; apply hx; simp [hz])
    (hv.const_mul (m:ℝ)) (contDiff_const.mul hV) (fun x hx => by rw [hVe x hx])
    hIo (hinj.mono hIC) hd

end ThreeTorus
end
end

section

/-! Quantitative physical and spectral conclusions for the same actual packet.
This is the analytic (not yet geometric finite-stage) transmission boundary. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

lemma continuous_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Continuous H) :
    Continuous (passageChart H) := by
  change Continuous (fun x : TripleTorus => (x.2.1,x.2.2,x.1+(-H x.2.1)))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (continuous_fst.add (hH.comp continuous_snd.fst).neg))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma core_subset (i : ι) : F.core i ⊆ Icc F.l F.u :=
  closure_minimal ((F.support_lift i 0).trans Ioc_subset_Icc_self) isClosed_Icc

lemma core_compact (i : ι) : IsCompact (F.core i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F.core_subset i)

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma weight_nonneg (i : ι) (s : ℝ) : 0 ≤ F.weight i s :=
  branchDensity_nonneg (fun _ => sq_nonneg _) s

lemma density_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.density i z :=
  foldCircleDensity_nonneg (F.weight_nonneg i) z

lemma smooth_zero_lift (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.A₀ i 0) := by
  simpa only [Function.comp_def, AddCircle.coe_zero] using
    (F.smooth_lift i).comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (x,(0:ℝ))) from contDiff_id.prodMk contDiff_const)

lemma weight_regular (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.weight i) ∧ HasCompactSupport (F.weight i) := by
  let q := fun x => ‖F.A₀ i 0 x‖^2
  have hqs : tsupport q ⊆ F.core i := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [q,hz])
  have hqc : HasCompactSupport q := (F.core_compact i).of_isClosed_subset isClosed_closure hqs
  have hs : tsupport q ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.core_subset i (hqs hx)
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have has : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have he := stationaryWeight_change_branch Ioo_subset_Icc_self hb.1 has
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (stationaryWeight _ _ _) ∧ HasCompactSupport (stationaryWeight _ _ _)
  rw [he]
  exact ⟨branchDensity_smooth (contDiff_const.mul F.smooth_speed) isOpen_Ioo
    (hb.1.mono Ioo_subset_Icc_self) hb.2 ((F.smooth_zero_lift i).norm_sq (𝕜 := ℂ)) hqc hs,
    branchDensity_compact (continuous_const.mul F.smooth_speed.continuous) hqc⟩

lemma density_smooth (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => F.density i (x:UnitAddCircle)) :=
  foldCircleDensity_smooth_lift (F.weight_regular i).1 (F.weight_regular i).2

lemma density_continuous (i : ι) : Continuous (F.density i) :=
  continuous_of_continuous_lift (F.density_smooth i).continuous

lemma speed_continuous : Continuous F.periodic.lift := by
  apply Continuous.quotient_lift
  exact F.smooth_speed.continuous

/-- The canonical density is the spectral measure of the actual angular packet. -/
theorem density_spectral (hmod : F.SpareIndependent) (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.density i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity_of_modulus (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.smooth_zero_lift i).continuous (hmod.2 i)
    (F.lift_matches i 0) ((F.support_lift i 0).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1, hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl)
    isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  simpa only [Int.cast_zero,sub_zero,density,weight] using he

end PassagePackets
end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

variable {F}

lemma Reflection.involutive {τ : ι → ι} (h : F.Reflection τ) (hi : Injective F.m) :
    Involutive τ := fun i => hi (by rw [h.index,h.index,neg_neg])

lemma Reflection.weight {τ : ι → ι} (h : F.Reflection τ) (i : ι) (s : ℝ) :
    F.weight (τ i) s = F.weight i (-s) := by
  have hinj := (scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv).1
  have ha : F.A₀ (τ i) 0 = fun x => conj (F.A₀ i 0 x) := funext (h.lift i 0)
  simp only [PassagePackets.weight,h.index,ha,Int.cast_neg,neg_mul]
  exact stationaryWeight_reflect hinj _ s

end PassagePackets

lemma foldCircleDensity_reflect (q : ℝ → ℝ) (z : UnitAddCircle) :
    foldCircleDensity (fun s => q (-s)) z = foldCircleDensity q (-z) := by
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  rw [← AddCircle.coe_neg,foldCircleDensity_coe_all,foldCircleDensity_coe_all]
  calc
    (∑' k : ℤ, q (-(x+k))) = ∑' k : ℤ, q (-x+(-k:ℤ)) := by
      apply tsum_congr
      intro k
      congr 1
      simp only [Int.cast_neg]
      ring
    _ = ∑' k : ℤ, q (-x+k) := (Equiv.neg ℤ).tsum_eq (fun k => q (-x+k))

lemma PassagePackets.Reflection.density {ι : Type*} {F : PassagePackets ι}
    {τ : ι → ι} (h : F.Reflection τ) (i : ι) (z : UnitAddCircle) :
    F.density (τ i) z = F.density i (-z) := by
  unfold PassagePackets.density
  rw [show F.weight (τ i) = (fun s => F.weight i (-s)) from funext (h.weight i)]
  exact foldCircleDensity_reflect _ z

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

/-! Finite summation and composition estimates in the original physical L².
These let the literal per-packet passages be assembled without replacing their
vectors by independent spectral models. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalError_integrable {f g : TripleTorus → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => ‖f x-g x‖^2) tripleVolume :=
  ((hf.sub hg).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma physicalError_nonneg (f g : TripleTorus → ℂ) : 0 ≤ physicalError f g :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma physicalError_chart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f g : TripleTorus → ℂ) :
    physicalError (f ∘ passageChart H) (g ∘ passageChart H) = physicalError f g :=
  integral_passageChart hH (fun x => ‖f x-g x‖^2)

lemma physicalError_triangle {f g h : TripleTorus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    physicalError f h ≤ 2*physicalError f g+2*physicalError g h := by
  have hp x : ‖f x-h x‖^2 ≤ 2*‖f x-g x‖^2+2*‖g x-h x‖^2 := by
    have hn : ‖f x-h x‖^2 ≤ (‖f x-g x‖+‖g x-h x‖)^2 := by
      gcongr
      simpa only [dist_eq_norm] using dist_triangle (f x) (g x) (h x)
    nlinarith [sq_nonneg (‖f x-g x‖-‖g x-h x‖)]
  unfold physicalError
  calc
    _ ≤ ∫ x, 2*‖f x-g x‖^2+2*‖g x-h x‖^2 ∂tripleVolume :=
      integral_mono (physicalError_integrable hf hh)
        (((physicalError_integrable hf hg).const_mul 2).add ((physicalError_integrable hg hh).const_mul 2)) hp
    _ = _ := by
      rw [integral_add ((physicalError_integrable hf hg).const_mul 2)
        ((physicalError_integrable hg hh).const_mul 2),integral_const_mul,integral_const_mul]

lemma physicalError_sum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) :
    physicalError (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤
      (Fintype.card ι:ℝ)*(∑ i, physicalError (f i) (g i)) := by
  have he x : (∑ i, f i x)-(∑ i, g i x) = ∑ i, (f i x-g i x) :=
    (Finset.sum_sub_distrib _ _).symm
  have hp x : ‖(∑ i, f i x)-(∑ i, g i x)‖^2 ≤
      (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) := by
    rw [he]
    calc
      _ ≤ (∑ i, ‖f i x-g i x‖)^2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ _ := by simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i x-g i x‖))
  unfold physicalError
  calc
    _ ≤ ∫ x, (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) ∂tripleVolume :=
      integral_mono
        (physicalError_integrable (continuous_finsetSum _ (fun i _ => hf i))
          (continuous_finsetSum _ (fun i _ => hg i)))
        ((integrable_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))).const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))]

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PredictionModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block tests, diagonal predictions, centering, and stability of finite-color models. -/

section

/-! Quantitative passage from the fixed pre-block model to actual color
 densities, source 04:239--286 and 409--437. No geometric approximation oracle
 is introduced: these are deterministic L1 stability estimates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma continuous_circle_integrable {f : UnitAddCircle → ℝ} (hf : Continuous f) :
    Integrable f phaseHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_TrackedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Literal color sums in the concrete packet state. Colors are labels, not
new independent spectral data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

variable {ι R : Type*} [Fintype ι] [DecidableEq R]

lemma continuous_colorVector (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorVector F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact continuous_packet (F.continuous_amplitude i) | exact continuous_const

lemma continuous_colorDensity (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorDensity F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact F.density_continuous i | exact continuous_const

lemma colorDensity_nonneg (F : PassagePackets ι) (c : ι → R) (r : R) (z : UnitAddCircle) :
    0 ≤ colorDensity F c r z := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> first | exact F.density_nonneg i z | exact le_refl _

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

attribute [instance] ColoredState.finite

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)
lemma density_continuous (r : R) : Continuous (C.density r) :=
  continuous_colorDensity C.packets C.color r
lemma vector_continuous (r : R) : Continuous (C.vector r) :=
  continuous_colorVector C.packets C.color r
lemma density_nonneg (r : R) (z : UnitAddCircle) : 0 ≤ C.density r z :=
  colorDensity_nonneg C.packets C.color r z

end ColoredState

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)
lemma chart_continuous : Continuous s.chart :=
  (continuous_passageChart (s.transmit.Hcontinuous N)).comp
    (continuous_passageChart (s.refresh.Hcontinuous s.n))
lemma chart_preserves : MeasurePreserving s.chart tripleVolume tripleVolume :=
  (measurePreserving_passageChart (s.transmit.Hcontinuous N).measurable).comp
    (measurePreserving_passageChart (s.refresh.Hcontinuous s.n).measurable)

end ColoredPair

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ColorBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block transfer, cofinal frequency trees, color-density products, finite iteration, and actual anchored blocks. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma ColoredPair.physicalError_chart {R : Type} {C : ColoredState R} {N : ℕ}
    (s : ColoredPair C N) (f g : TripleTorus → ℂ) :
    physicalError (f ∘ s.chart) (g ∘ s.chart) = physicalError f g := by
  change physicalError ((f ∘ passageChart (s.transmit.H N)) ∘ passageChart (s.refresh.H s.n))
    ((g ∘ passageChart (s.transmit.H N)) ∘ passageChart (s.refresh.H s.n)) = _
  rw [ThreeTorus.physicalError_chart (s.refresh.Hcontinuous s.n).measurable,
    ThreeTorus.physicalError_chart (s.transmit.Hcontinuous N).measurable]

namespace ColoredPath
variable {R : Type} {C D : ColoredState R} {k : ℕ} {L : Fin k → ℤ}
    {α : Equiv.Perm TripleTorus} (h : ColoredPath C L D α)
include h
lemma continuous : Continuous α := by
  induction h with
  | nil => exact continuous_id
  | snoc h s ih => exact s.chart_continuous.comp ih
lemma preserves : MeasurePreserving α tripleVolume tripleVolume := by
  induction h with
  | nil => exact MeasurePreserving.id tripleVolume
  | snoc h s ih => exact s.chart_preserves.comp ih
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ α) (g ∘ α) = physicalError f g := by
  induction h generalizing f g with
  | nil => rfl
  | @snoc k L D α h N s ih =>
    change physicalError ((f ∘ s.chart) ∘ α) ((g ∘ s.chart) ∘ α) = _
    rw [ih,s.physicalError_chart]
end ColoredPath

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)
lemma chart_continuous : Continuous s.chart := continuous_passageChart (s.geometry.Hcontinuous n)
lemma chart_preserves : MeasurePreserving s.chart tripleVolume tripleVolume :=
  measurePreserving_passageChart (s.geometry.Hcontinuous n).measurable
end ColoredAnchor

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketAlgebra
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet algebra and physical L2 metric estimates. -/

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalDist_nonneg (f g : TripleTorus → ℂ) : 0 ≤ physicalDist f g := Real.sqrt_nonneg _
lemma physicalDist_sq (f g : TripleTorus → ℂ) : physicalDist f g^2=physicalError f g :=
  Real.sq_sqrt (physicalError_nonneg f g)
lemma physicalDist_lt_iff (f g : TripleTorus → ℂ) {ε : ℝ} (hε : 0 < ε) :
    physicalDist f g < ε ↔ physicalError f g < ε^2 := Real.sqrt_lt' hε
lemma physicalDist_symm (f g : TripleTorus → ℂ) : physicalDist f g=physicalDist g f := by
  simp only [physicalDist,physicalError,norm_sub_rev]
lemma norm_toLp_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 ν) : ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂ν := by
  calc
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂ν := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
lemma physicalError_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalError f g=‖hf.toLp f-hg.toLp g‖^2 := by
  rw [← hf.toLp_sub hg,norm_toLp_sq]
  rfl
lemma physicalDist_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalDist f g=‖hf.toLp f-hg.toLp g‖ := by
  rw [physicalDist,physicalError_eq_norm hf hg,Real.sqrt_sq (norm_nonneg _)]
lemma physicalDist_triangle {f g h : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) (hh : MemLp h 2 tripleVolume) :
    physicalDist f h ≤ physicalDist f g+physicalDist g h := by
  rw [physicalDist_eq_norm hf hh,physicalDist_eq_norm hf hg,physicalDist_eq_norm hg hh]
  simpa only [dist_eq_norm] using dist_triangle (hf.toLp f) (hg.toLp g) (hh.toLp h)
lemma physicalDist_finsum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, MemLp (f i) 2 tripleVolume) (hg : ∀ i, MemLp (g i) 2 tripleVolume) :
    physicalDist (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤ ∑ i, physicalDist (f i) (g i) := by
  classical
  have hsum (a : ι → TripleTorus → ℂ) (ha : ∀ i, MemLp (a i) 2 tripleVolume) :
      (memLp_finsetSum Finset.univ (fun i _ => ha i)).toLp (fun x => ∑ i, a i x) =
        ∑ i, (ha i).toLp (a i) := by
    apply Lp.ext
    filter_upwards [(memLp_finsetSum Finset.univ (fun i _ => ha i)).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => (ha i).toLp (a i)),
      ae_all_iff.mpr (fun i => (ha i).coeFn_toLp)] with x hx hy hz
    rw [hx,hy]
    exact Finset.sum_congr rfl (fun i _ => (hz i).symm)
  rw [physicalDist_eq_norm (memLp_finsetSum Finset.univ (fun i _ => hf i))
    (memLp_finsetSum Finset.univ (fun i _ => hg i)),hsum f hf,hsum g hg,← Finset.sum_sub_distrib]
  simp_rw [physicalDist_eq_norm (hf _) (hg _)]
  exact norm_sum_le Finset.univ (fun i => (hf i).toLp (f i)-(hg i).toLp (g i))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SymmetricPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)

lemma Reflection.density {τR : R → R} (hr : C.Reflection τR)
    (hτR : Involutive τR) (r : R) (z : UnitAddCircle) :
    C.density (τR r) z = C.density r (-z) := by
  classical
  obtain ⟨τ,hτ,hcolor⟩ := hr
  let e := (hτ.involutive C.injective).toPerm
  change (∑ i, if C.color i = τR r then C.packets.density i z else 0) =
    ∑ i, if C.color i = r then C.packets.density i (-z) else 0
  rw [← Equiv.sum_comp e (fun i => if C.color i = τR r then C.packets.density i z else 0)]
  apply Finset.sum_congr rfl
  intro i _
  change (if C.color (τ i) = τR r then C.packets.density (τ i) z else 0) = _
  rw [hcolor,hτ.density]
  simp only [hτR.injective.eq_iff]

end ColoredState

end ThreeTorus
end
end

section

/-! Finite physical C-infinity restrictions, on both the map and inverse,
threaded through the actual refresh and transmission integer choices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PhysicalJetData

lemma Close.mono {Q : PhysicalJetData} {ε η : ℝ} {F G : PhysicalFrame} {V W : ℝ → ℝ}
    (h : Q.Close ε F V G W) (he : ε ≤ η) : Q.Close η F V G W :=
  fun i x hx => (h i x hx).trans he

end PhysicalJetData

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Whitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coefficient-space spectral whitening, including the zero-density set. -/

section

/-!
Exact coefficient-space whitening, including the zero
set of the spectral density. The frequency map is arbitrary; for torus packets
it is `(m,u,a) ↦ m φ(u) mod 1`. No nonvanishing of the density is imposed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical
namespace ThreeTorus

lemma measurable_energyWeight {X : Type*} [MeasurableSpace X] {F : X → ℂ}
    (hF : Measurable F) : Measurable (energyWeight F) :=
  (hF.norm.pow_const 2).ennreal_ofReal

lemma energyWeight_mul {X : Type*} (a F : X → ℂ) :
    energyWeight (fun x => a x * F x) = energyWeight F * energyWeight a := by
  funext x
  simp only [energyWeight, norm_mul, mul_pow, Pi.mul_apply,
    ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- Spectral multipliers act by multiplying the pushforward energy density. -/
lemma energy_map_multiplier {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p)
    (hpush : (μ.withDensity (energyWeight F)).map ζ = ν.withDensity p)
    {a : Y → ℂ} (ha : Measurable a) :
    (μ.withDensity (energyWeight (fun x => a (ζ x) * F x))).map ζ =
      ν.withDensity (p * energyWeight a) := by
  rw [energyWeight_mul]
  change (μ.withDensity (energyWeight F * (energyWeight a ∘ ζ))).map ζ = _
  rw [withDensity_mul μ (measurable_energyWeight hF)
    ((measurable_energyWeight ha).comp hζ),
    map_withDensity_comp _ hζ (measurable_energyWeight ha), hpush,
    ← withDensity_mul ν hp (measurable_energyWeight ha)]

/-- A coefficient is zero almost everywhere over the zero set of its spectral density. -/
lemma energy_zero_fiber {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) :
    ∀ᵐ x ∂μ, p (ζ x) = 0 → F x = 0 := by
  have hs : MeasurableSet {y | p y = 0} := measurableSet_eq_fun hp measurable_const
  have hz : (μ.withDensity (energyWeight F)) (ζ ⁻¹' {y | p y = 0}) = 0 := by
    rw [← Measure.map_apply hζ hs, hpush, withDensity_apply _ hs]
    apply setLIntegral_eq_zero hs
    intro y hy
    change p y = 0 at hy
    simp [hy]
  rw [withDensity_apply _ (hζ hs), lintegral_eq_zero_iff
    (measurable_energyWeight hF)] at hz
  have hza := (ae_restrict_iff' (hζ hs)).1 hz
  filter_upwards [hza] with x hx hpx
  have h := hx hpx
  have hz' : ‖F x‖ ^ 2 = 0 := (ENNReal.ofReal_eq_zero.mp h).antisymm (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz')

lemma measurable_whitenCoefficient {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ζ : X → Y} {p : Y → ℝ} {F V : X → ℂ}
    (hζ : Measurable ζ) (hp : Measurable p) (hF : Measurable F) (hV : Measurable V) :
    Measurable (whitenCoefficient ζ p F V) := by
  apply Measurable.ite (measurableSet_eq_fun (hp.comp hζ) measurable_const) hV
  exact hF.div (Complex.measurable_ofReal.comp ((hp.comp hζ).sqrt))

lemma whiten_reconstruct {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) :
    (fun x => (Real.sqrt (p (ζ x)) : ℂ) * whitenCoefficient ζ p F V x) =ᵐ[μ] F := by
  filter_upwards [energy_zero_fiber hζ hF hp hpush] with x hx
  by_cases h : p (ζ x) = 0
  · simp [whitenCoefficient, h, hx h]
  · have hp₀ : 0 < p (ζ x) := lt_of_le_of_ne (hpn _) (Ne.symm h)
    have hs : (Real.sqrt (p (ζ x)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hp₀).ne'
    simp only [whitenCoefficient, ite_eq_right h]
    exact mul_div_cancel₀ _ hs

/-- A piecewise multiplier rule: the two spectral supports can overlap in
angular index; it is their frequency supports that are disjoint. -/
lemma energy_map_piecewise {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ}
    {p q : Y → ℝ≥0∞} {s : Set Y}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hq : Measurable q) (hs : MeasurableSet s)
    (hpushF : (μ.withDensity (energyWeight F)).map ζ = ν.withDensity p)
    (hpushV : (μ.withDensity (energyWeight V)).map ζ = ν.withDensity q)
    {a b : Y → ℂ} (ha : Measurable a) (hb : Measurable b) :
    (μ.withDensity (energyWeight (fun x => if ζ x ∈ s then a (ζ x) * F x
      else b (ζ x) * V x))).map ζ =
      ν.withDensity (fun y => if y ∈ s then p y * energyWeight a y
        else q y * energyWeight b y) := by
  classical
  have henergy : energyWeight (fun x => if ζ x ∈ s then a (ζ x) * F x
      else b (ζ x) * V x) =
      energyWeight (fun x => (s.indicator a) (ζ x) * F x) +
      energyWeight (fun x => (sᶜ.indicator b) (ζ x) * V x) := by
    funext x
    by_cases hx : ζ x ∈ s <;> simp [hx, energyWeight]
  have hm : Measurable (energyWeight (fun x => (s.indicator a) (ζ x) * F x)) :=
    measurable_energyWeight (((ha.indicator hs).comp hζ).mul hF)
  rw [henergy, withDensity_add_left hm,
    Measure.map_add _ _ hζ,
    energy_map_multiplier hζ hF hp hpushF (ha.indicator hs),
    energy_map_multiplier hζ hV hq hpushV (hb.indicator hs.compl),
    ← withDensity_add_left (hp.mul (measurable_energyWeight (ha.indicator hs)))]
  congr 1
  funext y
  by_cases hy : y ∈ s <;> simp [hy, energyWeight]

lemma positive_whitening_weight {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * ENNReal.ofReal (‖(Real.sqrt t : ℂ)⁻¹‖ ^ 2) = 1 := by
  have he : ‖(Real.sqrt t : ℂ)⁻¹‖ ^ 2 = t⁻¹ := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt ht.le]
  rw [he, ← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one]

/-- Exact flat output intensity, including the zero set, without requiring
angular supports of the two coefficient families to be disjoint. -/
lemma whiten_energy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    (μ.withDensity (energyWeight (whitenCoefficient ζ p F V))).map ζ = ν := by
  have hs : MeasurableSet {y | p y = 0} := measurableSet_eq_fun hp measurable_const
  have hflat' : (μ.withDensity (energyWeight V)).map ζ = ν.withDensity (fun _ => 1) := by
    simpa only [withDensity_const, one_smul] using hflat
  have hm := energy_map_piecewise hζ hV hF measurable_const hp.ennreal_ofReal hs hflat' hpush
    (measurable_const (a := (1 : ℂ))) ((Complex.measurable_ofReal.comp hp.sqrt).inv)
  have he : (fun x => if ζ x ∈ {y | p y = 0} then (1 : ℂ) * V x
      else (Real.sqrt (p (ζ x)) : ℂ)⁻¹ * F x) = whitenCoefficient ζ p F V := by
    funext x
    simp only [whitenCoefficient, mem_ofPred_eq, one_mul, div_eq_mul_inv]
    congr 1
    exact mul_comm _ _
  change (μ.withDensity (energyWeight (fun x => if ζ x ∈ {y | p y = 0}
      then (1 : ℂ) * V x else (Real.sqrt (p (ζ x)) : ℂ)⁻¹ * F x))).map ζ =
    ν.withDensity (fun y => if y ∈ {y | p y = 0}
      then (1 : ℝ≥0∞) * energyWeight (fun _ => (1 : ℂ)) y
      else ENNReal.ofReal (p y) * energyWeight (fun y => (Real.sqrt (p y) : ℂ)⁻¹) y) at hm
  rw [he] at hm
  rw [hm]
  have hd : (fun y => if y ∈ {y | p y = 0} then (1 : ℝ≥0∞) * energyWeight (fun _ => (1 : ℂ)) y
      else ENNReal.ofReal (p y) * energyWeight (fun y => (Real.sqrt (p y) : ℂ)⁻¹) y) = 1 := by
    funext y
    by_cases hy : p y = 0
    · simp [hy, energyWeight]
    · simp only [mem_ofPred_eq, ite_eq_right hy, Pi.one_apply, energyWeight]
      exact positive_whitening_weight (lt_of_le_of_ne (hpn _) (Ne.symm hy))
  rw [hd, withDensity_one]

lemma whitening_scalar_distance {t : ℝ} (ht : 0 < t) :
    t * ‖(Real.sqrt t : ℂ)⁻¹ - 1‖ ^ 2 = (Real.sqrt t - 1) ^ 2 := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp
  nlinarith [sq_nonneg (Real.sqrt t - 1)]

/-- The error's entire spectral density, not just its total mass, is exactly
`(√p - 1)²`. This entails the source's whitening-distance identity. -/
lemma whiten_error_energy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    (μ.withDensity (energyWeight (fun x => whitenCoefficient ζ p F V x - F x))).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal ((Real.sqrt (p y) - 1) ^ 2)) := by
  have hs : MeasurableSet {y | p y = 0} := measurableSet_eq_fun hp measurable_const
  have hflat' : (μ.withDensity (energyWeight V)).map ζ = ν.withDensity (fun _ => 1) := by
    simpa only [withDensity_const, one_smul] using hflat
  have hm := energy_map_piecewise hζ hV hF measurable_const hp.ennreal_ofReal hs hflat' hpush
    (measurable_const (a := (1 : ℂ)))
    (((Complex.measurable_ofReal.comp hp.sqrt).inv).sub (measurable_const (a := (1 : ℂ))))
  change (μ.withDensity (energyWeight (fun x => if ζ x ∈ {y | p y = 0}
      then (1 : ℂ) * V x else ((Real.sqrt (p (ζ x)) : ℂ)⁻¹ - 1) * F x))).map ζ =
    ν.withDensity (fun y => if y ∈ {y | p y = 0}
      then (1 : ℝ≥0∞) * energyWeight (fun _ => (1 : ℂ)) y
      else ENNReal.ofReal (p y) * energyWeight (fun y => (Real.sqrt (p y) : ℂ)⁻¹ - 1) y) at hm
  have hae : energyWeight (fun x => whitenCoefficient ζ p F V x - F x) =ᵐ[μ]
      energyWeight (fun x => if ζ x ∈ {y | p y = 0} then (1 : ℂ) * V x
        else ((Real.sqrt (p (ζ x)) : ℂ)⁻¹ - 1) * F x) := by
    filter_upwards [energy_zero_fiber hζ hF hp hpush] with x hx
    unfold energyWeight
    congr 2
    by_cases h : p (ζ x) = 0
    · simp [whitenCoefficient, h, hx h]
    · simp only [whitenCoefficient, ite_eq_right h]
      ring_nf
  rw [withDensity_congr_ae hae, hm]
  congr 1
  funext y
  by_cases hy : p y = 0
  · simp [hy, energyWeight]
  · simp only [mem_ofPred_eq, ite_eq_right hy, energyWeight]
    rw [← ENNReal.ofReal_mul (hpn y),
      whitening_scalar_distance (lt_of_le_of_ne (hpn _) (Ne.symm hy))]

lemma energy_map_total {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ≥0∞}
    (hζ : Measurable ζ)
    (hpush : (μ.withDensity (energyWeight F)).map ζ = ν.withDensity p) :
    (∫⁻ x, energyWeight F x ∂μ) = ∫⁻ y, p y ∂ν := by
  have ht := congrArg (fun η : Measure Y => η univ) hpush
  simpa only [Measure.map_apply hζ MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using ht

/-- The whitened coefficient really belongs to L² whenever the spectral reference
measure is finite; its possible singular multiplier does not obstruct this. -/
lemma whiten_memLp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
    {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    MemLp (whitenCoefficient ζ p F V) 2 μ := by
  have hw := measurable_whitenCoefficient hζ hp hF hV
  apply (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).2
  refine ⟨(hw.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  change (∫⁻ x, energyWeight (whitenCoefficient ζ p F V) x ∂μ) < ∞
  have ht := whiten_energy_map hζ hF hV hp hpn hpush hflat
  have ht' : (μ.withDensity (energyWeight (whitenCoefficient ζ p F V))).map ζ =
      ν.withDensity (fun _ => 1) := by simpa only [withDensity_const, one_smul] using ht
  rw [energy_map_total hζ ht']
  simp

lemma whiten_distance_integral {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    (∫ x, ‖whitenCoefficient ζ p F V x - F x‖ ^ 2 ∂μ) =
      ∫ y, (Real.sqrt (p y) - 1) ^ 2 ∂ν := by
  have he := integral_eq_lintegral_of_nonneg_ae
    (f := fun x => ‖whitenCoefficient ζ p F V x - F x‖ ^ 2)
    (μ := μ) (Eventually.of_forall (fun _ => sq_nonneg _))
    (((measurable_whitenCoefficient hζ hp hF hV).sub hF).norm.pow_const 2).aestronglyMeasurable
  have hp' := integral_eq_lintegral_of_nonneg_ae
    (f := fun y => (Real.sqrt (p y) - 1) ^ 2)
    (μ := ν) (Eventually.of_forall (fun _ => sq_nonneg _))
    ((hp.sqrt.sub measurable_const).pow_const 2).aestronglyMeasurable
  rw [he, hp']
  exact congrArg ENNReal.toReal (energy_map_total hζ
    (whiten_error_energy_map hζ hF hV hp hpn hpush hflat))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FlatPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat support, finite packet L2 estimates, neutral selection, density invariance, and finite spectral whitening. -/

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology ENNReal NNReal
namespace ThreeTorus

lemma integral_packet_pair_L2 {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    (memLp_packet hA m).star.integrable_mul (memLp_packet hB k)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma map_jacobian_real {s : Set ℝ} {f D : ℝ → ℝ}
    (hs : MeasurableSet s) (hD : ∀ x ∈ s, HasDerivWithinAt f (D x) s x)
    (hinj : InjOn f s) :
    Measure.map f ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |D x|)) =
      volume.restrict (f '' s) := by
  simpa only [ContinuousLinearMap.det_toSpanSingleton] using
    map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
      (fun x hx => (hD x hx).hasFDerivWithinAt) hinj

lemma flat_branch_mod_one {f D : ℝ → ℝ} {l u : ℝ}
    (hlu : l ≤ u) (hfm : Measurable f)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1) :
    Measure.map (fun x : ℝ => (f x : UnitAddCircle))
      ((volume.restrict (Icc l u)).withDensity (fun x => ENNReal.ofReal |D x|)) =
      AddCircle.haarAddCircle := by
  have hc : ContinuousOn f (Icc l u) := fun x hx => (hD x hx).continuousWithinAt
  change Measure.map ((fun y : ℝ => (y : UnitAddCircle)) ∘ f) _ = _
  rw [← Measure.map_map (show Measurable (fun y : ℝ => (y : UnitAddCircle)) from
      AddCircle.measurable_mk') hfm,
    map_jacobian_real measurableSet_Icc hD hmono.injOn,
    hc.image_Icc_of_monotoneOn hlu hmono.monotoneOn, hperiod,
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using
    (AddCircle.measurePreserving_mk 1 (f l)).map_eq

lemma measurable_circleRep (o : ℝ) : Measurable (circleRep o) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 o).measurable

lemma circleRep_coe {o x : ℝ} (hx : x ∈ Ioc o (o+1)) :
    circleRep o (x : UnitAddCircle) = x := by
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq hx)

lemma coe_circleRep (o : ℝ) (z : UnitAddCircle) :
    (circleRep o z : UnitAddCircle) = z := by
  exact AddCircle.coe_equivIoc (p := 1) (a := o) (y := z)

lemma circle_weight_lift {o : ℝ} {q : ℝ → ℝ≥0∞} (hq : Measurable q)
    (hs : Function.support q ⊆ Ioc o (o+1)) :
    (volume.withDensity q).map (fun x : ℝ => (x : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (q ∘ circleRep o) := by
  have he : (volume : Measure ℝ).withDensity q =
      (volume.restrict (Ioc o (o+1))).withDensity
        ((q ∘ circleRep o) ∘ (fun x : ℝ => (x : UnitAddCircle))) := by
    rw [← withDensity_indicator measurableSet_Ioc]
    congr 1
    funext x
    by_cases hx : x ∈ Ioc o (o+1)
    · simp [hx, circleRep_coe hx]
    · have hz : q x = 0 := by by_contra hn; exact hx (hs hn)
      simp [hx, hz]
  rw [he, map_withDensity_comp _ AddCircle.measurable_mk'
    (hq.comp (measurable_circleRep o))]
  congr 1
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using
    (AddCircle.measurePreserving_mk 1 o).map_eq

/-- The branch Jacobian realizes Haar measure for any circle map agreeing with
that lifted frequency on the chosen interval. -/
lemma flat_circle_branch {f D : ℝ → ℝ} {l u o : ℝ}
    {ζ : UnitAddCircle → UnitAddCircle}
    (hlu : l ≤ u) (hfm : Measurable f) (hDm : Measurable D)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1)
    (hi : Icc l u ⊆ Ioc o (o+1)) (hζ : Measurable ζ)
    (hζf : ∀ x ∈ Icc l u, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)) :
    (AddCircle.haarAddCircle.withDensity
      (((Icc l u).indicator (fun x => ENNReal.ofReal |D x|)) ∘ circleRep o)).map ζ =
      AddCircle.haarAddCircle := by
  let q : ℝ → ℝ≥0∞ := (Icc l u).indicator (fun x => ENNReal.ofReal |D x|)
  have hq : Measurable q := hDm.abs.ennreal_ofReal.indicator measurableSet_Icc
  have hqs : Function.support q ⊆ Ioc o (o+1) := by
    intro x hx
    apply hi
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  change (AddCircle.haarAddCircle.withDensity (q ∘ circleRep o)).map ζ = _
  rw [← circle_weight_lift hq hqs,
    Measure.map_map hζ AddCircle.measurable_mk']
  calc
    _ = (volume.withDensity q).map (fun x : ℝ => (f x : UnitAddCircle)) := by
      apply Measure.map_congr
      change ∀ᵐ (x : ℝ) ∂volume.withDensity q, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)
      rw [ae_withDensity_iff hq]
      filter_upwards [] with x hx
      exact hζf x (by
        by_contra hn
        exact hx (indicator_of_notMem hn _))
    _ = _ := by
      rw [show volume.withDensity q =
        (volume.restrict (Icc l u)).withDensity (fun x => ENNReal.ofReal |D x|) from
          withDensity_indicator measurableSet_Icc _]
      exact flat_branch_mod_one hlu hfm hD hmono hperiod

lemma measurable_flatAmplitude {D : ℝ → ℝ} (hD : Measurable D) (o l u : ℝ) :
    Measurable (flatAmplitude o l u D) :=
  Complex.measurable_ofReal.comp
    (((hD.abs.div_const 2).sqrt.indicator measurableSet_Icc).comp
      (measurable_circleRep o))

lemma flatAmplitude_energy (o l u : ℝ) (D : ℝ → ℝ) :
    (fun z => ENNReal.ofReal (‖flatAmplitude o l u D z‖^2)) =
      (ENNReal.ofReal (1/2 : ℝ)) •
        (((Icc l u).indicator (fun x => ENNReal.ofReal |D x|)) ∘ circleRep o) := by
  funext z
  by_cases hz : circleRep o z ∈ Icc l u
  · simp only [flatAmplitude, indicator_of_mem hz, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)),
      Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    ring
  · simp [flatAmplitude, hz]

lemma flatAmplitude_pushforward {f D : ℝ → ℝ} {l u o : ℝ}
    {ζ : UnitAddCircle → UnitAddCircle}
    (hlu : l ≤ u) (hfm : Measurable f) (hDm : Measurable D)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1)
    (hi : Icc l u ⊆ Ioc o (o+1)) (hζ : Measurable ζ)
    (hζf : ∀ x ∈ Icc l u, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)) :
    (AddCircle.haarAddCircle.withDensity
      (fun z => ENNReal.ofReal (‖flatAmplitude o l u D z‖^2))).map ζ =
      ENNReal.ofReal (1/2 : ℝ) • AddCircle.haarAddCircle := by
  rw [flatAmplitude_energy, withDensity_smul _
    ((hDm.abs.ennreal_ofReal.indicator measurableSet_Icc).comp (measurable_circleRep o)),
    Measure.map_smul,
    flat_circle_branch hlu hfm hDm hD hmono hperiod hi hζ hζf]

/-- Finite total pushed energy implies L² membership, even without boundedness. -/
lemma memLp_of_energy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
    {F : X → ℂ} {ζ : X → Y} (hF : Measurable F) (hζ : Measurable ζ)
    (he : (μ.withDensity (fun x => ENNReal.ofReal (‖F x‖^2))).map ζ = ν) :
    MemLp F 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).2
  refine ⟨(hF.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  have ht := congrArg (fun η : Measure Y => η univ) he
  simp only [Measure.map_apply hζ MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at ht
  rw [ht]
  exact measure_lt_top ν univ

/-- Haar is invariant under reversing the additive spectral variable. -/
lemma frequency_energy_neg {A : UnitAddCircle → ℂ} {ζ : UnitAddCircle → UnitAddCircle}
    (hζ : Measurable ζ) {c : ℝ≥0∞}
    (hpush : (AddCircle.haarAddCircle.withDensity
      (fun z => ENNReal.ofReal (‖A z‖^2))).map ζ = c • AddCircle.haarAddCircle) :
    (AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (‖A z‖^2))).map
      (fun z => -(ζ z)) = c • AddCircle.haarAddCircle := by
  change Measure.map ((fun z : UnitAddCircle => -z) ∘ ζ) _ = _
  rw [← Measure.map_map measurable_neg hζ, hpush,
    Measure.map_smul,
    Measure.map_neg_eq_self]

lemma packetSpectrum_first_coeff {A : UnitAddCircle → ℂ} (hA : Measurable A)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (m : ℤ) :
    packetSpectralMeasure φ m (fun ua => A ua.1) =
      (AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (‖A z‖^2))).map
        (fun z => m • φ z) := by
  unfold packetSpectralMeasure
  change Measure.map ((fun z => m • φ z) ∘ Prod.fst)
    (slowVolume.withDensity ((fun z => ENNReal.ofReal (‖A z‖^2)) ∘ Prod.fst)) = _
  rw [← Measure.map_map (show Measurable (fun z => m • φ z) from hφ.const_smul m)
    (show Measurable (Prod.fst : UnitAddCircle × UnitAddCircle → UnitAddCircle) from measurable_fst),
    map_withDensity_comp _ measurable_fst (hA.norm.pow_const 2).ennreal_ofReal,
    measurePreserving_fst.map_eq]

lemma flatAmplitude_support (o l u : ℝ) (D : ℝ → ℝ) :
    Function.support (flatAmplitude o l u D) ⊆
      (fun x : ℝ => (x : UnitAddCircle)) '' Icc l u := by
  intro z hz
  have hi : circleRep o z ∈ Icc l u := by
    by_contra hn
    apply hz
    simp [flatAmplitude, hn]
  exact ⟨circleRep o z, hi, coe_circleRep o z⟩

end ThreeTorus
end
end

section

/-! Finite measurable packet coefficient families, needed for whitening the
actual output of reflected prediction. The physical vectors remain literal
finite packet sums, not arbitrary Hilbert-space replacements. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_coefficientFrequency {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) : Measurable (coefficientFrequency φ m) :=
  measurable_from_prod_countable_right (fun i => (hφ.comp measurable_fst).const_smul (m i))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_sub (m : ι → ℤ) (A B : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    finitePacketVector m (fun i x => A i x-B i x) =
      fun x => finitePacketVector m A x-finitePacketVector m B x := by
  funext x
  simp only [finitePacketVector,packet,sub_mul,Finset.sum_sub_distrib]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_inner {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m B x ∂tripleVolume) =
      ∑ i, ∫ x, conj (A i x)*B i x ∂slowVolume := by
  classical
  have hi i j : Integrable (fun x => conj (packet (m i) (A i) x)*packet (m j) (B j) x) tripleVolume :=
    (memLp_packet (hA i) (m i)).star.integrable_mul (memLp_packet (hB j) (m j))
  simp only [finitePacketVector,map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi j i))]
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),integral_packet_pair_L2 (hA _) (hB _)]
  simp only [hm.eq_iff]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_energy {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume) =
      ∑ i, ∫ x, ‖A i x‖^2 ∂slowVolume := by
  have hh := finitePacket_inner hm hA hA
  simp only [normSq_complex,integral_complex_ofReal,← Complex.ofReal_sum] at hh
  exact Complex.ofReal_injective hh

lemma coefficient_integral_normsq {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x : ι × (UnitAddCircle × UnitAddCircle), ‖A x.1 x.2‖^2 ∂coefficientVolume) =
      ∑ i, ∫ x, ‖A i x‖^2 ∂slowVolume := by
  rw [integral_prod _ (integrable_coefficient_normsq hAm hA),integral_count]

end FinitePacket
end ThreeTorus
end
end

section

/-! Exact measurable spectral calculus for the literal finite packets.
This is the bridge from the energy-map whitening to the
actual physical packet family. It does not assume a spectral constructor. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma coefficient_memLp_iff {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) :
    MemLp (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) 2 coefficientVolume ↔
      ∀ i, MemLp (A i) 2 slowVolume := by
  refine ⟨fun h i => ?_, coefficient_memLp hAm⟩
  apply (memLp_two_iff_integrable_sq_norm (hAm i).aestronglyMeasurable).2
  exact Measure.ae_count_iff.mp
    ((h.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae) i

lemma finitePacketSpectralMeasure_eq_sum {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) (m : ι → ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) :
    finitePacketSpectralMeasure φ m A = ∑ i, packetSpectralMeasure φ (m i) (A i) := by
  classical
  ext s hs
  have hz := measurable_coefficientFrequency hφ m
  have hAm : Measurable (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) :=
    measurable_from_prod_countable_right hA
  have he := measurable_energyWeight hAm
  rw [finitePacketSpectralMeasure, Measure.map_apply hz hs, withDensity_apply _ (hz hs),
    ← lintegral_indicator (hz hs)]
  rw [lintegral_prod _ (he.indicator (hz hs)).aemeasurable, lintegral_count, tsum_fintype,
    Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hzi : Measurable (fun ua : UnitAddCircle × UnitAddCircle => m i • φ ua.1) :=
    (hφ.comp measurable_fst).const_smul (m i)
  rw [packetSpectralMeasure, Measure.map_apply hzi hs, withDensity_apply _ (hzi hs),
    ← lintegral_indicator (hzi hs)]
  apply lintegral_congr
  intro ua
  simp only [indicator_apply, mem_preimage, coefficientFrequency, energyWeight]

lemma coefficient_normsq_eq_physical {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x : ι × (UnitAddCircle × UnitAddCircle), ‖A x.1 x.2‖^2 ∂coefficientVolume) =
      ∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume := by
  rw [coefficient_integral_normsq hAm hA, finitePacket_energy hm hA]

end FinitePacket
end ThreeTorus
end
end

section

/-! Whitening in the literal finite angular-packet family. All operations act on
its actual coefficient functions; angular collisions with the flat filler are
allowed, provided both are indexed by the same injective angular list. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma measurable_whitenPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (hV : ∀ i, Measurable (V i)) (i : ι) :
    Measurable (whitenPackets φ m p A V i) := by
  apply Measurable.ite (measurableSet_eq_fun
    (hp.comp ((hφ.comp measurable_fst).const_smul (m i))) measurable_const) (hV i)
  exact (hA i).div (Complex.measurable_ofReal.comp
    ((hp.comp ((hφ.comp measurable_fst).const_smul (m i))).sqrt))

lemma whitenPackets_flat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (hV : ∀ i, Measurable (V i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    finitePacketSpectralMeasure φ m (whitenPackets φ m p A V) = phaseHaar := by
  exact whiten_energy_map (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hA) (measurable_from_prod_countable_right hV)
    hp hpn hpush hflat

lemma memLp_whitenPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (hV : ∀ i, Measurable (V i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    ∀ i, MemLp (whitenPackets φ m p A V i) 2 slowVolume := by
  apply (coefficient_memLp_iff (measurable_whitenPackets hφ m hp hA hV)).1
  exact whiten_memLp (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hA) (measurable_from_prod_countable_right hV)
    hp hpn hpush hflat

lemma whitenPackets_distance {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {p : UnitAddCircle → ℝ} (hp : Measurable p)
    (hpn : ∀ z, 0 ≤ p z) {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hVm : ∀ i, Measurable (V i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    (∫ x, ‖finitePacketVector m (whitenPackets φ m p A V) x - finitePacketVector m A x‖^2
      ∂tripleVolume) = ∫ z, (Real.sqrt (p z)-1)^2 ∂phaseHaar := by
  have hWm := measurable_whitenPackets hφ m hp hAm hVm
  have hW := memLp_whitenPackets hφ m hp hpn hAm hVm hpush hflat
  simp_rw [← congrFun (finitePacketVector_sub m (whitenPackets φ m p A V) A)]
  rw [← coefficient_normsq_eq_physical (A := fun i ua => whitenPackets φ m p A V i ua - A i ua) hm
    (fun i => (hWm i).sub (hAm i)) (fun i => (hW i).sub (hA i))]
  exact whiten_distance_integral (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hAm) (measurable_from_prod_countable_right hVm)
    hp hpn hpush hflat

lemma whitenPackets_reconstruct {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z))) (i : ι) :
    (fun ua => (Real.sqrt (p (m i • φ ua.1)) : ℂ) * whitenPackets φ m p A V i ua)
      =ᵐ[slowVolume] A i := by
  have he := whiten_reconstruct (V := fun x : ι × (UnitAddCircle × UnitAddCircle) => V x.1 x.2)
    (measurable_coefficientFrequency hφ m) (measurable_from_prod_countable_right hA)
    hp hpn hpush
  exact Measure.ae_count_iff.mp (Measure.ae_ae_of_ae_prod he) i

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma whitenPackets_support (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (p : UnitAddCircle → ℝ) (A V : ι → UnitAddCircle × UnitAddCircle → ℂ)
    {s : Set (UnitAddCircle × UnitAddCircle)}
    (hA : ∀ i, support (A i) ⊆ s) (hV : ∀ i, support (V i) ⊆ s) (i : ι) :
    support (whitenPackets φ m p A V i) ⊆ s := by
  intro ua hua
  by_contra hs
  have ha : A i ua = 0 := by
    by_contra ha
    exact hs (hA i ha)
  have hv : V i ua = 0 := by
    by_contra hv
    exact hs (hV i hv)
  exact hua (by simp [whitenPackets,whitenCoefficient,ha,hv])

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma whitenPackets_reflection (φ : UnitAddCircle → UnitAddCircle) {m : ι → ℤ}
    (r : ι → ι) (hm : ∀ i, m (r i) = -m i)
    {p : UnitAddCircle → ℝ} (hp : ∀ z, p (-z) = p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i ua, A (r i) ua = conj (A i ua))
    (hV : ∀ i ua, V (r i) ua = conj (V i ua)) (i : ι) (ua : UnitAddCircle × UnitAddCircle) :
    whitenPackets φ m p A V (r i) ua = conj (whitenPackets φ m p A V i ua) := by
  classical
  have he : p (m (r i) • φ ua.1) = p (m i • φ ua.1) := by rw [hm,neg_smul,hp]
  by_cases hz : p (m i • φ ua.1) = 0
  · simp [whitenPackets,whitenCoefficient,coefficientFrequency,he,hz,hV]
  · simp [whitenPackets,whitenCoefficient,coefficientFrequency,he,hz,hA]

end FinitePacket
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PacketCalculus
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trigonometric approximation, spectral calculus, density distances, and reflected clipping. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Uniform Laurent approximation of a continuous spectral multiplier. -/
lemma exists_uniform_laurent {Ψ : UnitAddCircle → ℂ} (hΨ : Continuous Ψ)
    {δ : ℝ} (hd : 0 < δ) :
    ∃ c : ℤ →₀ ℂ, ∀ z, ‖Ψ z-∑ k ∈ c.support, c k*fourier k z‖ < δ := by
  let f : C(UnitAddCircle,ℂ) := ⟨Ψ,hΨ⟩
  have hf : f ∈ (Submodule.span ℂ (range (fourier (T := (1:ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  change f ∈ closure (Submodule.span ℂ (range (fourier (T := (1:ℝ)))) : Set C(UnitAddCircle,ℂ)) at hf
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hf δ hd
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hg
  refine ⟨c,?_⟩
  intro z
  have he : g z = ∑ k ∈ c.support, c k*fourier k z := by
    rw [← hc]
    simp [Finsupp.sum]
  rw [← he]
  exact (ContinuousMap.norm_coe_le_norm (f-g) z).trans_lt (by simpa only [dist_eq_norm] using hfg)

end ThreeTorus
end
end

section

/-! Literal measurable finite-packet spectral calculus and Laurent approximation.
No abstract unitary is substituted for the actual twist. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma energy_map_integral_real {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) :
    (∫ x, ‖F x‖^2 ∂μ) = ∫ y, p y ∂ν := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => sq_nonneg _))
    ((hF.norm.pow_const 2).aestronglyMeasurable),
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hpn) hp.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (energy_map_total hζ hpush)

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finitePacket_energy_density {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z))) :
    (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume) = ∫ z, p z ∂phaseHaar := by
  rw [← coefficient_normsq_eq_physical hm hAm hA]
  exact energy_map_integral_real (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hAm) hp hpn hpush

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma measurable_multiplyPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {a : UnitAddCircle → ℂ} (ha : Measurable a)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i)) (i : ι) :
    Measurable (multiplyPackets φ m a A i) :=
  (ha.comp ((hφ.comp measurable_fst).const_smul (m i))).mul (hA i)

lemma multiplyPackets_spectrum {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    {a : UnitAddCircle → ℂ} (ha : Measurable a) :
    finitePacketSpectralMeasure φ m (multiplyPackets φ m a A) =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z*‖a z‖^2)) := by
  have he := energy_map_multiplier (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hA) hp.ennreal_ofReal hpush ha
  calc
    _ = phaseHaar.withDensity ((fun z => ENNReal.ofReal (p z)) * energyWeight a) := he
    _ = _ := by
      congr 1
      funext z
      simp only [Pi.mul_apply,energyWeight,ENNReal.ofReal_mul (hpn z)]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_congr_ae {m : ι → ℤ}
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAB : ∀ i, A i =ᵐ[slowVolume] B i) :
    finitePacketVector m A =ᵐ[tripleVolume] finitePacketVector m B := by
  have he := ae_all_iff.2 hAB
  have ht := (measurePreserving_snd (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (ν := slowVolume)).quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  exact Finset.sum_congr rfl (fun i _ => by simp only [packet,hx i])

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus

lemma packetSpectralMeasure_zero (φ : UnitAddCircle → UnitAddCircle) (m : ℤ) :
    packetSpectralMeasure φ m (fun _ => 0) = 0 := by
  simp [packetSpectralMeasure]

end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ThreeTorus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sq_sqrt_sub_sqrt_le_abs (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x-Real.sqrt y)^2 ≤ |x-y| := by
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hxp := Real.sqrt_nonneg x
  have hyp := Real.sqrt_nonneg y
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have := Real.sqrt_le_sqrt h
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have := Real.sqrt_le_sqrt h
    nlinarith

lemma memLp_sqrt_of_integrable {p : Ω → ℝ} (hp : Integrable p μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) : MemLp (fun x => Real.sqrt (p x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (Real.continuous_sqrt.comp_aestronglyMeasurable hp.aestronglyMeasurable)).mpr
  apply hp.congr
  filter_upwards [hp0] with x hx
  simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hx]

lemma density_hellinger_error [IsProbabilityMeasure μ] {p q : Ω → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x) :
    |(∫ x, Real.sqrt (p x) ∂μ) - ∫ x, Real.sqrt (q x) ∂μ| ≤
      Real.sqrt (∫ x, |p x-q x| ∂μ) := by
  have hps := memLp_sqrt_of_integrable hp hp0
  have hqs := memLp_sqrt_of_integrable hq hq0
  have hs := hps.sub hqs
  have hpi := hps.integrable (by norm_num)
  have hqi := hqs.integrable (by norm_num)
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr (by norm_num))
    (f := fun x => Real.sqrt (p x)-Real.sqrt (q x)) (g := fun _ => (1 : ℝ))
    (by convert hs using 1 <;> first | rfl | norm_num)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, norm_one, one_pow, mul_one,
    integral_const, probReal_univ, one_smul, Real.sqrt_one] at hh
  rw [← integral_sub hpi hqi]
  calc
    |∫ x, Real.sqrt (p x)-Real.sqrt (q x) ∂μ| ≤ ∫ x, ‖Real.sqrt (p x)-Real.sqrt (q x)‖ ∂μ :=
      by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => Real.sqrt (p x)-Real.sqrt (q x)) (μ := μ))
    _ ≤ Real.sqrt (∫ x, ‖Real.sqrt (p x)-Real.sqrt (q x)‖^2 ∂μ) := hh
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs) ((hp.sub hq).abs)
      filter_upwards [hp0,hq0] with x hpx hqx
      simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using sq_sqrt_sub_sqrt_le_abs (p x) (q x) hpx hqx

end ThreeTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Preparation
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real perturbation, smooth cylinder approximation, tensor preparation, real packet families, and two neutral separations. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

attribute [instance] RealPacketFamily.finite
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma physicalDist_continuous_comp (α : Equiv.Perm TripleTorus) (hc : Continuous α)
    (hm : MeasurePreserving α tripleVolume tripleVolume) (f g : TripleTorus → ℂ) :
    physicalDist (f ∘ α) (g ∘ α)=physicalDist f g := by
  unfold physicalDist physicalError
  exact congrArg Real.sqrt (hm.integral_comp (hc.measurableEmbedding α.injective) (fun x => ‖f x-g x‖^2))

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Prediction
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laurent prediction, flat packet filling, color energies, measurable packets, reflected smoothing, and prepared pairs. -/

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma memLp_multiplyPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {a : UnitAddCircle → ℂ} (ha : Continuous a)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAm : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (i : ι) :
    MemLp (multiplyPackets φ m a A i) 2 slowVolume := by
  obtain ⟨C,hC⟩ := (isCompact_range ha).isBounded.exists_norm_le
  apply (hA i).of_le_mul (measurable_multiplyPackets hφ m ha.measurable hAm i).aestronglyMeasurable
  filter_upwards [] with ua
  exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (hC _ (mem_range_self _)) (norm_nonneg _))

lemma multiplyPackets_energy_flat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar)
    {a : UnitAddCircle → ℂ} (ha : Continuous a) :
    (∫ x, ‖finitePacketVector m (multiplyPackets φ m a A) x‖^2 ∂tripleVolume) =
      ∫ z, ‖a z‖^2 ∂phaseHaar := by
  have hpush : finitePacketSpectralMeasure φ m A = phaseHaar.withDensity (fun _ => ENNReal.ofReal (1:ℝ)) := by
    simpa only [ENNReal.ofReal_one,withDensity_const,one_smul] using hflat
  have he := multiplyPackets_spectrum hφ m measurable_const (fun _ => zero_le_one) hAm hpush ha.measurable
  simp only [one_mul] at he
  exact finitePacket_energy_density hφ hm (measurable_multiplyPackets hφ m ha.measurable hAm)
    (memLp_multiplyPackets hφ m ha hAm hA) (ha.measurable.norm.pow_const 2) (fun _ => sq_nonneg _) he

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma multiplyPackets_sub (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (a b : UnitAddCircle → ℂ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    multiplyPackets φ m (fun z => a z-b z) A =
      fun i ua => multiplyPackets φ m a A i ua - multiplyPackets φ m b A i ua := by
  funext i ua
  exact sub_mul _ _ _

lemma multiplyPackets_distance_flat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar)
    {a b : UnitAddCircle → ℂ} (ha : Continuous a) (hb : Continuous b) :
    (∫ x, ‖finitePacketVector m (multiplyPackets φ m a A) x -
      finitePacketVector m (multiplyPackets φ m b A) x‖^2 ∂tripleVolume) =
      ∫ z, ‖a z-b z‖^2 ∂phaseHaar := by
  simp_rw [← congrFun (finitePacketVector_sub m (multiplyPackets φ m a A) (multiplyPackets φ m b A))]
  rw [← multiplyPackets_sub]
  exact multiplyPackets_energy_flat hφ hm hAm hA hflat (ha.sub hb)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketLaurent_eq_multiplier (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (c : ℤ →₀ ℂ) (x : TripleTorus) :
    finitePacketLaurent φ m A c x =
      finitePacketVector m (multiplyPackets φ m (fun z => ∑ k ∈ c.support, c k*fourier k z) A) x := by
  simp only [finitePacketLaurent,finitePacketVector,Finset.mul_sum,packet_twistIter]
  simp only [multiplyPackets,packet]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma exists_finitePacketLaurent_approx {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar)
    {a : UnitAddCircle → ℂ} (ha : Continuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, (∫ x, ‖finitePacketVector m (multiplyPackets φ m a A) x -
      finitePacketLaurent φ m A c x‖^2 ∂tripleVolume) < ε^2 := by
  obtain ⟨c,hc⟩ := exists_uniform_laurent ha (show 0 < ε/2 by positivity)
  refine ⟨c,?_⟩
  simp_rw [finitePacketLaurent_eq_multiplier]
  have hpoly : Continuous (fun z : UnitAddCircle => ∑ k ∈ c.support, c k*fourier k z) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous)
  rw [multiplyPackets_distance_flat hφ hm hAm hA hflat ha hpoly]
  have hi : (∫ z, ‖a z-∑ k ∈ c.support, c k*fourier k z‖^2 ∂phaseHaar) ≤ (ε/2)^2 := by
    calc
      _ ≤ ∫ _z : UnitAddCircle, (ε/2)^2 ∂phaseHaar := by
        apply integral_mono
        · exact continuous_circle_integrable
            ((ha.sub (continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous))).norm.pow 2)
        · exact integrable_const _
        · intro z
          exact pow_le_pow_left₀ (norm_nonneg _) (hc z).le 2
      _ = _ := by simp
  exact hi.trans_lt (by nlinarith [sq_pos_of_pos hε])

end FinitePacket
end ThreeTorus
end
end

section

/-! The source's reconstruction and prediction survive whitening for the same
finite packet coefficients. The output is a literal Laurent polynomial in the
actual twist, not just membership in an abstract cyclic subspace. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma multiplyPackets_whiten_reconstruct_ae {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) (m : ι → ℤ) {p : UnitAddCircle → ℝ}
    (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z))) (D : UnitAddCircle → ℂ) :
    finitePacketVector m (multiplyPackets φ m (fun z => D z*(Real.sqrt (p z):ℂ))
      (whitenPackets φ m p A V)) =ᵐ[tripleVolume]
      finitePacketVector m (multiplyPackets φ m D A) := by
  apply finitePacketVector_congr_ae
  intro i
  filter_upwards [whitenPackets_reconstruct (V := V) hφ m hp hpn hA hpush i] with ua hua
  dsimp only [multiplyPackets]
  rw [mul_assoc,hua]

lemma exists_whitened_laurent_approx {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) {m : ι → ℤ} (hm : Injective m) {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hVm : ∀ i, Measurable (V i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar)
    {D : UnitAddCircle → ℂ} (hD : Continuous D) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, (∫ x, ‖finitePacketVector m (multiplyPackets φ m D A) x -
      finitePacketLaurent φ m (whitenPackets φ m p A V) c x‖^2 ∂tripleVolume) < ε^2 := by
  have hWm := measurable_whitenPackets hφ m hp.measurable hAm hVm
  have hW := memLp_whitenPackets hφ m hp.measurable hpn hAm hVm hpush hflat
  have hWflat := whitenPackets_flat hφ m hp.measurable hpn hAm hVm hpush hflat
  have hDs : Continuous (fun z => D z*(Real.sqrt (p z):ℂ)) :=
    hD.mul (Complex.continuous_ofReal.comp hp.sqrt)
  obtain ⟨c,hc⟩ := exists_finitePacketLaurent_approx hφ hm hWm hW hWflat hDs hε
  refine ⟨c,?_⟩
  have he := multiplyPackets_whiten_reconstruct_ae (V := V) hφ m hp.measurable hpn hAm hpush D
  have hei : (∫ x, ‖finitePacketVector m (multiplyPackets φ m (fun z => D z*(Real.sqrt (p z):ℂ))
      (whitenPackets φ m p A V)) x - finitePacketLaurent φ m (whitenPackets φ m p A V) c x‖^2
      ∂tripleVolume) = (∫ x, ‖finitePacketVector m (multiplyPackets φ m D A) x -
      finitePacketLaurent φ m (whitenPackets φ m p A V) c x‖^2 ∂tripleVolume) := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  exact hei ▸ hc

lemma whitenPackets_distance_mass {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) {m : ι → ℤ} (hm : Injective m) {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hVm : ∀ i, Measurable (V i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    (∫ x, ‖finitePacketVector m (whitenPackets φ m p A V) x-finitePacketVector m A x‖^2
      ∂tripleVolume) = (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume)+1-
        2*(∫ z, Real.sqrt (p z) ∂phaseHaar) := by
  rw [whitenPackets_distance hφ hm hp.measurable hpn hAm hVm hA hpush hflat,
    finitePacket_energy_density hφ hm hAm hA hp.measurable hpn hpush]
  have hpI := continuous_circle_integrable hp
  have hsI := continuous_circle_integrable hp.sqrt
  have he : (fun z => (Real.sqrt (p z)-1)^2) = fun z => p z+1-2*Real.sqrt (p z) := by
    funext z
    nlinarith [Real.sq_sqrt (hpn z)]
  have hsum : Integrable (fun z => p z+1) phaseHaar := hpI.add (integrable_const 1)
  have htwice : Integrable (fun z => 2*Real.sqrt (p z)) phaseHaar := hsI.const_mul 2
  rw [he,integral_sub hsum htwice,
    integral_add hpI (integrable_const 1),integral_const_mul]
  simp

end FinitePacket
end ThreeTorus
end
end

section

/-! The literal flat coefficient, with its two pushforward measures
retained and with an arbitrarily large angular index. This permits adjoining
it to any given finite packet list without changing that list's vector. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators ComplexConjugate
namespace ThreeTorus

lemma exists_integer_period_subinterval_above {ψ : ℝ → ℝ} {l u : ℝ}
    (hlu : l < u) (hc : ContinuousOn ψ (Icc l u))
    (hmono : StrictMonoOn ψ (Icc l u)) (B : ℕ) :
    ∃ m : ℕ, B < m ∧ 0 < m ∧ ∃ t ∈ Icc l u, l < t ∧ (m:ℝ)*(ψ t-ψ l) = 1 := by
  have hgap : 0 < ψ u-ψ l := sub_pos.mpr (hmono (left_mem_Icc.mpr hlu.le)
    (right_mem_Icc.mpr hlu.le) hlu)
  obtain ⟨m,hm⟩ := exists_nat_gt (max (1/(ψ u-ψ l)) (B:ℝ))
  have hmB : (B:ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0:ℝ) < m := lt_of_le_of_lt (Nat.cast_nonneg B) hmB
  have hmnat : 0 < m := Nat.cast_pos.mp hmpos
  have hsmall : 1/(m:ℝ) < ψ u-ψ l := (one_div_lt hmpos hgap).2
    (lt_of_le_of_lt (le_max_left _ _) hm)
  have hrange : ψ l+1/(m:ℝ) ∈ Icc (ψ l) (ψ u) :=
    ⟨by linarith [one_div_pos.mpr hmpos], by linarith⟩
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hlu.le hc hrange
  have hlt : l < t := by
    by_contra hh
    have htl : t = l := le_antisymm (le_of_not_gt hh) ht.1
    rw [htl] at he
    linarith [one_div_pos.mpr hmpos]
  refine ⟨m,by exact_mod_cast hmB,hmnat,t,ht,hlt,?_⟩
  rw [he]
  calc
    (m:ℝ)*(ψ l+1/(m:ℝ)-ψ l) = (m:ℝ)*(1/(m:ℝ)) := by ring
    _ = 1 := mul_one_div_cancel (ne_of_gt hmpos)

lemma exists_flat_packet_spectra_above {φ : UnitAddCircle → ℝ} {D : ℝ → ℝ}
    {l u o : ℝ} (hφ : Measurable φ) (hDm : Measurable D) (hlu : l < u)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt
      (fun y : ℝ => φ (y : UnitAddCircle)) (D x) (Icc l u) x)
    (hmono : StrictMonoOn (fun y : ℝ => φ (y : UnitAddCircle)) (Icc l u))
    (hi : Icc l u ⊆ Ioc o (o+1)) (B : ℕ) :
    ∃ m : ℕ, B < m ∧ 0 < m ∧ ∃ t ∈ Icc l u, l < t ∧
      let A := fun ua : UnitAddCircle × UnitAddCircle =>
        flatAmplitude o l t (fun x => (m:ℝ)*D x) ua.1
      Measurable A ∧ MemLp A 2 slowVolume ∧ (∀ ua, conj (A ua) = A ua) ∧
      packetSpectralMeasure (fun z => (φ z : UnitAddCircle)) (m:ℤ) A =
        ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
      packetSpectralMeasure (fun z => (φ z : UnitAddCircle)) (-(m:ℤ)) A =
        ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
      support A ⊆ ((fun x : ℝ => (x : UnitAddCircle)) '' Icc l t) ×ˢ univ := by
  have hc : ContinuousOn (fun y : ℝ => φ (y : UnitAddCircle)) (Icc l u) :=
    fun x hx => (hD x hx).continuousWithinAt
  obtain ⟨m,hmB,hm,t,ht,hlt,hperiod⟩ := exists_integer_period_subinterval_above hlu hc hmono B
  have hs : Icc l t ⊆ Icc l u := Icc_subset_Icc le_rfl ht.2
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  let φc : UnitAddCircle → UnitAddCircle := fun z => (φ z : UnitAddCircle)
  have hφc : Measurable φc := AddCircle.measurable_mk'.comp hφ
  let Ac : UnitAddCircle → ℂ := flatAmplitude o l t (fun x => (m:ℝ)*D x)
  have hAc : Measurable Ac := measurable_flatAmplitude (measurable_const.mul hDm) o l t
  have hp : (AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (‖Ac z‖^2))).map
      (fun z => (m:ℤ) • φc z) = ENNReal.ofReal (1/2:ℝ) • phaseHaar := by
    apply flatAmplitude_pushforward (f := fun x : ℝ => (m:ℝ)*φ (x : UnitAddCircle)) hlt.le
      (measurable_const.mul (hφ.comp AddCircle.measurable_mk')) (measurable_const.mul hDm)
    · intro x hx
      exact ((hD x (hs hx)).mono hs).const_mul (m:ℝ)
    · intro x hx y hy hxy
      exact mul_lt_mul_of_pos_left (hmono (hs hx) (hs hy) hxy) hmpos
    · nlinarith
    · exact hs.trans hi
    · exact hφc.const_smul m
    · intro x _
      dsimp only [φc]
      rw [← AddCircle.coe_zsmul,zsmul_eq_mul]
      simp
  have hn := frequency_energy_neg (hφc.const_smul (m:ℤ)) hp
  let : IsFiniteMeasure (ENNReal.ofReal (1/2:ℝ) • phaseHaar) :=
    ⟨by simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]; finiteness⟩
  have hAcLp := memLp_of_energy_map hAc (hφc.const_smul (m:ℤ)) hp
  refine ⟨m,hmB,hm,t,ht,hlt,hAc.comp measurable_fst,
    hAcLp.comp_measurePreserving measurePreserving_fst,?_,?_,?_,?_⟩
  · intro ua
    simp [flatAmplitude]
  · rw [packetSpectrum_first_coeff hAc hφc]
    exact hp
  · rw [packetSpectrum_first_coeff hAc hφc]
    simpa only [Pi.smul_apply,neg_smul] using hn
  · intro ua hua
    exact ⟨flatAmplitude_support o l t _ hua,mem_univ _⟩

section Padding
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

local instance instMeasurableSingletonClassSumBool_solutions : MeasurableSingletonClass (ι ⊕ Bool) := by
  constructor
  intro x
  cases x with
  | inl i => simpa only [Set.image_singleton] using (measurableSet_singleton i).inl_image (β := Bool)
  | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image (α := ι)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma paddedAngular_injective {m : ι → ℤ} (hm : Injective m) {k : ℤ} (hk : k ≠ 0)
    (havoid : ∀ i, m i ≠ k ∧ m i ≠ -k) : Injective (paddedAngular m k) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hm hxy)
    | inr b => cases b <;> simp_all [paddedAngular]
  | inr b =>
    cases y with
    | inl j =>
      cases b
      · exact False.elim ((havoid j).2 hxy.symm)
      · exact False.elim ((havoid j).1 hxy.symm)
    | inr b' =>
      cases b <;> cases b'
      · rfl
      · change -k = k at hxy
        exact False.elim (hk (by omega))
      · change k = -k at hxy
        exact False.elim (hk (by omega))
      · rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_paddedOld (m : ι → ℤ) (k : ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    finitePacketVector (paddedAngular m k) (paddedOld A) = finitePacketVector m A := by
  funext x
  simp [finitePacketVector,Fintype.sum_sum_type,paddedAngular,paddedOld,packet]

lemma finitePacketSpectralMeasure_paddedOld {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) (k : ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) :
    finitePacketSpectralMeasure φ (paddedAngular m k) (paddedOld A) = finitePacketSpectralMeasure φ m A := by
  rw [finitePacketSpectralMeasure_eq_sum hφ _ (by
    intro i
    cases i with
    | inl j => exact hA j
    | inr _ => exact measurable_const),
    finitePacketSpectralMeasure_eq_sum hφ m hA]
  simp [Fintype.sum_sum_type,paddedAngular,paddedOld,packetSpectralMeasure_zero]

lemma finitePacketSpectralMeasure_paddedFlat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) (k : ℤ) {V : UnitAddCircle × UnitAddCircle → ℂ} (hV : Measurable V)
    (hp : packetSpectralMeasure φ k V = ENNReal.ofReal (1/2:ℝ) • phaseHaar)
    (hn : packetSpectralMeasure φ (-k) V = ENNReal.ofReal (1/2:ℝ) • phaseHaar) :
    finitePacketSpectralMeasure φ (paddedAngular m k) (paddedFlat V) = phaseHaar := by
  rw [finitePacketSpectralMeasure_eq_sum hφ _ (by
    intro i
    cases i with
    | inl _ => exact measurable_const
    | inr _ => exact hV)]
  simp only [Fintype.sum_sum_type,paddedAngular,paddedFlat,Sum.elim_inl,Sum.elim_inr,
    packetSpectralMeasure_zero,Finset.sum_const_zero,zero_add,Fintype.sum_bool]
  simp only [Bool.false_eq_true,ite_false,ite_true,hp,hn,← add_smul]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Padding
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

lemma totalVector_eq (x : TripleTorus) :
    C.totalVector x = ∑ i, packet (C.packets.m i) (C.packets.A i) x := by
  classical
  simp only [totalVector,vector,colorVector]
  rw [Finset.sum_comm]
  simp
lemma totalDensity_eq (z : UnitAddCircle) :
    blockTotal C.density z = ∑ i, C.packets.density i z := by
  classical
  simp only [blockTotal,density,colorDensity]
  rw [Finset.sum_comm]
  simp
lemma totalVector_continuous : Continuous C.totalVector :=
  continuous_finsetSum _ (fun r _ => C.vector_continuous r)

lemma totalVector_spectral_moment (k : ℤ) :
    (∫ x : TripleTorus, conj (C.totalVector x)*C.totalVector
      (twistIter (fun a => (C.packets.periodic.lift a:UnitAddCircle)) k x) ∂tripleVolume) =
      ∫ z, (blockTotal C.density z:ℂ)*fourier k z ∂phaseHaar := by
  have hφ : Continuous (fun a => (C.packets.periodic.lift a:UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp C.packets.speed_continuous
  simp_rw [C.totalVector_eq]
  rw [disjoint_packet_list_correlation C.packets.m C.packets.A
    C.packets.continuous_amplitude hφ (fun i j hij hm => (hij (C.injective hm)).elim) k]
  simp_rw [C.packets.density_spectral C.spare]
  simp_rw [moment_withDensity_real (C.packets.density_continuous _).measurable
    (C.packets.density_nonneg _) (fourier k)]
  simp_rw [C.totalDensity_eq,Complex.ofReal_sum,Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ =>
    ((Complex.continuous_ofReal.comp (C.packets.density_continuous i)).mul (fourier k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm

lemma total_mass_energy :
    (∫ z, blockTotal C.density z ∂phaseHaar) =
      ∫ x, ‖C.totalVector x‖^2 ∂tripleVolume := by
  have h := C.totalVector_spectral_moment 0
  have he (x : TripleTorus) :
      conj (C.totalVector x)*C.totalVector (twistIter (fun a => (C.packets.periodic.lift a:UnitAddCircle)) 0 x) =
        ((‖C.totalVector x‖^2:ℝ):ℂ) := by
    simp only [twistIter,zero_zsmul,add_zero]
    rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
  simp_rw [he,fourier_zero,mul_one] at h
  rw [integral_complex_ofReal,integral_complex_ofReal] at h
  exact Complex.ofReal_injective h.symm

end ColoredState
end ThreeTorus
end
end

section

/-! Literal finite measurable packet states. The spectral measure is defined
from coefficient energy, not carried as an unspecified abstract spectrum. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

attribute [instance] MeasurablePackets.finite
namespace MeasurablePackets
variable (F : MeasurablePackets)
lemma spectrum_eq [MeasurableSpace F.Index] [MeasurableSingletonClass F.Index]
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) :
    F.spectrum φ = finitePacketSpectralMeasure φ F.m F.A :=
  (finitePacketSpectralMeasure_eq_sum hφ F.m F.measurable).symm

end MeasurablePackets

namespace ColoredState
variable {n : ℕ} (C : ColoredState (Fin n))

lemma measurablePackets_vector : C.measurablePackets.vector = C.totalVector := by
  funext x
  exact (C.totalVector_eq x).symm

lemma measurablePackets_spectrum :
    C.measurablePackets.spectrum (fun u => (C.packets.periodic.lift u:UnitAddCircle)) =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (blockTotal C.density z)) := by
  classical
  change (∑ i, packetSpectralMeasure _ (C.packets.m i) (C.packets.A i)) = _
  simp_rw [C.packets.density_spectral C.spare]
  ext s hs
  rw [Measure.finsetSum_apply,withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs,C.totalDensity_eq]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro z
    exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => C.packets.density_nonneg i z)).symm
  · intro i _
    exact (C.packets.density_continuous i).measurable.ennreal_ofReal

lemma totalDensity_even {τR : Fin n → Fin n} (hr : C.Reflection τR)
    (hτR : Involutive τR) (z : UnitAddCircle) :
    blockTotal C.density (-z) = blockTotal C.density z := by
  classical
  unfold blockTotal
  simp_rw [← Reflection.density C hr hτR]
  exact Equiv.sum_comp hτR.toPerm (fun r => C.density r z)

end ColoredState
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_FiniteBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric anchored blocks, unconditional block production, physical mass, and estimator regularity. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ActualColoredBlock
variable {m : ℕ} {C E : ColoredState (Fin m)} {β : Equiv.Perm TripleTorus}
    {D : UnitAddCircle → ℂ} (h : ActualColoredBlock C E β D)
include h
lemma continuous : Continuous β := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,_,hp,rfl,_⟩ := h.witness
  exact hp.continuous.comp s.chart_continuous
lemma preserves : MeasurePreserving β tripleVolume tripleVolume := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,_,hp,rfl,_⟩ := h.witness
  exact hp.preserves.comp s.chart_preserves
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ β) (g ∘ β) = physicalError f g := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,α,hp,rfl,_⟩ := h.witness
  change physicalError ((f ∘ α) ∘ passageChart (s.geometry.H _))
    ((g ∘ α) ∘ passageChart (s.geometry.H _)) = _
  rw [physicalError_chart (s.geometry.Hcontinuous _).measurable,hp.physicalError_eq]
end ActualColoredBlock

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_CyclicPrediction
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated blocks, prediction budgets, physical Laurent polynomials, and actual cyclic approximation. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ActualColoredBlocks
variable {m : ℕ} {C E : ColoredState (Fin m)} {k : ℕ} {α : Equiv.Perm TripleTorus}
    {A : UnitAddCircle → ℂ} (h : ActualColoredBlocks C E k α A)
include h
lemma continuous : Continuous α := by
  induction h with
  | nil => exact continuous_id
  | snoc h hb ih => exact hb.continuous.comp ih
lemma preserves : MeasurePreserving α tripleVolume tripleVolume := by
  induction h with
  | nil => exact MeasurePreserving.id _
  | snoc h hb ih => exact hb.preserves.comp ih
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ α) (g ∘ α) = physicalError f g := by
  induction h generalizing f g with
  | nil => rfl
  | @snoc E F k α β A D h hb ih =>
    change physicalError ((f ∘ β) ∘ α) ((g ∘ β) ∘ α) = _
    rw [ih,hb.physicalError_eq]
end ActualColoredBlocks

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

lemma weightedVector_continuous {a : C.Index → UnitAddCircle → ℂ}
    (ha : ∀ i, Continuous (a i)) : Continuous (C.weightedVector a) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_packet
  exact ((ha i).comp (((AddCircle.continuous_mk' 1).comp
    (C.packets.speed_continuous.comp continuous_fst)).const_smul (C.packets.m i))).mul
    (C.packets.continuous_amplitude i)

lemma weighted_packet_spectral {a : UnitAddCircle → ℂ} (ha : Continuous a) (i : C.Index) :
    packetSpectralMeasure (fun x => (C.packets.periodic.lift x:UnitAddCircle)) (C.packets.m i)
      (fun u => a (C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle))*C.packets.A i u) =
    phaseHaar.withDensity (fun z => ENNReal.ofReal (C.packets.density i z*‖a z‖^2)) := by
  have hz : Measurable (fun u : UnitAddCircle × UnitAddCircle =>
      C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle)) :=
    ((((AddCircle.continuous_mk' 1).comp C.packets.speed_continuous).comp
      continuous_fst).const_smul (C.packets.m i)).measurable
  have hs := energy_map_multiplier hz (C.packets.continuous_amplitude i).measurable
    (C.packets.density_continuous i).measurable.ennreal_ofReal
    (C.packets.density_spectral C.spare i) ha.measurable
  have hh : (fun z => ENNReal.ofReal (C.packets.density i z*‖a z‖^2)) =
      (fun z => ENNReal.ofReal (C.packets.density i z))*energyWeight a := by
    funext z
    exact ENNReal.ofReal_mul (C.packets.density_nonneg i z)
  rw [hh]
  exact hs

lemma weightedVector_energy {a : C.Index → UnitAddCircle → ℂ}
    (ha : ∀ i, Continuous (a i)) :
    (∫ x, ‖C.weightedVector a x‖^2 ∂tripleVolume) =
      ∑ i, ∫ z, C.packets.density i z*‖a i z‖^2 ∂phaseHaar := by
  let B (i : C.Index) (u : UnitAddCircle × UnitAddCircle) : ℂ :=
    a i (C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle))*C.packets.A i u
  have hB (i : C.Index) : Continuous (B i) :=
    ((ha i).comp (((AddCircle.continuous_mk' 1).comp
      (C.packets.speed_continuous.comp continuous_fst)).const_smul (C.packets.m i))).mul
      (C.packets.continuous_amplitude i)
  have hφ : Continuous (fun x => (C.packets.periodic.lift x:UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp C.packets.speed_continuous
  have h := disjoint_packet_list_correlation C.packets.m B hB hφ
    (fun i j hij hm => (hij (C.injective hm)).elim) 0
  have he (x : TripleTorus) :
      conj (∑ i, packet (C.packets.m i) (B i) x)*
      (∑ i, packet (C.packets.m i) (B i)
        (twistIter (fun u => (C.packets.periodic.lift u:UnitAddCircle)) 0 x)) =
      ((‖C.weightedVector a x‖^2:ℝ):ℂ) := by
    simp only [twistIter,zero_zsmul,add_zero]
    change conj (C.weightedVector a x)*C.weightedVector a x = _
    rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
  simp_rw [he] at h
  change _ = ∑ i, ∫ z, fourier 0 z ∂packetSpectralMeasure _ _ _ at h
  dsimp only [B] at h
  simp_rw [C.weighted_packet_spectral (ha _)] at h
  have hm (i : C.Index) : (∫ z, fourier 0 z ∂phaseHaar.withDensity
      (fun z => ENNReal.ofReal (C.packets.density i z*‖a i z‖^2))) =
      ((∫ z, C.packets.density i z*‖a i z‖^2 ∂phaseHaar:ℝ):ℂ) := by
    erw [moment_withDensity_real
      (((C.packets.density_continuous i).mul ((ha i).norm.pow 2)).measurable)
      (fun z => mul_nonneg (C.packets.density_nonneg i z) (sq_nonneg _)) (fourier 0)]
    simp only [fourier_zero,mul_one,integral_complex_ofReal]
    rfl
  simp_rw [hm] at h
  rw [integral_complex_ofReal,← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

lemma weightedVector_sub (a b : C.Index → UnitAddCircle → ℂ) (x : TripleTorus) :
    C.weightedVector (fun i z => a i z-b i z) x =
      C.weightedVector a x-C.weightedVector b x := by
  simp only [weightedVector,packet,sub_mul,Finset.sum_sub_distrib]

lemma weightedVector_tags (b : Fin m → ℂ) (x : TripleTorus) :
    C.weightedVector (fun i _ => b (C.color i)) x = ∑ r, b r*C.vector r x := by
  classical
  simp only [weightedVector,vector,colorVector,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite,mul_zero]
  simp [packet,mul_assoc]

lemma weighted_density_colors (b : Fin m → ℂ) {Ψ : UnitAddCircle → ℂ}
    (hΨ : Continuous Ψ) :
    (∑ i, ∫ z, C.packets.density i z*‖Ψ z-b (C.color i)‖^2 ∂phaseHaar) =
      ∑ r, ∫ z, C.density r z*‖Ψ z-b r‖^2 ∂phaseHaar := by
  classical
  have hint (i : C.Index) (r : Fin m) : Integrable
      (fun z => (if C.color i = r then C.packets.density i z else 0)*‖Ψ z-b r‖^2) phaseHaar := by
    apply continuous_circle_integrable
    split_ifs
    · exact (C.packets.density_continuous i).mul ((hΨ.sub continuous_const).norm.pow 2)
    · fun_prop
  simp only [density,colorDensity,Finset.sum_mul]
  simp_rw [integral_finsetSum _ (fun i _ => hint i _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he (r : Fin m) : (∫ z, (if C.color i = r then C.packets.density i z else 0)*
      ‖Ψ z-b r‖^2 ∂phaseHaar) =
      if C.color i = r then (∫ z, C.packets.density i z*‖Ψ z-b r‖^2 ∂phaseHaar) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp

/-- The density prediction error is exactly the squared physical L² error
for the literal packet multiplier; no cyclic-space calculus is assumed. -/
lemma physical_prediction_energy (b : Fin m → ℂ) {Ψ : UnitAddCircle → ℂ}
    (hΨ : Continuous Ψ) :
    (∫ x, ‖C.weightedVector (fun _ => Ψ) x-∑ r, b r*C.vector r x‖^2 ∂tripleVolume) =
      ∑ r, ∫ z, C.density r z*‖Ψ z-b r‖^2 ∂phaseHaar := by
  simp_rw [← C.weightedVector_tags,← C.weightedVector_sub]
  have hh (i : C.Index) : Continuous (fun z => Ψ z-b (C.color i)) :=
    hΨ.sub continuous_const
  rw [C.weightedVector_energy hh]
  exact C.weighted_density_colors b hΨ

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

lemma laurent_eq_multiplier (c : ℤ →₀ ℂ) (x : TripleTorus) :
    C.laurent c x = C.weightedVector (fun _ z => ∑ k ∈ c.support, c k*fourier k z) x := by
  simp only [laurent,C.totalVector_eq,Finset.mul_sum]
  simp only [packet_twistIter]
  simp only [weightedVector,packet]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma laurent_continuous (c : ℤ →₀ ℂ) : Continuous (C.laurent c) := by
  have hh : C.laurent c = C.weightedVector (fun _ z => ∑ k ∈ c.support, c k*fourier k z) :=
    funext (C.laurent_eq_multiplier c)
  rw [hh]
  exact C.weightedVector_continuous (fun _ => continuous_finsetSum _
    (fun k _ => continuous_const.mul (fourier k).continuous))

lemma multiplier_error_bound {Ψ Φ : UnitAddCircle → ℂ} (hΨ : Continuous Ψ) (hΦ : Continuous Φ)
    {δ : ℝ} (hbound : ∀ z, ‖Ψ z-Φ z‖ ≤ δ) :
    physicalError (C.weightedVector (fun _ => Ψ)) (C.weightedVector (fun _ => Φ)) ≤
      δ^2*(∫ z, blockTotal C.density z ∂phaseHaar) := by
  unfold physicalError
  simp_rw [← C.weightedVector_sub]
  have hh (i : C.Index) : Continuous (fun z => Ψ z-Φ z) := hΨ.sub hΦ
  rw [C.weightedVector_energy hh]
  have he : (∑ i, ∫ z, C.packets.density i z*‖Ψ z-Φ z‖^2 ∂phaseHaar) =
      ∫ z, (blockTotal C.density z)*‖Ψ z-Φ z‖^2 ∂phaseHaar := by
    simp_rw [C.totalDensity_eq,Finset.sum_mul]
    exact (integral_finsetSum _ (fun i _ => continuous_circle_integrable
      ((C.packets.density_continuous i).mul ((hΨ.sub hΦ).norm.pow 2)))).symm
  rw [he]
  calc
    _ ≤ ∫ z, (blockTotal C.density z)*δ^2 ∂phaseHaar := by
      apply integral_mono
      · exact continuous_circle_integrable ((continuous_finsetSum _ (fun r _ => C.density_continuous r)).mul
          ((hΨ.sub hΦ).norm.pow 2))
      · exact continuous_circle_integrable ((continuous_finsetSum _ (fun r _ => C.density_continuous r)).mul continuous_const)
      · intro z
        apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun r _ => C.density_nonneg r z))
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2
    _ = _ := by rw [integral_mul_const,mul_comm]

/-- Continuous spectral multiplication lies in the physical cyclic space,
proved by actual finite Laurent approximants, with any squared L² tolerance. -/
lemma exists_laurent_approx {Ψ : UnitAddCircle → ℂ} (hΨ : Continuous Ψ)
    {ε : ℝ} (he : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, physicalError (C.weightedVector (fun _ => Ψ)) (C.laurent c) < ε := by
  let M := ∫ z, blockTotal C.density z ∂phaseHaar
  have hM : 0 ≤ M := integral_nonneg (fun z => Finset.sum_nonneg (fun r _ => C.density_nonneg r z))
  let δ := min 1 (ε/(M+1))/2
  have hd : 0 < δ := half_pos (lt_min zero_lt_one (div_pos he (by positivity)))
  have hd1 : δ ≤ 1 := by dsimp only [δ]; linarith [min_le_left (1:ℝ) (ε/(M+1))]
  have hdε : δ*(M+1) < ε := by
    have hi := min_le_right (1:ℝ) (ε/(M+1))
    have heq : (ε/(M+1))*(M+1) = ε := div_mul_cancel₀ _ (by positivity)
    have hq : 0 < ε/(M+1) := div_pos he (by positivity)
    have hh : δ < ε/(M+1) := by dsimp only [δ]; linarith
    have hb := mul_lt_mul_of_pos_right hh (show 0 < M+1 by positivity)
    linarith
  have hsmall : δ^2*M < ε := by
    have hg : δ^2 ≤ δ := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hg hM
    nlinarith
  obtain ⟨c,hc⟩ := exists_uniform_laurent hΨ hd
  refine ⟨c,?_⟩
  have hΦ : Continuous (fun z : UnitAddCircle => ∑ k ∈ c.support, c k*fourier k z) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous)
  have hb := C.multiplier_error_bound hΨ hΦ (fun z => (hc z).le)
  have hv : C.laurent c = C.weightedVector (fun _ z => ∑ k ∈ c.support, c k*fourier k z) :=
    funext (C.laurent_eq_multiplier c)
  rw [← hv] at hb
  exact hb.trans_lt hsmall

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalError_symm (f g : TripleTorus → ℂ) : physicalError f g = physicalError g f := by
  unfold physicalError
  simp only [norm_sub_rev]

lemma physicalError_const_mul {f g : TripleTorus → ℂ} (b : ℂ) :
    physicalError (fun x => b*f x) (fun x => b*g x) = ‖b‖^2*physicalError f g := by
  unfold physicalError
  simp_rw [← mul_sub,norm_mul,mul_pow]
  rw [integral_const_mul]

lemma physicalError_tagged_sum {m : ℕ} {f g : Fin m → TripleTorus → ℂ}
    (hf : ∀ r, Continuous (f r)) (hg : ∀ r, Continuous (g r))
    (b : Fin m → ℂ) (hb : ∀ r, ‖b r‖ ≤ 1) {η : ℝ}
    (he : ∀ r, physicalError (f r) (g r) ≤ η) :
    physicalError (fun x => ∑ r, b r*f r x) (fun x => ∑ r, b r*g r x) ≤ (m:ℝ)^2*η := by
  have ht := physicalError_sum (fun r => continuous_const.mul (hf r))
    (fun r => continuous_const.mul (hg r)) (f := fun r x => b r*f r x) (g := fun r x => b r*g r x)
  simp_rw [physicalError_const_mul] at ht
  have hi r : ‖b r‖^2*physicalError (f r) (g r) ≤ η := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (b r)) (hb r) 2
    calc
      _ ≤ 1*physicalError (f r) (g r) := mul_le_mul_of_nonneg_right (by simpa using hsq) (physicalError_nonneg _ _)
      _ ≤ η := by simpa using he r
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin m))) => hi r)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs ht
  have hn : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hs hn
  nlinarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalDist_const_mul {f g : TripleTorus → ℂ} (b : ℂ) :
    physicalDist (fun x => b*f x) (fun x => b*g x) = ‖b‖*physicalDist f g := by
  rw [physicalDist,physicalError_const_mul,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma finite_weighted_dist_le {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (b : ι → ℂ) {r : ℝ} (hd : ∀ i, physicalDist (f i) (g i) ≤ r) :
    physicalDist (fun x => ∑ i, b i*f i x) (fun x => ∑ i, b i*g i x) ≤ (∑ i, ‖b i‖)*r := by
  calc
    _ ≤ ∑ i, physicalDist (fun x => b i*f i x) (fun x => b i*g i x) :=
      physicalDist_finsum (fun i => (continuous_const.mul (hf i)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (fun i => (continuous_const.mul (hg i)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ ≤ ∑ i, ‖b i‖*r := by
      simp_rw [physicalDist_const_mul]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_ControlledBlocks
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical signal and derivative control through actual repeated blocks, cyclic prediction, and tag selection. -/

section
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
/-- Actual finite Laurent approximation to the OLD tagged packet sum after
reflected signal blocks. Neither a cyclic-space oracle nor a formal spectral
operator is used: the witness is a literal finite sum of twist iterates. -/
theorem actual_controlled_cyclic_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ c : ℤ →₀ ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      physicalError (fun x => ∑ r, tags r*C.vector r x) (E.laurent c ∘ α) < ε^2 ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧ Q.Close η F₀ C.packets.V F' E.packets.V := by
  let e := min η (ε^2/(16*((m:ℝ)+1)^2))
  have he : 0 < e := lt_min hη (div_pos (sq_pos_of_pos hε) (by positivity))
  obtain ⟨E,α,Ψ,K,A,hK,hpath,hΨdef,hphys,hsqrt,hpred,hΨ,_,_,hmassE,hrE,hgood,F',hF',hjets⟩ :=
    actual_controlled_density_prediction C τR hτR hrC tags htags htrR (show 0 < ε/8 by positivity)
      hτ he hκ hmass Q F₀
  obtain ⟨c,hc⟩ := E.exists_laurent_approx hΨ (show 0 < ε^2/64 by positivity)
  refine ⟨E,α,c,K,A,hK,hpath,fun r => (hphys r).trans_le (min_le_left _ _),hsqrt,?_,hmassE,hrE,hgood,F',hF',hjets.mono (min_le_left _ _)⟩
  let G : TripleTorus → ℂ := fun x => ∑ r, tags r*E.vector r x
  let F : TripleTorus → ℂ := fun x => ∑ r, tags r*C.vector r x
  let W := E.weightedVector (fun _ => Ψ)
  have hG : Continuous G := continuous_finsetSum _ (fun r _ => continuous_const.mul (E.vector_continuous r))
  have hF : Continuous F := continuous_finsetSum _ (fun r _ => continuous_const.mul (C.vector_continuous r))
  have hW : Continuous W := E.weightedVector_continuous (fun _ => hΨ)
  have hp : physicalError G W < (ε/8)^2 := by
    rw [physicalError_symm]
    exact (E.physical_prediction_energy tags hΨ).trans_lt hpred
  have ht := physicalError_triangle hG hW (E.laurent_continuous c)
  have heL : physicalError G (E.laurent c) < ε^2/16 := by linarith
  have htag : physicalError F (G ∘ α) ≤ (m:ℝ)^2*e :=
    physicalError_tagged_sum C.vector_continuous
      (fun r => (E.vector_continuous r).comp hpath.continuous) tags htags
      (fun r => (hphys r).le)
  have hsmall : (m:ℝ)^2*e < ε^2/16 := by
    have he' : e ≤ ε^2/(16*((m:ℝ)+1)^2) := min_le_right _ _
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    have hden : 0 < 16*((m:ℝ)+1)^2 := by positivity
    have hmul : e*(16*((m:ℝ)+1)^2) ≤ ε^2 := (le_div_iff₀ hden).1 he'
    nlinarith [sq_nonneg (m:ℝ)]
  have hlast := physicalError_triangle hF (hG.comp hpath.continuous)
    ((E.laurent_continuous c).comp hpath.continuous)
  rw [hpath.physicalError_eq] at hlast
  change physicalError F (E.laurent c ∘ α) < ε^2
  linarith [sq_pos_of_pos hε]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma ColoredState.laurent_smul {m : ℕ} (C : ColoredState (Fin m)) (b : ℂ)
    (c : ℤ →₀ ℂ) (x : TripleTorus) : C.laurent (b • c) x = b * C.laurent c x := by
  change (b • c).sum (fun k z => z * C.totalVector
    (twistIter (fun u => (C.packets.periodic.lift u:UnitAddCircle)) k x)) = _
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, ColoredState.laurent, mul_assoc, Finset.mul_sum]

/-- Arbitrary finite reflected tags, rescaled before any signal/jet choices. -/
theorem actual_controlled_tagged_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2)
    (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ c : ℤ →₀ ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      physicalError (fun x => ∑ r, tags r*C.vector r x) (E.laurent c ∘ α) < ε^2 ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧
        Q.Close η F₀ C.packets.V F' E.packets.V := by
  let M : ℝ := 1 + ∑ r, ‖tags r‖
  have hM : 0 < M := by dsimp [M]; positivity
  have ht (r : Fin m) : ‖tags r‖ ≤ M := by
    have hs : ‖tags r‖ ≤ ∑ s, ‖tags s‖ :=
      Finset.single_le_sum (fun s _ => norm_nonneg (tags s)) (Finset.mem_univ r)
    dsimp [M]; linarith
  let b : Fin m → ℂ := fun r => tags r / (M:ℂ)
  have hb (r : Fin m) : ‖b r‖ ≤ 1 := by
    simp only [b, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    exact (div_le_one hM).2 (ht r)
  have hbr (r : Fin m) : b (τR r) = conj (b r) := by
    simp only [b,htrR,map_div₀,Complex.conj_ofReal]
  obtain ⟨E,α,c,K,A,hK,hpath,hphys,hsqrt,hpred,hmassE,hrE,hgood,F',hF',hjets⟩ :=
    actual_controlled_cyclic_prediction C τR hτR hrC b hb hbr (div_pos hε hM)
      hτ hη hκ hmass Q F₀
  refine ⟨E,α,(M:ℂ) • c,K,A,hK,hpath,hphys,hsqrt,?_,hmassE,hrE,hgood,F',hF',hjets⟩
  have he : (fun x => ∑ r, tags r*C.vector r x) =
      (fun x => (M:ℂ) * ∑ r, b r*C.vector r x) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [b]
    field_simp [show (M:ℂ) ≠ 0 by exact_mod_cast hM.ne']
  rw [he]
  have hl : E.laurent ((M:ℂ) • c) ∘ α = fun x => (M:ℂ) * E.laurent c (α x) := by
    funext x
    exact E.laurent_smul _ _ _
  rw [hl,physicalError_const_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
  have hi := mul_lt_mul_of_pos_left hpred (sq_pos_of_pos hM)
  have hid : M^2 * (ε/M)^2 = ε^2 := by field_simp
  exact hi.trans_eq hid

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Stages
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-arc flattening, exact predicted whitening, unconditional one-stage construction, and stage states and successors. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma PassagePackets.amplitude_supported {ι : Type*} (F : PassagePackets ι) (i : ι) :
    support (F.A i) ⊆ ((fun x : ℝ => (x : UnitAddCircle)) '' Icc F.l F.u) ×ˢ univ := by
  intro ua hua
  let x := circleRep F.o ua.1
  have hx : x ∈ Ioc F.o (F.o+1) := ((AddCircle.measurableEquivIoc 1 F.o) ua.1).2
  have he : F.A i ua = F.A₀ i ua.2 x := by
    simpa only [x,coe_circleRep] using F.lift_matches i ua.2 x hx
  have hxs : x ∈ Icc F.l F.u := Ioc_subset_Icc_self (F.support_lift i ua.2 (by change F.A₀ i ua.2 x ≠ 0; rwa [← he]))
  exact ⟨⟨x,hxs,coe_circleRep _ _⟩,mem_univ _⟩

/-- A literal spare-independent flat pair supported in the SAME good arc,
whose angular modes avoid the entire finite old family. -/
theorem PassagePackets.exists_disjoint_flat {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {δ : ℝ} (hδ : 0 < δ) (hg : F.GoodArc δ) :
    ∃ l u : ℝ, δ < l ∧ l < u ∧ u < 1-δ ∧
      (∀ i, support (F.A i) ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ) ∧
      ∃ k : ℤ, k ≠ 0 ∧ (∀ i, F.m i ≠ k ∧ F.m i ≠ -k) ∧
      ∃ A : UnitAddCircle × UnitAddCircle → ℂ,
        Measurable A ∧ MemLp A 2 slowVolume ∧ (∀ ua, conj (A ua) = A ua) ∧
        packetSpectralMeasure (fun z => (F.periodic.lift z:UnitAddCircle)) k A =
          ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
        packetSpectralMeasure (fun z => (F.periodic.lift z:UnitAddCircle)) (-k) A =
          ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
        support A ⊆ ((fun x : ℝ => (x:UnitAddCircle)) '' Icc l u) ×ˢ univ := by
  classical
  let l := (δ+F.l)/2
  let u := (F.u+1-δ)/2
  have hδl : δ < l := by dsimp [l]; linarith [hg.2.1]
  have hll : l < F.l := by dsimp [l]; linarith [hg.2.1]
  have huu : F.u < u := by dsimp [u]; linarith [hg.2.2.1]
  have huδ : u < 1-δ := by dsimp [u]; linarith [hg.2.2.1]
  have hlu : l < u := hll.trans_le (F.lu.trans huu.le)
  have hinc : Icc l u ⊆ Ioo δ (1-δ) := fun _ hx => ⟨hδl.trans_le hx.1,hx.2.trans_lt huδ⟩
  have he : (fun y : ℝ => F.periodic.lift (y:UnitAddCircle)) = F.V := by
    funext y
    exact F.periodic.lift_coe y
  have hD : ∀ x ∈ Icc l u, HasDerivWithinAt
      (fun y : ℝ => F.periodic.lift (y:UnitAddCircle)) (deriv F.V x) (Icc l u) x := by
    rw [he]
    intro x _
    exact (F.smooth_speed.differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hmono : StrictMonoOn (fun y : ℝ => F.periodic.lift (y:UnitAddCircle)) (Icc l u) := by
    rw [he]
    exact strictMonoOn_of_deriv_pos (convex_Icc _ _) F.smooth_speed.continuous.continuousOn
      (fun x hx => hg.2.2.2 x (hinc (interior_subset hx)))
  let B := ∑ i, (F.m i).natAbs
  obtain ⟨k,hBk,hk,t,ht,hlt,hm,hLp,hr,hp,hn,hs⟩ := exists_flat_packet_spectra_above
    F.speed_continuous.measurable (F.smooth_speed.continuous_deriv (by simp)).measurable
    hlu hD hmono (o := 0) (fun x hx => ⟨by linarith [hinc hx |>.1],by linarith [hinc hx |>.2]⟩) B
  refine ⟨l,u,hδl,hlu,huδ,?_,(k:ℤ),by exact_mod_cast hk.ne',?_,_,hm,hLp,hr,hp,hn,?_⟩
  · intro i ua hua
    obtain ⟨⟨x,hx,hxe⟩,_⟩ := F.amplitude_supported i hua
    exact ⟨⟨x,⟨hll.le.trans hx.1,hx.2.trans huu.le⟩,hxe⟩,mem_univ _⟩
  · intro i
    have hi : (F.m i).natAbs ≤ B := Finset.single_le_sum (f := fun j => (F.m j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    constructor <;> intro hh <;> rw [hh] at hi <;> exact (not_le_of_gt hBk) (by simpa using hi)
  · intro ua hua
    obtain ⟨⟨x,hx,hxe⟩,_⟩ := hs hua
    exact ⟨⟨x,⟨hx.1,hx.2.trans ht.2⟩,hxe⟩,mem_univ _⟩

end ThreeTorus
end
end

section

/-! Whitening of the VERY SAME actual predicted output, retaining compact
support in its good arc, reality and literal Laurent approximation. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma paddedReflection_involutive {ι : Type*} {τ : ι → ι} (hτ : Involutive τ) :
    Involutive (Sum.map τ Bool.not) := by
  intro i
  cases i with
  | inl j => exact congrArg Sum.inl (hτ j)
  | inr b => cases b <;> rfl

namespace ColoredState
variable {n : ℕ} (C : ColoredState (Fin n))

/-- This theorem is unconditional once the concrete predicted smooth packet
family has been produced. The flat filler uses fresh actual angular modes. -/
theorem exists_whitening {τR : Fin n → Fin n} (hr : C.Reflection τR)
    (hτR : Involutive τR) {δ : ℝ} (hδ : 0 < δ) (hg : C.packets.GoodArc δ) :
    ∃ W : MeasurablePackets, ∃ l u : ℝ, δ < l ∧ l < u ∧ u < 1-δ ∧
      W.Supported l u ∧ (∃ τ, W.Reflection τ) ∧
      W.spectrum (fun z => (C.packets.periodic.lift z:UnitAddCircle)) = phaseHaar ∧
      (∫ x, ‖W.vector x-C.totalVector x‖^2 ∂tripleVolume) =
        (∫ z, blockTotal C.density z ∂phaseHaar)+1-
          2*(∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar) ∧
      ∀ (c : ℤ →₀ ℂ) (ε : ℝ), 0 < ε → ∃ d : ℤ →₀ ℂ,
        physicalError (C.laurent c) (finitePacketLaurent
          (fun z => (C.packets.periodic.lift z:UnitAddCircle)) W.m W.A d) < ε^2 := by
  classical
  let : MeasurableSpace C.Index := ⊤
  let : MeasurableSingletonClass C.Index := ⟨fun _ => trivial⟩
  let : MeasurableSingletonClass (C.Index ⊕ Bool) := by
    constructor
    intro i
    cases i with
    | inl j => simpa only [Set.image_singleton] using (measurableSet_singleton j).inl_image (β := Bool)
    | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image (α := C.Index)
  let φ : UnitAddCircle → UnitAddCircle := fun z => (C.packets.periodic.lift z:UnitAddCircle)
  have hφ : Measurable φ := AddCircle.measurable_mk'.comp C.packets.speed_continuous.measurable
  let p := blockTotal C.density
  have hp : Continuous p := continuous_finsetSum _ (fun r _ => C.density_continuous r)
  have hpn : ∀ z, 0 ≤ p z := fun z => Finset.sum_nonneg (fun r _ => C.density_nonneg r z)
  obtain ⟨l,u,hdl,hlu,hud,hAs,k,hk,havoid,V,hVm,hVlp,hVr,hVp,hVn,hVs⟩ :=
    C.packets.exists_disjoint_flat hδ hg
  let m := paddedAngular C.packets.m k
  let A := paddedOld C.packets.A
  let B := paddedFlat (ι := C.Index) V
  have hmi : Injective m := paddedAngular_injective C.injective hk havoid
  have hmn : ∀ i, m i ≠ 0 := by
    intro i
    cases i with
    | inl j => exact C.packets.nonzero j
    | inr b => cases b <;> simpa [m,paddedAngular] using hk
  have hAm : ∀ i, Measurable (A i) := by
    intro i
    cases i with
    | inl j => exact (C.packets.continuous_amplitude j).measurable
    | inr _ => exact measurable_const
  have hBm : ∀ i, Measurable (B i) := by
    intro i
    cases i with
    | inl _ => exact measurable_const
    | inr _ => exact hVm
  have hAlp : ∀ i, MemLp (A i) 2 slowVolume := by
    intro i
    cases i with
    | inl j => exact C.measurablePackets.memLp j
    | inr _ => exact MemLp.zero
  have hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)) := by
    rw [finitePacketSpectralMeasure_paddedOld hφ _ _ (fun i => (C.packets.continuous_amplitude i).measurable)]
    rw [finitePacketSpectralMeasure_eq_sum hφ _ (fun i => (C.packets.continuous_amplitude i).measurable)]
    exact C.measurablePackets_spectrum
  have hflat : finitePacketSpectralMeasure φ m B = phaseHaar :=
    finitePacketSpectralMeasure_paddedFlat hφ _ _ hVm hVp hVn
  let W : MeasurablePackets := {
    Index := C.Index ⊕ Bool
    finite := inferInstance
    m := m
    injective := hmi
    nonzero := hmn
    A := whitenPackets φ m p A B
    measurable := measurable_whitenPackets hφ m hp.measurable hAm hBm
    memLp := memLp_whitenPackets hφ m hp.measurable hpn hAm hBm hpush hflat }
  have heA : finitePacketVector m A = C.totalVector :=
    (finitePacketVector_paddedOld _ _ _).trans C.measurablePackets_vector
  have hW : finitePacketSpectralMeasure φ m W.A = phaseHaar :=
    whitenPackets_flat hφ m hp.measurable hpn hAm hBm hpush hflat
  refine ⟨W,l,u,hdl,hlu,hud,?_,?_,?_,?_,?_⟩
  · apply whitenPackets_support
    · intro i
      cases i with
      | inl j => exact hAs j
      | inr _ => simp [paddedOld]
    · intro i
      cases i with
      | inl _ => simp [paddedFlat]
      | inr _ => exact hVs
  · have heven := C.totalDensity_even hr hτR
    obtain ⟨τ,hτ,hcolor⟩ := hr
    have hτi := hτ.involutive C.injective
    refine ⟨Sum.map τ Bool.not,paddedReflection_involutive hτi,?_,?_⟩
    · intro i
      cases i with
      | inl j => exact hτ.index j
      | inr b => cases b <;> simp [W,m,paddedAngular]
    · apply whitenPackets_reflection
      · intro i
        cases i with
        | inl j => exact hτ.index j
        | inr b => cases b <;> simp [m,paddedAngular]
      · exact heven
      · intro i ua
        cases i with
        | inl j => exact hτ.amplitude j ua
        | inr _ => simp [paddedOld]
      · intro i ua
        cases i with
        | inl _ => simp [paddedFlat]
        | inr _ => exact (hVr ua).symm
  · exact (W.spectrum_eq hφ).trans hW
  · have he := whitenPackets_distance_mass hφ hmi hp hpn hAm hBm hAlp hpush hflat
    rw [heA,← C.total_mass_energy] at he
    exact he
  · intro c ε hε
    let D : UnitAddCircle → ℂ := fun z => ∑ k ∈ c.support, c k*fourier k z
    have hD : Continuous D := continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous)
    obtain ⟨d,hd⟩ := exists_whitened_laurent_approx hφ hmi hp hpn hAm hBm hpush hflat hD hε
    refine ⟨d,?_⟩
    have he : finitePacketVector m (multiplyPackets φ m D A) = C.laurent c := by
      funext x
      change finitePacketVector m (multiplyPackets φ m (fun z => ∑ k ∈ c.support, c k*fourier k z) A) x = _
      rw [← finitePacketLaurent_eq_multiplier]
      simp only [finitePacketLaurent,heA,laurent]
      rfl
    rw [he] at hd
    exact hd

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma MeasurablePackets.laurent_memLp (W : MeasurablePackets)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (c : ℤ →₀ ℂ) :
    MemLp (finitePacketLaurent φ W.m W.A c) 2 tripleVolume := by
  have he : finitePacketLaurent φ W.m W.A c = finitePacketVector W.m
      (multiplyPackets φ W.m (fun z => ∑ k ∈ c.support, c k*fourier k z) W.A) :=
    funext (finitePacketLaurent_eq_multiplier φ W.m W.A c)
  rw [he]
  apply memLp_finitePacketVector
  exact memLp_multiplyPackets hφ W.m (continuous_finsetSum _
    (fun k _ => continuous_const.mul (fourier k).continuous)) W.measurable W.memLp

lemma ColoredState.density_integrable {n : ℕ} (C : ColoredState (Fin n)) :
    Integrable (blockTotal C.density) phaseHaar :=
  integrable_finsetSum _ (fun i _ => (C.density_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

lemma ColoredState.mass_eq_norm_sq {n : ℕ} (C : ColoredState (Fin n)) :
    (∫ z, blockTotal C.density z ∂phaseHaar)=physicalDist C.totalVector 0^2 := by
  rw [physicalDist_sq,physicalError]
  simpa only [Pi.zero_apply,sub_zero] using C.total_mass_energy

/-- The ACTUAL reflected prediction output is whitened, not replaced by an
unrelated Hilbert witness. Small input density error controls the same vector. -/
theorem exists_predicted_whitening_oai {n : ℕ} (C : ColoredState (Fin n))
    (ρ : Fin n → Fin n) (hρ : Involutive ρ) (hr : C.Reflection ρ)
    (b : Fin n → ℂ) (hb : ∀ i, b (ρ i)=conj (b i))
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {e r η κ ζ : ℝ} (he : 0 < e) (hr0 : 0 < r) (hr1 : r < 1)
    (her : e ≤ (r^2/64)^2) (hη : 0 < η) (hκ : 0 < κ) (hζ : 0 < ζ)
    (hpC : (∫ z, |blockTotal C.density z-1| ∂phaseHaar) < e) :
    ∃ W : MeasurablePackets, ∃ V : ℝ → ℝ, ∃ hp : Periodic V 1,
      ∃ _hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V,
      ∃ δ l u : ℝ, ∃ β : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame, ∃ d : ℤ →₀ ℂ,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ δ < l ∧ l < u ∧ u < 1-δ ∧
      (∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) ∧ W.Supported l u ∧
      (∃ τ, W.Reflection τ) ∧ W.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar ∧
      Continuous β ∧ MeasurePreserving β tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans β ∧ Q.Close ζ frame C.packets.V frame' V ∧
      physicalDist C.totalVector (W.vector ∘ β) < e+r ∧
      physicalDist (fun x => ∑ i, b i*C.vector i x)
        (finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A d ∘ β) < η := by
  classical
  let s := r^2/64
  have hs0 : 0 < s := div_pos (sq_pos_of_pos hr0) (by norm_num)
  have hs1 : s < 1 := by dsimp [s]; nlinarith
  have hes : e ≤ s := by change e ≤ s^2 at her; nlinarith
  have he1 : e < 1 := hes.trans_lt hs1
  have hsqrt : Real.sqrt e ≤ s := (Real.sqrt_le_iff).2 ⟨hs0.le,her⟩
  have hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 1+e := by
    have ht := norm_integral_le_integral_norm (fun z => blockTotal C.density z-1) (μ := phaseHaar)
    rw [integral_sub C.density_integrable (integrable_const _)] at ht
    simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,Real.norm_eq_abs] at ht
    have hh := le_abs_self ((∫ z, blockTotal C.density z ∂phaseHaar)-1)
    linarith
  have hnC : physicalDist C.totalVector 0 < 1+e := by
    rw [C.mass_eq_norm_sq] at hmass
    nlinarith [physicalDist_nonneg C.totalVector 0]
  have hHellinger : 1-Real.sqrt e < ∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar := by
    have hh := density_hellinger_error C.density_integrable (integrable_const (1:ℝ))
      (Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun i _ => C.density_nonneg i z)))
      (Filter.Eventually.of_forall (fun _ => zero_le_one))
    simp only [Real.sqrt_one,integral_const,probReal_univ,smul_eq_mul,mul_one] at hh
    have hh' := (neg_le_abs ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-1)).trans hh
    have he' := Real.sqrt_lt_sqrt (integral_nonneg fun z => abs_nonneg _) hpC
    linarith
  let t := e/((n:ℝ)+1)
  have ht : 0 < t := div_pos he (by positivity)
  let a := min (t^2) ζ
  have ha : 0 < a := lt_min (sq_pos_of_pos ht) hζ
  obtain ⟨E,β,c,K,A,hK,hpath,hphys,hHell,hpred,hEmass,hEr,⟨δ,hδ,hδ8,hδκ,hEg⟩,frame',hfr,hjet⟩ :=
    actual_controlled_tagged_prediction C ρ hρ hr b hb (half_pos hη) hs0 ha hκ
      (hmass.trans (by linarith)) Q frame
  have hCE : physicalDist C.totalVector (E.totalVector ∘ β) < e := by
    have hg i : physicalDist (C.vector i) (E.vector i ∘ β) ≤ t := by
      apply ((physicalDist_lt_iff _ _ ht).2 ?_).le
      exact (hphys i).trans_le (min_le_left _ _)
    have hh := finite_weighted_dist_le C.vector_continuous
      (fun i => (E.vector_continuous i).comp hpath.continuous) (fun _ => (1:ℂ)) hg
    simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    refine hh.trans_lt ?_
    dsimp [t]
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (n:ℝ)+1)).2
    nlinarith
  have hnE : physicalDist E.totalVector 0 < 1+2*e := by
    have hh := physicalDist_triangle (continuous_triple_memLp (E.totalVector_continuous.comp hpath.continuous))
      (continuous_triple_memLp C.totalVector_continuous) MemLp.zero
    rw [physicalDist_symm (E.totalVector ∘ β) C.totalVector] at hh
    have hz : (0 : TripleTorus → ℂ) ∘ β = 0 := rfl
    rw [← hz,physicalDist_continuous_comp β hpath.continuous hpath.preserves] at hh
    simp only [hz] at hh
    linarith
  obtain ⟨W,l,u,hdl,hlu,hud,hWs,hWr,hWflat,hWdist,hWrecon⟩ := E.exists_whitening hEr hρ hδ hEg
  have hWE : physicalDist W.vector E.totalVector < r := by
    apply (physicalDist_lt_iff _ _ hr0).2
    change physicalError W.vector E.totalVector = _ at hWdist
    rw [hWdist,E.mass_eq_norm_sq]
    have hnE0 := physicalDist_nonneg E.totalVector 0
    have he2 : e^2 ≤ e := by nlinarith
    have hnorm : physicalDist E.totalVector 0^2 < (1+2*e)^2 := by nlinarith
    have hHell' : 1-2*s < ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar := by linarith
    have hsdef : 64*s=r^2 := by dsimp [s]; ring
    nlinarith
  obtain ⟨d,hd⟩ := hWrecon c (η/2) (half_pos hη)
  let V := E.packets.V
  let hp := E.packets.periodic
  have hφ : Measurable (fun z => (hp.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp E.packets.speed_continuous.measurable
  refine ⟨W,V,hp,E.packets.smooth_speed,δ,l,u,β,frame',d,hδ,hδ8,hδκ,hdl,hlu,hud,
    hEg.2.2.2,hWs,hWr,hWflat,hpath.continuous,hpath.preserves,hfr,hjet.mono (min_le_right _ _),?_,?_⟩
  · have hEW : physicalDist (E.totalVector ∘ β) (W.vector ∘ β) < r := by
      rw [physicalDist_continuous_comp β hpath.continuous hpath.preserves,physicalDist_symm]
      exact hWE
    exact (physicalDist_triangle (continuous_triple_memLp C.totalVector_continuous)
      (continuous_triple_memLp (E.totalVector_continuous.comp hpath.continuous))
      (W.vector_memLp.comp_measurePreserving hpath.preserves)).trans_lt (add_lt_add hCE hEW)
  · have htag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    have hpr := (physicalDist_lt_iff _ _ (half_pos hη)).2 hpred
    have hrec : physicalDist (E.laurent c ∘ β)
        (finitePacketLaurent (fun z => (hp.lift z:UnitAddCircle)) W.m W.A d ∘ β) < η/2 := by
      rw [physicalDist_continuous_comp β hpath.continuous hpath.preserves]
      exact (physicalDist_lt_iff _ _ (half_pos hη)).2 hd
    exact (physicalDist_triangle (continuous_triple_memLp htag)
      (continuous_triple_memLp ((E.laurent_continuous c).comp hpath.continuous))
      ((W.laurent_memLp hφ d).comp_measurePreserving hpath.preserves)).trans_lt (by linarith)
end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exists_predicted_whitening_oai := @OAI.ThreeTorus.exists_predicted_whitening_oai
