-- Prove2me | solution 1 for OAI.ThreeTorus.exists_physical_basis
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:13:59.226139+00:00
-- url     : https://prove2.me/submissions/6a18d902-322f-416d-abef-6168eeb613d0

import Mathlib
import Definitions.Def_ThreeTorus
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_StageState_exists_step

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

lemma twistIter_add (φ : UnitAddCircle → UnitAddCircle) (n k : ℤ) (x : TripleTorus) :
    twistIter φ (n+k) x = twistIter φ n (twistIter φ k x) := by
  dsimp [twistIter]
  simp only [add_zsmul]
  congr 1
  abel

lemma packet_twistIter (φ : UnitAddCircle → UnitAddCircle) (n m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A (twistIter φ n x) = fourier n (m • φ x.2.1) * packet m A x := by
  change A x.2 * fourier m (x.1+n • φ x.2.1) =
    fourier n (m • φ x.2.1)*(A x.2*fourier m x.1)
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_smul]
  rw [mul_comm n m]
  ring

lemma integral_fourier_pair (m k : ℤ) :
    (∫ θ : UnitAddCircle, starRingEnd ℂ (fourier m θ)*fourier k θ
      ∂AddCircle.haarAddCircle) = if m = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) m k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [RCLike.inner_apply,mul_comm] using hh

lemma normSq_complex (z : ℂ) : starRingEnd ℂ z*z = (‖z‖^2 : ℝ) := by
  simp only [Complex.conj_mul',Complex.ofReal_pow]

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

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

lemma neutralJitterReal_smooth {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (neutralJitterReal c L β) :=
  contDiff_periodize (c.ξ_smooth.mul (contDiff_const.mul contDiff_id |>.add contDiff_const))
    c.ξ_compact.mul_right

lemma neutralJitterReal_affine {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (L β : ℝ)
    {a : ℝ} (ha : a ∈ Icc δ (1-δ)) : neutralJitterReal c L β a = L*a+β := by
  unfold neutralJitterReal
  rw [periodize_eq_on_unit (fun x hx => c.ξ_support (subset_tsupport _ (left_ne_zero_of_mul hx)))
    (show a ∈ Icc (0:ℝ) 1 from ⟨by linarith [ha.1],by linarith [ha.2]⟩),c.ξ_one a ha,one_mul]

lemma neutralJitterReal_deriv {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (L β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) : deriv (neutralJitterReal c L β) a = L := by
  have he : neutralJitterReal c L β =ᶠ[𝓝 a] (fun x => L*x+β) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact neutralJitterReal_affine c hδ L β ⟨hb.1.le,hb.2.le⟩
  rw [he.deriv_eq]
  simp

lemma continuous_neutralJitter {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    Continuous (neutralJitter c L β) :=
by
  apply Continuous.quotient_lift
  exact (neutralJitterReal_smooth c L β).continuous

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
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

end ThreeTorus
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

/-! Global smooth cover charts with independently chosen deck representatives
for the two signs. This makes the corrected physical passage lift compatible
with further coordinate changes, rather than losing the integer carrier. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PhysicalFrame

lemma mapLift_smooth (F : PhysicalFrame) {V : ℝ → ℝ}
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (k : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.mapLift V k) := by
  apply (F.backward_smooth k).comp
  apply ContDiff.comp _ F.forward_smooth
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverTwist] <;> fun_prop

end PhysicalFrame

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

lemma memLp_frequency_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {A : X → ℂ} (hA : MemLp A 2 ν) {ζ : X → UnitAddCircle}
    (hζ : Measurable ζ) (n : ℤ) :
    MemLp (fun x => fourier n (ζ x)*A x) 2 ν := by
  apply hA.congr_norm
  · exact (((fourier n).continuous.measurable.comp hζ).aestronglyMeasurable).mul
      hA.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-- Exact correlation formula, requiring no smoothness of the coefficients. -/
lemma packet_correlation_L2 {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : MemLp B 2 slowVolume := memLp_frequency_mul hA
    ((hφ.comp measurable_fst).const_smul m) n
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair_L2 hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

/-- Exact pushforward measure even for the endpoint-discontinuous flat vector. -/
lemma packet_spectral_moment_L2 {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hAm : Measurable A)
    (hA : MemLp A 2 slowVolume) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation_L2 hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hAm.norm.pow_const 2).ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

lemma packet_integral_zero {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {m : ℤ} (hm : m ≠ 0) :
    (∫ x, packet m A x ∂tripleVolume) = 0 := by
  rw [integral_prod_symm _ ((memLp_packet hA m).integrable (by norm_num))]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, packet m A (θ,ua) ∂AddCircle.haarAddCircle) = 0 := by
    simp only [packet,integral_const_mul]
    have hp := integral_fourier_pair 0 m
    simp only [fourier_zero, map_one, one_mul,
      ite_eq_right (Ne.symm hm)] at hp
    rw [hp, mul_zero]
  simp_rw [he]
  simp

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

lemma integral_fourier_haar (n : ℤ) :
    (∫ z : UnitAddCircle, fourier n z ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have hh := integral_fourier_pair 0 n
  simpa only [fourier_zero, map_one, one_mul, eq_comm] using hh

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

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_integral_zero {m : ι → ℤ} (hm : ∀ i, m i ≠ 0)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x, finitePacketVector m A x ∂tripleVolume) = 0 := by
  change (∫ x, ∑ i, packet (m i) (A i) x ∂tripleVolume) = 0
  rw [integral_finsetSum _
    (fun i _ => (memLp_packet (hA i) (m i)).integrable (by norm_num))]
  simp_rw [packet_integral_zero (hA _) (hm _)]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_twist (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (n : ℤ) (x : TripleTorus) :
    finitePacketVector m A (twistIter φ n x) =
      finitePacketVector m (fun i ua => fourier n (m i • φ ua.1) * A i ua) x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [packet_twistIter]
  dsimp only [packet]
  ring

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_correlation {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x) * finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) =
      ∑ i, ∫ ua, fourier n (m i • φ ua.1) * (‖A i ua‖^2 : ℝ) ∂slowVolume := by
  simp_rw [finitePacket_twist]
  have hB : ∀ i, MemLp (fun ua => fourier n (m i • φ ua.1) * A i ua) 2 slowVolume :=
    fun i => memLp_frequency_mul (hA i) ((hφ.comp measurable_fst).const_smul (m i)) n
  rw [finitePacket_inner hm hA hB]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with ua
  rw [show conj (A i ua) * (fourier n (m i • φ ua.1) * A i ua) =
    fourier n (m i • φ ua.1) * (conj (A i ua) * A i ua) by ring, normSq_complex]

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

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_real {m : ι → ℤ} (r : ι → ι) (hr : Involutive r)
    (hm : ∀ i, m (r i) = -m i) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i ua, A (r i) ua = conj (A i ua)) (x : TripleTorus) :
    conj (finitePacketVector m A x) = finitePacketVector m A x := by
  classical
  have he : ∀ i, conj (packet (m i) (A i) x) = packet (m (r i)) (A (r i)) x := by
    intro i
    simp only [packet,map_mul,hm,hA,fourier_neg]
  simp only [finitePacketVector,map_sum,he]
  exact Equiv.sum_comp (Involutive.toPerm r hr) (fun i => packet (m i) (A i) x)

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

/-! Literal measurable finite-packet spectral calculus and Laurent approximation.
No abstract unitary is substituted for the actual twist. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma finite_energy_measure {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : X → ℂ}
    (hF : MemLp F 2 μ) : IsFiniteMeasure (μ.withDensity (energyWeight F)) := by
  apply isFiniteMeasure_withDensity
  have hf := (hasFiniteIntegral_iff_norm _).1
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).hasFiniteIntegral
  simpa only [energyWeight,Real.norm_eq_abs,abs_pow,abs_norm] using hf.ne

lemma packetSpectralMeasure_finite {φ : UnitAddCircle → UnitAddCircle} (m : ℤ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : MemLp A 2 slowVolume) :
    IsFiniteMeasure (packetSpectralMeasure φ m A) := by
  let := finite_energy_measure hA
  exact Measure.isFiniteMeasure_map (slowVolume.withDensity (energyWeight A)) _

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finitePacket_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) = ∫ z, fourier n z ∂finitePacketSpectralMeasure φ m A := by
  rw [finitePacketSpectralMeasure_eq_sum hφ m hAm,integral_finsetSum_measure]
  · rw [finitePacket_correlation hφ hm hA n]
    apply Finset.sum_congr rfl
    intro i _
    rw [packet_spectral_moment_L2 hφ (hAm i) (hA i),packet_correlation_L2 (hA i) hφ]
  · intro i _
    let := packetSpectralMeasure_finite (φ := φ) (m i) (hA i)
    exact (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma finitePacket_flat_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) = if n = 0 then 1 else 0 := by
  rw [finitePacket_spectral_moment hφ hm hAm hA,hflat]
  exact integral_fourier_haar n

end FinitePacket
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
lemma vector_centered : (∫ x, F.vector x ∂tripleVolume) = 0 :=
  finitePacket_integral_zero F.nonzero F.memLp
lemma vector_real {τ : F.Index → F.Index} (hr : F.Reflection τ) (x : TripleTorus) :
    conj (F.vector x) = F.vector x := finitePacketVector_real τ hr.1 hr.2.1 hr.2.2 x
lemma spectrum_eq [MeasurableSpace F.Index] [MeasurableSingletonClass F.Index]
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) :
    F.spectrum φ = finitePacketSpectralMeasure φ F.m F.A :=
  (finitePacketSpectralMeasure_eq_sum hφ F.m F.measurable).symm

lemma flat_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hflat : F.spectrum φ = phaseHaar) (n : ℤ) :
    (∫ x, conj (F.vector x)*F.vector (twistIter φ n x) ∂tripleVolume) =
      if n = 0 then 1 else 0 := by
  let : MeasurableSpace F.Index := ⊤
  let : MeasurableSingletonClass F.Index := ⟨fun _ => trivial⟩
  exact finitePacket_flat_moment hφ F.injective F.measurable F.memLp
    ((F.spectrum_eq hφ).symm.trans hflat) n
end MeasurablePackets

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Stages
attribute [-instance] _root_.OAI.ThreeTorus.PhysicalTest.instNonempty _root_.OAI.ThreeTorus.PhysicalTest.instSecondCountableTopology _root_.OAI.ThreeTorus.PhysicalTest.instTopologicalSpace _root_.OAI.ThreeTorus.StageState.instTopologicalSpace _root_.OAI.ThreeTorus.tripleVolume_regular
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

namespace StageState
variable (s : StageState)
lemma vec_ae : s.vec =ᵐ[tripleVolume] s.vector := MemLp.coeFn_toLp _

lemma mapPow_apply (k : ℤ) (x : TripleTorus) :
    s.mapPow k x = s.frame.chart.symm (twistIter s.speed k (s.frame.chart x)) := by
  rfl
lemma mapPow_add (k j : ℤ) (x : TripleTorus) :
    s.mapPow (k+j) x = s.mapPow k (s.mapPow j x) := by
  simp only [mapPow_apply,s.frame.chart.apply_symm_apply,twistIter_add]
lemma mapPow_zero (x : TripleTorus) : s.mapPow 0 x = x := by
  simp [mapPow_apply,twistIter]
lemma mapPow_graph (k : ℤ) (x : Cover) :
    tripleProject (s.frame.mapLift s.V k x) = s.mapPow k (tripleProject x) := by
  rw [PhysicalFrame.mapLift,Function.comp_apply,Function.comp_apply,s.frame.backward_graph]
  rw [mapPow_apply,← s.frame.forward_graph]
  congr 1
  change (((s.frame.forward x 0+(k:ℝ)*s.V (s.frame.forward x 1):ℝ):UnitAddCircle),
    (s.frame.forward x 1:UnitAddCircle),(s.frame.forward x 2:UnitAddCircle)) = _
  change (((s.frame.forward x 0+(k:ℝ)*s.V (s.frame.forward x 1):ℝ):UnitAddCircle),
    (s.frame.forward x 1:UnitAddCircle),(s.frame.forward x 2:UnitAddCircle)) =
    ((s.frame.forward x 0:UnitAddCircle)+k • (s.V (s.frame.forward x 1):UnitAddCircle),
      (s.frame.forward x 1:UnitAddCircle),(s.frame.forward x 2:UnitAddCircle))
  simp only [AddCircle.coe_add,← zsmul_eq_mul,AddCircle.coe_zsmul]

lemma vector_centered : ∫ x, s.vector x ∂tripleVolume = 0 := by
  simp only [vector,Function.comp_apply]
  rw [s.chart_mp.integral_comp s.chartHomeo.toMeasurableEquiv.measurableEmbedding]
  exact s.packets.vector_centered
lemma vector_real (x : TripleTorus) : conj (s.vector x)=s.vector x := by
  obtain ⟨τ,hτ⟩ := s.reflected
  exact s.packets.vector_real hτ _

lemma orbit_ae (k : ℤ) : s.orbit k =ᵐ[tripleVolume] fun x => s.vector (s.mapPow k x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving s.vec (s.mapPow_mp k),
    (s.mapPow_mp k).quasiMeasurePreserving.ae s.vec_ae] with x hx hy
  exact hx.trans hy

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace PhysicalTest
variable (h : PhysicalTest)
lemma vec_ae : h.vec =ᵐ[tripleVolume] h.fn := MemLp.coeFn_toLp _
end PhysicalTest

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_SmoothLimits
attribute [-instance] _root_.OAI.ThreeTorus.StageState.instTopologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-order local smooth jet limits, positive and negative iterate diagonal, cover descent, and volume preservation. -/

section

noncomputable section
open Set Function Filter
open scoped Topology ContDiff
namespace ThreeTorus

/-- Locally uniform limits of EVERY actual spatial jet are a smooth map.
The limiting derivative data are not an assumed smooth diagonal. -/
theorem smooth_of_jet_limits {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℕ → E → F) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (q : (d : ℕ) → E → E [×d]→L[ℝ] F)
    (hq : ∀ d, TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ d (f n)) (q d) atTop) :
    ContDiff ℝ ∞ (fun x => (q 0 x).curry0) := by
  refine ⟨fun x d => q d x, ?_⟩
  refine ⟨fun _ => rfl,?_,?_⟩
  · intro d hd x
    let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d+1) => E) F
    have hconv := e.isometry.uniformContinuous.comp_tendstoLocallyUniformly (hq (d+1))
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      hconv.tendstoLocallyUniformlyOn
    · intro n y _
      exact (hf n).ftaylorSeries.fderiv d hd y
    · intro y _
      exact (hq d).tendstoLocallyUniformlyOn.tendsto_at (mem_univ y)
    · trivial
  · intro d hd
    exact (hq d).continuous (.of_forall fun n => (hf n).continuous_iteratedFDeriv hd)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace ThreeTorus

lemma uniform_incrementLimit {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (f : ℕ → X → F) {s : Set X} {b : ℕ → ℝ} (hb : Summable b)
    (h : ∀ᶠ n in atTop, ∀ x ∈ s, dist (f (n+1) x) (f n x) ≤ b n) :
    TendstoUniformlyOn f (incrementLimit f) atTop s := by
  have ht := tendstoUniformlyOn_tsum_nat_eventually hb (h.mono fun n hn x hx =>
    show ‖f (n+1) x-f n x‖ ≤ b n by simpa only [dist_eq_norm] using hn x hx)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hn
  intro x hx
  specialize hn x hx
  rw [Finset.sum_range_sub (fun k => f k x)] at hn
  convert hn using 1
  all_goals try with_reducible_and_instances rfl
  rw [dist_eq_norm,dist_eq_norm,incrementLimit]
  congr 1
  abel

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace ThreeTorus

lemma continuous_tripleProject : Continuous tripleProject := by
  change Continuous (fun x : Cover => ((x 0:UnitAddCircle),(x 1:UnitAddCircle),(x 2:UnitAddCircle)))
  exact ((AddCircle.continuous_mk' 1).comp (continuous_apply 0)).prodMk
    (((AddCircle.continuous_mk' 1).comp (continuous_apply 1)).prodMk
      ((AddCircle.continuous_mk' 1).comp (continuous_apply 2)))

lemma circle_dist_coe_le (x y : ℝ) : dist (x:UnitAddCircle) (y:UnitAddCircle) ≤ dist x y := by
  rw [dist_eq_norm,dist_eq_norm,← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma tripleProject_dist_le (x y : Cover) : dist (tripleProject x) (tripleProject y) ≤ dist x y := by
  change max (dist (x 0:UnitAddCircle) (y 0:UnitAddCircle))
    (max (dist (x 1:UnitAddCircle) (y 1:UnitAddCircle)) (dist (x 2:UnitAddCircle) (y 2:UnitAddCircle))) ≤ _
  exact max_le ((circle_dist_coe_le _ _).trans (dist_le_pi_dist x y 0))
    (max_le ((circle_dist_coe_le _ _).trans (dist_le_pi_dist x y 1))
      ((circle_dist_coe_le _ _).trans (dist_le_pi_dist x y 2)))

lemma tripleProject_section (z : TripleTorus) : tripleProject (tripleSection z)=z := by
  change ((circleRep 0 z.1:UnitAddCircle),(circleRep 0 z.2.1:UnitAddCircle),(circleRep 0 z.2.2:UnitAddCircle))=z
  simp only [coe_circleRep]
lemma tripleSection_norm (z : TripleTorus) : ‖tripleSection z‖ ≤ 1 := by
  apply pi_norm_le_iff_of_nonneg zero_le_one |>.2
  intro i
  have h (w : UnitAddCircle) : ‖circleRep 0 w‖ ≤ 1 := by
    have hw := ((AddCircle.measurableEquivIoc 1 0) w).2
    change 0 < circleRep 0 w ∧ circleRep 0 w ≤ 0+1 at hw
    simpa only [Real.norm_eq_abs,abs_of_pos hw.1,zero_add] using hw.2
  fin_cases i <;> exact h _

/-- Local uniform cover convergence, plus the exact graph equations, descends
uniformly on the compact torus. The section is only a proof device; no
continuity of the measurable representatives is asserted. -/
lemma descend_uniform_limit (f : ℕ → Cover → Cover) (g : Cover → Cover)
    (F : ℕ → TripleTorus → TripleTorus)
    (hg : TendstoLocallyUniformly f g atTop)
    (hgraph : ∀ n x, tripleProject (f n x) = F n (tripleProject x)) :
    TendstoUniformly F (fun z => tripleProject (g (tripleSection z))) atTop := by
  have hc : IsCompact (Metric.closedBall (0:Cover) 1) := isCompact_closedBall _ _
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hg) _ hc
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn
  intro z
  have hz : tripleSection z ∈ Metric.closedBall (0:Cover) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using tripleSection_norm z
  have hh := (tripleProject_dist_le (g (tripleSection z)) (f n (tripleSection z))).trans_lt (hn _ hz)
  simpa only [hgraph,tripleProject_section] using hh

lemma descend_limit_graph (f : ℕ → Cover → Cover) (g : Cover → Cover)
    (F : ℕ → TripleTorus → TripleTorus)
    (hg : TendstoLocallyUniformly f g atTop)
    (hgraph : ∀ n x, tripleProject (f n x) = F n (tripleProject x)) (x : Cover) :
    tripleProject (g (tripleSection (tripleProject x))) = tripleProject (g x) := by
  have h₁ := (descend_uniform_limit f g F hg hgraph).tendsto_at (tripleProject x)
  have h₂ := continuous_tripleProject.continuousAt.tendsto.comp (((tendstoLocallyUniformly_iff_forall_isCompact.mp hg) {x} (isCompact_singleton)).tendsto_at (mem_singleton x))
  have he : (fun n => tripleProject (f n x)) = (fun n => F n (tripleProject x)) := by
    funext n; exact hgraph n x
  change Tendsto (fun n => tripleProject (f n x)) atTop (𝓝 (tripleProject (g x))) at h₂
  rw [he] at h₂
  exact tendsto_nhds_unique h₁ h₂

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma mem_jetIndices {N : ℕ} {k : ℤ} {d : ℕ} :
    (k,d) ∈ jetIndices N ↔ k.natAbs ≤ N ∧ d ≤ N := by
  simp only [jetIndices,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,Finset.mem_range]
  omega

lemma jetExhaustion_close_iff {N : ℕ} {ε : ℝ} {F G : PhysicalFrame} {V W : ℝ → ℝ} :
    (jetExhaustion N).Close ε F V G W ↔
      ∀ k : ℤ, k.natAbs ≤ N → ∀ d : ℕ, d ≤ N → ∀ x : Cover, ‖x‖ ≤ (N:ℝ)+1 →
        dist (iteratedFDeriv ℝ d (G.mapLift W k) x)
          (iteratedFDeriv ℝ d (F.mapLift V k) x) ≤ ε := by
  constructor
  · intro h k hk d hd x hx
    let j : ↥(jetIndices N) := ⟨(k,d),mem_jetIndices.mpr ⟨hk,hd⟩⟩
    let P (q : ℤ × ℕ) : Prop := ∀ y : Cover, ‖y‖ ≤ (N:ℝ)+1 →
      dist (iteratedFDeriv ℝ q.2 (G.mapLift W q.1) y)
        (iteratedFDeriv ℝ q.2 (F.mapLift V q.1) y) ≤ ε
    have hh : P (((Fintype.equivFin ↥(jetIndices N)).symm
        ((Fintype.equivFin ↥(jetIndices N)) j)).val) := by
      intro y hy
      exact h _ y (by simpa only [jetExhaustion,Metric.mem_closedBall,dist_zero_right] using hy)
    have he : ((Fintype.equivFin ↥(jetIndices N)).symm
        ((Fintype.equivFin ↥(jetIndices N)) j)).val = (k,d) :=
      congrArg Subtype.val ((Fintype.equivFin ↥(jetIndices N)).symm_apply_apply j)
    exact (Eq.mp (congrArg P he) hh) x hx
  · intro h i x hx
    let j := (Fintype.equivFin ↥(jetIndices N)).symm i
    have hj := mem_jetIndices.mp j.property
    exact h j.val.1 hj.1 j.val.2 hj.2 x
      (by simpa only [jetExhaustion,Metric.mem_closedBall,dist_zero_right] using hx)

lemma jetExhaustion_mono {M N : ℕ} (hMN : M ≤ N) {ε : ℝ}
    {F G : PhysicalFrame} {V W : ℝ → ℝ}
    (h : (jetExhaustion N).Close ε F V G W) :
    (jetExhaustion M).Close ε F V G W := by
  rw [jetExhaustion_close_iff] at h ⊢
  intro k hk d hd x hx
  exact h k (hk.trans hMN) d (hd.trans hMN) x
    (hx.trans (by exact_mod_cast Nat.add_le_add_right hMN 1))

namespace StageState

lemma mapCont_dist_of_jets {s t : StageState} {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hj : (jetExhaustion N).Close ε s.frame s.V t.frame t.V)
    {k : ℤ} (hk : k.natAbs ≤ N) : dist (mapCont s k) (mapCont t k) ≤ ε := by
  apply (ContinuousMap.dist_le hε).mpr
  intro z
  have hx : ‖tripleSection z‖ ≤ (N:ℝ)+1 :=
    (tripleSection_norm z).trans (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hh := jetExhaustion_close_iff.mp hj k hk 0 (Nat.zero_le _) (tripleSection z) hx
  have h0 (F : Cover → Cover) :
      (continuousMultilinearCurryFin0 ℝ Cover Cover) (iteratedFDeriv ℝ 0 F (tripleSection z)) =
        F (tripleSection z) := by simp
  have hd := (continuousMultilinearCurryFin0 ℝ Cover Cover).dist_map
    (iteratedFDeriv ℝ 0 (t.frame.mapLift t.V k) (tripleSection z))
    (iteratedFDeriv ℝ 0 (s.frame.mapLift s.V k) (tripleSection z))
  rw [h0,h0] at hd
  rw [← hd] at hh
  have he := (tripleProject_dist_le _ _).trans hh
  change dist (s.mapPow k z) (t.mapPow k z) ≤ ε
  simpa only [t.mapPow_graph,s.mapPow_graph,tripleProject_section,dist_comm] using he

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace ThreeTorus

/-- Volume invariance is closed under uniform convergence of continuous maps
on the actual compact torus. No invertibility of the limit is assumed here. -/
lemma measurePreserving_uniform_limit {F : ℕ → C(TripleTorus,TripleTorus)}
    {G : C(TripleTorus,TripleTorus)} (hG : Tendsto F atTop (𝓝 G))
    (hF : ∀ n, MeasurePreserving (F n) tripleVolume tripleVolume) :
    MeasurePreserving G tripleVolume tripleVolume := by
  let : (Measure.map G tripleVolume).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine ⟨G.continuous.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have ht : Tendsto (fun n => ∫ x, f (F n x) ∂tripleVolume) atTop
      (𝓝 (∫ x, f (G x) ∂tripleVolume)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f.toContinuousMap‖)
    · intro n
      exact (f.continuous.comp (F n).continuous).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun x => f.toContinuousMap.norm_coe_le_norm (F n x))
    · exact ae_of_all _ (fun x => f.continuous.continuousAt.tendsto.comp (hG.eval_const x))
  have hconst (n : ℕ) : (∫ x, f (F n x) ∂tripleVolume)=∫ x, f x ∂tripleVolume := by
    change (∫ x, f.toContinuousMap (F n x) ∂tripleVolume)=∫ x, f.toContinuousMap x ∂tripleVolume
    rw [← integral_map (hF n).measurable.aemeasurable f.continuous.aestronglyMeasurable,(hF n).map_eq]
  simp only [hconst] at ht
  change (∫ x, f.toContinuousMap x ∂Measure.map G tripleVolume)=∫ x, f.toContinuousMap x ∂tripleVolume
  rw [integral_map G.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique ht tendsto_const_nhds

end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_DynamicsLimit
attribute [-instance] _root_.OAI.ThreeTorus.PhysicalTest.instNonempty _root_.OAI.ThreeTorus.PhysicalTest.instSecondCountableTopology _root_.OAI.ThreeTorus.PhysicalTest.instTopologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stage topology, genuine smooth limiting dynamics, initial stage, unconditional diagonal, and limiting moments. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace StageState

lemma continuous_coordinate : Continuous coordinate := continuous_induced_dom
lemma continuous_vec : Continuous (fun s : StageState => s.vec) := continuous_coordinate.fst
lemma continuous_mapCont (k : ℤ) : Continuous (fun s : StageState => s.mapCont k) :=
  (continuous_apply k).comp continuous_coordinate.snd
lemma continuous_orbit (k : ℤ) : Continuous (fun s : StageState => s.orbit k) :=
  continuous_vec.compMeasurePreservingLp (continuous_mapCont k) (fun s => s.mapPow_mp k) (by norm_num)
lemma continuous_laurent (c : ℤ →₀ ℂ) : Continuous (fun s : StageState => s.laurent c) := by
  classical
  exact continuous_finsetSum _ (fun k _ => (continuous_orbit k).const_smul (c k))

/-- Finite jets and a physical vector tolerance reach every neighborhood needed
for retaining previously chosen Laurent polynomials. -/
lemma finite_neighborhood_control (s : StageState) {U : Set StageState} (hU : U ∈ 𝓝 s) :
    ∃ N : ℕ, ∃ ε > 0, ∀ t : StageState,
      dist s.vec t.vec < ε → (jetExhaustion N).Close ε s.frame s.V t.frame t.V → t ∈ U := by
  classical
  by_contra hh
  push Not at hh
  have hp (n : ℕ) : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _
  choose t hvt hjt hut using fun n => hh n ((1/2:ℝ)^n) (hp n)
  have hz : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hv : Tendsto (fun n => (t n).vec) atTop (𝓝 s.vec) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds hε))
    exact ⟨N,fun n hn => by simpa only [dist_comm] using (hvt n).trans (hN n hn)⟩
  have hm (k : ℤ) : Tendsto (fun n => (t n).mapCont k) atTop (𝓝 (s.mapCont k)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds hε))
    refine ⟨max N k.natAbs,fun n hn => ?_⟩
    have hh' := mapCont_dist_of_jets (hp n).le (hjt n) (le_trans (le_max_right _ _) hn)
    have hh'' : dist ((t n).mapCont k) (s.mapCont k) ≤ (1/2:ℝ)^n := by
      simpa only [dist_comm] using hh'
    exact hh''.trans_lt (hN n (le_trans (le_max_left _ _) hn))
  have ht : Tendsto t atTop (𝓝 s) := by
    apply (Topology.IsInducing.induced coordinate).tendsto_nhds_iff.mpr
    exact hv.prodMk_nhds (tendsto_pi_nhds.mpr hm)
  obtain ⟨n,hn⟩ := (ht.eventually hU).exists
  exact hut n hn

end StageState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace ThreeTorus

lemma smooth_diagonal_eventual_jets (f : ℕ → Cover → Cover)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) {b : ℕ → ℝ} (hb : Summable b)
    (hstep : ∀ (d : ℕ) (R : ℝ), ∀ᶠ n in atTop, ∀ x : Cover, ‖x‖ ≤ R →
      dist (iteratedFDeriv ℝ d (f (n+1)) x) (iteratedFDeriv ℝ d (f n) x) ≤ b n) :
    ∃ g : Cover → Cover, ContDiff ℝ ∞ g ∧ TendstoLocallyUniformly f g atTop := by
  let q (d : ℕ) := incrementLimit (fun n => iteratedFDeriv ℝ d (f n))
  have hq (d : ℕ) : TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ d (f n)) (q d) atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:Cover)
    apply uniform_incrementLimit _ hb
    filter_upwards [hstep d R] with n hn
    intro x hx
    exact hn x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hx)
  refine ⟨fun x => (q 0 x).curry0,smooth_of_jet_limits f hf q hq,?_⟩
  have hh := (continuousMultilinearCurryFin0 ℝ Cover Cover).isometry.uniformContinuous.comp_tendstoLocallyUniformly (hq 0)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,ContinuousMultilinearMap.curry0_apply,iteratedFDeriv_zero_apply] using hh

/-- Mere summable finite jet changes suffice for the genuine smooth action,
including the inverse and standard volume; every fixed integer power is kept. -/
theorem smooth_dynamics_of_jets (s : ℕ → StageState) {b : ℕ → ℝ} (hb : Summable b)
    (hj : ∀ n, (jetExhaustion n).Close (b n) (s n).frame (s n).V (s (n+1)).frame (s (n+1)).V) :
    ∃ D : SmoothDynamics, ∀ k : ℤ, Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (D.map k)) := by
  have hh (k : ℤ) : ∃ g : Cover → Cover, ContDiff ℝ ∞ g ∧
      TendstoLocallyUniformly (fun n => (s n).frame.mapLift (s n).V k) g atTop := by
    apply smooth_diagonal_eventual_jets _ (fun n => (s n).frame.mapLift_smooth (s n).smooth k) hb
    intro d R
    obtain ⟨N,hN⟩ := exists_nat_ge R
    filter_upwards [eventually_ge_atTop (max N (max k.natAbs d))] with n hn
    intro x hx
    apply jetExhaustion_close_iff.mp (hj n) k (by omega) d (by omega) x
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    linarith
  choose G hGs hGc using hh
  have hu (k : ℤ) := descend_uniform_limit _ (G k) (fun n => (s n).mapPow k) (hGc k)
    (fun n => (s n).mapPow_graph k)
  let T (k : ℤ) : C(TripleTorus,TripleTorus) :=
    ⟨fun z => tripleProject (G k (tripleSection z)),
      (hu k).continuous ((Eventually.of_forall (fun n => (s n).mapPow_cont k)).frequently)⟩
  have hT (k : ℤ) : Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (T k)) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mpr (hu k)
  have h0 (x : TripleTorus) : T 0 x=x := by
    have hh := (hT 0).eval_const x
    have he (n : ℕ) : (s n).mapCont 0 x=x := (s n).mapPow_zero x
    simp only [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hadd (k j : ℤ) (x : TripleTorus) : T (k+j) x=T k (T j x) := by
    have h₁ := (hT (k+j)).eval_const x
    have h₂ := (hT k).eval ((hT j).eval_const x)
    have he : (fun n => (s n).mapCont (k+j) x)=
        (fun n => (s n).mapCont k ((s n).mapCont j x)) := by
      funext n; exact (s n).mapPow_add k j x
    rw [he] at h₁
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨{
    map := T, zero := h0, add := hadd,
    mp := fun k => measurePreserving_uniform_limit (hT k) (fun n => (s n).mapPow_mp k),
    lift := G, smooth := hGs,
    graph := fun k x => (descend_limit_graph _ _ _ (hGc k) (fun n => (s n).mapPow_graph k) x).symm },hT⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- Starting the actual construction needs no dynamical oracle: two reflected
angular packets on a single affine good arc have exactly Haar spectrum. -/
theorem exists_initial_stage {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/8) :
    ∃ s : StageState, s.δ = δ := by
  let cut := lawCutoffs δ hδ hδ'
  let V := neutralJitterReal cut 1 0
  let p := neutralJitterReal_periodic cut 1 0
  let φ := p.lift
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V := neutralJitterReal_smooth cut 1 0
  have hc : Continuous φ := continuous_neutralJitter cut 1 0
  have hv (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) (3/4)) : φ (x:UnitAddCircle)=x := by
    change V x=x
    simpa only [one_mul,add_zero] using neutralJitterReal_affine cut hδ 1 0
      (a := x) (show x ∈ Icc δ (1-δ) by constructor <;> linarith [hx.1,hx.2])
  have hd (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) (3/4)) :
      HasDerivWithinAt (fun y : ℝ => φ (y:UnitAddCircle)) 1 (Icc (1/4:ℝ) (3/4)) x := by
    have he : deriv V x=1 := neutralJitterReal_deriv cut hδ 1 0
      (show x ∈ Ioo δ (1-δ) by constructor <;> linarith [hx.1,hx.2])
    change HasDerivWithinAt V 1 _ x
    rw [← he]
    exact ((hs.differentiable (by simp)).differentiableAt.hasDerivAt).hasDerivWithinAt
  obtain ⟨m,_,hm,t,ht,hlt,hA,hAL,hAr,hp,hn,hAs⟩ := exists_flat_packet_spectra_above
    hc.measurable (measurable_const : Measurable (fun _ : ℝ => (1:ℝ)))
    (show (1/4:ℝ)<3/4 by norm_num) hd
    (by intro x hx y hy hxy; simpa only [hv x hx,hv y hy] using hxy)
    (show Icc (1/4:ℝ) (3/4) ⊆ Ioc (0:ℝ) (0+1) by intro x hx; constructor <;> linarith [hx.1,hx.2]) 0
  let A := fun ua : UnitAddCircle × UnitAddCircle =>
    flatAmplitude 0 (1/4) t (fun _ => (m:ℝ)*1) ua.1
  have hmz : (m:ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  let F : MeasurablePackets := {
    Index := Bool, finite := inferInstance,
    m := fun b => if b then (m:ℤ) else -(m:ℤ),
    injective := by intro b c h; cases b <;> cases c <;> simp_all,
    nonzero := by intro b; cases b <;> simpa using hmz,
    A := fun _ => A, measurable := fun _ => hA, memLp := fun _ => hAL }
  have hr : F.Reflection Bool.not := by
    refine ⟨(by intro b; cases b <;> rfl),?_,?_⟩
    · intro b; cases b <;> simp [F]
    · intro b ua; exact (hAr ua).symm
  have hflat : F.spectrum (fun z => (φ z:UnitAddCircle))=phaseHaar := by
    change (∑ b : Bool, packetSpectralMeasure (fun z => (φ z:UnitAddCircle))
      (if b then (m:ℤ) else -(m:ℤ)) A)=phaseHaar
    simp only [A,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,hp,hn,← add_smul]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hsupport : F.Supported (1/4) (3/4) := by
    intro b ua hua
    obtain ⟨x,hx,hxe⟩ := (hAs hua).1
    exact ⟨⟨x,⟨hx.1,hx.2.trans ht.2⟩,hxe⟩,mem_univ _⟩
  refine ⟨{
    frame := PhysicalFrame.ident,
    chart_cont := continuous_id,
    chart_mp := MeasurePreserving.id _,
    packets := F, reflected := ⟨Bool.not,hr⟩,
    V := V, periodic := p, smooth := hs,
    δ := δ, l := 1/4, u := 3/4, δ_pos := hδ, δ_half := by linarith,
    δ_l := by linarith, l_u := by norm_num, u_δ := by linarith,
    increasing := by intro x hx; rw [neutralJitterReal_deriv cut hδ 1 0 hx]; norm_num,
    supported := hsupport, flat := hflat },rfl⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace StageHistory
variable {test : ℕ → PhysicalTest} {e : ℕ → ℝ} (he : ∀ n, 0 < e n)
include he

lemma exists_start : Nonempty (StageHistory test e 0) := by
  let δ := min ((e 0)^2/16) (1/16:ℝ)
  have hδ : 0 < δ := lt_min (div_pos (sq_pos_of_pos (he 0)) (by norm_num)) (by norm_num)
  obtain ⟨s,hs⟩ := exists_initial_stage hδ (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  refine ⟨⟨s,fun _ => 0,?_,by omega⟩⟩
  rw [hs]
  have hh := min_le_left ((e 0)^2/16) (1/16:ℝ)
  have hp := sq_pos_of_pos (he 0)
  dsimp [δ] at *
  linarith

lemma exists_next {n : ℕ} (a : StageHistory test e n) {b : ℝ} (hb : 0 < b) :
    ∃ t : StageHistory test e (n+1),
      (∀ i < n, t.coeff i=a.coeff i) ∧
      dist a.stage.vec t.stage.vec < b ∧
      (jetExhaustion n).Close b a.stage.frame a.stage.V t.stage.frame t.stage.V := by
  classical
  let U : Set StageState := {s | ∀ i : Fin n,
    dist (test i).vec (s.laurent (a.coeff i)) < e i}
  have hUo : IsOpen U := by
    have hUeq : U = ⋂ i : Fin n, {s : StageState | dist (test i).vec (s.laurent (a.coeff i)) < e i} := by
      ext s; simp only [U,mem_ofPred_eq,mem_iInter]
    rw [hUeq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      (continuous_const.dist (StageState.continuous_laurent (a.coeff i))) continuous_const)
  have hUa : a.stage ∈ U := fun i => a.retained i i.isLt
  obtain ⟨N,ε,hε,hcontrol⟩ := a.stage.finite_neighborhood_control (hUo.mem_nhds hUa)
  let z := min b (ε/2)
  have hz : 0 < z := lt_min hb (half_pos hε)
  obtain ⟨s,c,hsδ,hjs,hvs,hcs⟩ := a.stage.exists_step (test n)
    (jetExhaustion (max n N)) (ε := z) (η := e n/2) (κ := (e (n+1))^2/8) (ζ := z) hz (half_pos (he n))
    (div_pos (sq_pos_of_pos (he (n+1))) (by norm_num)) hz
  have hsU : s ∈ U := hcontrol s
    (hvs.trans_le ((min_le_right _ _).trans (by linarith)))
    ((jetExhaustion_mono (le_max_right n N) hjs).mono
      ((min_le_right _ _).trans (by linarith)))
  have hsq : Real.sqrt (2*a.stage.δ) < e n/2 := by
    apply (Real.sqrt_lt' (half_pos (he n))).mpr
    nlinarith [a.small]
  let t : StageHistory test e (n+1) := {
    stage := s,
    coeff := Function.update a.coeff n c,
    small := hsδ,
    retained := by
      intro i hi
      by_cases hin : i=n
      · subst i
        simp only [Function.update_self]
        exact hcs.trans (by linarith)
      · rw [Function.update_of_ne hin]
        exact hsU ⟨i,by omega⟩ }
  refine ⟨t,?_,hvs.trans_le (min_le_left _ _),
    (jetExhaustion_mono (le_max_left n N) hjs).mono (min_le_left _ _)⟩
  intro i hi
  exact Function.update_of_ne (by omega : i ≠ n) c a.coeff

end StageHistory

/-- A literal diagonal of actual stage states with simultaneously retained
finite polynomials. Only the externally selected real tests occur in the input;
all dynamics, packets and coefficient choices are produced by the stage. -/
theorem exists_stage_diagonal (test : ℕ → PhysicalTest) (e b : ℕ → ℝ)
    (he : ∀ n, 0 < e n) (hb : ∀ n, 0 < b n) :
    ∃ s : ℕ → StageState, ∃ c : ℕ → (ℤ →₀ ℂ),
      (∀ n, dist (s n).vec (s (n+1)).vec < b n) ∧
      (∀ n, (jetExhaustion n).Close (b n) (s n).frame (s n).V
        (s (n+1)).frame (s (n+1)).V) ∧
      (∀ i n, i < n → dist (test i).vec ((s n).laurent (c i)) < e i) := by
  classical
  let next {n : ℕ} (a : StageHistory test e n) : StageHistory test e (n+1) :=
    Classical.choose (a.exists_next he (hb n))
  have hn {n : ℕ} (a : StageHistory test e n) :=
    Classical.choose_spec (a.exists_next he (hb n))
  let a : (n : ℕ) → StageHistory test e n :=
    fun n => Nat.rec (Classical.choice (StageHistory.exists_start (test := test) he))
      (fun _ an => next an) n
  have has (n : ℕ) : a (n+1)=next (a n) := rfl
  have hc (i n : ℕ) (hin : i<n) : (a n).coeff i=(a (i+1)).coeff i := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases h : i=n
      · subst i; rfl
      · rw [has,(hn (a n)).1 i (by omega)]
        exact ih (by omega)
  refine ⟨fun n => (a n).stage,fun i => (a (i+1)).coeff i,?_,?_,?_⟩
  · intro n; exact (hn (a n)).2.1
  · intro n; exact (hn (a n)).2.2
  · intro i n hin
    change dist (test i).vec ((a n).stage.laurent ((a (i+1)).coeff i)) < e i
    rw [← hc i n hin]
    exact (a n).retained i hin

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace StageState
variable (s : StageState)

lemma orbit_comp (k j : ℤ) :
    Lp.compMeasurePreserving (s.mapPow j) (s.mapPow_mp j) (s.orbit k)=s.orbit (k+j) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (s.orbit k) (s.mapPow_mp j),
    (s.mapPow_mp j).quasiMeasurePreserving.ae (s.orbit_ae k),s.orbit_ae (k+j)] with x hx hy hz
  simpa only [Function.comp_apply,hy,hz,s.mapPow_add] using hx

lemma inner_vec_orbit (k : ℤ) : inner ℂ s.vec (s.orbit k)=if k=0 then 1 else 0 := by
  rw [L2.inner_def]
  have he : (fun x => inner ℂ (s.vec x) (s.orbit k x)) =ᵐ[tripleVolume]
      fun x => conj (s.packets.vector (s.frame.chart x))*
        s.packets.vector (twistIter s.speed k (s.frame.chart x)) := by
    filter_upwards [s.vec_ae,s.orbit_ae k] with x hx hy
    rw [hx,hy]
    simp only [vector,mapPow_apply,Function.comp_apply,s.frame.chart.apply_symm_apply,
      RCLike.inner_apply,mul_comm]
  rw [integral_congr_ae he,
    s.chart_mp.integral_comp s.chartHomeo.toMeasurableEquiv.measurableEmbedding
      (g := fun x => conj (s.packets.vector x)*s.packets.vector (twistIter s.speed k x))]
  exact s.packets.flat_moment s.speed_cont.measurable s.flat k

lemma orbit_orthonormal : Orthonormal ℂ s.orbit := by
  rw [orthonormal_iff_ite]
  intro k j
  have hh := (Lp.compMeasurePreservingₗᵢ ℂ (s.mapPow k) (s.mapPow_mp k)).inner_map_map
    s.vec (s.orbit (j-k))
  change inner ℂ (s.orbit k)
    (Lp.compMeasurePreserving (s.mapPow k) (s.mapPow_mp k) (s.orbit (j-k))) = _ at hh
  rw [s.orbit_comp,sub_add_cancel,s.inner_vec_orbit] at hh
  simpa only [sub_eq_zero,eq_comm] using hh

end StageState
end ThreeTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PhysicalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Hilbert space, L2 limiting real orbit, full test density, and complete physical basis. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace ThreeTorus

lemma physicalMeanZero_closed : IsClosed (physicalMeanZero : Set PhysicalL2) := physicalIntegral.isClosed_ker

lemma continuous_physicalCenter : Continuous physicalCenter :=
  continuous_id.sub (physicalIntegral.continuous.smul continuous_const)
lemma physicalCenter_ae (f : PhysicalL2) : physicalCenter f =ᵐ[tripleVolume]
    fun x => f x-physicalIntegral f := by
  filter_upwards [Lp.coeFn_sub f (physicalIntegral f • Lp.const 2 tripleVolume (1:ℂ)),
    Lp.coeFn_smul (physicalIntegral f) (Lp.const 2 tripleVolume (1:ℂ)),
    Lp.coeFn_const 2 tripleVolume (1:ℂ)] with x hx hy hz
  simpa only [physicalCenter,Pi.sub_apply,Pi.smul_apply,hy,hz,Function.const_apply,smul_eq_mul,mul_one] using hx
lemma physicalCenter_eq_self {f : PhysicalL2} (hf : f ∈ physicalMeanZero) : physicalCenter f=f := by
  change physicalIntegral f=0 at hf
  simp only [physicalCenter,hf,zero_smul,sub_zero]

lemma continuousCenter_centered (g : C(TripleTorus,ℂ)) :
    ∫ x, continuousCenter g x ∂tripleVolume=0 := by
  change (∫ x, g x-(∫ y, g y ∂tripleVolume) ∂tripleVolume)=0
  rw [integral_sub ((continuous_triple_memLp g.continuous).integrable (by norm_num)) (integrable_const _)]
  simp
lemma toLp_continuousCenter (g : C(TripleTorus,ℂ)) :
    ContinuousMap.toLp 2 tripleVolume ℂ (continuousCenter g)=
      physicalCenter (ContinuousMap.toLp 2 tripleVolume ℂ g) := by
  apply Lp.ext
  have hg := ContinuousMap.coeFn_toLp tripleVolume (𝕜 := ℂ) (p := 2) g
  have hi : physicalIntegral (ContinuousMap.toLp 2 tripleVolume ℂ g)=∫ x, g x ∂tripleVolume := by
    rw [physicalIntegral_apply,integral_congr_ae hg]
  filter_upwards [ContinuousMap.coeFn_toLp tripleVolume (𝕜 := ℂ) (p := 2) (continuousCenter g),
    physicalCenter_ae (ContinuousMap.toLp 2 tripleVolume ℂ g),hg] with x hx hy hz
  rw [hx,hy]
  change g x - (∫ y, g y ∂tripleVolume)=_
  rw [hi,hz]

lemma physical_real_closed : IsClosed {f : PhysicalL2 | ∀ᵐ x ∂tripleVolume, (f x).im=0} := by
  let I : PhysicalL2 →L[ℝ] Lp ℝ 2 tripleVolume := Complex.imCLM.compLpL 2 tripleVolume
  have he : {f : PhysicalL2 | ∀ᵐ x ∂tripleVolume, (f x).im=0}={f | I f=0} := by
    ext f
    constructor
    · intro h
      apply Lp.ext
      filter_upwards [Complex.imCLM.coeFn_compLp f,h,Lp.coeFn_zero ℝ 2 tripleVolume] with x hx hy hz
      exact hx.trans (hy.trans hz.symm)
    · intro h
      filter_upwards [Complex.imCLM.coeFn_compLp f,Lp.coeFn_zero ℝ 2 tripleVolume] with x hx hz
      change I f x=(f x).im at hx
      rw [h,hz] at hx
      exact hx.symm
  rw [he]
  exact isClosed_eq I.continuous continuous_const

namespace PhysicalTest
lemma vec_eq_toLp (h : PhysicalTest) : h.vec=ContinuousMap.toLp 2 tripleVolume ℂ h.fn := by
  apply Lp.ext
  exact h.vec_ae.trans (ContinuousMap.coeFn_toLp tripleVolume h.fn).symm
lemma continuous_vec : Continuous (fun h : PhysicalTest => h.vec) := by
  have hh : Continuous (fun h : PhysicalTest => ContinuousMap.toLp 2 tripleVolume ℂ h.fn) :=
    (ContinuousMap.toLp 2 tripleVolume ℂ).continuous.comp
      (continuous_induced_dom : Continuous PhysicalTest.fn)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  exact funext vec_eq_toLp
end PhysicalTest

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace SmoothDynamics
variable (D : SmoothDynamics)

lemma orbit_ae (f : PhysicalL2) (k : ℤ) : D.orbit f k =ᵐ[tripleVolume]
    fun x => f (D.map k x) := Lp.coeFn_compMeasurePreserving f (D.mp k)
lemma orbit_centered {f : PhysicalL2} (hf : f ∈ physicalMeanZero) (k : ℤ) :
    D.orbit f k ∈ physicalMeanZero := by
  rw [mem_physicalMeanZero,integral_congr_ae (D.orbit_ae f k),
    (D.mp k).integral_comp (D.homeo k).toMeasurableEquiv.measurableEmbedding]
  exact (mem_physicalMeanZero f).mp hf

lemma laurent_mem_span (f : PhysicalL2) (c : ℤ →₀ ℂ) :
    D.laurent f c ∈ Submodule.span ℂ (Set.range (D.orbit f)) := by
  classical
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩))

lemma tendsto_orbit {s : ℕ → StageState} {f : PhysicalL2}
    (hf : Tendsto (fun n => (s n).vec) atTop (𝓝 f))
    (hT : ∀ k, Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (D.map k))) (k : ℤ) :
    Tendsto (fun n => (s n).orbit k) atTop (𝓝 (D.orbit f k)) :=
  hf.compMeasurePreservingLp (hT k) (fun n => (s n).mapPow_mp k) (D.mp k) (by norm_num)
lemma tendsto_laurent {s : ℕ → StageState} {f : PhysicalL2}
    (hf : Tendsto (fun n => (s n).vec) atTop (𝓝 f))
    (hT : ∀ k, Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (D.map k))) (c : ℤ →₀ ℂ) :
    Tendsto (fun n => (s n).laurent c) atTop (𝓝 (D.laurent f c)) := by
  classical
  exact tendsto_finsetSum _ (fun k _ => (D.tendsto_orbit hf hT k).const_smul (c k))
end SmoothDynamics

/-- The diagonal produces an actual real centered vector and exact bilateral
orthonormality, while retaining EVERY earlier polynomial in the same limit map. -/
theorem exists_physical_limit (test : ℕ → PhysicalTest) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n) :
    ∃ D : SmoothDynamics, ∃ f : PhysicalL2,
      f ∈ physicalMeanZero ∧ (∀ᵐ x ∂tripleVolume, (f x).im=0) ∧
      Orthonormal ℂ (D.orbit f) ∧
      ∃ c : ℕ → (ℤ →₀ ℂ), ∀ i, dist (test i).vec (D.laurent f (c i)) ≤ e i := by
  let b (n : ℕ) : ℝ := (1/2)^n
  have hb (n : ℕ) : 0 < b n := pow_pos (by norm_num) _
  have hbs : Summable b := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨s,c,hv,hj,hc⟩ := exists_stage_diagonal test e b he hb
  have hC : CauchySeq (fun n => (s n).vec) :=
    cauchySeq_of_dist_le_of_summable b (fun n => (hv n).le) hbs
  obtain ⟨f,hf⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨D,hT⟩ := smooth_dynamics_of_jets s hbs hj
  have hf0 : f ∈ physicalMeanZero := physicalMeanZero_closed.mem_of_tendsto hf
    (Eventually.of_forall (fun n => by
      change (s n).vec ∈ physicalMeanZero
      rw [mem_physicalMeanZero,integral_congr_ae (s n).vec_ae,(s n).vector_centered]))
  have hfr : ∀ᵐ x ∂tripleVolume, (f x).im=0 := physical_real_closed.mem_of_tendsto hf
    (Eventually.of_forall (fun n => by
      filter_upwards [(s n).vec_ae] with x hx
      rw [hx]
      exact Complex.conj_eq_iff_im.mp ((s n).vector_real x)))
  have ho : Orthonormal ℂ (D.orbit f) := by
    rw [orthonormal_iff_ite]
    intro k j
    have hL := (D.tendsto_orbit hf hT k).inner (𝕜 := ℂ) (D.tendsto_orbit hf hT j)
    have hE (n : ℕ) : inner ℂ ((s n).orbit k) ((s n).orbit j)=if k=j then 1 else 0 :=
      orthonormal_iff_ite.mp (s n).orbit_orthonormal k j
    simp only [hE] at hL
    exact tendsto_nhds_unique hL tendsto_const_nhds
  refine ⟨D,f,hf0,hfr,ho,c,fun i => ?_⟩
  exact le_of_tendsto (tendsto_const_nhds.dist (D.tendsto_laurent hf hT (c i)))
    (eventually_atTop.mpr ⟨i+1,fun n hn => (hc i n (by omega)).le⟩)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace ThreeTorus

/-- Every real centered continuous vector belongs to the linear span of the
bounded physical tests, with its actual normalization scalar. -/
lemma continuous_real_mem_of_tests (K : Submodule ℂ PhysicalL2)
    (hK : ∀ h : PhysicalTest, h.vec ∈ K)
    (g : C(TripleTorus,ℂ)) (hg : ∀ x, conj (g x)=g x)
    (hgc : ∫ x, g x ∂tripleVolume=0) : ContinuousMap.toLp 2 tripleVolume ℂ g ∈ K := by
  let M : ℝ := ‖g‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMc : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let h : PhysicalTest := {
    fn := (M:ℂ)⁻¹ • g,
    real := by
      intro x
      simp only [ContinuousMap.smul_apply,smul_eq_mul,map_mul,map_inv₀,Complex.conj_ofReal,hg],
    centered := by
      change (∫ x, (M:ℂ)⁻¹ • g x ∂tripleVolume)=0
      rw [integral_smul,hgc,smul_zero],
    bound := by
      intro x
      simp only [ContinuousMap.smul_apply,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
      have hx := g.norm_coe_le_norm x
      rw [inv_mul_eq_div]
      exact (div_le_one hM).mpr (hx.trans (by dsimp [M]; linarith)) }
  have hh : h.vec=(M:ℂ)⁻¹ • ContinuousMap.toLp 2 tripleVolume ℂ g := by
    rw [PhysicalTest.vec_eq_toLp]
    exact map_smul (ContinuousMap.toLp 2 tripleVolume ℂ) _ _
  have hm := K.smul_mem (M:ℂ) (hK h)
  rw [hh,smul_smul,mul_inv_cancel₀ hMc,one_smul] at hm
  exact hm

lemma continuous_centered_mem_of_tests (K : Submodule ℂ PhysicalL2)
    (hK : ∀ h : PhysicalTest, h.vec ∈ K)
    (g : C(TripleTorus,ℂ)) (hgc : ∫ x, g x ∂tripleVolume=0) :
    ContinuousMap.toLp 2 tripleVolume ℂ g ∈ K := by
  let r : C(TripleTorus,ℂ) := ⟨fun x => ((g x).re:ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp g.continuous)⟩
  let j : C(TripleTorus,ℂ) := ⟨fun x => ((g x).im:ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp g.continuous)⟩
  have hi : Integrable g tripleVolume := (continuous_triple_memLp g.continuous).integrable (by norm_num)
  have hr : ∫ x, r x ∂tripleVolume=0 := by
    change (∫ x, ((g x).re:ℂ) ∂tripleVolume)=0
    rw [integral_complex_ofReal]
    have hh := integral_re hi
    change (∫ x, (g x).re ∂tripleVolume)=(∫ x, g x ∂tripleVolume).re at hh
    rw [hh,hgc]
    simp
  have hj : ∫ x, j x ∂tripleVolume=0 := by
    change (∫ x, ((g x).im:ℂ) ∂tripleVolume)=0
    rw [integral_complex_ofReal]
    have hh := integral_im hi
    change (∫ x, (g x).im ∂tripleVolume)=(∫ x, g x ∂tripleVolume).im at hh
    rw [hh,hgc]
    simp
  have he : g=r+Complex.I • j := by
    ext x
    change g x=((g x).re:ℂ)+Complex.I*((g x).im:ℂ)
    simpa only [mul_comm] using (Complex.re_add_im (g x)).symm
  rw [he,map_add,map_smul]
  exact K.add_mem (continuous_real_mem_of_tests K hK r (by intro x; exact Complex.conj_ofReal _) hr)
    (K.smul_mem Complex.I (continuous_real_mem_of_tests K hK j (by intro x; exact Complex.conj_ofReal _) hj))

/-- Bounded real tests exhaust the FULL complex centered L2 space, not just a
real or cyclic subspace. -/
lemma physical_tests_total (K : Submodule ℂ PhysicalL2) (hclosed : IsClosed (K : Set PhysicalL2))
    (hK : ∀ h : PhysicalTest, h.vec ∈ K) {f : PhysicalL2} (hf : f ∈ physicalMeanZero) : f ∈ K := by
  have hd : DenseRange (ContinuousMap.toLp 2 tripleVolume ℂ : C(TripleTorus,ℂ) →L[ℂ] PhysicalL2) :=
    ContinuousMap.toLp_denseRange ℂ tripleVolume ℂ (p := 2) (by norm_num)
  have hh : physicalCenter f ∈ K := by
    apply hd.induction_on (p := fun x => physicalCenter x ∈ K) f (hclosed.preimage continuous_physicalCenter)
    intro g
    rw [← toLp_continuousCenter]
    exact continuous_centered_mem_of_tests K hK _ (continuousCenter_centered g)
  rwa [physicalCenter_eq_self hf] at hh

/-- A single honest countable family of real bounded centered continuous tests
suffices. Its full complex span is dense after closure. -/
theorem exists_total_physical_tests : ∃ test : ℕ → PhysicalTest,
    ∀ K : Submodule ℂ PhysicalL2, IsClosed (K : Set PhysicalL2) →
      (∀ n, (test n).vec ∈ K) → ∀ f ∈ physicalMeanZero, f ∈ K := by
  obtain ⟨test,htest⟩ := TopologicalSpace.exists_dense_seq PhysicalTest
  refine ⟨test,fun K hclosed hK f hf => physical_tests_total K hclosed ?_ hf⟩
  intro h
  exact htest.induction_on h (hclosed.preimage PhysicalTest.continuous_vec) hK

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Unconditional geometric spectral basis on the physical product torus.
The closure here is exactly the FULL complex kernel of the volume integral. -/
theorem exists_physical_basis_oai : ∃ D : SmoothDynamics, ∃ f : PhysicalL2,
    f ∈ physicalMeanZero ∧ (∀ᵐ x ∂tripleVolume, (f x).im=0) ∧
    Orthonormal ℂ (D.orbit f) ∧
    (Submodule.span ℂ (Set.range (D.orbit f))).topologicalClosure=physicalMeanZero := by
  obtain ⟨test,htest⟩ := exists_total_physical_tests
  let a (n : ℕ) := test (Nat.unpair n).1
  let e (n : ℕ) : ℝ := (1/2)^((Nat.unpair n).2)
  have he (n : ℕ) : 0 < e n := pow_pos (by norm_num) _
  obtain ⟨D,f,hf,hfr,ho,c,hc⟩ := exists_physical_limit a e he
  let S := Submodule.span ℂ (Set.range (D.orbit f))
  have htestmem (i : ℕ) : (test i).vec ∈ S.topologicalClosure := by
    change (test i).vec ∈ closure (S : Set PhysicalL2)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hz : Tendsto (fun m : ℕ => (1/2:ℝ)^m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨m,hm⟩ := (hz.eventually (gt_mem_nhds hε)).exists
    refine ⟨D.laurent f (c (Nat.pair i m)),D.laurent_mem_span f _,?_⟩
    have hh := hc (Nat.pair i m)
    simp only [a,e,Nat.unpair_pair] at hh
    exact hh.trans_lt hm
  refine ⟨D,f,hf,hfr,ho,le_antisymm ?_ ?_⟩
  · exact S.topologicalClosure_minimal
      (Submodule.span_le.mpr (by rintro _ ⟨k,rfl⟩; exact D.orbit_centered hf k))
      physicalMeanZero_closed
  · exact fun g hg => htest S.topologicalClosure S.isClosed_topologicalClosure htestmem g hg

end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exists_physical_basis_oai := @OAI.ThreeTorus.exists_physical_basis_oai
