-- Prove2me | solution 1 for OAI.SignedDisk.CommonPrices.physical_joint_price
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:32:10.093988+00:00
-- url     : https://prove2.me/submissions/62df0e2f-5ddc-421f-83ec-1ef557b57806

import Mathlib
import Definitions.Def_OAIW2SD000
import Theorems.Thm_OAI_SignedDisk_CommonPrices_physical_size_price

section
-- module Solutions.OAIW2_SignedDisk.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskGeometry2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace

noncomputable section

namespace SignedDisk

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

namespace DiskMoments

lemma integral_translate_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, f (x + z)) = ∫ y in Metric.ball x r, f y := by
  have hpre : (fun z : ℂ => x + z) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x r)
  rwa [hpre] at h

lemma integral_scale_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, f (t • z)) =
      (t^2)⁻¹ • ∫ z in Metric.ball (0 : ℂ) t, f z := by
  convert Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball 0 1) ht using 1
  rw [Complex.finrank_real_complex, smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht, mul_one]

lemma signedAverage_fixedDomain (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage g x t = (∫ z in Metric.ball (0 : ℂ) 1, g (x + t • z)) / Real.pi := by
  rw [integral_scale_ball (fun z => g (x+z)) ht, integral_translate_ball]
  simp only [signedAverage, smul_eq_mul]
  ring

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal

noncomputable section

namespace SignedDisk

namespace LocalCancellation

lemma ErrorPiece.mass_nonneg {Cs : ℝ} (b : ErrorPiece Cs) : 0 ≤ b.mass :=
  integral_nonneg (fun _ => norm_nonneg _)

end LocalCancellation

open MeasureTheory Set Filter
open scoped Topology NNReal Real

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace DiskMaximalTools

lemma volume_dilate_five (x : ℂ) (r : ℝ) :
    volume (ball x (5*r)) = 25 * volume (ball x r) := by
  rw [Complex.volume_ball, Complex.volume_ball, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num [mul_pow]
  ring

/-- The actual Vitali weak-(1,1) estimate, with no assumed maximal inequality. -/
theorem weak_bound_bounded_family {ι : Type*} (t : Set ι) (x : ι → ℂ) (r : ι → ℝ)
    (ν : Measure ℂ) {R a : ℝ} (ha : 0 < a)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (hav : ∀ i ∈ t, ENNReal.ofReal a * volume (ball (x i) (r i)) ≤ ν (ball (x i) (r i))) :
    volume (⋃ i ∈ t, ball (x i) (r i)) ≤ (25 / ENNReal.ofReal a) * ν univ := by
  obtain ⟨u,hut,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    t x r R hR 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun i hi => ⟨x i,mem_ball_self (hr i (hut hi))⟩)
  have : Countable u := huc.to_subtype
  have hsub : (⋃ i ∈ t, ball (x i) (r i)) ⊆ ⋃ i : u, ball (x i) (5*r i) := by
    intro y hy
    obtain ⟨i,hi,hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hij hy⟩
  have hmass : (∑' i : u, ν (ball (x i) (r i))) ≤ ν univ := by
    rw [← measure_iUnion (fun (i j : u) hij => hdisj i.property j.property (fun h => hij (Subtype.ext h)))
      (fun _ => measurableSet_ball)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ volume (⋃ i : u, ball (x i) (5*r i)) := measure_mono hsub
    _ ≤ ∑' i : u, volume (ball (x i) (5*r i)) := measure_iUnion_le _
    _ = ∑' i : u, 25 * volume (ball (x i) (r i)) := by simp_rw [volume_dilate_five]
    _ ≤ ∑' i : u, (25 / ENNReal.ofReal a) * ν (ball (x i) (r i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hb := hav i (hut i.property)
      calc
        _ = (25 / ENNReal.ofReal a) * (ENNReal.ofReal a * volume (ball (x i) (r i))) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top]
        _ ≤ _ := by gcongr
    _ = (25 / ENNReal.ofReal a) * ∑' i : u, ν (ball (x i) (r i)) := by rw [ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

lemma volume_disk_real (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [Complex.volume_ball,ENNReal.ofReal_mul Real.pi_nonneg,ENNReal.ofReal_pow hr]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  exact mul_comm _ _

/-- All high-average balls of a finite measure have a common finite radius
bound; the bounded-family Vitali argument therefore controls every radius. -/
theorem weak_bound {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x : ℂ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal a * volume (ball x r) ≤ ν (ball x r)} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  let t : Set (ℂ × ℝ) := {p | 0 < p.2 ∧
    ENNReal.ofReal a * volume (ball p.1 p.2) ≤ ν (ball p.1 p.2)}
  let B : ℝ := (ν univ).toReal/(a*Real.pi)
  have hB : 0 ≤ B := div_nonneg ENNReal.toReal_nonneg (mul_pos ha Real.pi_pos).le
  have hR : ∀ p ∈ t, p.2 ≤ B+1 := by
    intro p hp
    have hh := hp.2.trans (measure_mono (subset_univ _))
    rw [volume_disk_real _ hp.1.le,← ENNReal.ofReal_mul ha.le] at hh
    have hh' : a*(Real.pi*p.2^2) ≤ (ν univ).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hh
    have hs : p.2^2 ≤ B := (le_div_iff₀ (mul_pos ha Real.pi_pos)).mpr (by nlinarith)
    nlinarith [sq_nonneg (p.2-1)]
  have hweak := weak_bound_bounded_family t Prod.fst Prod.snd ν ha
    (fun _ hp => hp.1) hR (fun _ hp => hp.2)
  apply le_trans (measure_mono ?_) hweak
  intro x hx
  obtain ⟨r,hr,havg⟩ := hx
  exact mem_iUnion₂.mpr ⟨(x,r),⟨hr,havg⟩,mem_ball_self hr⟩

lemma measurable_ball_mass (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (ball x r)) := by
  have hm : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} :=
    isOpen_lt (continuous_snd.dist continuous_fst) continuous_const |>.measurableSet
  exact measurable_measure_prodMk_left hm

lemma measurable_rationalMaximal (ν : Measure ℂ) [SFinite ν] :
    Measurable (rationalMaximal ν) := by
  unfold rationalMaximal
  apply Measurable.iSup
  intro q
  apply Measurable.iSup
  intro _
  have hd : Measurable (fun x : ℂ => volume (ball x (q:ℝ))) := by
    simp only [Complex.volume_ball]
    exact measurable_const
  exact (measurable_ball_mass ν (q:ℝ)).div hd

/-- Truncating an input below half the testing height sharpens weak type by
charging only its large values. This is the interpolation mechanism. -/
lemma weak_split {ν η : Measure ℂ} [IsFiniteMeasure η] {a : ℝ} (ha : 0 < a)
    (hsplit : ∀ x r, 0 < r → ν (ball x r) ≤ η (ball x r)+
      ENNReal.ofReal (a/2)*volume (ball x r)) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal (a/2)) * η univ := by
  apply le_trans (measure_mono ?_) (weak_bound (by linarith : 0 < a/2))
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  have hh' := (ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh
  refine ⟨q,hq',?_⟩
  by_contra h
  have hη : η (ball x (q:ℝ)) ≤ ENNReal.ofReal (a/2)*volume (ball x (q:ℝ)) := (lt_of_not_ge h).le
  have hfull := (hsplit x q hq').trans (add_le_add hη le_rfl)
  have hsum : ENNReal.ofReal (a/2)+ENNReal.ofReal (a/2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ a/2) (by linarith : 0 ≤ a/2)]
    congr 1
    ring
  rw [← add_mul,hsum] at hfull
  exact (not_lt_of_ge hfull) hh'

lemma weak_truncated {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure (volume.withDensity f)] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal (volume.withDensity f) x} ≤
      (25 / ENNReal.ofReal (a/2)) *
        ∫⁻ x, {x | ENNReal.ofReal (a/2) < f x}.indicator f x := by
  let H := {x | ENNReal.ofReal (a/2) < f x}
  let η := volume.withDensity (H.indicator f)
  have hle : η ≤ volume.withDensity f := withDensity_mono (ae_of_all _ (indicator_le_self _ _))
  have : IsFiniteMeasure η := isFiniteMeasure_of_le _ hle
  have hweak := weak_split (ν := volume.withDensity f) (η := η) ha ?_
  · simpa only [η,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ] using hweak
  · intro x r _
    rw [withDensity_apply _ measurableSet_ball,show η = volume.withDensity (H.indicator f) from rfl,
      withDensity_apply _ measurableSet_ball]
    calc
      _ ≤ ∫⁻ y in ball x r, H.indicator f y+ENNReal.ofReal (a/2) := by
        apply lintegral_mono
        intro y
        dsimp only
        by_cases hy : y ∈ H
        · rw [indicator_of_mem hy]
          exact le_add_right le_rfl
        · rw [indicator_of_notMem hy,zero_add]
          exact le_of_not_gt hy
      _ = _ := by
        rw [lintegral_add_left (hf.indicator (measurableSet_lt measurable_const hf))]
        simp only [lintegral_const,Measure.restrict_apply_univ]
        rfl

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DiskMaximalTools

lemma lintegral_rpow_Ioo {b s : ℝ} (hb : 0 ≤ b) (hs : -1 < s) :
    (∫⁻ t in Ioo 0 b, ENNReal.ofReal (t^s)) = ENNReal.ofReal (b^(s+1)/(s+1)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
  · have hi : IntegrableOn (fun t : ℝ => t^s) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr hs
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.le,
        integral_rpow (Or.inl hs)]
      simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _

lemma truncation_layer_single {b p : ℝ} (hb : 0 ≤ b) (hp : 1 < p) :
    (∫⁻ t in Ioi 0, (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal (b^p) := by
  have heq : (fun t : ℝ => (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      (Iio (2*b)).indicator (fun t => ENNReal.ofReal b * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases ht : t < 2*b <;> simp [ht]
  rw [heq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio (2*b) ∩ Ioi (0:ℝ) = Ioo 0 (2*b) := by ext t; simp [and_comm]
  rw [hi,lintegral_const_mul'' _ (by fun_prop)]
  rw [lintegral_rpow_Ioo (by positivity : 0 ≤ 2*b) (by linarith : -1 < p-2)]
  have hpp : p-2+1 = p-1 := by ring
  rw [hpp]
  have h2 : 0 ≤ (2:ℝ)^(p-1)/(p-1) := div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  rw [← ENNReal.ofReal_mul hb,← ENNReal.ofReal_mul h2]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb]
  have hp0 : 0 < p-1 := by linarith
  have hpow : b*b^(p-1) = b^p := by
    rcases eq_or_lt_of_le hb with rfl | hb
    · simp [Real.zero_rpow hp0.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        b*b^(p-1) = b^(1:ℝ)*b^(p-1) := by rw [Real.rpow_one]
        _ = b^(1+(p-1)) := (Real.rpow_add hb _ _).symm
        _ = b^p := by congr 1; ring
  calc
    b * (2^(p-1)*b^(p-1)/(p-1)) = (2^(p-1)/(p-1))*(b*b^(p-1)) := by ring
    _ = _ := by rw [hpow]

/-- Exact Tonelli computation behind strong maximal interpolation, for every
p > 1. The singularity at testing height zero is actually integrated. -/
theorem truncation_layer_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0,
      (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 ∂μ)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*(∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) := by
  have hm : Measurable (fun z : ℝ × α =>
      (if z.1 < 2*f z.2 then ENNReal.ofReal (f z.2) else 0)*ENNReal.ofReal (z.1^(p-2))) := by
    apply Measurable.mul
    · exact ((hf.comp measurable_snd).ennreal_ofReal).ite
        (measurableSet_lt measurable_fst ((hf.comp measurable_snd).const_mul 2)) measurable_const
    · exact (measurable_fst.pow_const _).ennreal_ofReal
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)) ∂μ := by
      apply lintegral_congr
      intro t
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x, (∫⁻ t in Ioi 0,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal ((f x)^p) ∂μ := by
      apply lintegral_congr
      intro x
      exact truncation_layer_single (hf0 x) hp
    _ = _ := lintegral_const_mul'' _ ((hf.pow_const _).ennreal_ofReal.aemeasurable)

end DiskMaximalTools

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMaximalTools1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

namespace DiskMaximalTools

lemma maximal_layer_coefficient {t p : ℝ} (ht : 0 < t) :
    (25 / ENNReal.ofReal (t/2))*ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal 50*ENNReal.ofReal (t^(p-2)) := by
  rw [← show ENNReal.ofReal (25:ℝ) = 25 by norm_num,
    ← ENNReal.ofReal_div_of_pos (by linarith : 0 < t/2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (25:ℝ)/(t/2)),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50)]
  congr 1
  have hpow : t^(p-1) = t*t^(p-2) := by
    calc
      _ = t^(1+(p-2)) := by congr 1; ring
      _ = t^(1:ℝ)*t^(p-2) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- A full strong p estimate from Vitali, truncation and Tonelli. No maximal
inequality is supplied as an assumption. The real representative is controlled
even before a separate almost-everywhere finiteness argument. -/
theorem strong_rationalMaximal {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal ((rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal^p)) ≤
      ENNReal.ofReal (50*p*2^(p-1)/(p-1)) * (∫⁻ x, ENNReal.ofReal ((f x)^p)) := by
  let M := rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x)))
  have hM : Measurable M := measurable_rationalMaximal _
  have htail (t : ℝ) (ht : 0 < t) : volume {x | t < (M x).toReal} ≤
      (25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 := by
    have hsub : {x | t < (M x).toReal} ⊆ {x | ENNReal.ofReal t < M x} := by
      intro x hx
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx |>.trans_le ENNReal.ofReal_toReal_le
    apply le_trans (measure_mono hsub)
    have hweak := weak_truncated hf.ennreal_ofReal ht
    apply hweak.trans_eq
    congr 1
    apply lintegral_congr
    intro x
    have heq : ENNReal.ofReal (t/2) < ENNReal.ofReal (f x) ↔ t < 2*f x := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith : 0 ≤ t/2)]
      constructor <;> intro h <;> linarith
    simp only [Set.indicator,Set.mem_ofPred_eq,heq]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    hM.ennreal_toReal.aemeasurable (by linarith : 0 < p)]
  have hlayer : (∫⁻ t in Ioi 0, volume {x | t < (M x).toReal}*ENNReal.ofReal (t^(p-1))) ≤
      ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
    calc
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal 50 *
          ((∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        calc
          _ ≤ ((25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*
              ENNReal.ofReal (t^(p-1)) := by gcongr; exact htail t ht
          _ = _ := by
            rw [mul_right_comm, maximal_layer_coefficient ht]
            ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal p*(ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)))) := by
      gcongr
    _ = _ := by
      rw [truncation_layer_integral hf hf0 hp]
      have hc : ENNReal.ofReal p*(ENNReal.ofReal 50 * ENNReal.ofReal (2^(p-1)/(p-1))) =
          ENNReal.ofReal (50*p*2^(p-1)/(p-1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50),
          ← ENNReal.ofReal_mul (by linarith : 0 ≤ p)]
        congr 1
        ring
      simpa only [mul_assoc] using congrArg
        (fun c => c*(∫⁻ x, ENNReal.ofReal ((f x)^p))) hc

lemma disk_average_le_rationalMaximal_exact (ν : Measure ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ν (ball x r) / volume (ball x r) ≤ rationalMaximal ν x := by
  let I := {q : ℚ // 0 < q ∧ (q:ℝ) < r}
  have hdir : Directed (· ⊆ ·) (fun q : I => ball x (q:ℚ)) := by
    intro i j
    refine ⟨⟨max i.val j.val,?_,?_⟩,?_,?_⟩
    · exact lt_max_of_lt_left i.property.1
    · exact_mod_cast max_lt i.property.2 j.property.2
    · exact ball_subset_ball (by exact_mod_cast le_max_left i.val j.val)
    · exact ball_subset_ball (by exact_mod_cast le_max_right i.val j.val)
  have heq : (⋃ q : I, ball x (q:ℚ)) = ball x r := by
    ext y
    constructor
    · intro hy
      obtain ⟨q,hq⟩ := mem_iUnion.mp hy
      exact (ball_subset_ball q.property.2.le) hq
    · intro hy
      have hd : dist y x < r := hy
      obtain ⟨q,hq0,hqr⟩ := exists_rat_btwn (show max 0 (dist y x) < r by exact max_lt hr hd)
      have hq : 0 < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq0
      have hqRat : (0:ℚ) < q := by exact_mod_cast hq
      refine mem_iUnion.mpr ⟨⟨q,hqRat,hqr⟩,?_⟩
      exact lt_of_le_of_lt (le_max_right _ _) hq0
  have hv0 : volume (ball x r) ≠ 0 := by
    rw [volume_disk_real _ hr.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [← heq,hdir.measure_iUnion]
  apply iSup_le
  intro q
  have hq0 : 0 < (q.val:ℝ) := by exact_mod_cast q.property.1
  have hqv : volume (ball x (q.val:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq0.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq0)))
  have hav : ν (ball x (q.val:ℝ)) / volume (ball x (q.val:ℝ)) ≤ rationalMaximal ν x :=
    le_iSup_of_le q.val (le_iSup_of_le q.property.1 le_rfl)
  calc
    _ ≤ rationalMaximal ν x * volume (ball x (q.val:ℝ)) :=
      (ENNReal.div_le_iff hqv measure_ball_lt_top.ne).mp hav
    _ ≤ _ := by
      gcongr
      exact subset_iUnion (fun q : I => ball x (q:ℚ)) q

lemma rationalMaximal_le_of_density_le {f : ℂ → ℝ≥0∞} {B : ℝ≥0∞} (hf : ∀ x, f x ≤ B) (x : ℂ) :
    rationalMaximal (volume.withDensity f) x ≤ B := by
  unfold rationalMaximal
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ ≤ ∫⁻ y in ball x (q:ℝ), B := lintegral_mono hf
    _ = _ := by simp

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ScalarCancellation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {ι : Type*} [Fintype ι]

lemma roots_abs_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |roots μ w f k q x| ∂μ) = |∫ x, refined w f k q x ∂μ| := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.1
  | succ k =>
    have hs := root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))
    change (∫ x, |root μ _ x| ∂μ) = _
    rw [hs.2.2.1,← hs.2.1]
    exact congrArg abs (roots_mass w hf (k+1) q)

/-- The whole scalar cancellation tree is built by backward splitting. Each
nonterminal zero-mass piece costs at most its positive refinement norm defect. -/
theorem errors_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    {f : ι → α → ℝ} (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ| := by
  have hi : Integrable (fun x => ∑ s, w k q s*roots μ w f k s x) μ :=
    integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)
  have hs := root_spec hi
  change (∫ x, |(∑ s, w k q s*roots μ w f k s x)-root μ _ x| ∂μ) ≤ _
  rw [hs.2.2.2.1]
  have hm : (∫ x, ∑ s, w k q s*roots μ w f k s x ∂μ) = ∫ x, refined w f (k+1) q x ∂μ := by
    rw [← hs.2.1]
    exact roots_mass w hf (k+1) q
  rw [hm]
  apply sub_le_sub_right
  calc
    _ ≤ ∫ x, ∑ s, w k q s*|roots μ w f k s x| ∂μ := by
      apply integral_mono hi.abs (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _))
      intro x
      calc
        _ ≤ ∑ s, |w k q s*roots μ w f k s x| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw k q _)]
    _ = _ := by
      rw [integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _)]
      simp_rw [integral_const_mul,roots_abs_mass w hf]

lemma errors_terminal_cost (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (q : ι) :
    (∫ x, |errors μ w f 0 q x| ∂μ) = (∫ x, |f q x| ∂μ)-|∫ x, f q x ∂μ| :=
  (root_spec (hf q)).2.2.2.1

end ScalarCancellation

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ScalarCancellation1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

namespace ScalarCancellation
open Finset
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

/-- Exact expansion in a coherent family of refinement coefficients. The
finite zero-mass pieces are the explicitly constructed `errors`, not merely
scalar mass certificates. -/
theorem telescoped_decomposition [DecidableEq ι] (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ)
    (Λ : ℕ → ℕ → ι → ι → ℝ)
    (hdiag : ∀ k q s, Λ k k q s = if q = s then 1 else 0)
    (hstep : ∀ k j q s, j ≤ k → Λ (k+1) j q s = ∑ a, w k q a*Λ k j a s)
    (k : ℕ) (q : ι) (x : α) :
    refined w f k q x = roots μ w f k q x +
      ∑ j ∈ range (k+1), ∑ s, Λ k j q s*errors μ w f j s x := by
  classical
  induction k generalizing q with
  | zero =>
    simp only [Nat.zero_add,Finset.range_one,sum_singleton,hdiag,ite_mul,one_mul,zero_mul]
    rw [sum_ite_eq univ q]
    simp only [Finset.mem_univ,ite_true,errors,refined]
    ring
  | succ k ih =>
    rw [sum_range_succ]
    have hlast : (∑ s, Λ (k+1) (k+1) q s*errors μ w f (k+1) s x) = errors μ w f (k+1) q x := by
      simp only [hdiag,ite_mul,one_mul,zero_mul]
      simp
    rw [hlast,errors,refined]
    simp_rw [ih]
    simp only [mul_add,sum_add_distrib]
    have hsum : (∑ a, w k q a*(∑ j ∈ range (k+1), ∑ s, Λ k j a s*errors μ w f j s x)) =
        ∑ j ∈ range (k+1), ∑ s, Λ (k+1) j q s*errors μ w f j s x := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [hstep k j q s (Nat.le_of_lt_succ (mem_range.mp hj)),sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum]
    ring

end ScalarCancellation

open MeasureTheory Set
open scoped ENNReal NNReal Topology

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace PlanePotential

lemma dim_complex : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

lemma volume_real_unit_ball : volume.real (ball (0:ℂ) 1) = Real.pi := by
  rw [measureReal_def,Complex.volume_ball]
  simp

lemma integral_radial (f : ℝ → ℝ) :
    (∫ x : ℂ, f ‖x‖) = 2*Real.pi * ∫ r in Ioi (0:ℝ), r*f r := by
  rw [integral_fun_norm_addHaar volume f]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul,volume_real_unit_ball,
    nsmul_eq_mul,Nat.cast_ofNat]
  ring

lemma integrable_radial_iff (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun r => r*f r) (Ioi (0:ℝ)) := by
  simpa only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul] using
    integrable_fun_norm_addHaar (E := ℂ) volume (f := f)

lemma radial_near_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t * (Iio r).indicator (fun u : ℝ => u^a) t = (Ioo 0 r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : t < r
  · simp only [indicator_of_mem (show t ∈ Iio r from htr),indicator_of_mem (show t ∈ Ioo 0 r from ⟨ht,htr⟩)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Iio r from htr),indicator_of_notMem (show t ∉ Ioo 0 r by simp [htr]),mul_zero]

lemma integrable_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun t : ℝ => t^a)]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioo 0 r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
  apply hi.congr_fun _ measurableSet_Ioo
  intro t ht
  change t^(a+1) = t*t^a
  rw [Real.rpow_add ht.1,Real.rpow_one,mul_comm]

/-- Exact planar singular-kernel integral; the center point is not excluded by
an unproved integrability convention. -/
theorem integral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫ x in ball (0:ℂ) r, ‖x‖^a) = 2*Real.pi * (r^(a+2)/(a+2)) := by
  have heq : (ball (0:ℂ) r).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Iio r).indicator (fun t : ℝ => t^a) ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ < r <;> simp [indicator,hx]
  rw [← integral_indicator measurableSet_ball,heq,integral_radial]
  have hinner : (∫ t in Ioi (0:ℝ), t*(Iio r).indicator (fun u : ℝ => u^a) t) =
      ∫ t in Ioo 0 r, t^(a+1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_near_identity a r ht)]
    rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioi_self)]
  rw [hinner,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith : -1 < a+1))]
  rw [show a+1+1=a+2 by ring,Real.zero_rpow (by linarith : a+2 ≠ 0),sub_zero]

lemma radial_far_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t*(Ioi r).indicator (fun u : ℝ => u^a) t = (Ioi r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : r < t
  · simp only [indicator_of_mem (show t ∈ Ioi r from htr)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Ioi r from htr),mul_zero]

lemma integrable_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) {x | r < ‖x‖} := by
  rw [← integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
  have heq : ({x : ℂ | r < ‖x‖}).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Ioi r).indicator (fun t : ℝ => t^a) ‖x‖ := by rfl
  rw [heq,integrable_radial_iff]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr
  have hi' : Integrable ((Ioi r).indicator (fun t : ℝ => t^(a+1))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hi
  apply hi'.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  exact (radial_far_identity a r ht).symm

theorem integral_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    (∫ x : ℂ in {x | r < ‖x‖}, ‖x‖^a) = 2*Real.pi * (-r^(a+2)/(a+2)) := by
  have heq : ({x : ℂ | r < ‖x‖}).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Ioi r).indicator (fun t : ℝ => t^a) ‖x‖ := by rfl
  rw [← integral_indicator (measurableSet_lt measurable_const measurable_norm),heq,integral_radial]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_far_identity a r ht)]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hr.le),integral_Ioi_rpow_of_lt (by linarith : a+1 < -1) hr]
  congr 2
  rw [show a+1+1 = a+2 by ring]
  ring

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PlanePotential1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal

open Finset
open scoped RealInnerProductSpace

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace PlanePotential

lemma segment_support {ψ : ℂ → ℝ} {R X : ℝ}
    (hψ : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ X)
    {t : ℝ} (ht : 0 < t) (hn : ψ (x+t⁻¹ • (y-x)) ≠ 0) :
    ‖y-x‖ ≤ t*(R+X) := by
  have heq : y-x = t • ((x+t⁻¹ • (y-x))-x) := by
    simp [ht.ne']
  calc
    ‖y-x‖ = t*‖(x+t⁻¹ • (y-x))-x‖ := by
      conv_lhs => rw [heq]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    _ ≤ t*(‖x+t⁻¹ • (y-x)‖+‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht.le
    _ ≤ t*(R+X) := mul_le_mul_of_nonneg_left (add_le_add (hψ _ hn) hx) ht.le

lemma integrable_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    Integrable ((Ioi δ).indicator (fun t : ℝ => B*t^q)) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  exact (integrableOn_Ioi_rpow_of_lt hq hδ).const_mul B

lemma integral_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    (∫ t : ℝ, (Ioi δ).indicator (fun t : ℝ => B*t^q) t) = B*(-δ^(q+1)/(q+1)) := by
  rw [integral_indicator measurableSet_Ioi,integral_const_mul,integral_Ioi_rpow_of_lt hq hδ]

/-- A singular segment integral is genuinely integrable because of its geometric
lower cutoff. The bound retains the exact power, rather than a supremum times 1. -/
lemma singular_integral_bound {F : ℝ → ℝ} (hFm : Measurable F)
    {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0)
    (hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ B*t^q) :
    IntegrableOn F (Ioc (0:ℝ) 1) ∧
      |∫ t in Ioc (0:ℝ) 1, F t| ≤ B*(-(δ/2)^(q+1)/(q+1)) := by
  let H := (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q)
  have hH : Integrable H := integrable_power_cutoff hq (by linarith)
  have hH0 (t : ℝ) : 0 ≤ H t := by
    unfold H
    apply indicator_nonneg
    intro t ht
    exact mul_nonneg hB (Real.rpow_nonneg (by change δ/2 < t at ht; linarith) _)
  have hle : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ H t := by
    intro t ht
    by_cases hd : t < δ
    · rw [hzero t ht hd]
      simpa only [abs_zero] using hH0 t
    · have htδ : t ∈ Ioi (δ/2) := by change δ/2 < t; linarith
      change |F t| ≤ (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q) t
      rw [indicator_of_mem htδ]
      exact hbound t ht
  have hFi : IntegrableOn F (Ioc (0:ℝ) 1) := by
    apply hH.integrableOn.mono' hFm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hle t ht
  refine ⟨hFi,?_⟩
  calc
    _ ≤ ∫ t in Ioc (0:ℝ) 1, |F t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioc (0:ℝ) 1, H t := integral_mono_ae hFi.abs hH.integrableOn (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hle t ht)
    _ ≤ ∫ t, H t := integral_mono_measure Measure.restrict_le_self (ae_of_all _ hH0) hH
    _ = _ := integral_power_cutoff hq (by linarith)

lemma greenScalar_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => greenScalar ψ p.1 p.2) := by
  unfold greenScalar
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  have harg : Measurable (fun p : (ℂ × ℂ) × ℝ => p.1.1+p.2⁻¹ • (p.1.2-p.1.1)) := by measurability
  exact ((hψ.comp harg).mul (measurable_snd.pow_const _)).stronglyMeasurable

lemma green_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => green ψ p.1 p.2) := by
  exact (greenScalar_measurable ψ hψ).neg.smul (measurable_snd.sub measurable_fst)

/-- Quantitative kernel size on every observation ball, with an explicit constant. -/
theorem green_norm_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) (hxy : y ≠ x) :
    ‖green ψ x y‖ ≤ 2*B*(R+X)^2/‖y-x‖ := by
  have hd : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let δ := ‖y-x‖/(R+X)
  have hδ : 0 < δ := div_pos hd hM
  have hFm : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
    apply Measurable.mul
    · apply hψm.comp
      measurability
    · exact measurable_id.pow_const _
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have hψ0 : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have : t*(R+X) < ‖y-x‖ := (lt_div_iff₀ hM).mp hlt
      linarith
    rw [hψ0,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  have h := (singular_integral_bound hFm (by norm_num : (-3:ℝ) < -1) hδ hB hzero hb).2
  change |greenScalar ψ x y| ≤ _ at h
  have hrpow : (δ/2)^((-3:ℝ)+1) = (δ/2)^(-2:ℤ) := by norm_num [Real.rpow_intCast]
  rw [hrpow,zpow_neg,zpow_ofNat] at h
  have hs : |greenScalar ψ x y| ≤ 2*B*(R+X)^2/‖y-x‖^2 := by
    convert h using 1
    dsimp [δ]
    field_simp
    ring
  rw [green,norm_smul,Real.norm_eq_abs,abs_neg]
  calc
    _ ≤ (2*B*(R+X)^2/‖y-x‖^2)*‖y-x‖ := mul_le_mul_of_nonneg_right hs hd.le
    _ = _ := by field_simp

lemma segment_integrand_measurable {ψ : ℂ → ℝ} (hψ : Measurable ψ) (x y : ℂ) :
    Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
  apply Measurable.mul
  · apply hψ.comp
    measurability
  · exact measurable_id.pow_const _

lemma scalar_data {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B δ : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hδ : 0 < δ)
    {x y : ℂ} (hx : ‖x‖ ≤ X) (hd : δ*(R+X) ≤ ‖y-x‖) :
    IntegrableOn (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) (Ioc (0:ℝ) 1) ∧
      |greenScalar ψ x y| ≤ 2*B/δ^2 := by
  have hz : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have := mul_lt_mul_of_pos_right hlt hM
      linarith
    rw [this,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  obtain ⟨hi,h⟩ := singular_integral_bound (segment_integrand_measurable hψm x y)
    (by norm_num : (-3:ℝ) < -1) hδ hB hz hb
  refine ⟨hi, h.trans_eq ?_⟩
  rw [show (-3:ℝ)+1 = -2 by norm_num, show (δ/2)^(-2:ℝ) = (δ/2)^(-2:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
  norm_num
  field_simp

/-- A difference bound proves the needed cancellation estimate without hiding
any differentiation under the singular integral. -/
theorem green_difference_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {x y z : ℂ} (hx : ‖x‖ ≤ X) (hzx : z ≠ x) (hyz : ‖y-z‖ ≤ ‖z-x‖/2) :
    ‖green ψ x y-green ψ x z‖ ≤
      (8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*‖y-z‖/‖z-x‖^2 := by
  let d := ‖z-x‖
  let a := ‖y-z‖
  let M := R+X
  let δ := d/(2*M)
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  have ha : 0 ≤ a := norm_nonneg _
  have hδ : 0 < δ := div_pos hd (mul_pos (by norm_num) hM)
  have hnear : d/2 ≤ ‖y-x‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z y x
    rw [norm_sub_rev z y] at ht
    dsimp [d] at *
    linarith
  have hcut : δ*M = d/2 := by dsimp [δ]; field_simp [show M ≠ 0 from hM.ne']
  have hdy : δ*(R+X) ≤ ‖y-x‖ := by change δ*M ≤ _; rw [hcut]; exact hnear
  have hdz : δ*(R+X) ≤ ‖z-x‖ := by change δ*M ≤ d; rw [hcut]; linarith
  obtain ⟨hIy,hKy⟩ := scalar_data hψm hψs hψB hM hB hδ hx hdy
  obtain ⟨hIz,_⟩ := scalar_data hψm hψs hψB hM hB hδ hx hdz
  let F := fun t : ℝ => (ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ)
  have hFm : Measurable F := by
    change Measurable (fun t : ℝ => _)
    have hm (v : ℂ) : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (v-x))) := by
      apply hψm.comp
      measurability
    exact ((hm y).sub (hm z)).mul (measurable_id.pow_const _)
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0 := by
    intro t ht htδ
    have h0 (v : ℂ) (hv : δ*M ≤ ‖v-x‖) : ψ (x+t⁻¹ • (v-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have := mul_lt_mul_of_pos_right htδ hM
      dsimp [M] at hv
      linarith
    change (ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ) = 0
    rw [h0 y hdy,h0 z hdz,sub_self,zero_mul]
  have hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ (L*a)*t^(-4:ℝ) := by
    intro t ht
    have harg : (x+t⁻¹ • (y-x))-(x+t⁻¹ • (z-x)) = t⁻¹ • (y-z) := by module
    have hLip := hψL (x+t⁻¹ • (y-x)) (x+t⁻¹ • (z-x))
    rw [harg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht.1)] at hLip
    calc
      |F t| = |ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x))| *t^(-3:ℝ) := by
        change |(ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ)| = _
        rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      _ ≤ (L*(t⁻¹*a))*t^(-3:ℝ) := mul_le_mul_of_nonneg_right hLip (Real.rpow_nonneg ht.1.le _)
      _ = (L*a)*t^(-4:ℝ) := by
        rw [← Real.rpow_neg_one t]
        calc
          _ = (L*a)*(t^(-1:ℝ)*t^(-3:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add ht.1]; norm_num
  have hdiff := (singular_integral_bound hFm (by norm_num : (-4:ℝ) < -1)
    hδ (mul_nonneg hL ha) hzero hbound).2
  have hIF : (∫ t in Ioc (0:ℝ) 1, F t) = greenScalar ψ x y-greenScalar ψ x z := by
    simp only [F,sub_mul,greenScalar]
    exact integral_sub hIy hIz
  rw [hIF] at hdiff
  have hKd : |greenScalar ψ x y-greenScalar ψ x z| ≤ (64/3:ℝ)*L*a*M^3/d^3 := by
    refine hdiff.trans_eq ?_
    rw [show (-4:ℝ)+1 = -3 by norm_num, show (δ/2)^(-3:ℝ) = (δ/2)^(-3:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
    dsimp [δ]
    field_simp
    ring
  have hKy' : |greenScalar ψ x y| ≤ 8*B*M^2/d^2 := by
    refine hKy.trans_eq ?_
    dsimp [δ]
    field_simp
    ring
  have heq : green ψ x y-green ψ x z =
      (-greenScalar ψ x y) • (y-z) - (greenScalar ψ x y-greenScalar ψ x z) • (z-x) := by
    unfold green
    module
  rw [heq]
  calc
    _ ≤ ‖(-greenScalar ψ x y) • (y-z)‖ +
        ‖(greenScalar ψ x y-greenScalar ψ x z) • (z-x)‖ := norm_sub_le _ _
    _ = |greenScalar ψ x y| *a + |greenScalar ψ x y-greenScalar ψ x z| *d := by
      simp only [norm_smul,Real.norm_eq_abs,abs_neg,a,d]
    _ ≤ (8*B*M^2/d^2)*a + ((64/3:ℝ)*L*a*M^3/d^3)*d :=
      add_le_add (mul_le_mul_of_nonneg_right hKy' ha) (mul_le_mul_of_nonneg_right hKd hd.le)
    _ = _ := by change _ = (8*B*M^2+(64/3:ℝ)*L*M^3)*a/d^2; field_simp

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_VectorRefinement1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PlanePotential

lemma integral_affine (F : ℂ → ℝ) (x : ℂ) (t : ℝ) :
    (∫ z : ℂ, F (x+t • (z-x))) = (t^2)⁻¹ * ∫ y : ℂ, F y := by
  calc
    _ = ∫ w : ℂ, F (x+t • w) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fun w : ℂ => F (x+t • w)) (-x)
    _ = |(t^2)⁻¹| * ∫ y, F (x+y) := by
      simpa only [Complex.finrank_real_complex,smul_eq_mul] using
        Measure.integral_comp_smul volume (fun y : ℂ => F (x+y)) t
    _ = _ := by rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),integral_add_left_eq_self]

lemma integrable_affine_iff (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun z : ℂ => F (x+t • (z-x))) ↔ Integrable F := by
  constructor
  · intro h
    have h1 : Integrable (fun z : ℂ => F (x+t • z)) := by
      simpa only [add_sub_cancel_right] using h.comp_add_right x
    have h2 := (integrable_comp_smul_iff volume (fun z : ℂ => F (x+z)) ht).mp h1
    simpa only [add_neg_cancel_left] using h2.comp_add_left (-x)
  · intro h
    simpa only [sub_eq_add_neg] using ((h.comp_add_left x).comp_smul ht).comp_add_right (-x)

lemma integral_affine_reverse (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℂ, F y) = t^2 * ∫ z : ℂ, F (x+t • (z-x)) := by
  rw [integral_affine]
  field_simp

lemma segment_ftc {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x z : ℂ) :
    (∫ t in Ioc (0:ℝ) 1, fderiv ℝ g (x+t • (z-x)) (z-x)) = g z-g x := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => g (x+s • (z-x)))
      (fderiv ℝ g (x+t • (z-x)) (z-x)) t := by
    have hline : HasDerivAt (fun s : ℝ => x+s • (z-x)) (z-x) t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (z-x)).const_add x
    exact ((hg.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t hline
  have hc : Continuous (fun t : ℝ => fderiv ℝ g (x+t • (z-x)) (z-x)) := by
    exact ((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),one_smul,
    add_sub_cancel,zero_smul,add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)

lemma pullback_identity (ψ g : ℂ → ℝ) (x z : ℂ) {t : ℝ} (ht : 0 < t) :
    pullbackForm ψ g x t (x+t • (z-x)) = (t^2)⁻¹*segmentForm ψ g x t z := by
  have ha : x+t⁻¹ • (x+t • (z-x)-x) = z := by simp [ht.ne']
  unfold pullbackForm segmentForm
  rw [ha,add_sub_cancel_left,map_smul,smul_eq_mul]
  have hp : t^(-3:ℝ) = (t^3)⁻¹ := by
    rw [show (-3:ℝ) = ((-3:ℤ):ℝ) by norm_num,Real.rpow_intCast,zpow_neg,zpow_ofNat]
  rw [hp]
  field_simp

lemma segmentForm_continuous {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2) := by
  unfold segmentForm
  exact (hψ.comp continuous_snd).mul
    (((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply (by fun_prop))

lemma segmentForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    Integrable (segmentForm ψ g x t) := by
  apply ((segmentForm_continuous hψ hg x).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact hψc.mul_right

lemma pullbackForm_measurable {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Measurable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2) := by
  unfold pullbackForm
  have ha : Measurable (fun p : ℝ × ℂ => x+p.1⁻¹ • (p.2-x)) := by measurability
  exact ((hψ.measurable.comp ha).mul (measurable_fst.pow_const _)).mul
    ((((hg.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (by fun_prop)).measurable)

lemma pullbackForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    Integrable (pullbackForm ψ g x t) := by
  apply (integrable_affine_iff _ x ht.ne').mp
  simpa only [pullback_identity ψ g x _ ht] using
    (segmentForm_integrable_column hψ hψc hg x t).const_mul ((t^2)⁻¹)

lemma pullback_column_integral (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, pullbackForm ψ g x t y) = ∫ z, segmentForm ψ g x t z := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht]
  rw [integral_const_mul]
  field_simp

lemma pullback_column_norm (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, ‖pullbackForm ψ g x t y‖) = ∫ z, ‖segmentForm ψ g x t z‖ := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  rw [integral_const_mul]
  field_simp

lemma segmentForm_bound {ψ g : ℂ → ℝ} {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D)
    (x : ℂ) (t : ℝ) (z : ℂ) :
    ‖segmentForm ψ g x t z‖ ≤ |ψ z| *D*‖z-x‖ := by
  rw [segmentForm,norm_mul,Real.norm_eq_abs]
  calc
    _ ≤ |ψ z| *(‖fderiv ℝ g (x+t • (z-x))‖*‖z-x‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ g _).le_opNorm _) (abs_nonneg _)
    _ ≤ |ψ z| *(D*‖z-x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

lemma segment_weight_integrable {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (x : ℂ) (D : ℝ) :
    Integrable (fun z : ℂ => |ψ z| *D*‖z-x‖) := by
  apply (show Continuous (fun z : ℂ => |ψ z| *D*‖z-x‖) by fun_prop).integrable_of_hasCompactSupport
  exact (hψc.norm.mul_right).mul_right

/-- Absolute integrability justifies the double integral even at t approaching zero. -/
theorem pullbackForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (pullbackForm_measurable hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pullbackForm_integrable_column hψ hψc hg x ht.1
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| *D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [pullback_column_norm ψ g x ht.1,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma segmentForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (segmentForm_continuous hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ (fun t => segmentForm_integrable_column hψ hψc hg x t)
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| * D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma green_pullback (ψ g : ℂ → ℝ) (x y : ℂ) :
    fderiv ℝ g y (green ψ x y) = -∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y := by
  simp only [green,map_smul,smul_eq_mul,greenScalar,pullbackForm,integral_mul_const,neg_mul]

/-- The true segment-kernel representation, with Fubini justified absolutely. -/
theorem green_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, fderiv ℝ g y (green ψ x y)) = g x-∫ z, ψ z*g z := by
  have hseg := segmentForm_integrable hψ hψc hg hD x
  have hpull := pullbackForm_integrable hψ hψc hg hD x
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hψgi : Integrable (fun z => ψ z*g z) :=
    (hψ.mul hg.continuous).integrable_of_hasCompactSupport hψc.mul_right
  calc
    _ = -(∫ y, ∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y) := by
      simp_rw [green_pullback]; rw [integral_neg]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ y, pullbackForm ψ g x t y) := by
      rw [← integral_integral_swap hpull]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ z, segmentForm ψ g x t z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pullback_column_integral ψ g x ht.1
    _ = -(∫ z, ∫ t in Ioc (0:ℝ) 1, segmentForm ψ g x t z) := by
      rw [integral_integral_swap hseg]
    _ = -(∫ z, ψ z*(g z-g x)) := by
      simp_rw [segmentForm,integral_const_mul,segment_ftc hg]
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hψgi (hψi.mul_const _),integral_mul_const,hψ1]
      ring

end PlanePotential

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace PlanePotential
lemma lintegral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫⁻ x in ball (0:ℂ) r, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_near ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_near ha hr]

lemma lintegral_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    (∫⁻ x : ℂ in {x | r < ‖x‖}, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(-r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_far ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_far ha hr]

lemma lintegral_translated_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x in ball y r, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_near ha hr,← lintegral_indicator measurableSet_ball,
    ← lintegral_indicator measurableSet_ball]
  have heq : (ball y r).indicator (fun x => ENNReal.ofReal (‖x-y‖^a)) =
      fun x => (ball (0:ℂ) r).indicator (fun w => ENNReal.ofReal (‖w‖^a)) (x-y) := by
    funext x
    simp only [indicator,mem_ball,dist_eq_norm,sub_zero]
  rw [heq]
  exact lintegral_add_right_eq_self (fun x : ℂ => (ball 0 r).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma lintegral_translated_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x : ℂ in {x | r < ‖x-y‖}, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(-r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_far ha hr,
    ← lintegral_indicator (show MeasurableSet {x : ℂ | r < ‖x-y‖} from measurableSet_lt measurable_const (by fun_prop)),
    ← lintegral_indicator (measurableSet_lt measurable_const measurable_norm)]
  exact lintegral_add_right_eq_self (fun x : ℂ => ({x | r < ‖x‖}).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma norm_power_bound {F : ℂ → ℂ} {C q : ℝ} (hC : 0 ≤ C) (x y : ℂ)
    (hF : ‖F x‖ ≤ C*‖x-y‖^q) :
    (ENNReal.ofReal ‖F x‖)^(3/2:ℝ) ≤
      ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(q*(3/2:ℝ))) := by
  calc
    _ = ENNReal.ofReal (‖F x‖^(3/2:ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)
    _ ≤ ENNReal.ofReal ((C*‖x-y‖^q)^(3/2:ℝ)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hF (by norm_num))
    _ = _ := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg _) _),← Real.rpow_mul (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]

lemma kernel_near_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ ball y r)
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-1:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(4*Real.pi*r^(1/2:ℝ))) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x in ball y r, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_near (by norm_num : (-2:ℝ) < -3/2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num
      exact Or.inl (by ring)

lemma kernel_far_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ {x | r < ‖x-y‖})
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-2:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(2*Real.pi/r)) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x : ℂ in {x | r < ‖x-y‖}, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_far (by norm_num : (-3:ℝ) < -2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num [Real.rpow_neg_one]
      exact Or.inl (by ring)

end PlanePotential

open scoped RealInnerProductSpace
namespace PlanePotential

lemma green_diagonal (ψ : ℂ → ℝ) (x : ℂ) : green ψ x x = 0 := by
  simp [green]

lemma green_size_all {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) :
    ‖green ψ x y‖ ≤ (2*B*(R+X)^2)*‖x-y‖^(-1:ℝ) := by
  by_cases hxy : y = x
  · subst y
    simp [green_diagonal]
  · simpa only [Real.rpow_neg_one,div_eq_mul_inv,norm_sub_rev] using
      green_norm_bound hψm hψs hψB hM hB hx hxy

lemma green_near_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (ha : 0 < a) (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ ‖x-z‖ ≤ 2*a},
      (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 4*a) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have ht := norm_sub_le (x-z) (y-z)
    rw [sub_sub_sub_cancel_right] at ht
    linarith [hx.2]
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx.1

lemma green_far_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖},
      (ENNReal.ofReal ‖green ψ x y-green ψ x z‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a))) := by
  apply kernel_far_three_halves (by positivity) (by positivity : 0 < 2*a) z
  · exact fun _ hx => hx.2
  · intro x hx
    have hzx : z ≠ x := by
      intro h
      have hh := hx.2
      rw [← h,sub_self,norm_zero] at hh
      linarith
    have hn : ‖z-x‖ = ‖x-z‖ := norm_sub_rev z x
    have h := green_difference_bound (x := x) (y := y) (z := z) hψm hψs hψB hψL hM hB hL hx.1 hzx (by
      rw [hn]
      linarith [hx.2])
    rw [hn] at h
    calc
      _ ≤ (8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a/‖x-z‖^2 :=
        h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by positivity)) (sq_nonneg _))
      _ = _ := by
        rw [show ‖x-z‖^(-2:ℝ) = ‖x-z‖^(-2:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
        rfl

lemma cancelledGreen_measurable {ψ : ℂ → ℝ} (hψ : Measurable ψ) (z : ℂ) (a : ℝ) :
    Measurable (fun p : ℂ × ℂ => cancelledGreen ψ z a p.1 p.2) := by
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact green_measurable ψ hψ
  · exact (green_measurable ψ hψ).sub
      ((green_measurable ψ hψ).comp (measurable_fst.prodMk measurable_const))

lemma green_piece_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z y : ℂ) (hy : ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a))) := by
  let E := {x : ℂ | ‖x‖ ≤ X}
  let N := {x : ℂ | ‖x-z‖ ≤ 2*a}
  have hN : MeasurableSet N := measurableSet_le (by fun_prop) measurable_const
  have hE : MeasurableSet E := measurableSet_le measurable_norm measurable_const
  have hsplit := lintegral_add_compl (μ := volume.restrict E)
    (fun x => (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ)) hN
  rw [← hsplit]
  have hn : (∫⁻ x in N, (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ) ∂volume.restrict E) =
      ∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ ‖x-z‖ ≤ 2*a}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ) := by
    rw [Measure.restrict_restrict hN,inter_comm]
    apply setLIntegral_congr_fun (hE.inter hN)
    intro x hx
    have hxN : ‖x-z‖ ≤ 2*a := hx.2
    simp only [cancelledGreen,ite_eq_left hxN]
  have hf : (∫⁻ x in Nᶜ, (ENNReal.ofReal ‖cancelledGreen ψ z a x y‖)^(3/2:ℝ) ∂volume.restrict E) =
      ∫⁻ x in {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖}, (ENNReal.ofReal ‖green ψ x y-green ψ x z‖)^(3/2:ℝ) := by
    rw [Measure.restrict_restrict hN.compl,inter_comm]
    have he : E ∩ Nᶜ = {x : ℂ | ‖x‖ ≤ X ∧ 2*a < ‖x-z‖} := by ext x; simp [E,N]
    rw [he]
    apply setLIntegral_congr_fun ((measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_id.sub_const z).norm)))
    intro x hx
    have hxF : 2*a < ‖x-z‖ := hx.2
    simp only [cancelledGreen,ite_eq_right (not_le.mpr hxF)]
  rw [hn,hf]
  exact add_le_add (green_near_column hψm hψs hψB hM hB ha z y hy)
    (green_far_column hψm hψs hψB hψL hM hB hL ha z y hy)

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PlanePotential2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SignedDisk

namespace PlanePotential

theorem kernel_column_lp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α × β → ℝ≥0∞} (hK : Measurable K) {C : ℝ≥0∞}
    (hC : ∀ᵐ y ∂ν, (∫⁻ x, (K (x,y))^(3/2:ℝ) ∂μ) ≤ C) :
    (∫⁻ x, (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ∂μ) ≤ C*(ν univ)^(3/2:ℝ) := by
  have hpq : Real.HolderConjugate (3/2) 3 := by rw [Real.holderConjugate_iff]; norm_num
  have hpoint (x : α) : (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ≤
      (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => K (x,y)) (g := fun _ => 1)
      ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (aemeasurable_const (b := (1:ℝ≥0∞)))
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 3/2)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),← ENNReal.rpow_mul,
      show (1/(3/2:ℝ))*(3/2)=1 by norm_num,
      show (1/(3:ℝ))*(3/2)=1/2 by norm_num,ENNReal.rpow_one,one_mul] using h'
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ∫⁻ x, K (x,y)^(3/2:ℝ) ∂μ ∂ν)*(ν univ)^(1/2:ℝ) := by
      rw [lintegral_mul_const _ (hK.pow_const _).lintegral_prod_right,
        lintegral_lintegral_swap (hK.pow_const _).aemeasurable]
    _ ≤ (C*ν univ)*(ν univ)^(1/2:ℝ) :=
      mul_le_mul_left ((lintegral_mono_ae hC).trans_eq (lintegral_const _)) _
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (ν univ)^(1:ℝ)*(ν univ)^(1/2:ℝ) := by rw [ENNReal.rpow_one]
        _ = (ν univ)^((1:ℝ)+1/2) :=
          (ENNReal.rpow_add_of_nonneg 1 (1/2) (by norm_num) (by norm_num)).symm
        _ = _ := by norm_num

/-- No pointwise integrability assertion for the singular kernel is needed
in this domination: the Bochner integral is bounded by the nonnegative integral. -/
lemma potential_domination {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    ENNReal.ofReal |∫ y, ⟪L y,b y⟫| ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  calc
    _ = ‖∫ y, ⟪L y,b y⟫‖ₑ := by rw [← ofReal_norm,Real.norm_eq_abs]
    _ ≤ ∫⁻ y, ‖⟪L y,b y⟫‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only [Pi.mul_apply]
      rw [← ofReal_norm]
      change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

theorem cancelled_potential_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪cancelledGreen ψ z a x y,β y⟫|)^(3/2:ℝ)) ≤
    (ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
    ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ) *
        (2*Real.pi/(2*a)))) * (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := cancelledGreen_measurable hψm z a
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ))) +
      ENNReal.ofReal (((8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*a)^(3/2:ℝ)*(2*Real.pi/(2*a))))
    (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_piece_column hψm hψs hψB hψL hM hB hL ha z y
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

lemma zero_mass_kernel_shift {L : ℂ → ℂ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (c : ℂ) :
    (∫ y, ⟪L y,β y⟫) = ∫ y, ⟪L y-c,β y⟫ := by
  have hc : Integrable (fun y => ⟪c,β y⟫) := hβ.const_inner c
  have hci : (∫ y, ⟪c,β y⟫) = 0 := by rw [integral_inner hβ,hzero,inner_zero_right]
  simp only [inner_sub_left]
  by_cases hi : Integrable (fun y => ⟪L y,β y⟫)
  · rw [integral_sub hi hc,hci,sub_zero]
  · rw [integral_undef hi,integral_undef]
    intro hs
    have hh := hs.add hc
    change Integrable (fun y => (⟪L y,β y⟫-⟪c,β y⟫)+⟪c,β y⟫) at hh
    simp only [sub_add_cancel] at hh
    exact hi hh

lemma cancelled_potential_eq {ψ : ℂ → ℝ} {β : ℂ → ℂ} (hβ : Integrable β)
    (hzero : ∫ y, β y = 0) (z : ℂ) (a : ℝ) (x : ℂ) :
    (∫ y, ⟪green ψ x y,β y⟫) = ∫ y, ⟪cancelledGreen ψ z a x y,β y⟫ := by
  by_cases hx : ‖x-z‖ ≤ 2*a
  · simp only [cancelledGreen,ite_eq_left hx]
  · simp only [cancelledGreen,ite_eq_right hx]
    exact zero_mass_kernel_shift hβ hzero _

/-- Uniform scaling of the exact p-th power column constant: in dimension two
and at p=3/2 its radius dependence is precisely a^(1/2). -/
lemma column_scaling {K D a : ℝ} (hD : 0 ≤ D) (ha : 0 < a) :
    K^(3/2:ℝ)*(4*Real.pi*(4*a)^(1/2:ℝ)) +
      (D*a)^(3/2:ℝ)*(2*Real.pi/(2*a)) =
      (8*Real.pi*K^(3/2:ℝ)+Real.pi*D^(3/2:ℝ))*a^(1/2:ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) ha.le,Real.mul_rpow hD ha.le]
  have hfour : (4:ℝ)^(1/2:ℝ) = 2 := by norm_num [← Real.sqrt_eq_rpow]
  have hpow : a^(3/2:ℝ)/a = a^(1/2:ℝ) := by
    rw [← Real.rpow_sub_one ha.ne']
    norm_num
  rw [hfour]
  calc
    _ = 8*Real.pi*K^(3/2:ℝ)*a^(1/2:ℝ)+Real.pi*D^(3/2:ℝ)*(a^(3/2:ℝ)/a) := by ring
    _ = _ := by rw [hpow]; ring

theorem green_zero_piece_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  simp_rw [cancelled_potential_eq hβ hzero z a]
  have h := cancelled_potential_lp hψm hψs hψB hψL hM hB hL ha z hβ hβs
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    column_scaling (by positivity) ha] at h
  exact h

end PlanePotential

open scoped RealInnerProductSpace

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_IntrinsicMarks1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SignedDisk

open scoped ContDiff
namespace PlanePotential
lemma potential_norm_lintegral {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    (∫⁻ y, ‖⟪L y,b y⟫‖ₑ) ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  apply lintegral_mono
  intro y
  dsimp only [Pi.mul_apply]
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

lemma potential_integrable_of_density {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b)
    (hfinite : (∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)) < ⊤) :
    Integrable (fun y => ⟪L y,b y⟫) := by
  refine ⟨hL.aestronglyMeasurable.inner hb.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (potential_norm_lintegral hL hb).trans_lt hfinite

/-- Finiteness of the genuine singular integrals, obtained from the column
estimate itself. This justifies insertion of the finite vector decomposition. -/
theorem kernel_potential_ae_integrable (μ : Measure ℂ) [SFinite μ]
    {K : ℂ × ℂ → ℂ} (hK : Measurable K) {b : ℂ → ℂ} (hb : Integrable b)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hcol : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖),
      (∫⁻ x, (ENNReal.ofReal ‖K (x,y)‖)^(3/2:ℝ) ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, Integrable (fun y => ⟪K (x,y),b y⟫) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)
  have hm : ν univ = ENNReal.ofReal (∫ y, ‖b y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hb.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have hν : ν univ < ⊤ := by rw [hm]; exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := ⟨hν⟩
  have hlp := kernel_column_lp μ ν hK.norm.ennreal_ofReal hcol
  have hfinite : (∫⁻ x, (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν)^(3/2:ℝ) ∂μ) ≠ ⊤ :=
    ne_of_lt (hlp.trans_lt (ENNReal.mul_lt_top hC (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hν.ne)))
  have hae := ae_lt_top (hK.norm.ennreal_ofReal.lintegral_prod_right.pow_const _) hfinite
  filter_upwards [hae] with x hx
  apply potential_integrable_of_density (hK.comp (measurable_const.prodMk measurable_id)) hb
  apply lt_top_iff_ne_top.mpr
  intro htop
  change (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν) = ⊤ at htop
  rw [htop,ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 3/2)] at hx
  exact (lt_irrefl _ hx)

lemma green_root_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y) {y : ℂ} (hy : ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 2*(X+Y)) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have hn := norm_sub_le x y
    change ‖x‖ ≤ X at hx
    linarith
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx

lemma green_ae_integrable {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X}, Integrable (fun y => ⟪green ψ x y,β y⟫) := by
  apply kernel_potential_ae_integrable _ (green_measurable ψ hψm) hβ ENNReal.ofReal_lt_top
  rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
  filter_upwards with y hy
  apply green_root_column hψm hψs hψB hM hB hXY
  apply hβs y
  intro hy0
  simp [hy0] at hy

lemma green_root_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := green_measurable ψ hψm
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ)))) (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_root_column hψm hψs hψB hM hB hXY
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

lemma eLpNorm_three_halves_bound (μ : Measure ℂ) {F : ℂ → ℝ} {K m : ℝ≥0∞}
    (h : (∫⁻ x, (ENNReal.ofReal |F x|)^(3/2:ℝ) ∂μ) ≤ K*m^(3/2:ℝ)) :
    eLpNorm' F (3/2:ℝ) μ ≤ K^(2/3:ℝ)*m := by
  rw [eLpNorm'_eq_lintegral_enorm]
  norm_num only [one_div_div]
  have hpow := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul] at hpow
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,ENNReal.rpow_one] at hpow
  simpa only [← ofReal_norm,Real.norm_eq_abs] using hpow

lemma potential_aestronglyMeasurable (μ : Measure ℂ) {K : ℂ × ℂ → ℂ}
    (hK : Measurable K) {β : ℂ → ℂ} (hβ : Integrable β) :
    AEStronglyMeasurable (fun x => ∫ y, ⟪K (x,y),β y⟫) μ := by
  have h : AEStronglyMeasurable (fun z : ℂ × ℂ => @inner ℝ ℂ _ (K z) (β z.2)) (μ.prod volume) :=
    hK.aestronglyMeasurable.inner hβ.aestronglyMeasurable.comp_snd
  exact h.integral_prod_right'

/-- A genuine fixed smooth probability cutoff. Its finite size and Lipschitz
constants depend on no input, no dyadic level and no number of scales. -/
theorem exists_kernel_cutoff : ∃ (ψ : ℂ → ℝ) (B L : ℝ),
    0 ≤ B ∧ 0 ≤ L ∧ ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x) = 1 ∧ (∀ x, ψ x ≠ 0 → ‖x‖ ≤ 1) ∧
    (∀ x, |ψ x| ≤ B) ∧ (∀ x y, |ψ x-ψ y| ≤ L*‖x-y‖) := by
  let φ : ContDiffBump (0:ℂ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let ψ := φ.normed volume
  have hc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hd : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hd.continuous
  obtain ⟨L,hL⟩ := hd.lipschitzWith_of_hasCompactSupport hc (by simp)
  refine ⟨ψ,B,L,le_trans (norm_nonneg (ψ 0)) (hB 0),L.coe_nonneg,hd,hc,
    φ.integral_normed,?_,?_,?_⟩
  · intro x hx
    have hs : x ∈ Function.support ψ := hx
    rw [φ.support_normed_eq] at hs
    exact (show ‖x‖ < 1 by simpa only [mem_ball,dist_zero_right] using hs).le
  · intro x
    simpa only [Real.norm_eq_abs] using hB x
  · intro x y
    simpa only [Real.norm_eq_abs] using hL.norm_sub_le x y

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LabelSwitches1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff

noncomputable section

namespace SignedDisk

open Finset

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace PlanePotential

/-- The global segment kernel vanishes off the region on which the actual
finite density decomposition is valid. -/
lemma green_eq_zero_of_outside {ψ : ℂ → ℝ} {R X : ℝ}
    (hs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X) {x y : ℂ}
    (hx : ‖x‖ ≤ X) (hy : X < ‖y‖) : green ψ x y = 0 := by
  have hz (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ψ (x+t⁻¹ • (y-x)) = 0 := by
    by_contra hh
    have hw := hs _ hh
    have heq : y = (1-t) • x+t • (x+t⁻¹ • (y-x)) := by
      rw [smul_add,smul_smul,mul_inv_cancel₀ ht.1.ne',one_smul]
      module
    have hn := norm_add_le ((1-t) • x) (t • (x+t⁻¹ • (y-x)))
    rw [← heq,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_pos ht.1] at hn
    have hle := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hw.trans hRX) ht.1.le)
    nlinarith
  have hi : greenScalar ψ x y = 0 := by
    unfold greenScalar
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    simp only [hz t ht,zero_mul]
  simp only [green,hi,neg_zero,zero_smul]

lemma green_gradient_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, ⟪green ψ x y,gradient g y⟫) = g x-∫ z, ψ z*g z := by
  simpa only [inner_gradient_right,RCLike.conj_to_real] using
    green_representation hψ hψc hg hD hψ1 x

theorem green_finite_decomposition {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X Y B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hβs : ∀ i y, β i y ≠ 0 → ‖y‖ ≤ Y)
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X},
      g x-∫ z, ψ z*g z = ∑ i, ∫ y, ⟪green ψ x y,β i y⟫ := by
  have hall := ae_all_iff.mpr (fun i => green_ae_integrable hψ.measurable hψs hψB hM hB hXY
    (hβ i) (hβs i))
  filter_upwards [hall,ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hi hx
  rw [← green_gradient_representation hψ hψc hg hD hψ1 x,← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [hdecomp] with y hy
  by_cases hyX : ‖y‖ ≤ X
  · rw [hy hyX,inner_sum]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hyX)]
    simp

/-- The complete finite Minkowski step, after genuine kernel insertion. -/
theorem green_decomposition_norm {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X Y B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hβs : ∀ i y, β i y ≠ 0 → ‖y‖ ≤ Y)
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    eLpNorm (fun x => g x-∫ z, ψ z*g z) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ≤
      ∑ i, eLpNorm (fun x => ∫ y, ⟪green ψ x y,β i y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ X}) := by
  let μ := volume.restrict {x : ℂ | ‖x‖ ≤ X}
  let F : ι → ℂ → ℝ := fun i x => ∫ y, ⟪green ψ x y,β i y⟫
  have hmeas : ∀ i, AEStronglyMeasurable (F i) μ := fun i =>
    potential_aestronglyMeasurable _ (green_measurable ψ hψ.measurable) (hβ i)
  have heq : (fun x => g x-∫ z, ψ z*g z) =ᵐ[μ] fun x => ∑ i, F i x :=
    green_finite_decomposition hψ hψc hg hD hψ1 hψs hψB hRX hM hB hXY β hβ hβs hdecomp
  have hsum : eLpNorm (∑ i, F i) (3/2) μ ≤ ∑ i, eLpNorm (F i) (3/2) μ :=
    eLpNorm_sum_le (fun i _ => hmeas i) (by
      rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
      norm_num)
  rw [eLpNorm_congr_ae heq]
  have hfun : (∑ i, F i) = fun x => ∑ i, F i x := by ext x; simp
  rw [hfun] at hsum
  exact hsum

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace SignedDisk

namespace DyadicHats

lemma boxNorm_le_norm (x : ℂ) : boxNorm x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
lemma boxNorm_add_le (x y : ℂ) : boxNorm (x+y) ≤ boxNorm x+boxNorm y := by
  apply max_le
  · exact (abs_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
lemma boxNorm_neg (x : ℂ) : boxNorm (-x) = boxNorm x := by simp [boxNorm]
lemma boxNorm_sub_comm (x y : ℂ) : boxNorm (x-y) = boxNorm (y-x) := by
  rw [← neg_sub y x,boxNorm_neg]

open scoped BigOperators

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DyadicHats

lemma density_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x*h x) = h x := by
  have he : (∑' p : ℤ × ℤ, hat r p x*h x) = ∑ p ∈ indexBox N, hat r p x*h x :=
    tsum_eq_sum (fun p hp => hat_mul_zero_outside hr hN hs hp x)
  rw [Finset.sum_coe_sort (indexBox N) (fun p => hat r p x*h x),← he,
    tsum_mul_right,tsum_hat,one_mul]

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats

section
open scoped BigOperators

variable {N : ℕ}

lemma densityRoot_abs_mass {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityRoot N r h k q x|) = |∫ x, hat (scale r k) q x*h x| := by
  have he := ScalarCancellation.roots_abs_mass (weights N) (pieces_integrable hh r) k q
  simpa only [densityRoot,refined_eq_density hr hR hN hs] using he

lemma densityError_cost {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityError N r h k q x|) ≤ 2*densityDefect N r h k q := by
  cases k with
  | zero =>
    have he := ScalarCancellation.errors_terminal_cost (weights N) (pieces_integrable hh r) q
    simp only [pieces,abs_mul,abs_of_nonneg (hat_nonneg r q _)] at he
    rw [densityDefect]
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) 0 q x|) ≤ _
    rw [he]
    linarith
  | succ k =>
    have he := ScalarCancellation.errors_cost (weights N) (fun _ p s => step_nonneg p s)
      (pieces_integrable hh r) k q
    simp only [refined_eq_density hr hR hN hs,weights] at he
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) (k+1) q x|) ≤ _
    rw [densityDefect]
    linarith

end

open Finset

lemma coeff_nonneg (N d : ℕ) (p q : Grid N) : 0 ≤ coeff N d p q := by
  induction d generalizing p with
  | zero => simp only [coeff]; split_ifs <;> norm_num
  | succ d ih => exact sum_nonneg fun a _ => mul_nonneg (step_nonneg p a) (ih a)

/-- All lower-level error densities, with their actual coherent coefficients,
reconstruct the genuine coarse hat density exactly. -/
theorem density_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) (x : ℂ) :
    hat (scale r k) q x*h x = densityRoot N r h k q x+
      ∑ j ∈ range (k+1), ∑ s : Grid N, coeff N (k-j) q s*densityError N r h j s x := by
  rw [← refined_eq_density hr hR hN hs]
  apply ScalarCancellation.telescoped_decomposition (weights N) (pieces N r h)
    (fun k j p s => coeff N (k-j) p s)
  · intro j p s
    simp only [Nat.sub_self,coeff]
  · intro k j p s hj
    rw [show k+1-j = k-j+1 by omega,coeff]
    rfl

lemma densityDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ densityDefect N r h k q := by
  have he := densityError_cost hr hR hN hh hs k q
  have hn : 0 ≤ ∫ x, |densityError N r h k q x| := integral_nonneg (fun x => abs_nonneg _)
  linarith

open Finset

open Finset

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DirectionNeighbors
open DyadicHats Finset

lemma mem_window_iff {r : ℝ} (hr : 0 < r) (d : ℕ) (q z : ℤ × ℤ) :
    z ∈ window d q ↔ boxNorm (point r z-point r q) ≤ (d:ℝ)*r := by
  have hh (a b : ℤ) : |r*a-r*b| ≤ (d:ℝ)*r ↔ b-(d:ℤ) ≤ a ∧ a ≤ b+d := by
    rw [← mul_sub,abs_mul,abs_of_pos hr,mul_comm (d:ℝ) r,mul_le_mul_iff_right₀ hr]
    have hc : |(a:ℝ)-(b:ℝ)| ≤ (d:ℝ) ↔ |a-b| ≤ (d:ℤ) := by
      exact_mod_cast Iff.rfl
    rw [hc,abs_le]
    omega
  change (_ ∈ ((Finset.Icc _ _) ×ˢ (Finset.Icc _ _))) ↔ max _ _ ≤ _
  rw [Finset.mem_product,Finset.mem_Icc,Finset.mem_Icc,max_le_iff]
  exact (hh _ _).symm.and (hh _ _).symm

open DyadicHats

end DirectionNeighbors

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DirectionNeighbors1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

/-! Actual fixed palette and literal cone coordinates. -/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ConeCoordinates

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt3_bounds : 3/2 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have := sqrt3_sq
  have := sqrt3_pos
  constructor <;> nlinarith
lemma inner_re (n z : ℂ) : inner ℝ n z = (star n*z).re := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re]
  ring
lemma coordinate_apply (n z : ℂ) (s : ℝ) :
    coordinate n s z = (star n*z).re / Real.sqrt 3 + s*(star n*z).im := by
  change (1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z = _
  rw [inner_re,inner_im]
  ring
lemma expansion {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) = z := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos
  have hz : n*(star n*z) = z := by rw [← mul_assoc,mul_star_of_unit hn,one_mul]
  have he : coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) =
      n*(star n*z) := by
    apply Complex.ext <;> simp [axis,coordinate_apply,Complex.mul_re,Complex.mul_im] <;> field_simp <;> ring
  exact he.trans hz
lemma coordinate_norm_le {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : |s| ≤ 1) (z : ℂ) :
    |coordinate n s z| ≤ 2 * ‖z‖ := by
  have ha : |inner ℝ n z| ≤ ‖z‖ := by simpa [hn] using abs_real_inner_le_norm n z
  have hb : |inner ℝ (Complex.I*n) z| ≤ ‖z‖ := by
    simpa [norm_mul,hn] using abs_real_inner_le_norm (Complex.I*n) z
  have hr : 1 / Real.sqrt 3 ≤ 1 := by rw [div_le_one sqrt3_pos]; linarith [sqrt3_bounds]
  have hnon : 0 ≤ 1 / Real.sqrt 3 := (div_pos (by norm_num) sqrt3_pos).le
  calc
    |coordinate n s z| ≤ (1/Real.sqrt 3)*|inner ℝ n z| + |s| *|inner ℝ (Complex.I*n) z| := by
      change |(1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z| ≤ _
      simpa only [abs_mul,abs_of_nonneg hnon] using
        abs_add_le ((1/Real.sqrt 3)*inner ℝ n z) (s*inner ℝ (Complex.I*n) z)
    _ ≤ 1*‖z‖+1*‖z‖ := add_le_add (mul_le_mul hr ha (abs_nonneg _) (by norm_num))
      (mul_le_mul hs hb (abs_nonneg _) (by norm_num))
    _ = 2*‖z‖ := by ring

end ConeCoordinates

namespace ConeScalar
open ConeCoordinates DyadicHats IntrinsicMarks

lemma root_mass_norm {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) =
      |coordinate n s (vectorMass h (scale r k) q)| := by
  simp only [norm_smul,axis_norm hn hs,Real.norm_eq_abs,mul_one]
  rw [densityRoot_abs_mass hr hR hN (scalar_integrable hh _) (scalar_support hsupp _),scalar_mass hh]

lemma root_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) ≤
      2*scalarMass h (scale r k) q := by
  rw [root_mass_norm hr hR hN hh hsupp k q hn hs]
  apply coordinate_norm_le hn
  exact (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith)

end ConeScalar

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_AffineDensities1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace AffineDensities

lemma mass_rescale (h : ℂ → ℂ) (p : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ X, ‖rescale p r h X‖) = r⁻¹*(∫ y, ‖h y‖) := by
  simp only [rescale,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le,integral_const_mul]
  have he := Measure.integral_comp_smul volume (fun y : ℂ => ‖h (p+y)‖) r
  simp only [Complex.finrank_real_complex,smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] at he
  rw [he, integral_add_left_eq_self (fun y : ℂ => ‖h y‖)]
  field_simp

end AffineDensities

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma errorPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k j : ℕ) (hj : j ≤ k) (p : ℂ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (errorPiece hh hr k j hj p q n s).mass ≤ (scale r k)⁻¹*
      (2*densityDefect N r (fun x => coordinate n s (h x)) j q) := by
  change (∫ X, ‖rescale _ _ _ X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simp only [norm_smul,axis_norm hn hs,mul_one,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (densityError_cost hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) j q)
    (inv_nonneg.mpr (scale_pos hr k).le)

end PricePieces

namespace LocalCancellation

lemma ErrorPiece.mass_weight {Cs : ℝ} (b : ErrorPiece Cs) {w : ℝ} (hw : 0 ≤ w) :
    (b.weight w).mass = w*b.mass := by
  simp only [ErrorPiece.mass,ErrorPiece.weight,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw,
    integral_const_mul]

end LocalCancellation

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma vector_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) (y : ℂ) :
    hat (scale r k) q y • h y = rootVector N r h k q n y+
      ∑ j ∈ Finset.range (k+1), ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y := by
  have hp := density_decomposition hr hR hN (scalar_support hsupp (coordinate n 1)) k q y
  have hm := density_decomposition hr hR hN (scalar_support hsupp (coordinate n (-1))) k q y
  have hx := congrArg (fun z : ℂ => hat (scale r k) q y • z) (expansion hn (h y))
  rw [smul_add,smul_smul,smul_smul,hp,hm,add_smul,add_smul] at hx
  simp only [rootVector,errorVector,smul_add,smul_smul,Finset.sum_add_distrib]
  rw [← hx]
  simp only [Finset.sum_smul]
  abel

lemma rootVector_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootVector N r h k q n y‖) ≤ 4*scalarMass h (scale r k) q := by
  calc
    _ ≤ (∫ y, ‖densityRoot N r (fun x => coordinate n 1 (h x)) k q y • axis n 1‖)+
      (∫ y, ‖densityRoot N r (fun x => coordinate n (-1) (h x)) k q y • axis n (-1)‖) :=
      by
        rw [← integral_add (root_vector_integrable hh r k q n 1).norm
          (root_vector_integrable hh r k q n (-1)).norm]
        exact integral_mono (rootVector_integrable hh r k q n).norm
          ((root_vector_integrable hh r k q n 1).norm.add
            (root_vector_integrable hh r k q n (-1)).norm) (fun y => norm_add_le _ _)
    _ ≤ 2*scalarMass h (scale r k) q+2*scalarMass h (scale r k) q :=
      add_le_add (root_bound hr hR hN hh hsupp k q hn (by norm_num))
        (root_bound hr hR hN hh hsupp k q hn (by norm_num))
    _ = _ := by ring

end PricePieces

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset

lemma rho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _

lemma scale_ratio {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    scale r j / scale r k = (1/2:ℝ)^(k-j) := by
  dsimp [scale]
  rw [mul_div_mul_right _ _ hr.ne']
  have hk : k = j+(k-j) := (Nat.add_sub_of_le hj).symm
  conv_lhs => rw [hk,pow_add]
  simp only [div_pow,one_pow]
  field_simp

lemma scale_discount {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    (scale r j / scale r k)^(1/100:ℝ) = rho^(k-j) := by
  rw [scale_ratio hr hj]
  unfold rho
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),mul_comm ((k-j:ℕ):ℝ),
    Real.rpow_mul (by norm_num),Real.rpow_natCast]

lemma scalarPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ scalarPrice N r h rho k q := by
  apply sum_nonneg
  intro j _
  apply mul_nonneg (pow_nonneg rho_pos.le _)
  exact sum_nonneg (fun s _ => mul_nonneg (coeff_nonneg N (k-j) q s)
    (densityDefect_nonneg hr hR hN hh hsupp j s))

lemma rootPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ rootPrice N r h k q := by
  apply sum_nonneg
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualMarkTrees1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma sign_sq (b : Bool) : sign b^2 = 1 := by cases b <;> norm_num [sign]

lemma rootWeight_nonneg {N : ℕ} (S : Finset (Grid N)) (k j : ℕ) (s : Grid N) :
    0 ≤ rootWeight S k j s := sum_nonneg (fun q _ => coeff_nonneg N (k-j) q s)

lemma smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).mass ≤ (scale r k)⁻¹*2*
      (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1) := by
  rw [smallPiece,ErrorPiece.mass_weight _ (rootWeight_nonneg ..)]
  calc
    _ ≤ rootWeight S k i.1 i.2.1*((scale r k)⁻¹*
        (2*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (errorPiece_mass hr hR hN hh hsupp k i.1
        (Nat.le_of_lt_succ i.1.isLt) p i.2.1 hn (sign_sq _)) (rootWeight_nonneg ..)
    _ = _ := by ring

lemma discounted_smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass ≤
      (scale r k)⁻¹*2*(rho^(k-i.1)*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) := by
  have hs : (smallPiece hh hr k p S n i).size^(1/100:ℝ) = rho^(k-i.1) :=
    scale_discount hr (Nat.le_of_lt_succ i.1.isLt)
  rw [hs]
  calc
    _ ≤ rho^(k-i.1)*((scale r k)⁻¹*2*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (smallPiece_mass hr hR hN hh hsupp k p S hn i) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

lemma weighted_defect_sum {N : ℕ} (r : ℝ) (h : ℂ → ℝ) (k : ℕ) (S : Finset (Grid N)) :
    (∑ j : Fin (k+1), ∑ s : Grid N, rho^(k-j.val)*(rootWeight S k j s*densityDefect N r h j s)) =
      ∑ q ∈ S, scalarPrice N r h rho k q := by
  simp only [rootWeight,sum_mul,mul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  unfold scalarPrice
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]

lemma smallPiece_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*
      ∑ q ∈ S, (scalarPrice N r (fun x => coordinate n 1 (h x)) rho k q+
        scalarPrice N r (fun x => coordinate n (-1) (h x)) rho k q) := by
  apply (sum_le_sum (fun i _ => discounted_smallPiece_mass hr hR hN hh hsupp k p S hn i)).trans_eq
  rw [← mul_sum]
  congr 1
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,sign,Bool.false_eq_true,
    ite_false,ite_true,sum_add_distrib]
  rw [weighted_defect_sum,weighted_defect_sum,← sum_add_distrib]

lemma smallPiece_common_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*cellPrice N r h k S := by
  apply (smallPiece_price hr hR hN hh hsupp k p S (fixedPalette.unit n hn)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr (scale_pos hr k).le) (by norm_num))
  apply sum_le_sum
  intro q _
  apply single_le_sum _ hn
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma rootSum_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootSum h r k S n y‖) ≤ 4*∑ q ∈ S, scalarMass h (scale r k) q := by
  calc
    _ ≤ ∫ y, ∑ q ∈ S, ‖rootVector N r h k q n y‖ :=
      integral_mono (rootSum_integrable hh r k S n).norm
        (integrable_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm))
        (fun y => norm_sum_le _ _)
    _ = ∑ q ∈ S, ∫ y, ‖rootVector N r h k q n y‖ :=
      integral_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm)
    _ ≤ _ := by rw [mul_sum]; exact sum_le_sum (fun q _ => rootVector_mass hr hR hN hh hsupp k q hn)

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma smallPiece_pair_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (j : Fin (k+1)) (q : Grid N) (X : ℂ) :
    (∑ b : Bool, (smallPiece hh hr k p S n (j,q,b)).density X) =
      rootWeight S k j q • rescale p (scale r k) (errorVector N r h j q n) X := by
  simp only [Fintype.sum_bool,smallPiece,ErrorPiece.weight,errorPiece,sign,
    Bool.false_eq_true,ite_false,ite_true,rescale,errorVector]
  module

lemma smallPiece_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (X : ℂ) :
    (∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) =
      rescale p (scale r k) (fun y => ∑ q ∈ S, ∑ j ∈ range (k+1),
        ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y) X := by
  simp only [Fintype.sum_prod_type,smallPiece_pair_sum,rootWeight,sum_smul,rescale,smul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro s _
  module

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace AffineDensities
lemma gradient_affine {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ) (X : ℂ) :
    gradient (fun Y => g (p+r • Y)) X = rescale p r (gradient g) X := by
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y) (r • ContinuousLinearMap.id ℝ ℂ) X :=
    ((hasFDerivAt_id X).const_smul r).const_add p
  have hc := (hg (p+r • X)).hasFDerivAt.comp X hA
  change HasFDerivAt (fun Y => g (p+r • Y)) _ X at hc
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient,rescale,map_smul]
  rw [hc.fderiv]
  ext z
  simp
end AffineDensities

namespace DyadicHats
open Finset
lemma vector_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x) • h x = h x := by
  by_cases hx : h x = 0
  · simp only [hx,smul_zero]
  · have he := density_partition_grid hr hN (h := fun y => ‖h y‖)
      (fun y hy => hs y (fun hh => hy (by rw [hh,norm_zero]))) x
    rw [← sum_mul] at he
    have hsum : (∑ p : Grid N, hat r p x) = 1 := by
      apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hx)
      simpa only [one_mul] using he
    rw [hsum,one_smul]
end DyadicHats

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments

lemma hat_mem_cellRoots {N : ℕ} {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12)
    (q : Grid N) (hq : hat r q (point r p+r • X) ≠ 0) : q ∈ cellRoots N p := by
  have hl := (hat_ne_zero_iff hr q (point r p+r • X)).mp hq
  have hnorm : boxNorm (r • X) ≤ 12*r := by
    apply (boxNorm_le_norm _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hh := boxNorm_add_le (point r q-(point r p+r • X)) (r • X)
  rw [boxNorm_sub_comm (point r q)] at hh
  have hie : point r q-(point r p+r • X)+r • X = point r q-point r p := by abel
  rw [hie] at hh
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rw [mem_window_iff hr 20]
  norm_num
  linarith

lemma cell_partition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hN : R/r+1 ≤ (N:ℝ))
    {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) • h (point r p+r • X) = h (point r p+r • X) := by
  have he : (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) =
      ∑ q : Grid N, hat r q (point r p+r • X) := by
    apply sum_subset (subset_univ _)
    intro q _ hq
    by_contra hh
    exact hq (hat_mem_cellRoots hr p X hX q hh)
  rw [he]
  exact vector_partition_grid hr hN hs _

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualMarkTrees2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

lemma rootMass_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ rootMass h r k S := sum_nonneg (fun _ _ => norm_nonneg _)

lemma sizeErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (sizeErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*rootMass h r k S+2*cellPrice N r h k S) := by
  have hb : (sizeErrors hr hh k p S n none).mass ≤ (scale r k)⁻¹*4*rootMass h r k S := by
    change (∫ X, ‖rescale p (scale r k) (rootSum h r k S n) X‖) ≤ _
    rw [mass_rescale _ _ (scale_pos hr k)]
    simpa only [mul_assoc,rootMass] using mul_le_mul_of_nonneg_left
      (rootSum_mass hr hR hN hh hsupp k S (fixedPalette.unit n hn)) (inv_nonneg.mpr (scale_pos hr k).le)
  have hs := smallPiece_common_price hr hR hN hh hsupp k p S hn
  change (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*
    (smallPiece hh hr k p S n i).mass) ≤ _ at hs
  simp only [errorPrice,Fintype.sum_option,show (sizeErrors hr hh k p S n none).size = 1 from rfl,
    Real.one_rpow,one_mul]
  change (sizeErrors hr hh k p S n none).mass + (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass) ≤ _
  linarith

lemma sizeErrors_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ i, (sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [Fintype.sum_option]
  change rescale _ _ (rootSum _ _ _ _ _) X+
    (∑ i : ErrorIndex N k, (smallPiece hh hr k _ _ n i).density X) = _
  rw [smallPiece_sum,gradient_affine hg]
  simp only [rescale,← smul_add,rootSum,← sum_add_distrib]
  have he := sum_congr rfl (fun q (_ : q ∈ cellRoots N p) =>
    (vector_decomposition hr hR hN hsupp k q hn (point (scale r k) p+scale r k • X)).symm)
  rw [he,← sum_smul,cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

end CommonPrices

namespace PlanePotential
open LocalCancellation

lemma green_restrict_density {ψ : ℂ → ℝ} {R X : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X)
    (β : ℂ → ℂ) {x : ℂ} (hx : ‖x‖ ≤ X) (y : ℂ) :
    ⟪green ψ x y, ({y : ℂ | ‖y‖ ≤ X}.indicator β) y⟫ = ⟪green ψ x y,β y⟫ := by
  by_cases hy : ‖y‖ ≤ X
  · simp [hy]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hy)]
    simp

lemma green_root_lp_local {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hX : 0 < X)
    (hβ : Integrable β) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(4*X)^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let β' := {y : ℂ | ‖y‖ ≤ X}.indicator β
  have hi : Integrable β' := hβ.indicator (measurableSet_le measurable_norm measurable_const)
  have hs : ∀ y, β' y ≠ 0 → ‖y‖ ≤ X := by
    intro y hy
    by_contra hn
    exact hy (by simp [β',hn])
  have h := green_root_lp hψm hψs hψB hM hB (show 0 < X+X by linarith) hi hs
  have he : (fun x => (ENNReal.ofReal |∫ y, ⟪green ψ x y,β' y⟫|)^(3/2:ℝ)) =ᵐ[volume.restrict {x : ℂ | ‖x‖ ≤ X}]
      (fun x => (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hx
    congr 3
    exact integral_congr_ae (ae_of_all _ (green_restrict_density hψs hRX β hx))
  rw [lintegral_congr_ae he] at h
  have hm : (∫ y, ‖β' y‖) ≤ ∫ y, ‖β y‖ :=
    integral_mono hi.norm hβ.norm (fun y => norm_indicator_le_norm_self β y)
  have hm' := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hm) (by norm_num : (0:ℝ) ≤ 3/2)
  have h' := h.trans (mul_le_mul_right hm' _)
  simpa only [show 2*(X+X)=4*X by ring] using h'

lemma green_zero_piece_lp_ae {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X B L a : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L) (ha : 0 < a)
    (z : ℂ) (hβ : Integrable β) (hzero : ∫ y, β y = 0)
    (hβs : ∀ᵐ y, β y ≠ 0 → ‖y-z‖ ≤ a) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X},
      (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((8*Real.pi*(2*B*(R+X)^2)^(3/2:ℝ)+
      Real.pi*(8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)^(3/2:ℝ))*a^(1/2:ℝ)) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let β' := {y : ℂ | ‖y-z‖ ≤ a}.indicator β
  have he : β' =ᵐ[volume] β := by
    filter_upwards [hβs] with y hy
    by_cases hs : ‖y-z‖ ≤ a
    · simp [β',hs]
    · have hz : β y = 0 := by by_contra hn; exact hs (hy hn)
      simp [β',hs,hz]
  have hi : Integrable β' := hβ.congr he.symm
  have hz : ∫ y, β' y = 0 := (integral_congr_ae he).trans hzero
  have hs : ∀ y, β' y ≠ 0 → ‖y-z‖ ≤ a := by
    intro y hy
    by_contra hn
    exact hy (by simp [β',hn])
  have hp (x : ℂ) : (∫ y, ⟪green ψ x y,β' y⟫) = ∫ y, ⟪green ψ x y,β y⟫ :=
    integral_congr_ae (he.mono (fun y hy => by simpa only using congrArg (fun z => ⟪green ψ x y,z⟫) hy))
  have hm : (∫ y, ‖β' y‖) = ∫ y, ‖β y‖ := integral_congr_ae (he.mono (fun y hy => by simpa only using congrArg norm hy))
  simpa only [hp,hm] using green_zero_piece_lp hψm hψs hψB hψL hM hB hL ha z hi hz hs

/-- The local decomposition theorem does not demand artificial bounded support
of the original densities: the actual Green kernel vanishes outside the
observation ball. -/
theorem green_decomposition_norm_local {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hX : 0 < X)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    eLpNorm (fun x => g x-∫ z, ψ z*g z) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ≤
      ∑ i, eLpNorm (fun x => ∫ y, ⟪green ψ x y,β i y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ X}) := by
  let β' := fun i => {y : ℂ | ‖y‖ ≤ X}.indicator (β i)
  have hi (i : ι) : Integrable (β' i) := (hβ i).indicator (measurableSet_le measurable_norm measurable_const)
  have hs (i : ι) (y : ℂ) (hy : β' i y ≠ 0) : ‖y‖ ≤ X := by
    by_contra hn
    exact hy (by simp [β',hn])
  have hd : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β' i y := by
    filter_upwards [hdecomp] with y hy hY
    simpa [β',hY] using hy hY
  have h := green_decomposition_norm hψ hψc hg hD hψ1 hψs hψB hRX hM hB
    (show 0 < X+X by linarith) β' hi hs hd
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hx
  exact integral_congr_ae (ae_of_all _ (green_restrict_density hψs hRX (β i) hx))

/-- Uniform fractional small-support gain expressed in the common price
exponent 1/100, including the unrestricted unit-size terms. -/
theorem exists_green_price : ∃ (ψ : ℂ → ℝ) (C : ℝ), 0 < C ∧
    ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ z, ψ z) = 1 ∧
    (∀ z, ψ z ≠ 0 → ‖z‖ ≤ 1) ∧
    ∀ b : ErrorPiece 2,
      eLpNorm (fun x => ∫ y, ⟪green ψ x y,b.density y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) ≤
        ENNReal.ofReal (C*b.size^(1/100:ℝ)*b.mass) := by
  obtain ⟨ψ,B,L,hB,hL,hψ,hψc,hψ1,hψs,hψB,hψL⟩ := exists_kernel_cutoff
  let A : ℝ := (2*B*(1+8)^2)^(3/2:ℝ)*(4*Real.pi*(4*8)^(1/2:ℝ))
  let Z : ℝ := 8*Real.pi*(2*B*(1+8)^2)^(3/2:ℝ)+
    Real.pi*(8*B*(1+8)^2+(64/3:ℝ)*L*(1+8)^3)^(3/2:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C : ℝ := A^(2/3:ℝ)+Z^(2/3:ℝ)*2^(1/3:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ψ,C,hC,hψ,hψc,hψ1,hψs,?_⟩
  intro b
  have hb0 := b.size_pos.le
  have hm0 := b.mass_nonneg
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0) (by finiteness)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  by_cases hb : b.size < 1
  · have ha : 0 < 2*b.size := mul_pos (by norm_num) b.size_pos
    have hp := green_zero_piece_lp_ae hψ.continuous.measurable hψs hψB hψL (by norm_num : (0:ℝ) < 1+8)
      hB hL ha b.center b.integrable (b.zero_mass hb) (b.support hb)
    have hn := eLpNorm_three_halves_bound _ hp
    change _ ≤ (ENNReal.ofReal (Z*(2*b.size)^(1/2:ℝ)))^(2/3:ℝ)*ENNReal.ofReal b.mass at hn
    have he : (ENNReal.ofReal (Z*(2*b.size)^(1/2:ℝ)))^(2/3:ℝ)*ENNReal.ofReal b.mass =
        ENNReal.ofReal (Z^(2/3:ℝ)*2^(1/3:ℝ)*b.size^(1/3:ℝ)*b.mass) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow hZ (by positivity),← Real.rpow_mul (by positivity),show (1/2:ℝ)*(2/3)=1/3 by norm_num,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) b.size_pos.le]
      ring
    rw [he] at hn
    apply hn.trans (ENNReal.ofReal_le_ofReal _)
    have hbpow : b.size^(1/3:ℝ) ≤ b.size^(1/100:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge b.size_pos b.size_le_one (by norm_num)
    have hZC : Z^(2/3:ℝ)*2^(1/3:ℝ) ≤ C := by dsimp [C]; linarith [Real.rpow_nonneg hA (2/3)]
    exact mul_le_mul_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_left hbpow (by positivity))
        (mul_le_mul_of_nonneg_right hZC (by positivity))) b.mass_nonneg
  · have hb1 : b.size = 1 := le_antisymm b.size_le_one (le_of_not_gt hb)
    have hp := green_root_lp_local hψ.continuous.measurable hψs hψB (by norm_num : (1:ℝ) ≤ 8)
      (by norm_num : (0:ℝ) < 1+8) hB (by norm_num : (0:ℝ) < 8) b.integrable
    have hn := eLpNorm_three_halves_bound _ hp
    change _ ≤ (ENNReal.ofReal A)^(2/3:ℝ)*ENNReal.ofReal b.mass at hn
    rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),← ENNReal.ofReal_mul (by positivity)] at hn
    simp only [hb1,Real.one_rpow,mul_one]
    apply hn.trans (ENNReal.ofReal_le_ofReal _)
    apply mul_le_mul_of_nonneg_right _ b.mass_nonneg
    dsimp [C]
    linarith [mul_nonneg (Real.rpow_nonneg hZ (2/3)) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (1/3))]
end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMaximalTools2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DiskMaximalTools

lemma strong_three_halves_norm {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))] :
    eLpNorm (fun x => (rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal)
      (3/2) volume ≤ ENNReal.ofReal ((150*2^(1/2:ℝ))^(2/3:ℝ))*eLpNorm f (3/2) volume := by
  have h := strong_rationalMaximal hf hf0 (by norm_num : (1:ℝ) < 3/2)
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3)] at hs
  have hp : (50*(3/2:ℝ)*2^((3/2:ℝ)-1)/((3/2:ℝ)-1)) = 150*2^(1/2:ℝ) := by
    norm_num
    ring
  rw [hp,ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat,one_div_div]
  simp only [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (hf0 _),ENNReal.ofReal_rpow_of_nonneg (hf0 _) (by norm_num : (0:ℝ) ≤ 3/2),
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ) ≤ 3/2)] at hs ⊢
  exact hs

lemma lintegral_le_three_halves_norm {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x) {Q : Set ℂ} (hQ : volume Q ≤ 1) :
    (∫⁻ x in Q, ENNReal.ofReal (f x)) ≤ eLpNorm f (3/2) volume := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1:ℝ≥0∞) ≤ 3/2 by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num) hf.restrict (μ := volume.restrict Q)
  have he : (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal (3/2)) = (1/3:ℝ) := by norm_num
  rw [he,Measure.restrict_apply_univ] at h
  have hpow : (volume Q)^(1/3:ℝ) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hQ (by norm_num : (0:ℝ) ≤ 1/3)
  calc
    _ = eLpNorm f 1 (volume.restrict Q) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp only [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf0 _)]
    _ ≤ eLpNorm f (3/2) (volume.restrict Q)*(volume Q)^(1/3:ℝ) := h
    _ ≤ eLpNorm f (3/2) (volume.restrict Q) := by simpa using mul_le_mul_right hpow _
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
end DiskMaximalTools

namespace PlanePotential
open LocalCancellation

/-- The complete local L^(3/2) value estimate for a genuine finite vector
cancellation decomposition, with the common 1/100 price. -/
theorem local_value_lp : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (b : ι → ErrorPiece 2) {g : ℂ → ℝ},
    ContDiff ℝ 1 g → (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    (∀ᵐ y, ‖y‖ ≤ 8 → gradient g y = ∑ i, (b i).density y) →
    ∃ c : ℝ, eLpNorm (fun x => g x-c) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) ≤
      ENNReal.ofReal (C * errorPrice b (1/100)) := by
  obtain ⟨ψ,C,hC,hψ,hψc,hψ1,hψs,hprice⟩ := exists_green_price
  obtain ⟨B,hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  have hψB (z : ℂ) : |ψ z| ≤ B := by simpa only [Real.norm_eq_abs] using hB z
  refine ⟨C,hC,?_⟩
  intro ι _ b g hg hD hdecomp
  obtain ⟨D,hD⟩ := hD
  refine ⟨∫ z, ψ z*g z,?_⟩
  apply (green_decomposition_norm_local hψ.continuous hψc hg hD hψ1 hψs hψB
    (by norm_num : (1:ℝ) ≤ 8) (by norm_num : (0:ℝ) < 1+8) hB0 (by norm_num : (0:ℝ) < 8)
    (fun i => (b i).density) (fun i => (b i).integrable) hdecomp).trans
  apply (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hprice (b i))).trans_eq
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (b i).size_pos.le _)) (b i).mass_nonneg)]
  congr 1
  rw [errorPrice,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end PlanePotential

namespace DiskMoments
open DiskMaximalTools

lemma signedAverage_sub_const {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage (fun y => g y-c) x t = signedAverage g x t-c := by
  have hi : IntegrableOn g (Metric.ball x t) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x t)).mono_set Metric.ball_subset_closedBall
  have hc : IntegrableOn (fun _ : ℂ => c) (Metric.ball x t) := integrableOn_const measure_ball_lt_top.ne
  unfold signedAverage
  rw [integral_sub hi hc,integral_const]
  have hv : (volume (Metric.ball x t)).toReal = Real.pi*t^2 := by
    rw [volume_disk_real x ht.le,ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real,Measure.restrict_apply_univ,hv,smul_eq_mul]
  field_simp

/-- A true disk average of a continuous function is controlled by the local
absolute-density maximal function. No maximizing-radius selection is used. -/
lemma local_average_le {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ)
    {x : ℂ} (hx : ‖x‖ ≤ 2) {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 4) :
    ENNReal.ofReal |signedAverage g x t-c| ≤
      rationalMaximal (volume.withDensity (fun y => ENNReal.ofReal
        (({y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)) y))) x := by
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.sub continuous_const).abs.continuousOn
  have hsub (y : ℂ) (hy : y ∈ Metric.ball x t) : ‖y‖ ≤ 8 := by
    have hy' : ‖y-x‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := norm_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have he : (∫ y in Metric.ball x t, f y) = ∫ y in Metric.ball x t, |g y-c| := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [f,hsub y hy]
  have hav : |signedAverage g x t-c| ≤ (∫ y in Metric.ball x t, f y)/(Real.pi*t^2) := by
    rw [← signedAverage_sub_const hg c x ht,signedAverage,abs_div,abs_of_pos (by positivity : 0 < Real.pi*t^2),he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y-c) (μ := volume.restrict (Metric.ball x t))
  have hν : (volume.withDensity (fun y => ENNReal.ofReal (f y))) (Metric.ball x t) =
      ENNReal.ofReal (∫ y in Metric.ball x t, f y) := by
    rw [withDensity_apply _ measurableSet_ball]
    exact (ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (ae_of_all _ (fun y => by dsimp [f]; exact Set.indicator_nonneg (fun _ _ => abs_nonneg _ ) y))).symm
  apply (ENNReal.ofReal_le_ofReal hav).trans
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi*t^2),← hν,← volume_disk_real x ht.le]
  exact disk_average_le_rationalMaximal_exact _ x ht
end DiskMoments

namespace PlanePotential
open LocalCancellation DiskMaximalTools DiskMoments

/-- Full local value-oscillation price, for every pair of positive radii at
most four. The measurable majorant is an actual centered Euclidean disk
maximal function, not an assumed analytic input. -/
theorem local_value_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (b : ι → ErrorPiece 2) {g : ℂ → ℝ},
    ContDiff ℝ 1 g → (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    (∀ᵐ y, ‖y‖ ≤ 8 → gradient g y = ∑ i, (b i).density y) →
    ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
      ∀ x, ‖x‖ ≤ 2 → ∀ t t', 0 < t → t ≤ 4 → 0 < t' → t' ≤ 4 →
        ENNReal.ofReal |signedAverage g x t-signedAverage g x t'| ≤ F x := by
  obtain ⟨C,hC,hlocal⟩ := local_value_lp
  let K : ℝ := (150*2^(1/2:ℝ))^(2/3:ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2*K*C,by positivity,?_⟩
  intro ι _ b g hg hD hdecomp Q hQ
  obtain ⟨c,hc⟩ := hlocal b hg hD hdecomp
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.continuous.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hf0 (y : ℂ) : 0 ≤ f y := Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.continuous.sub continuous_const).abs.continuousOn
  let ν := volume.withDensity (fun y => ENNReal.ofReal (f y))
  have hν : ν univ = ENNReal.ofReal (∫ y, f y) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  let M : ℂ → ℝ := fun x => (rationalMaximal ν x).toReal
  have hM : Measurable M := (measurable_rationalMaximal ν).ennreal_toReal
  have hMf : ∀ x, rationalMaximal ν x ≠ ⊤ := by
    obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 8).exists_bound_of_continuousOn
      (hg.continuous.sub (continuous_const (y := c))).continuousOn
    have hbnd (y : ℂ) : f y ≤ max B 0 := by
      by_cases hy : ‖y‖ ≤ 8
      · have hby := hB y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)
        simpa [f, hy, Real.norm_eq_abs] using hby.trans (le_max_left B 0)
      · simp [f, hy]
    intro x
    exact ne_of_lt ((rationalMaximal_le_of_density_le (fun y => ENNReal.ofReal_le_ofReal (hbnd y)) x).trans_lt ENNReal.ofReal_lt_top)
  have hfnorm : eLpNorm f (3/2) volume = eLpNorm (fun x => g x-c) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ 8}) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_le measurable_norm measurable_const)]
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun x => g x-c)
      (p := (3/2:ℝ≥0∞)) (μ := volume.restrict {x : ℂ | ‖x‖ ≤ 8})
  have hn : eLpNorm M (3/2) volume ≤ ENNReal.ofReal K*ENNReal.ofReal (C*errorPrice b (1/100)) := by
    apply (strong_three_halves_norm hf hf0).trans
    apply mul_le_mul_right _ _
    simpa only [hfnorm] using hc
  refine ⟨fun x => ENNReal.ofReal 2*ENNReal.ofReal (M x),measurable_const.mul hM.ennreal_ofReal,?_,?_⟩
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply (mul_le_mul_right (lintegral_le_three_halves_norm hM.aestronglyMeasurable
      (fun _ => ENNReal.toReal_nonneg) (by simpa using hQ)) _).trans
    apply (mul_le_mul_right hn _).trans_eq
    rw [← ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  · intro x hx t t' ht ht4 ht' ht4'
    have ha : |signedAverage g x t-c| ≤ M x :=
      (ENNReal.ofReal_le_iff_le_toReal (hMf x)).mp (local_average_le hg.continuous c hx ht ht4)
    have hb : |signedAverage g x t'-c| ≤ M x :=
      (ENNReal.ofReal_le_iff_le_toReal (hMf x)).mp (local_average_le hg.continuous c hx ht' ht4')
    change ENNReal.ofReal _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (M x)
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hh := abs_sub_le (signedAverage g x t) c (signedAverage g x t')
    rw [abs_sub_comm c] at hh
    linarith
end PlanePotential

namespace AffineDensities
lemma fderiv_affine_bound {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ)
    {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) :
    ∃ B : ℝ, ∀ X, ‖fderiv ℝ (fun Y => g (p+r • Y)) X‖ ≤ B := by
  refine ⟨D*|r|,?_⟩
  intro X
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y)
      (r • ContinuousLinearMap.id ℝ ℂ) X := by
    simpa using ((hasFDerivAt_id X).const_smul r).const_add p
  have hd := (hg (p+r • X)).hasFDerivAt.comp X hA
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_id, mul_one]
  exact mul_le_mul_of_nonneg_right (hD _) (abs_nonneg _)
end AffineDensities

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

/-- The actual common-price value estimate, including every terminal error and
all roots. This is the third local analytic input to signed run assembly. -/
theorem value_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t t', 0 < t → t ≤ 4 → 0 < t' → t' ≤ 4 →
        ENNReal.ofReal |signedAverage (fun Y => g (point (scale r k) p+scale r k • Y)) X t-
          signedAverage (fun Y => g (point (scale r k) p+scale r k • Y)) X t'| ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := PlanePotential.local_value_majorant
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn Q hQ
  let b := sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨D,hD⟩ := hD
  have hD' := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  have hd : ∀ᵐ X, ‖X‖ ≤ 8 →
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X = ∑ i, (b i).density X := by
    filter_upwards with X hX
    exact (sizeErrors_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p
      (fixedPalette.unit n hn) X (by linarith)).symm
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor b hg' hD' hd Q hQ
  refine ⟨F,hFm,?_,hFb⟩
  apply hFi.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := sizeErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
  have hDp : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
    sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
  change errorPrice b (1/100) ≤ _ at hb
  have hrk := scale_pos hr k
  nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
    mul_nonneg (inv_nonneg.mpr hrk.le) hDp]
end CommonPrices

namespace PhysicalCells
open MeasureTheory Set

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
lemma volume_unitCell : volume unitCell = 1 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  change volume unitCell = _ at he
  rw [he]
  change (volume.prod volume) (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num
lemma norm_unitCell {X : ℂ} (hX : X ∈ unitCell) : ‖X‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im X
  rw [abs_of_nonneg hX.1.1,abs_of_nonneg hX.2.1] at h
  linarith [hX.1.2,hX.2.2]
lemma toUnit_affine (p : ℂ) {r : ℝ} (hr : r ≠ 0) (X : ℂ) : toUnit p r (p+r • X) = X := by
  simp [toUnit,hr]
lemma affine_toUnit (p : ℂ) {r : ℝ} (hr : r ≠ 0) (y : ℂ) : p+r • toUnit p r y = y := by
  simp [toUnit,hr]

lemma lintegral_smul (F : ℂ → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ X : ℂ, F (r • X)) = ENNReal.ofReal ((r^2)⁻¹)*(∫⁻ y, F y) := by
  have he := (lintegral_map_equiv (μ := volume) F
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv).symm
  change (∫⁻ X : ℂ, F (r • X)) = ∫⁻ y, F y ∂Measure.map (fun X : ℂ => r • X) volume at he
  rw [he,Measure.map_addHaar_smul volume hr,lintegral_smul_measure]
  simp only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),smul_eq_mul]

lemma lintegral_toUnit (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y : ℂ, F (toUnit p r y)) = ENNReal.ofReal (r^2)*(∫⁻ X, F X) := by
  calc
    (∫⁻ y : ℂ, F (r⁻¹ • (y-p))) = ∫⁻ y : ℂ, F (r⁻¹ • y) :=
      lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun y : ℂ => F (r⁻¹ • y)) p
    _ = _ := by rw [lintegral_smul _ (inv_ne_zero hr),inv_pow,inv_inv]

/-- Exact physical-space change of variables, with the two-dimensional volume
factor and no integrability or measurability assumptions on the majorant. -/
lemma lintegral_cell (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F y) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F (p+r • X) := by
  rw [← lintegral_indicator (cell_measurable p r),← lintegral_indicator unitCell_measurable]
  have he (y : ℂ) : (cell p r).indicator F y =
      unitCell.indicator (fun X => F (p+r • X)) (toUnit p r y) := by
    by_cases hy : y ∈ cell p r
    · rw [Set.indicator_of_mem hy,Set.indicator_of_mem (show toUnit p r y ∈ unitCell from hy),affine_toUnit p hr]
    · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem (show toUnit p r y ∉ unitCell from hy)]
  simp_rw [he]
  exact lintegral_toUnit _ p hr

lemma cell_majorant {F : ℂ → ℝ≥0∞} (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F (toUnit p r y)) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F X := by
  rw [lintegral_cell _ p hr]
  simp only [toUnit_affine p hr]
end PhysicalCells

namespace DiskMoments
lemma signedAverage_affine (g : ℂ → ℝ) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    signedAverage (fun Y => g (p+r • Y)) X t = signedAverage g (p+r • X) (r*t) := by
  rw [signedAverage_fixedDomain _ _ ht,signedAverage_fixedDomain _ _ (mul_pos hr ht)]
  congr 1
  apply setIntegral_congr_fun measurableSet_ball
  intro Z _
  change g (p+r • (X+t • Z)) = g (p+r • X+(r*t) • Z)
  congr 1
  rw [smul_add,smul_smul]
  abel

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PhysicalCells1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace PhysicalCells

lemma value_majorant_integral {F : ℂ → ℝ≥0∞} {C P : ℝ} (p : ℂ) {r : ℝ}
    (hr : 0 < r) (hF : (∫⁻ X in unitCell, F X) ≤ ENNReal.ofReal (C*r⁻¹*P)) :
    (∫⁻ y in cell p r, F (toUnit p r y)) ≤ ENNReal.ofReal (C*r*P) := by
  rw [cell_majorant p hr.ne']
  apply (mul_le_mul' le_rfl hF).trans_eq
  rw [← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  field_simp
end PhysicalCells

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells

theorem physical_value_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*scale r k*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal |signedAverage g y t-signedAverage g y t'| ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := value_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp hD k p hn unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => F (toUnit (point (scale r k) p) (scale r k) y),
    hFm.comp (toUnit_continuous _ _).measurable,
    value_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t t' ht hb ht' hb'
  let X := toUnit (point (scale r k) p) (scale r k) y
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have hrk := scale_pos hr k
  have hf := hFb X (norm_unitCell hy) (t/scale r k) (t'/scale r k)
    (div_pos ht hrk) ((div_le_iff₀ hrk).mpr hb) (div_pos ht' hrk) ((div_le_iff₀ hrk).mpr hb')
  simpa only [signedAverage_affine _ _ _ hrk (div_pos ht hrk),
    signedAverage_affine _ _ _ hrk (div_pos ht' hrk),he,mul_div_cancel₀ _ hrk.ne'] using hf
end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

lemma cellPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ cellPrice N r h k S := sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

/-- A single actual endpoint price pays both the gradient and the normalized
oscillation. It is introduced before any spatial supremum is taken. -/
theorem physical_joint_price_oai : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal (|signedAverage g y t-signedAverage g y t'|/scale r k) ≤ F y) := by
  obtain ⟨Cs,hCs,hp⟩ := physical_size_price
  obtain ⟨Cv,hCv,hq⟩ := physical_value_price
  refine ⟨Cs+Cv,add_pos hCs hCv,?_⟩
  intro N r R hr hR hN g hg hh hs hd k p n
  obtain ⟨F,hFm,hFi,hFb⟩ := hp hr hR hN hg hh hs hd k p n.property
  obtain ⟨G,hGm,hGi,hGb⟩ := hq hr hR hN hg hh hs hd k p n.property
  have hrk := scale_pos hr k
  let B := rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p)
  have hB : 0 ≤ B := add_nonneg (rootMass_nonneg _ _ _ _) (cellPrice_nonneg hr hR hN hh hs k _)
  have hG : (∫⁻ y in cell (point (scale r k) p) (scale r k), ENNReal.ofReal (scale r k)⁻¹*G y) ≤ ENNReal.ofReal (Cv*B) := by
    rw [lintegral_const_mul _ hGm]
    calc
      _ ≤ ENNReal.ofReal (scale r k)⁻¹*ENNReal.ofReal (Cv*scale r k*B) := mul_le_mul' le_rfl hGi
      _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrk.le)]; congr 1; field_simp
  refine ⟨fun y => F y+ENNReal.ofReal (scale r k)⁻¹*G y,
    hFm.add (measurable_const.mul hGm),?_,?_,?_⟩
  · rw [lintegral_add_left hFm]
    calc
      _ ≤ ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cv*B) := add_le_add hFi hG
      _ = _ := by rw [← ENNReal.ofReal_add (mul_nonneg hCs.le hB) (mul_nonneg hCv.le hB),← add_mul]
  · intro y hy t ht
    exact (hFb y hy t ht).trans le_self_add
  · intro y hy t t' ht hb ht' hb'
    have hgg := mul_le_mul' (le_refl (ENNReal.ofReal (scale r k)⁻¹)) (hGb y hy t t' ht hb ht' hb')
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrk.le),inv_mul_eq_div] at hgg
    exact hgg.trans le_add_self
end CommonPrices

end SignedDisk

end

end OAI
end

theorem solution : type_of% @OAI.SignedDisk.CommonPrices.physical_joint_price_oai := @OAI.SignedDisk.CommonPrices.physical_joint_price_oai
