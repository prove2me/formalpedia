-- Prove2me | solution 1 for OAI.ExactModuli.kadets_werner_existence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:14:42.536405+00:00
-- url     : https://prove2.me/submissions/a67674bf-a583-4939-8597-f69159103a5a

import Mathlib
import Definitions.Def_DaugavetModuli

namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI

universe uX u_1 uY uIota uKappa uBeta uAlpha uGamma uB uR

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]










variable {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)






end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli

/-- Scalar clipping, equivalently sign(a) * min(|a|,h) when h >= 0. -/
def scalarClip (h a : ℝ) : ℝ := max (-h) (min h a)

lemma scalarClip_bounds {h a : ℝ} (hh : 0 ≤ h) :
    -h ≤ scalarClip h a ∧ scalarClip h a ≤ h := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma abs_scalarClip_le {h a : ℝ} (hh : 0 ≤ h) : |scalarClip h a| ≤ h :=
  abs_le.mpr (scalarClip_bounds hh)

lemma scalarClip_eq_of_mem {h a : ℝ} (ha : -h ≤ a) (hb : a ≤ h) :
    scalarClip h a = a := by
  simp [scalarClip, min_eq_right hb, max_eq_right ha]

lemma abs_sub_scalarClip {h a : ℝ} (hh : 0 ≤ h) :
    |a - scalarClip h a| = |a| - |scalarClip h a| := by
  by_cases ha : a < -h
  · have ha0 : a ≤ 0 := by linarith
    have hc : scalarClip h a = -h := by
      simp [scalarClip, min_eq_right (show a ≤ h by linarith), max_eq_left ha.le]
    rw [hc, abs_of_nonpos ha0, abs_of_nonpos (neg_nonpos.mpr hh),
      abs_of_nonpos (show a - -h ≤ 0 by linarith)]
    ring
  · by_cases hb : h < a
    · have hc : scalarClip h a = h := by
        simp [scalarClip, min_eq_left hb.le, max_eq_right (show -h ≤ h by linarith)]
      rw [hc, abs_of_nonneg (show 0 ≤ a by linarith), abs_of_nonneg hh,
        abs_of_nonneg (show 0 ≤ a - h by linarith)]
    · rw [scalarClip_eq_of_mem (le_of_not_gt ha) (le_of_not_gt hb)]
      simp

lemma abs_scalarClip_eq_min {h a : ℝ} (hh : 0 ≤ h) :
    |scalarClip h a| = min |a| h := by
  by_cases ha : a < -h
  · have hc : scalarClip h a = -h := by
      simp [scalarClip, min_eq_right (show a ≤ h by linarith), max_eq_left ha.le]
    rw [hc, abs_neg, abs_of_nonneg hh, abs_of_nonpos (show a ≤ 0 by linarith)]
    exact (min_eq_right (by linarith)).symm
  · by_cases hb : h < a
    · have hc : scalarClip h a = h := by
        simp [scalarClip, min_eq_left hb.le, max_eq_right (show -h ≤ h by linarith)]
      rw [hc, abs_of_nonneg hh, abs_of_nonneg (show 0 ≤ a by linarith)]
      exact (min_eq_right hb.le).symm
    · rw [scalarClip_eq_of_mem (le_of_not_gt ha) (le_of_not_gt hb)]
      exact (min_eq_left (abs_le.mpr ⟨le_of_not_gt ha, le_of_not_gt hb⟩)).symm

lemma scalarClip_mono (h : ℝ) : Monotone (scalarClip h) := by
  intro a b hab
  exact max_le_max_left _ (min_le_min_left _ hab)

lemma scalarClip_sub_le {h a b : ℝ} (hab : b ≤ a) :
    scalarClip h a - scalarClip h b ≤ a - b := by
  unfold scalarClip
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma abs_scalarClip_sub_le (h a b : ℝ) :
    |scalarClip h a - scalarClip h b| ≤ |a - b| := by
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (scalarClip_mono h hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact scalarClip_sub_le hab
  · rw [abs_sub_comm, abs_sub_comm a b]
    rw [abs_of_nonneg (sub_nonneg.mpr (scalarClip_mono h hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact scalarClip_sub_le hab

lemma scalar_average_abs (a b : ℝ) :
    (|a + b| + |a - b|) / 2 = max |a| |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (add_nonneg ha hb)]
    by_cases h : b ≤ a
    · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left h]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)), max_eq_right (le_of_not_ge h)]
      ring
  · rw [abs_of_nonneg ha, abs_of_nonpos hb,
        abs_of_nonneg (sub_nonneg.mpr (le_trans hb ha))]
    by_cases h : -b ≤ a
    · rw [abs_of_nonneg (by linarith : 0 ≤ a + b), max_eq_left h]; ring
    · rw [abs_of_nonpos (by linarith : a + b ≤ 0), max_eq_right (le_of_not_ge h)]; ring
  · rw [abs_of_nonpos ha, abs_of_nonneg hb,
        abs_of_nonpos (sub_nonpos.mpr (le_trans ha hb))]
    by_cases h : b ≤ -a
    · rw [abs_of_nonpos (by linarith : a + b ≤ 0), max_eq_left h]; ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ a + b), max_eq_right (le_of_not_ge h)]; ring
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (add_nonpos ha hb)]
    by_cases h : b ≤ a
    · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (by linarith : -a ≤ -b)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (by linarith : -b ≤ -a)]; ring

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Clip at a nonnegative L1 height. Clips are not required to belong to E. -/
def clip (h y : Lp ℝ 1 μ) : Lp ℝ 1 μ := (-h) ⊔ (h ⊓ y)

lemma coeFn_clip (h y : Lp ℝ 1 μ) :
    ⇑(clip h y) =ᵐ[μ] fun ω => scalarClip (h ω) (y ω) := by
  filter_upwards [Lp.coeFn_sup (-h) (h ⊓ y), Lp.coeFn_inf h y,
    Lp.coeFn_neg h] with ω h₁ h₂ h₃
  simp only [clip, h₁, h₂, h₃, Pi.sup_apply, Pi.inf_apply, Pi.neg_apply, scalarClip]

lemma norm_sub_clip (h y : Lp ℝ 1 μ) (hh : 0 ≤ h) :
    ‖y - clip h y‖ = ‖y‖ - ‖clip h y‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm y,
    L1.norm_eq_integral_norm (clip h y),
    ← integral_sub (L1.integrable_coeFn y).norm (L1.integrable_coeFn (clip h y)).norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub y (clip h y), coeFn_clip h y,
    (Lp.coeFn_nonneg h).mpr hh] with ω hs hc hpos
  simpa only [hs, hc, Pi.sub_apply, Real.norm_eq_abs] using abs_sub_scalarClip hpos

end ExactModuli

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma cofinite_ker [FiniteDimensional ℝ Y] (P : X →L[ℝ] Y) :
    Cofinite P.toLinearMap.ker := by
  refine ⟨P.isClosed_ker, ?_⟩
  exact FiniteDimensional.of_injective
    (LinearMap.quotKerEquivRange P.toLinearMap).toLinearMap
    (LinearMap.quotKerEquivRange P.toLinearMap).injective

/-- The finite norming-functional step of the clipping argument. In L1 the
    functionals can be taken to be signs; Hahn--Banach gives the same estimate. -/
lemma finite_norming_kernel (j : X →L[ℝ] Y) (s : Finset Y) :
    ∃ F : Submodule ℝ X, Cofinite F ∧
      ∀ y ∈ F, ∀ b ∈ s, ‖b‖ ≤ ‖b - j y‖ := by
  classical
  choose φ hφnorm hφval using fun b : s => exists_dual_vector'' ℝ (b : Y)
  let P : X →L[ℝ] (s → ℝ) := ContinuousLinearMap.pi fun b => (φ b).comp j
  refine ⟨P.toLinearMap.ker, cofinite_ker P, ?_⟩
  intro y hy b hb
  have hy' : P y = 0 := hy
  have hzero : φ ⟨b, hb⟩ (j y) = 0 := congrFun hy' ⟨b, hb⟩
  have heq : φ ⟨b, hb⟩ (b - j y) = ‖b‖ := by
    rw [map_sub, hzero, sub_zero, hφval ⟨b, hb⟩]
    rfl
  calc
    ‖b‖ = |φ ⟨b, hb⟩ (b - j y)| := by rw [heq, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖φ ⟨b, hb⟩‖ * ‖b - j y‖ := (φ ⟨b, hb⟩).le_opNorm _
    _ ≤ 1 * ‖b - j y‖ := mul_le_mul_of_nonneg_right (hφnorm _) (norm_nonneg _)
    _ = ‖b - j y‖ := one_mul _

end ExactModuli

namespace ExactModuli

/-- The quantitative half-mass estimate, before the net radius tends to zero. -/
lemma half_mass_of_norming {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {b c u : Y} {ε : ℝ}
    (hunit : ‖u‖ = 1) (hres : ‖u - c‖ = ‖u‖ - ‖c‖)
    (hnet : ‖c - b‖ < ε) (hker : ‖b‖ ≤ ‖b - u‖) :
    ‖c‖ < 1 / 2 + ε := by
  have h₁ := norm_sub_norm_le c b
  have h₂ : ‖b - u‖ ≤ ‖b - c‖ + ‖c - u‖ := by
    calc ‖b - u‖ = ‖(b - c) + (c - u)‖ := by congr 1; abel
         _ ≤ ‖b - c‖ + ‖c - u‖ := norm_add_le _ _
  rw [norm_sub_rev b c, norm_sub_rev c u, hres, hunit] at h₂
  linarith

end ExactModuli

namespace ExactModuli
variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

lemma small_set_integral_norm [IsFiniteMeasure μ] (f : Lp ℝ 1 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set Ω, MeasurableSet s → μ.real s ≤ δ →
      (∫ ω in s, |f ω| ∂μ) ≤ ε := by
  obtain ⟨δ, hδ, hbound⟩ :=
    MemLp.eLpNorm_indicator_le (p := (1 : ℝ≥0∞)) le_rfl (by norm_num) (Lp.memLp f) hε
  refine ⟨δ, hδ, fun s hs hμs => ?_⟩
  have hs' : μ s ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ s)]
    exact ENNReal.ofReal_le_ofReal hμs
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound s hs hs')
  rw [ENNReal.toReal_ofReal hε.le,
    eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm ((Lp.aestronglyMeasurable f).indicator hs)] at hle
  simpa only [norm_indicator_eq_indicator_norm, integral_indicator hs, Real.norm_eq_abs] using hle

lemma measureDistance_threshold_nonempty [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) :
    {a : ℝ | 0 < a ∧ μ.real {ω | a < |f ω - g ω|} < a}.Nonempty := by
  refine ⟨2, by norm_num, ?_⟩
  exact lt_of_le_of_lt measureReal_le_one (by norm_num)

lemma measureDistance_nonneg [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) :
    0 ≤ measureDistance μ f g := by
  exact le_csInf (measureDistance_threshold_nonempty f g) (fun _ ha => ha.1.le)

lemma tail_lt_of_measureDistance_lt [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ)
    {ε : ℝ} (h : measureDistance μ f g < ε) :
    μ.real {ω | ε < |f ω - g ω|} < ε := by
  obtain ⟨a, ⟨ha, htail⟩, haε⟩ :=
    (csInf_lt_iff ⟨0, fun _ ha => ha.1.le⟩ (measureDistance_threshold_nonempty f g)).mp h
  have hsub : {ω | ε < |f ω - g ω|} ⊆ {ω | a < |f ω - g ω|} :=
    fun _ hω => lt_trans haε hω
  exact lt_trans (lt_of_le_of_lt (measureReal_mono hsub) htail) haε

lemma scalarClip_diff_le_two {h a b : ℝ} (hh : 0 ≤ h) :
    |scalarClip h a - scalarClip h b| ≤ 2 * h := by
  have hab : |scalarClip h a - scalarClip h b| ≤
      |scalarClip h a| + |scalarClip h b| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (scalarClip h a) (scalarClip h b)
  linarith [abs_scalarClip_le (a := a) hh, abs_scalarClip_le (a := b) hh]

/-- Uniform passage from the measure metric to the L1 norm on the clipped image.
    This proves the norm-precompactness step without needing to choose subsequences. -/
lemma clip_small_tail [IsProbabilityMeasure μ] (h : Lp ℝ 1 μ) (hh : 0 ≤ h)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f g : Lp ℝ 1 μ,
      μ.real {ω | δ < |f ω - g ω|} < δ → ‖clip h f - clip h g‖ < ε := by
  obtain ⟨d, hd, hsmall⟩ := small_set_integral_norm h (show 0 < ε / 4 by linarith)
  let δ := min (ε / 4) (d / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδd : δ ≤ d := (min_le_right _ _).trans (by linarith)
  refine ⟨δ, hδ, fun f g htail => ?_⟩
  let s := {ω | δ < |f ω - g ω|}
  have hs : MeasurableSet s :=
    isOpen_Ioi.measurableSet.preimage
      (((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable).abs)
  have hsmall' : (∫ ω in s, |h ω| ∂μ) ≤ ε / 4 :=
    hsmall s hs (htail.le.trans hδd)
  have hbound : ∀ᵐ ω ∂μ, ‖(clip h f - clip h g) ω‖ ≤
      δ + s.indicator (fun ω => 2 * |h ω|) ω := by
    filter_upwards [Lp.coeFn_sub (clip h f) (clip h g), coeFn_clip h f,
      coeFn_clip h g, (Lp.coeFn_nonneg h).mpr hh] with ω hsub hf hg hnonneg
    simp only [hsub, Pi.sub_apply, hf, hg, Real.norm_eq_abs]
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω, abs_of_nonneg hnonneg]
      exact (scalarClip_diff_le_two hnonneg).trans (by linarith)
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact (abs_scalarClip_sub_le _ _ _).trans (le_of_not_gt hω)
  have hbound_int := integral_mono_ae
    (L1.integrable_coeFn (clip h f - clip h g)).norm
    ((integrable_const δ).add (((L1.integrable_coeFn h).abs.const_mul 2).indicator hs)) hbound
  simp only [Pi.add_apply] at hbound_int
  rw [← L1.norm_eq_integral_norm,
    integral_add (integrable_const δ) (((L1.integrable_coeFn h).abs.const_mul 2).indicator hs),
    integral_indicator hs, integral_const_mul] at hbound_int
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbound_int
  linarith

lemma finite_clip_net [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (hpre : MeasurePrecompactBall μ E) (h : Lp ℝ 1 μ) (hh : 0 ≤ h)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (Lp ℝ 1 μ), ∀ y : E, ‖y‖ ≤ 1 →
      ∃ b ∈ s, ‖clip h (y : Lp ℝ 1 μ) - b‖ < ε := by
  classical
  obtain ⟨δ, hδ, hclip⟩ := clip_small_tail h hh hε
  obtain ⟨s, hs⟩ := hpre δ hδ
  refine ⟨s.image (clip h), fun y hy => ?_⟩
  obtain ⟨b, hb, hdist⟩ := hs y hy
  exact ⟨clip h b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
    hclip _ _ (tail_lt_of_measureDistance_lt _ _ hdist)⟩

lemma finite_cokernel_half_clip [IsProbabilityMeasure μ]
    (E : Submodule ℝ (Lp ℝ 1 μ)) (hpre : MeasurePrecompactBall μ E)
    (h : Lp ℝ 1 μ) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Submodule ℝ E, Cofinite F ∧ ∀ y ∈ F, ‖y‖ = 1 →
      ‖clip h (y : Lp ℝ 1 μ)‖ < 1 / 2 + ε := by
  obtain ⟨s, hs⟩ := finite_clip_net E hpre h hh hε
  obtain ⟨F, hF, hker⟩ := finite_norming_kernel E.subtypeL s
  refine ⟨F, hF, fun y hy hunit => ?_⟩
  obtain ⟨b, hb, hnet⟩ := hs y hunit.le
  exact half_mass_of_norming hunit (norm_sub_clip h _ hh) hnet (hker y hy b hb)

end ExactModuli

namespace ExactModuli

lemma scalar_overlap (a b t : ℝ) (ht : 0 < t) :
    (|a + t * b| + |a - t * b|) / 2 =
      |a| + t * (|b| - |scalarClip (|a| / t) b|) := by
  rw [scalar_average_abs, abs_mul, abs_of_pos ht,
    abs_scalarClip_eq_min (div_nonneg (abs_nonneg _) ht.le)]
  by_cases hb : |b| ≤ |a| / t
  · have hb' : t * |b| ≤ |a| := by simpa [mul_comm] using (le_div_iff₀ ht).mp hb
    rw [min_eq_left hb, max_eq_left hb']
    ring
  · have hb' : |a| ≤ t * |b| := by
      have := (div_lt_iff₀ ht).mp (lt_of_not_ge hb)
      linarith
    rw [min_eq_right (le_of_not_ge hb), max_eq_right hb']
    field_simp
    ring

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

def clipHeight (x : Lp ℝ 1 μ) (t : ℝ) : Lp ℝ 1 μ := t⁻¹ • |x|

lemma coeFn_clipHeight (x : Lp ℝ 1 μ) (t : ℝ) :
    ⇑(clipHeight x t) =ᵐ[μ] fun ω => |x ω| / t := by
  filter_upwards [Lp.coeFn_smul t⁻¹ |x|, Lp.coeFn_abs x] with ω h₁ h₂
  simp only [clipHeight, h₁, h₂, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma clipHeight_nonneg (x : Lp ℝ 1 μ) {t : ℝ} (ht : 0 < t) :
    0 ≤ clipHeight x t := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [coeFn_clipHeight x t] with ω hω
  rw [hω]
  exact div_nonneg (abs_nonneg _) ht.le

lemma overlap_identity (x y : Lp ℝ 1 μ) {t : ℝ} (ht : 0 < t) :
    (‖x + t • y‖ + ‖x - t • y‖) / 2 =
      ‖x‖ + t * (‖y‖ - ‖clip (clipHeight x t) y‖) := by
  let c := clip (clipHeight x t) y
  have hx := (L1.integrable_coeFn x).norm
  have hy := (L1.integrable_coeFn y).norm
  have hc := (L1.integrable_coeFn c).norm
  have hplus := (L1.integrable_coeFn (x + t • y)).norm
  have hminus := (L1.integrable_coeFn (x - t • y)).norm
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm (x - t • y),
    L1.norm_eq_integral_norm x, L1.norm_eq_integral_norm y,
    L1.norm_eq_integral_norm (clip (clipHeight x t) y)]
  calc
    ((∫ ω, ‖(x + t • y) ω‖ ∂μ) + (∫ ω, ‖(x - t • y) ω‖ ∂μ)) / 2 =
        ∫ ω, (‖(x + t • y) ω‖ + ‖(x - t • y) ω‖) / 2 ∂μ := by
          rw [integral_div, integral_add hplus hminus]
    _ = ∫ ω, ‖x ω‖ + t * (‖y ω‖ - ‖c ω‖) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add x (t • y), Lp.coeFn_sub x (t • y),
        Lp.coeFn_smul t y, coeFn_clip (clipHeight x t) y,
        coeFn_clipHeight x t] with ω hp hm hty hclip hh
      simpa only [hp, hm, hty, hclip, hh, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, c] using scalar_overlap (x ω) (y ω) t ht
    _ = (∫ ω, ‖x ω‖ ∂μ) + t * ((∫ ω, ‖y ω‖ ∂μ) - ∫ ω, ‖c ω‖ ∂μ) := by
      have hdiff : Integrable (fun ω => ‖y ω‖ - ‖c ω‖) μ := hy.sub hc
      rw [integral_add hx (hdiff.const_mul t), integral_const_mul, integral_sub hy hc]

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma cofinite_top : Cofinite (⊤ : Submodule ℝ X) := by
  refine ⟨?_, inferInstance⟩
  simpa only [Submodule.top_coe] using isClosed_univ (X := X)

lemma cofinite_nontrivial (hinf : ¬ FiniteDimensional ℝ X) {F : Submodule ℝ X}
    (hF : Cofinite F) : Nontrivial F := by
  by_contra hn
  have : Subsingleton F := not_nontrivial_iff_subsingleton.mp hn
  have : FiniteDimensional ℝ (X ⧸ F) := hF.2
  exact hinf (Module.Finite.of_submodule_quotient F)

lemma cofinite_has_unit (hinf : ¬ FiniteDimensional ℝ X) {F : Submodule ℝ X}
    (hF : Cofinite F) : ∃ y ∈ F, ‖y‖ = 1 := by
  have : Nontrivial F := cofinite_nontrivial hinf hF
  obtain ⟨y, hy⟩ := exists_norm_eq F (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨y, y.property, hy⟩

lemma norm_average_scale_le (x z : X) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (‖x + r • z‖ + ‖x - r • z‖) / 2 ≤ (‖x + z‖ + ‖x - z‖) / 2 := by
  have h₁ : x + r • z = ((1 + r) / 2) • (x + z) + ((1 - r) / 2) • (x - z) := by
    module
  have h₂ : x - r • z = ((1 - r) / 2) • (x + z) + ((1 + r) / 2) • (x - z) := by
    module
  have hpos : 0 ≤ (1 + r) / 2 := by linarith
  have hneg : 0 ≤ (1 - r) / 2 := by linarith
  have hp := norm_add_le (((1 + r) / 2) • (x + z)) (((1 - r) / 2) • (x - z))
  have hm := norm_add_le (((1 - r) / 2) • (x + z)) (((1 + r) / 2) • (x - z))
  rw [← h₁, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hpos, abs_of_nonneg hneg] at hp
  rw [← h₂, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hpos, abs_of_nonneg hneg] at hm
  nlinarith

lemma increment_normalize_le (x y : X) {t : ℝ} (hy : 1 ≤ ‖y‖) :
    averagedIncrement (normSeminorm ℝ X) x t (‖y‖⁻¹ • y) ≤
      averagedIncrement (normSeminorm ℝ X) x t y := by
  have hyn : 0 < ‖y‖ := by linarith
  have hi : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hyn).mpr hy
  have h := norm_average_scale_le x (t • y) (inv_nonneg.mpr hyn.le) hi
  simpa only [averagedIncrement, coe_normSeminorm, smul_smul, mul_comm t,
    sub_le_sub_iff_right] using h

lemma averagedIncrement_nonneg {x y : X} (hx : ‖x‖ = 1) (t : ℝ) :
    0 ≤ averagedIncrement (normSeminorm ℝ X) x t y := by
  have h := norm_add_le (x + t • y) (x - t • y)
  have heq : x + t • y + (x - t • y) = (2 : ℝ) • x := by module
  rw [heq, norm_smul, hx] at h
  norm_num at h
  change 0 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1
  linarith

lemma averagedIncrement_le {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : averagedIncrement (normSeminorm ℝ X) x t y ≤ t := by
  have hp := norm_add_le x (t • y)
  have hm := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy, hx, mul_one] at hp hm
  change (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ t
  linarith

lemma averagedIncrement_ge_t_sub_one {x y : X} {t : ℝ} (ht : 0 ≤ t) (hy : 1 ≤ ‖y‖) :
    t - 1 ≤ averagedIncrement (normSeminorm ℝ X) x t y := by
  have h := norm_sub_le (x + t • y) (x - t • y)
  have heq : x + t • y - (x - t • y) = (2 * t) • y := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * t)] at h
  change t - 1 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1
  nlinarith

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Inner sets are kept explicit to make nonemptiness and conditional completeness visible. -/
def averageValues (x : X) (t : ℝ) (F : Submodule ℝ X) : Set ℝ :=
  {a | ∃ y ∈ F, 1 ≤ ‖y‖ ∧ a = averagedIncrement (normSeminorm ℝ X) x t y}

def oneSidedValues (x : X) (t : ℝ) (F : Submodule ℝ X) : Set ℝ :=
  {a | ∃ y ∈ F, ‖y‖ = 1 ∧ a = ‖x + t • y‖ - 1}

lemma averageValues_nonempty (hinf : ¬ FiniteDimensional ℝ X) (x : X) (t : ℝ)
    {F : Submodule ℝ X} (hF : Cofinite F) : (averageValues x t F).Nonempty := by
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  exact ⟨_, y, hy, hny.ge, rfl⟩

lemma averageValues_bddBelow (x : X) (t : ℝ) (F : Submodule ℝ X) :
    BddBelow (averageValues x t F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y, hy, hny, rfl⟩
  change -1 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1
  linarith [norm_nonneg (x + t • y), norm_nonneg (x - t • y)]

lemma oneSidedValues_nonempty (hinf : ¬ FiniteDimensional ℝ X) (x : X) (t : ℝ)
    {F : Submodule ℝ X} (hF : Cofinite F) : (oneSidedValues x t F).Nonempty := by
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  exact ⟨_, y, hy, hny, rfl⟩

lemma oneSidedValues_bddBelow (x : X) (t : ℝ) (F : Submodule ℝ X) :
    BddBelow (oneSidedValues x t F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y, hy, hny, rfl⟩
  linarith [norm_nonneg (x + t • y)]

lemma H_outer_bddAbove (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {r | ∃ F : Submodule ℝ X, Cofinite F ∧ r = sInf (averageValues x t F)} := by
  refine ⟨t, ?_⟩
  rintro r ⟨F, hF, rfl⟩
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  exact (csInf_le (averageValues_bddBelow x t F) ⟨y, hy, hny.ge, rfl⟩).trans
    (averagedIncrement_le hx hny ht)

lemma D_outer_bddAbove (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {r | ∃ F : Submodule ℝ X, Cofinite F ∧ r = sInf (oneSidedValues x t F)} := by
  refine ⟨t, ?_⟩
  rintro r ⟨F, hF, rfl⟩
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  apply (csInf_le (oneSidedValues_bddBelow x t F) ⟨y, hy, hny, rfl⟩).trans
  have h := norm_add_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hny, mul_one, hx] at h
  linarith

lemma le_H_of_cofinite (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {F : Submodule ℝ X} (hF : Cofinite F) {a : ℝ}
    (ha : ∀ y ∈ F, 1 ≤ ‖y‖ → a ≤ averagedIncrement (normSeminorm ℝ X) x t y) :
    a ≤ H (normSeminorm ℝ X) x t := by
  apply le_trans (b := sInf (averageValues x t F))
  · apply le_csInf (averageValues_nonempty hinf x t hF)
    rintro r ⟨y, hy, hny, rfl⟩
    exact ha y hy hny
  · exact le_csSup (H_outer_bddAbove hinf hx ht) ⟨F, hF, rfl⟩

lemma le_D_of_cofinite (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {F : Submodule ℝ X} (hF : Cofinite F) {a : ℝ}
    (ha : ∀ y ∈ F, ‖y‖ = 1 → a ≤ ‖x + t • y‖ - 1) :
    a ≤ D (normSeminorm ℝ X) x t := by
  apply le_trans (b := sInf (oneSidedValues x t F))
  · apply le_csInf (oneSidedValues_nonempty hinf x t hF)
    rintro r ⟨y, hy, hny, rfl⟩
    exact ha y hy hny
  · exact le_csSup (D_outer_bddAbove hinf hx ht) ⟨F, hF, rfl⟩

lemma H_ge_t_sub_one (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : t - 1 ≤ H (normSeminorm ℝ X) x t :=
  le_H_of_cofinite hinf hx ht cofinite_top
    (fun _ _ hy => averagedIncrement_ge_t_sub_one ht hy)

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The sharp half-mass lower estimate from the measure-precompactness hypothesis. -/
lemma H_ge_half [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (hinf : ¬ FiniteDimensional ℝ E) (hpre : MeasurePrecompactBall μ E)
    {x : E} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 < t) :
    t / 2 ≤ H (normSeminorm ℝ E) x t := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hclip⟩ := finite_cokernel_half_clip E hpre (clipHeight (x : Lp ℝ 1 μ) t)
    (clipHeight_nonneg _ ht) (show 0 < ε / t by positivity)
  have heps : t * (ε / t) = ε := by field_simp
  have hb : t / 2 - ε ≤ H (normSeminorm ℝ E) x t := by
    apply le_H_of_cofinite hinf hx ht.le hF
    intro y hy hny
    let u : E := ‖y‖⁻¹ • y
    have hyz : y ≠ 0 := by intro h; norm_num [h] at hny
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hyz
    have huF : u ∈ F := F.smul_mem _ hy
    have hcu := hclip u huF hu
    have hident := overlap_identity (x : Lp ℝ 1 μ) (u : Lp ℝ 1 μ) ht
    have hxu : ‖(x : Lp ℝ 1 μ)‖ = 1 := hx
    have huu : ‖(u : Lp ℝ 1 μ)‖ = 1 := hu
    rw [hxu, huu] at hident
    have hunitlower : t / 2 - ε ≤ averagedIncrement (normSeminorm ℝ E) x t u := by
      change t / 2 - ε ≤
        (‖(x : Lp ℝ 1 μ) + t • (u : Lp ℝ 1 μ)‖ +
          ‖(x : Lp ℝ 1 μ) - t • (u : Lp ℝ 1 μ)‖) / 2 - 1
      rw [hident]
      nlinarith
    exact hunitlower.trans (increment_normalize_le x y hny)
  linarith

theorem clipping_lower_bound [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (hinf : ¬ FiniteDimensional ℝ E) (hpre : MeasurePrecompactBall μ E)
    {x : E} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 < t) :
    max (t / 2) (t - 1) ≤ H (normSeminorm ℝ E) x t := by
  exact max_le (H_ge_half E hinf hpre hx ht) (H_ge_t_sub_one hinf hx ht.le)

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma norm_ray_ge_t_sub_one {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : t - 1 ≤ ‖x + t • y‖ := by
  have h := norm_sub_le (x + t • y) x
  have heq : x + t • y - x = t • y := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy, mul_one, hx] at h
  linarith

/-- The one-sided lower estimate needs only a norming functional. -/
theorem oneSided_lower_bound (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : max 0 (t - 2) ≤ D (normSeminorm ℝ X) x t := by
  obtain ⟨φ, hφnorm, hφx⟩ := exists_dual_vector ℝ x (by rw [hx]; norm_num)
  have hφx' : φ x = 1 := by
    change φ x = ‖x‖ at hφx
    simpa only [hx] using hφx
  apply le_D_of_cofinite hinf hx ht (cofinite_ker φ)
  intro y hy hny
  have hφy : φ y = 0 := hy
  have happ : φ (x + t • y) = 1 := by simp [hφx', hφy]
  have hnorm := φ.le_opNorm (x + t • y)
  rw [happ, hφnorm, one_mul, norm_one] at hnorm
  have hrev := norm_ray_ge_t_sub_one hx hny ht
  exact max_le (by linarith) (by linarith)

/-- A single almost antipodal endpoint controls all radii, including the corner t=2. -/
lemma norm_ray_endpoint_bound {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {L ε t : ℝ} (hL : 0 < L) (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hend : ‖x + L • y‖ ≤ 1 + ε) :
    ‖x + t • y‖ ≤ 1 + ε + max 0 (t - L) := by
  by_cases htL : t ≤ L
  · have hr : 0 ≤ t / L := div_nonneg ht hL.le
    have hr' : t / L ≤ 1 := (div_le_one hL).mpr htL
    have hid : x + t • y = (1 - t / L) • x + (t / L) • (x + L • y) := by
      have hmul : t / L * L = t := div_mul_cancel₀ t hL.ne'
      rw [smul_add, smul_smul, hmul]
      module
    rw [max_eq_left (sub_nonpos.mpr htL), add_zero, hid]
    have h := norm_add_le ((1 - t / L) • x) ((t / L) • (x + L • y))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hr'), abs_of_nonneg hr, hx, mul_one] at h
    nlinarith
  · have hLt : L ≤ t := le_of_not_ge htL
    have hid : x + t • y = (x + L • y) + (t - L) • y := by module
    rw [max_eq_right (sub_nonneg.mpr hLt), hid]
    have h := norm_add_le (x + L • y) ((t - L) • y)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hLt), hy, mul_one] at h
    linarith

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma exists_unit_near_opNorm (T : X →L[ℝ] Y) {r : ℝ} (hr : 0 ≤ r) (hrT : r < ‖T‖) :
    ∃ y : X, ‖y‖ = 1 ∧ r < ‖T y‖ := by
  obtain ⟨u, hu, hTu⟩ := T.exists_lt_apply_of_lt_opNorm hrT
  have hu0 : u ≠ 0 := by
    intro heq
    simp only [heq, map_zero, norm_zero] at hTu
    linarith
  have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  refine ⟨‖u‖⁻¹ • u, norm_smul_inv_norm hu0, ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos)]
  have hinv : 1 ≤ ‖u‖⁻¹ := (one_le_inv₀ hnpos).mpr hu.le
  have := mul_le_mul_of_nonneg_right hinv (norm_nonneg (T u))
  exact hTu.trans_le (by simpa only [one_mul] using this)

lemma daugavet_normalized_slice (hd : Daugavet X) {w : X} (hw : ‖w‖ = 1)
    (ell : X →L[ℝ] ℝ) (hell : ‖ell‖ = 1) {α ρ : ℝ} (hα : α < 1) (hρ : 0 < ρ) :
    ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖ := by
  let η := min (1 - α) (min (ρ / 2) 1) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηα : η < 1 - α := by
    have := min_le_left (1 - α) (min (ρ / 2) 1)
    dsimp [η] at *; linarith
  have hηρ : 2 * η < ρ := by
    have := (min_le_right (1 - α) (min (ρ / 2) 1)).trans (min_le_left _ _)
    dsimp [η] at *; linarith
  have hη1 : η < 1 := by
    have := (min_le_right (1 - α) (min (ρ / 2) 1)).trans (min_le_right _ _)
    dsimp [η] at *; linarith
  let T : X →L[ℝ] X := ContinuousLinearMap.id ℝ X + ell.smulRight w
  have hT : ‖T‖ = 2 := by
    change ‖ContinuousLinearMap.id ℝ X + ell.smulRight w‖ = 2
    rw [hd ell w, ContinuousLinearMap.norm_smulRight_apply, hell, hw]
    norm_num
  obtain ⟨u, hu, hval⟩ := exists_unit_near_opNorm T (show 0 ≤ 2 - η by linarith)
    (show 2 - η < ‖T‖ by rw [hT]; linarith)
  obtain ⟨y, hy, hsign, hyval⟩ : ∃ y : X, ‖y‖ = 1 ∧ 0 ≤ ell y ∧
      2 - η < ‖y + ell y • w‖ := by
    by_cases he : 0 ≤ ell u
    · exact ⟨u, hu, he, hval⟩
    · refine ⟨-u, by simpa using hu, by simpa using (neg_nonneg.mpr (le_of_not_ge he)), ?_⟩
      change 2 - η < ‖T (-u)‖
      simpa only [map_neg, norm_neg] using hval
  have he1 : ell y ≤ 1 := by
    have hb := ell.le_opNorm y
    rw [hell, hy, one_mul, Real.norm_eq_abs] at hb
    exact le_trans (le_abs_self _) hb
  have hnear : 1 - η < ell y := by
    have hb := norm_add_le y (ell y • w)
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsign, hw, mul_one] at hb
    linarith
  refine ⟨y, hy, by linarith, ?_⟩
  have hid : y + ell y • w = (w + y) + (ell y - 1) • w := by module
  have hb := norm_add_le (w + y) ((ell y - 1) • w)
  rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr he1), hw,
    mul_one] at hb
  linarith

/-- Forward half of the actual rank-one/slice equivalence, with a unit-sphere witness. -/
theorem daugavet_unitSlice (hd : Daugavet X) : UnitSliceProperty X := by
  intro w hw ell α hne ρ hρ
  obtain ⟨u, hu, hau⟩ := hne
  by_cases he0 : ell = 0
  · have hα : α < 0 := by simpa [he0] using hau
    refine ⟨w, hw, by simpa [he0] using hα, ?_⟩
    have htwo : ‖w + w‖ = 2 := by rw [← two_smul ℝ w, norm_smul, hw]; norm_num
    rw [htwo]; linarith
  · have hn : 0 < ‖ell‖ := norm_pos_iff.mpr he0
    have hα : α < ‖ell‖ := by
      have hbound := ell.le_opNorm u
      have := le_abs_self (ell u)
      rw [Real.norm_eq_abs] at hbound
      nlinarith
    have hnormalized : ‖‖ell‖⁻¹ • ell‖ = 1 := norm_smul_inv_norm he0
    obtain ⟨y, hy, hslice, hfar⟩ := daugavet_normalized_slice hd hw (‖ell‖⁻¹ • ell)
      hnormalized ((div_lt_one hn).mpr hα) hρ
    refine ⟨y, hy, ?_, hfar⟩
    change α / ‖ell‖ < ‖ell‖⁻¹ * ell y at hslice
    rw [← div_eq_inv_mul] at hslice
    exact (div_lt_div_iff_of_pos_right hn).mp hslice

end ExactModuli

namespace ExactModuli
open scoped RealInnerProductSpace
variable {Y : Type uY} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma exposed_support_approx {K : Set Y} (hK : IsCompact K) {q : Y} (hq : q ∈ K)
    (ell : Y →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ K.exposedPoints ℝ, ell q - ε < ell p := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  let c : ℝ := ε / (M ^ 2 + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_eq : c * (M ^ 2 + 1) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨q, hq⟩
    ((ell.continuous.add (continuous_const.mul (continuous_norm.pow 2))).continuousOn :
      ContinuousOn (fun z : Y => ell z + c * ‖z‖ ^ 2) K)
  have hpM : ‖p‖ ^ 2 ≤ M ^ 2 := by nlinarith [hM p hp, norm_nonneg p]
  refine ⟨p, ⟨hp, ell + (2 * c) • innerSL ℝ p, ?_⟩, ?_⟩
  · intro z hz
    have hcomp := hmax hz
    change ell z + c * ‖z‖ ^ 2 ≤ ell p + c * ‖p‖ ^ 2 at hcomp
    have hsq := norm_sub_sq_real p z
    change (ell z + (2 * c) * ⟪p, z⟫ ≤ ell p + (2 * c) * ⟪p, p⟫) ∧
      ((ell p + (2 * c) * ⟪p, p⟫ ≤ ell z + (2 * c) * ⟪p, z⟫) → z = p)
    rw [real_inner_self_eq_norm_sq]
    constructor
    · nlinarith [sq_nonneg ‖p - z‖]
    · intro he
      have hsqc := congrArg (fun a : ℝ => c * a) hsq
      have hprod : c * ‖p - z‖ ^ 2 ≤ 0 := by nlinarith only [hcomp, he, hsqc]
      have hsqzero : ‖p - z‖ ^ 2 ≤ 0 := by
        by_contra hn
        have hh := mul_pos hc (lt_of_not_ge hn)
        linarith
      have hzero : ‖p - z‖ = 0 := by nlinarith [norm_nonneg (p - z)]
      exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  · have hcomp := hmax hq
    change ell q + c * ‖q‖ ^ 2 ≤ ell p + c * ‖p‖ ^ 2 at hcomp
    nlinarith [sq_nonneg ‖q‖]

lemma closure_convexHull_exposed {K : Set Y} (hK : IsCompact K) (hconv : Convex ℝ K) :
    closure (convexHull ℝ (K.exposedPoints ℝ)) = K := by
  apply (closure_minimal (convexHull_min exposedPoints_subset hconv) hK.isClosed).antisymm
  intro q hq
  by_contra hq'
  obtain ⟨ell, a, ha, haq⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (K.exposedPoints ℝ)).closure isClosed_closure hq'
  obtain ⟨p, hp, happ⟩ := exposed_support_approx hK hq ell (sub_pos.mpr haq)
  have hb := ha p (subset_closure (subset_convexHull ℝ _ hp))
  linarith

/-- Compactness shrinks a slice about its uniquely exposed maximizer. -/
lemma exposed_small_slice {K : Set Y} (hK : IsCompact K) {p : Y}
    (hp : p ∈ K.exposedPoints ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ (ell : Y →L[ℝ] ℝ) (β : ℝ), β < ell p ∧
      ∀ q ∈ K, β < ell q → ‖q - p‖ < r := by
  obtain ⟨hpK, ell, hell⟩ := hp
  let C := K ∩ {q : Y | r ≤ ‖q - p‖}
  have hC : IsCompact C := hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  by_cases hne : C.Nonempty
  · obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne ell.continuous.continuousOn
    have hlt : ell q < ell p := by
      refine lt_of_le_of_ne (hell q hq.1).1 ?_
      intro he
      have hqp := (hell q hq.1).2 he.ge
      have : r ≤ ‖q - p‖ := hq.2
      simp only [hqp, sub_self, norm_zero] at this
      linarith
    refine ⟨ell, ell q, hlt, ?_⟩
    intro z hz hβ
    by_contra hdist
    exact (hmax ⟨hz, le_of_not_gt hdist⟩).not_gt hβ
  · refine ⟨ell, ell p - 1, by linarith, ?_⟩
    intro q hq _
    by_contra hdist
    exact hne ⟨q, hq, le_of_not_gt hdist⟩

end ExactModuli

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Bourgain's finite-dimensional slice-combination lemma, in the exact form needed for
finite-quotient neighborhoods. Zero weights are harmless and allowed. -/
lemma bourgain_image (T : X →L[ℝ] Y) {u : X} (hu : ‖u‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ) (ell : ι → X →L[ℝ] ℝ) (β : ι → ℝ),
      (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧
      (∀ i, ∃ y : X, ‖y‖ ≤ 1 ∧ β i < ell i y) ∧
      ∀ y : ι → X, (∀ i, ‖y i‖ ≤ 1 ∧ β i < ell i (y i)) →
        ‖T (∑ i, a i • y i) - T u‖ < r := by
  let B := Metric.closedBall (0 : X) 1
  let K := closure (T '' B)
  have hK : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closure, ((Metric.isBounded_closedBall (x := (0 : X)) (r := 1)).image T).closure⟩
  have hconv : Convex ℝ K := ((convex_closedBall (0 : X) 1).linear_image T.toLinearMap).closure
  have hTu : T u ∈ K := subset_closure ⟨u, by simpa [B] using hu, rfl⟩
  rw [← closure_convexHull_exposed hK hconv] at hTu
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hTu (r / 2) (by positivity)
  obtain ⟨ι, hι, a, v, ha, hsum, hv, hpv⟩ := mem_convexHull_iff_exists_fintype.mp hp
  let := hι
  choose ell β hβ hsmall using fun i => exposed_small_slice hK (hv i) (show 0 < r / 2 by positivity)
  have hne : ∀ i, ∃ y : X, ‖y‖ ≤ 1 ∧ β i < ell i (T y) := by
    intro i
    have hvi : v i ∈ closure (T '' B) := (hv i).1
    obtain ⟨q, hqβ, y, hy, rfl⟩ := mem_closure_iff.mp hvi {q | β i < ell i q}
      (isOpen_lt continuous_const (ell i).continuous) (hβ i)
    exact ⟨y, by simpa [B] using hy, hqβ⟩
  refine ⟨ι, hι, a, fun i => (ell i).comp T, β, ha, hsum, hne, ?_⟩
  intro y hy
  have hpbound : ‖T (∑ i, a i • y i) - p‖ ≤ r / 2 := by
    have hid : T (∑ i, a i • y i) - p = ∑ i, a i • (T (y i) - v i) := by
      rw [← hpv]
      simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    rw [hid]
    calc
      ‖∑ i, a i • (T (y i) - v i)‖ ≤ ∑ i, ‖a i • (T (y i) - v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, a i * (r / 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)]
        apply mul_le_mul_of_nonneg_left _ (ha i)
        exact (hsmall i (T (y i)) (subset_closure ⟨y i, by simpa [B] using (hy i).1, rfl⟩)
          (hy i).2).le
      _ = r / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hpu : ‖p - T u‖ < r / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hb := norm_add_le (T (∑ i, a i • y i) - p) (p - T u)
  rw [sub_add_sub_cancel] at hb
  linarith

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma dual_apply_le_norm (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (z : X) : φ z ≤ ‖z‖ := by
  have hb := φ.le_opNorm z
  rw [Real.norm_eq_abs] at hb
  have hc := mul_le_mul_of_nonneg_right hφ (norm_nonneg z)
  linarith [le_abs_self (φ z)]

/-- One induction step in the diametral argument, with additive rather than multiplicative error. -/
lemma slice_add_almost (hsp : UnitSliceProperty X) {w₀ : X} (hw₀ : ‖w₀‖ = 1)
    (ell : X →L[ℝ] ℝ) (β : ℝ) (hne : ∃ y : X, ‖y‖ ≤ 1 ∧ β < ell y)
    (z : X) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∃ y : X, ‖y‖ = 1 ∧ β < ell y ∧ ‖z‖ + a - δ ≤ ‖z + a • y‖ := by
  by_cases hz : z = 0
  · obtain ⟨y, hy, hβ, _⟩ := hsp w₀ hw₀ ell β hne 1 zero_lt_one
    refine ⟨y, hy, hβ, ?_⟩
    simp only [hz, norm_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hy, mul_one]
    linarith
  · let u := ‖z‖⁻¹ • z
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hz
    let ρ := δ / (‖z‖ + a + 1)
    have hden : 0 < ‖z‖ + a + 1 := by positivity
    have hρ : 0 < ρ := div_pos hδ hden
    have hρmul : ρ * (‖z‖ + a + 1) = δ := div_mul_cancel₀ _ hden.ne'
    obtain ⟨y, hy, hβ, hfar⟩ := hsp u hu ell β hne ρ hρ
    obtain ⟨φ, hφ, hφsum⟩ := exists_dual_vector'' ℝ (u + y)
    change φ (u + y) = ‖u + y‖ at hφsum
    have hφu : φ u ≤ 1 := by simpa [hu] using dual_apply_le_norm φ hφ u
    have hφy : φ y ≤ 1 := by simpa [hy] using dual_apply_le_norm φ hφ y
    rw [map_add] at hφsum
    have hlowu : 1 - ρ ≤ φ u := by linarith
    have hlowy : 1 - ρ ≤ φ y := by linarith
    have hzid : z = ‖z‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
    have hφz : φ z = ‖z‖ * φ u := by conv_lhs => rw [hzid]; rw [map_smul, smul_eq_mul]
    have hb := dual_apply_le_norm φ hφ (z + a • y)
    rw [map_add, map_smul, smul_eq_mul, hφz] at hb
    have hb₁ := mul_le_mul_of_nonneg_left hlowu (norm_nonneg z)
    have hb₂ := mul_le_mul_of_nonneg_left hlowy ha
    exact ⟨y, hy, hβ, by nlinarith⟩

lemma slices_finite_sum (hsp : UnitSliceProperty X) {w₀ : X} (hw₀ : ‖w₀‖ = 1)
    {ι : Type uIota} (a : ι → ℝ) (ell : ι → X →L[ℝ] ℝ) (β : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hne : ∀ i, ∃ y : X, ‖y‖ ≤ 1 ∧ β i < ell i y)
    (s : Finset ι) (z : X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : ι → X, (∀ i ∈ s, ‖y i‖ = 1 ∧ β i < ell i (y i)) ∧
      ‖z‖ + ∑ i ∈ s, a i - δ ≤ ‖z + ∑ i ∈ s, a i • y i‖ := by
  classical
  induction s using Finset.induction generalizing z δ with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    simp only [Finset.sum_empty, add_zero]
    linarith
  | @insert i s hi ih =>
    obtain ⟨y, hy, hsum⟩ := ih z (half_pos hδ)
    obtain ⟨v, hv, hβv, hvfar⟩ := slice_add_almost hsp hw₀ (ell i) (β i) (hne i)
      (z + ∑ j ∈ s, a j • y j) (ha i) (half_pos hδ)
    let y' := Function.update y i v
    have hsame : ∀ j ∈ s, y' j = y j := by
      intro j hj
      have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
      simp [y', hji]
    have hins : y' i = v := by simp [y']
    have hsum' : ∑ j ∈ s, a j • y' j = ∑ j ∈ s, a j • y j :=
      Finset.sum_congr rfl (fun j hj => by rw [hsame j hj])
    refine ⟨y', ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hins ▸ ⟨hv, hβv⟩
      · rw [hsame j hj]
        exact hy j hj
    · rw [Finset.sum_insert hi, Finset.sum_insert hi, hins, hsum']
      have hid : z + (a i • v + ∑ j ∈ s, a j • y j) =
          (z + ∑ j ∈ s, a j • y j) + a i • v := by abel
      rw [hid]
      linarith

variable {Y : Type uY} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The weak-open diametral lemma in finite-dimensional coordinates. -/
theorem diametral_finite_image (hsp : UnitSliceProperty X) {x u : X} (hx : ‖x‖ = 1)
    (hu : ‖u‖ ≤ 1) (T : X →L[ℝ] Y) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ v : X, ‖v‖ ≤ 1 ∧ ‖T v - T u‖ < r ∧ 2 - δ ≤ ‖v - x‖ := by
  obtain ⟨ι, hι, a, ell, β, ha, hsum, hne, hnear⟩ := bourgain_image T hu hr
  let := hι
  obtain ⟨y, hy, hfar⟩ := slices_finite_sum hsp hx a ell β ha hne Finset.univ (-x) hδ
  let v := ∑ i, a i • y i
  have hv : ‖v‖ ≤ 1 := by
    have hm := (convex_closedBall (0 : X) 1).sum_mem (fun i _ => ha i) hsum
      (fun i _ => show y i ∈ Metric.closedBall (0 : X) 1 by simpa using (hy i (Finset.mem_univ i)).1.le)
    simpa [v] using hm
  refine ⟨v, hv, hnear y (fun i => ⟨(hy i (Finset.mem_univ i)).1.le, (hy i (Finset.mem_univ i)).2⟩), ?_⟩
  simpa only [norm_neg, hx, hsum, one_add_one_eq_two, v, sub_eq_add_neg, add_comm] using hfar

end ExactModuli

namespace ExactModuli
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

lemma diametral_finite_norm (hsp : UnitSliceProperty X) {x u : X} (hx : ‖x‖ = 1)
    (hu : ‖u‖ ≤ 1) (T : X →L[ℝ] Y) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ v : X, ‖v‖ ≤ 1 ∧ ‖T v - T u‖ < r ∧ 2 - δ ≤ ‖v - x‖ := by
  let e : Y ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Y)) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin])
  let C := ‖e.symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨v, hv, hnear, hfar⟩ := diametral_finite_image hsp hx hu
    (e.toContinuousLinearMap.comp T) (div_pos hr hCp) hδ
  refine ⟨v, hv, ?_, hfar⟩
  have hb := e.symm.toContinuousLinearMap.le_opNorm (e (T v) - e (T u))
  have hid : e.symm (e (T v) - e (T u)) = T v - T u := by simp only [map_sub, e.symm_apply_apply]
  change ‖e.symm (e (T v) - e (T u))‖ ≤ C * ‖e (T v) - e (T u)‖ at hb
  rw [hid] at hb
  change ‖e (T v) - e (T u)‖ < r / (C + 1) at hnear
  have hb' : ‖T v - T u‖ ≤ (C + 1) * ‖e (T v) - e (T u)‖ := by
    nlinarith [norm_nonneg (e (T v) - e (T u))]
  have hstrict := mul_lt_mul_of_pos_left hnear hCp
  rw [mul_div_cancel₀ _ hCp.ne'] at hstrict
  exact hb'.trans_lt hstrict

/-- Finite quotient correction, retaining the small error vector for equivalent-norm estimates. -/
lemma cofinite_diametral_correction (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {F : Submodule ℝ X} (hF : Cofinite F) {ε : ℝ} (hε : 0 < ε) :
    ∃ v e : X, ‖v‖ ≤ 1 ∧ ‖e‖ < ε ∧ v - x - e ∈ F ∧ 2 - ε ≤ ‖v - x‖ := by
  let : IsClosed (F : Set X) := hF.1
  let : FiniteDimensional ℝ (X ⧸ F) := hF.2
  obtain ⟨v, hv, hnear, hfar⟩ := diametral_finite_norm hsp hx hx.le F.mkQL (half_pos hε) hε
  obtain ⟨e, he, heNorm⟩ := Submodule.Quotient.norm_mk_lt (F.mkQL (v - x)) (half_pos hε)
  have hq : ‖F.mkQL (v - x)‖ < ε / 2 := by simpa only [map_sub] using hnear
  refine ⟨v, e, hv, by linarith, ?_, hfar⟩
  apply (Submodule.Quotient.mk_eq_zero F).mp
  change F.mkQL (v - x - e) = 0
  rw [map_sub]
  change F.mkQL (v - x) - Submodule.Quotient.mk e = 0
  rw [he, sub_self]

lemma cofinite_antipodal_endpoint (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {F : Submodule ℝ X} (hF : Cofinite F) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ F, 2 - 2 * ε < ‖z‖ ∧ ‖z‖ ≤ 2 + ε ∧ ‖x + z‖ ≤ 1 + ε := by
  obtain ⟨v, e, hv, he, hzF, hfar⟩ := cofinite_diametral_correction hsp hx hF hε
  refine ⟨v - x - e, hzF, ?_, ?_, ?_⟩
  · have hb := norm_sub_le (v - x - e) (-e)
    have hid : v - x - e - -e = v - x := by abel
    rw [hid, norm_neg] at hb
    linarith
  · have hb := norm_sub_le (v - x) e
    have hb' := norm_sub_le v x
    rw [hx] at hb'
    linarith
  · have hid : x + (v - x - e) = v - e := by abel
    rw [hid]
    have hb := norm_sub_le v e
    linarith

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma half_envelope (t : ℝ) : (t + max 0 (t - 2)) / 2 = max (t / 2) (t - 1) := by
  by_cases h : t ≤ 2
  · rw [max_eq_left (sub_nonpos.mpr h), max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge h)), max_eq_right (by linarith)]
    ring

lemma cofinite_direction_upper (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {F : Submodule ℝ X} (hF : Cofinite F) {ε t : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (ht : 0 ≤ t) :
    ∃ y ∈ F, ‖y‖ = 1 ∧ ‖x + t • y‖ ≤ 1 + max 0 (t - 2) + 3 * ε := by
  obtain ⟨z, hzF, hzlo, hzhi, hend⟩ := cofinite_antipodal_endpoint hsp hx hF hε
  have hL : 0 < ‖z‖ := by linarith
  have hz : z ≠ 0 := norm_pos_iff.mp hL
  let y := ‖z‖⁻¹ • z
  have hy : ‖y‖ = 1 := norm_smul_inv_norm hz
  have hid : ‖z‖ • y = z := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hb := norm_ray_endpoint_bound hx hy hL hε.le ht (show ‖x + ‖z‖ • y‖ ≤ 1 + ε by rwa [hid])
  have hmax : max 0 (t - ‖z‖) ≤ max 0 (t - 2) + 2 * ε := by
    apply max_le
    · linarith [le_max_left (0 : ℝ) (t - 2)]
    · linarith [le_max_right (0 : ℝ) (t - 2)]
  exact ⟨y, F.smul_mem _ hzF, hy, by linarith⟩

/-- Matching averaged upper curve, from one family of cofinite directions. -/
theorem averaged_upper_bound (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : H (normSeminorm ℝ X) x t ≤ max (t / 2) (t - 1) := by
  unfold H
  refine csSup_le ?_ ?_
  · exact ⟨_, ⊤, cofinite_top, rfl⟩
  rintro a ⟨F, hF, rfl⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min (1 / 4 : ℝ) (δ / 6)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ / 6 := min_le_right _ _
  obtain ⟨y, hyF, hy, hplus⟩ := cofinite_direction_upper hsp hx hF hε hε1 ht
  have hinf := csInf_le (averageValues_bddBelow x t F) ⟨y, hyF, hy.ge, rfl⟩
  have hminus := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy, mul_one] at hminus
  change sInf (averageValues x t F) ≤ _
  change sInf (averageValues x t F) ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 at hinf
  rw [← half_envelope]
  linarith

/-- Matching one-sided upper curve, including the radius-two corner. -/
theorem oneSided_upper_bound (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : D (normSeminorm ℝ X) x t ≤ max 0 (t - 2) := by
  unfold D
  refine csSup_le ?_ ?_
  · exact ⟨_, ⊤, cofinite_top, rfl⟩
  rintro a ⟨F, hF, rfl⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min (1 / 4 : ℝ) (δ / 6)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ / 6 := min_le_right _ _
  obtain ⟨y, hyF, hy, hplus⟩ := cofinite_direction_upper hsp hx hF hε hε1 ht
  have hinf := csInf_le (oneSidedValues_bddBelow x t F) ⟨y, hyF, hy, rfl⟩
  change sInf (oneSidedValues x t F) ≤ _
  linarith

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exact_pointwise (E : Submodule ℝ (Lp ℝ 1 μ))
    (hdim : ¬ FiniteDimensional ℝ E) (hpre : MeasurePrecompactBall μ E) (hd : Daugavet E)
    {x : E} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 < t) :
    H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
    D (normSeminorm ℝ E) x t = max 0 (t - 2) := by
  exact ⟨le_antisymm (averaged_upper_bound (daugavet_unitSlice hd) hx ht.le)
      (clipping_lower_bound E hdim hpre hx ht),
    le_antisymm (oneSided_upper_bound (daugavet_unitSlice hd) hx ht.le)
      (oneSided_lower_bound hdim hx ht.le)⟩

/-- The infimum over centers is a separate conclusion, not an identification of definitions. -/
theorem exact_center_infima (E : Submodule ℝ (Lp ℝ 1 μ))
    (hdim : ¬ FiniteDimensional ℝ E) (hpre : MeasurePrecompactBall μ E) (hd : Daugavet E)
    {t : ℝ} (ht : 0 < t) :
    averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
    oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2) := by
  obtain ⟨x, _, hx⟩ := cofinite_has_unit hdim (cofinite_top (X := E))
  have hH : {r | ∃ x : E, ‖x‖ = 1 ∧ r = H (normSeminorm ℝ E) x t} =
      {max (t / 2) (t - 1)} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨x, hx, (exact_pointwise E hdim hpre hd hx ht).1.symm⟩, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact (exact_pointwise E hdim hpre hd hy ht).1
  have hD : {r | ∃ x : E, ‖x‖ = 1 ∧ r = D (normSeminorm ℝ E) x t} =
      {max 0 (t - 2)} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨x, hx, (exact_pointwise E hdim hpre hd hx ht).2.symm⟩, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact (exact_pointwise E hdim hpre hd hy ht).2
  constructor
  · change sInf {r | ∃ x : E, ‖x‖ = 1 ∧ r = H (normSeminorm ℝ E) x t} = _
    rw [hH, csInf_singleton]
  · change sInf {r | ∃ x : E, ‖x‖ = 1 ∧ r = D (normSeminorm ℝ E) x t} = _
    rw [hD, csInf_singleton]

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma equivalentNorm_pos {N : Seminorm ℝ X} (hN : EquivalentNorm N) {x : X} (hx : x ≠ 0) :
    0 < N x := by
  obtain ⟨a, b, ha, hb, hbound⟩ := hN
  exact (mul_pos ha (norm_pos_iff.mpr hx)).trans_le (hbound x).1

lemma seminorm_normalize (N : Seminorm ℝ X) {x : X} (hx : 0 < N x) :
    N ((N x)⁻¹ • x) = 1 := by
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']

lemma cofinite_has_Nunit (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {F : Submodule ℝ X} (hF : Cofinite F) :
    ∃ y ∈ F, N y = 1 := by
  obtain ⟨y, hyF, hy⟩ := cofinite_has_unit hinf hF
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  refine ⟨(N y)⁻¹ • y, F.smul_mem _ hyF, seminorm_normalize N (equivalentNorm_pos hN hy0)⟩

def normOneSidedValues (N : Seminorm ℝ X) (x : X) (t : ℝ) (F : Submodule ℝ X) : Set ℝ :=
  {a | ∃ y ∈ F, N y = 1 ∧ a = N (x + t • y) - 1}

lemma normOneSidedValues_bddBelow (N : Seminorm ℝ X) (x : X) (t : ℝ) (F : Submodule ℝ X) :
    BddBelow (normOneSidedValues N x t F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y, hyF, hy, rfl⟩
  linarith [apply_nonneg N (x + t • y)]

lemma normOneSidedValues_nonempty (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) (x : X) (t : ℝ) {F : Submodule ℝ X} (hF : Cofinite F) :
    (normOneSidedValues N x t F).Nonempty := by
  obtain ⟨y, hyF, hy⟩ := cofinite_has_Nunit hinf hN hF
  exact ⟨_, y, hyF, hy, rfl⟩

lemma normD_outer_bddAbove (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {x : X} (hx : N x = 1) {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {r | ∃ F : Submodule ℝ X, Cofinite F ∧ r = sInf (normOneSidedValues N x t F)} := by
  refine ⟨t, ?_⟩
  rintro a ⟨F, hF, rfl⟩
  obtain ⟨y, hyF, hy⟩ := cofinite_has_Nunit hinf hN hF
  have hinf := csInf_le (normOneSidedValues_bddBelow N x t F) ⟨y, hyF, hy, rfl⟩
  have hb := map_add_le_add N x (t • y)
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy, mul_one] at hb
  linarith

lemma normD_ge_neg_one (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {x : X} (hx : N x = 1) {t : ℝ} (ht : 0 ≤ t) : -1 ≤ D N x t := by
  apply le_trans (b := sInf (normOneSidedValues N x t ⊤))
  · apply le_csInf (normOneSidedValues_nonempty hinf hN x t cofinite_top)
    rintro r ⟨y, _, _, rfl⟩
    linarith [apply_nonneg N (x + t • y)]
  · exact le_csSup (normD_outer_bddAbove hinf hN hx ht) ⟨⊤, cofinite_top, rfl⟩

lemma normD_centers_bddBelow (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) {t : ℝ} (ht : 0 ≤ t) :
    BddBelow {r | ∃ x : X, N x = 1 ∧ r = D N x t} := by
  refine ⟨-1, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact normD_ge_neg_one hinf hN hx ht

/-- Seminorm convexity with an explicit common endpoint bound. -/
lemma seminorm_segment_le (N : Seminorm ℝ X) {x y : X} {r M : ℝ}
    (hr : 0 ≤ r) (hr' : r ≤ 1) (hx : N x ≤ M) (hy : N y ≤ M) :
    N ((1 - r) • x + r • y) ≤ M := by
  have h := map_add_le_add N ((1 - r) • x) (r • y)
  rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hr'), abs_of_nonneg hr] at h
  have h₁ := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hr')
  have h₂ := mul_le_mul_of_nonneg_left hy hr
  nlinarith

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma equivalentNorm_supremum (hinf : ¬ FiniteDimensional ℝ X) {N : Seminorm ℝ X}
    (hN : EquivalentNorm N) :
    ∃ R : ℝ, 0 < R ∧ (∀ u : X, ‖u‖ ≤ 1 → N u ≤ R) ∧
      ∀ ε : ℝ, 0 < ε → ∃ x : X, ‖x‖ = 1 ∧ R / (1 + ε) < N x := by
  obtain ⟨a, b, ha, hb, hab⟩ := hN
  let S : Set ℝ := {r | ∃ x : X, ‖x‖ = 1 ∧ r = N x}
  obtain ⟨w, _, hw⟩ := cofinite_has_unit hinf (cofinite_top (X := X))
  have hS : S.Nonempty := ⟨N w, w, hw, rfl⟩
  have hSb : BddAbove S := by
    refine ⟨b, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    simpa only [hx, mul_one] using (hab x).2
  let R := sSup S
  have hSR : ∀ x : X, ‖x‖ = 1 → N x ≤ R := fun x hx => le_csSup hSb ⟨x, hx, rfl⟩
  have hR : 0 < R := by
    have hb := (hab w).1
    rw [hw, mul_one] at hb
    exact ha.trans_le (hb.trans (hSR w hw))
  refine ⟨R, hR, ?_, ?_⟩
  · intro u hu
    by_cases hu0 : u = 0
    · simpa only [hu0, map_zero] using hR.le
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      let x := ‖u‖⁻¹ • u
      have hx : ‖x‖ = 1 := norm_smul_inv_norm hu0
      have hid : u = ‖u‖ • x := by dsimp [x]; rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      calc
        N u = N (‖u‖ • x) := congrArg N hid
        _ = ‖u‖ * N x := by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hn.le]
        _ ≤ ‖u‖ * R := mul_le_mul_of_nonneg_left (hSR x hx) hn.le
        _ ≤ R := by nlinarith
  · intro ε hε
    have hden : 0 < 1 + ε := by linarith
    have hlt : R / (1 + ε) < R := (div_lt_iff₀ hden).mpr (by nlinarith)
    obtain ⟨r, ⟨x, hx, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hS hlt
    exact ⟨x, hx, hr⟩

lemma seminorm_normalized_segment (N : Seminorm ℝ X) {x z : X} (hx : 0 < N x)
    (hz : 0 < N z) {t M : ℝ} (ht : 0 ≤ t) (htz : t * N x ≤ N z)
    (hxM : N x ≤ M) (hzM : N (x + z) ≤ M) :
    N ((N x)⁻¹ • x + t • ((N z)⁻¹ • z)) ≤ M / N x := by
  let r := t * N x / N z
  have hr : 0 ≤ r := div_nonneg (mul_nonneg ht hx.le) hz.le
  have hr' : r ≤ 1 := (div_le_one hz).mpr htz
  have hid : (N x)⁻¹ • x + t • ((N z)⁻¹ • z) =
      (1 - r) • ((N x)⁻¹ • x) + r • ((N x)⁻¹ • (x + z)) := by
    dsimp [r]
    match_scalars <;> field_simp [hx.ne', hz.ne']
    ring
  rw [hid]
  apply seminorm_segment_le N hr hr'
  · rw [seminorm_normalize N hx]
    exact (one_le_div hx).mpr hxM
  · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), ← div_eq_inv_mul]
    exact (div_le_div_iff_of_pos_right hx).mpr hzM

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma normD_bound_at_original_unit (hsp : UnitSliceProperty X) (N : Seminorm ℝ X)
    {a b R : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : ∀ u : X, a * ‖u‖ ≤ N u ∧ N u ≤ b * ‖u‖)
    (hR : ∀ u : X, ‖u‖ ≤ 1 → N u ≤ R) {x : X} (hx : ‖x‖ = 1) :
    D N ((N x)⁻¹ • x) (a / (4 * b)) ≤ R / N x - 1 := by
  have hNx : 0 < N x := by have := (hab x).1; rw [hx, mul_one] at this; linarith
  have hNxb : N x ≤ b := by simpa only [hx, mul_one] using (hab x).2
  have hNxR : N x ≤ R := hR x hx.le
  let t := a / (4 * b)
  have ht : 0 < t := by dsimp [t]; positivity
  have htb : t * (4 * b) = a := div_mul_cancel₀ _ (by positivity)
  have htb' : t * b = a / 4 := by linarith
  unfold D
  refine csSup_le ?_ ?_
  · exact ⟨_, ⊤, cofinite_top, rfl⟩
  rintro q ⟨F, hF, rfl⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min (1 / 4 : ℝ) (δ * N x / (2 * b))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ * N x / (2 * b) := min_le_right _ _
  have hεδ' : b * ε ≤ δ * N x / 2 := by
    have hd := (le_div_iff₀ (show 0 < 2 * b by positivity)).mp hεδ
    nlinarith
  obtain ⟨v, e, hv, he, hzF, hfar⟩ := cofinite_diametral_correction hsp hx hF hε
  let z := v - x - e
  have hzlo : 1 < ‖z‖ := by
    have hn := norm_sub_le z (-e)
    have hid : z - -e = v - x := by dsimp [z]; abel
    rw [hid, norm_neg] at hn
    linarith
  have hNz : 0 < N z := (mul_pos ha (by linarith)).trans_le (hab z).1
  have htz : t * N x ≤ N z := by
    have hc := mul_le_mul_of_nonneg_left hNxb ht.le
    have hd := (hab z).1
    nlinarith
  have hend : N (x + z) ≤ R + b * ε := by
    have hid : x + z = v - e := by dsimp [z]; abel
    rw [hid]
    have hc := map_sub_le_add N v e
    have hb' := (hab e).2
    have hRv := hR v hv
    nlinarith
  have hxM : N x ≤ R + b * ε := by nlinarith
  have hvalue := seminorm_normalized_segment N hNx hNz ht.le htz hxM hend
  have hy : N ((N z)⁻¹ • z) = 1 := seminorm_normalize N hNz
  have hyF : (N z)⁻¹ • z ∈ F := F.smul_mem _ hzF
  have hinf := csInf_le (normOneSidedValues_bddBelow N ((N x)⁻¹ • x) t F)
    ⟨(N z)⁻¹ • z, hyF, hy, rfl⟩
  change sInf (normOneSidedValues N ((N x)⁻¹ • x) t F) ≤ _
  have hquot : (R + b * ε) / N x ≤ R / N x + δ := by
    apply (div_le_iff₀ hNx).mpr
    rw [add_mul, div_mul_cancel₀ R hNx.ne']
    nlinarith
  linarith

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The renorming obstruction is a consequence of the weak-neighborhood geometry, not merely
of the vanishing inherited-norm one-sided modulus. -/
theorem no_equivalent_auc (hinf : ¬ FiniteDimensional ℝ X) (hsp : UnitSliceProperty X)
    (N : Seminorm ℝ X) (hN : EquivalentNorm N) : ¬ AUC N := by
  obtain ⟨R, hRpos, hRball, hRapprox⟩ := equivalentNorm_supremum hinf hN
  obtain ⟨a, b, ha, hb, hab⟩ := hN
  have hN' : EquivalentNorm N := ⟨a, b, ha, hb, hab⟩
  let t := a / (4 * b)
  have ht : 0 < t := by dsimp [t]; positivity
  have hmod : oneSidedModulus N t ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hopt⟩ := hRapprox ε hε
    have hNx : 0 < N x := by have := (hab x).1; rw [hx, mul_one] at this; linarith
    have hxN : N ((N x)⁻¹ • x) = 1 := seminorm_normalize N hNx
    have hD := normD_bound_at_original_unit hsp N ha hb hab hRball hx
    have hopt' : R < N x * (1 + ε) := (div_lt_iff₀ (by linarith)).mp hopt
    have hquot : R / N x - 1 ≤ ε := by
      have : R / N x < 1 + ε := (div_lt_iff₀ hNx).mpr (by nlinarith)
      linarith
    have hinf := csInf_le (normD_centers_bddBelow hinf hN' ht.le)
      ⟨(N x)⁻¹ • x, hxN, rfl⟩
    change oneSidedModulus N t ≤ D N ((N x)⁻¹ • x) t at hinf
    change D N ((N x)⁻¹ • x) t ≤ R / N x - 1 at hD
    simpa only [zero_add] using hinf.trans (hD.trans hquot)
  intro hauc
  exact (hauc t ht).not_ge hmod

theorem exact_main {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (_hclosed : IsClosed (E : Set (Lp ℝ 1 μ))) (hdim : ¬ FiniteDimensional ℝ E)
    (hprecompact : MeasurePrecompactBall μ E) (hdaugavet : Daugavet E) :
    (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
      H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
      D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
    (∀ t : ℝ, 0 < t →
      averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
      oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
    (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  exact ⟨fun x hx t ht => exact_pointwise E hdim hprecompact hdaugavet hx ht,
    fun t ht => exact_center_infima E hdim hprecompact hdaugavet ht,
    no_equivalent_auc hdim (daugavet_unitSlice hdaugavet)⟩

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology


namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma normalized_functional_slice_nonempty (ell : X →L[ℝ] ℝ) (hell : ‖ell‖ = 1)
    {η : ℝ} (hη : 0 < η) : ∃ y : X, ‖y‖ ≤ 1 ∧ 1 - η < ell y := by
  obtain ⟨u, hu, hval⟩ := ell.exists_lt_apply_of_lt_opNorm
    (show 1 - η < ‖ell‖ by rw [hell]; linarith)
  rw [Real.norm_eq_abs] at hval
  by_cases hs : 0 ≤ ell u
  · exact ⟨u, hu.le, by rwa [abs_of_nonneg hs] at hval⟩
  · refine ⟨-u, by simpa using hu.le, ?_⟩
    rw [abs_of_neg (lt_of_not_ge hs)] at hval
    simpa only [map_neg] using hval

/-- Converse slice characterization, needed for the explicitly constructed example. -/
theorem unitSlice_daugavet [Nontrivial X] (hsp : UnitSliceProperty X) : Daugavet X := by
  intro ell v
  by_cases he0 : ell = 0
  · simp [he0, ContinuousLinearMap.norm_id]
  by_cases hv0 : v = 0
  · simp [hv0, ContinuousLinearMap.norm_id]
  have he : 0 < ‖ell‖ := norm_pos_iff.mpr he0
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let f : X →L[ℝ] ℝ := ‖ell‖⁻¹ • ell
  have hf : ‖f‖ = 1 := norm_smul_inv_norm he0
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv0
  let a := ‖ell‖ * ‖v‖
  have ha : 0 < a := mul_pos he hv
  let T : X →L[ℝ] X := ContinuousLinearMap.id ℝ X + ell.smulRight v
  have hnrank : ‖ell.smulRight v‖ = a := ContinuousLinearMap.norm_smulRight_apply _ _
  apply le_antisymm
  · have hb := norm_add_le (ContinuousLinearMap.id ℝ X) (ell.smulRight v)
    simpa only [ContinuousLinearMap.norm_id] using hb
  · rw [hnrank]
    change 1 + a ≤ ‖T‖
    apply le_of_forall_pos_le_add
    intro δ hδ
    let η := min (1 / 2 : ℝ) (δ / (4 * (a + 1)))
    have hη : 0 < η := by dsimp [η]; positivity
    have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hηδ : η * (4 * (a + 1)) ≤ δ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    obtain ⟨y, hy, hfy, hfar⟩ := hsp w hw f (1 - η)
      (normalized_functional_slice_nonempty f hf hη) η hη
    obtain ⟨φ, hφ, hφsum⟩ := exists_dual_vector'' ℝ (w + y)
    change φ (w + y) = ‖w + y‖ at hφsum
    rw [map_add] at hφsum
    have hφw : φ w ≤ 1 := by simpa only [hw] using dual_apply_le_norm φ hφ w
    have hφy : φ y ≤ 1 := by simpa only [hy] using dual_apply_le_norm φ hφ y
    have hwlo : 1 - η ≤ φ w := by linarith
    have hylo : 1 - η ≤ φ y := by linarith
    have hfylo : 1 - η ≤ f y := hfy.le
    have hprod : (1 - η) ^ 2 ≤ f y * φ w := by
      have hp := mul_le_mul hfylo hwlo (by linarith : 0 ≤ 1 - η) (by linarith : 0 ≤ f y)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod ha.le
    have heval : ell y = ‖ell‖ * f y := by
      change ell y = ‖ell‖ * (‖ell‖⁻¹ * ell y)
      rw [← mul_assoc, mul_inv_cancel₀ he.ne', one_mul]
    have hvid : v = ‖v‖ • w := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hv.ne', one_smul]
    have hφv : φ v = ‖v‖ * φ w := by conv_lhs => rw [hvid]; rw [map_smul, smul_eq_mul]
    have hTφ : φ (T y) = φ y + a * (f y * φ w) := by
      change φ (y + ell y • v) = _
      rw [map_add, map_smul, smul_eq_mul, heval, hφv]
      dsimp [a]
      ring
    have hbound := dual_apply_le_norm φ hφ (T y)
    have hop := T.le_opNorm y
    rw [hy, mul_one] at hop
    rw [hTφ] at hbound
    nlinarith [mul_nonneg ha.le (sq_nonneg η)]

end ExactModuli

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

def scale (p : ℝ) : ℝ := (p - 1) / p

def multiplier (p : ℝ) (v : unitInterval) : ℝ := scale p * (v : ℝ) ^ (-1 / p)

lemma scale_pos {p : ℝ} (hp : 1 < p) : 0 < scale p := by
  dsimp [scale]; positivity

lemma scale_lt_one {p : ℝ} (hp : 1 < p) : scale p < 1 := by
  unfold scale
  rw [div_lt_one (by linarith : 0 < p)]
  linarith

lemma multiplier_nonneg {p : ℝ} (hp : 1 < p) (v : unitInterval) :
    0 ≤ multiplier p v := mul_nonneg (scale_pos hp).le (Real.rpow_nonneg v.property.1 _)

lemma measurable_multiplier (p : ℝ) : Measurable (multiplier p) := by
  unfold multiplier
  fun_prop

lemma integrable_multiplier {p : ℝ} (hp : 1 < p) :
    Integrable (multiplier p) (volume : Measure unitInterval) := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 < -1 / p := by rw [lt_div_iff₀ hp0]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (-1 / p)) (Icc 0 1) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
      ((intervalIntegral.intervalIntegrable_rpow' hexp).1)
  have hc := (unitInterval.measurePreserving_coe.integrable_comp hi.aestronglyMeasurable).mpr hi
  exact hc.const_mul (scale p)

lemma integral_multiplier {p : ℝ} (hp : 1 < p) :
    ∫ v : unitInterval, multiplier p v = 1 := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 < -1 / p := by rw [lt_div_iff₀ hp0]; linarith
  unfold multiplier
  rw [integral_const_mul]
  change scale p * (∫ x : Icc (0:ℝ) 1, (x:ℝ) ^ (-1 / p)) = 1
  rw [integral_subtype measurableSet_Icc (fun x : ℝ => x ^ (-1 / p)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_rpow (Or.inl hexp)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : -1 / p + 1 ≠ 0)]
  dsimp [scale]
  field_simp [hp0.ne', show p - 1 ≠ 0 by linarith, show -1 + p ≠ 0 by linarith]
  ring

lemma multiplier_tail {p u : ℝ} (hp : 1 < p) (hu : scale p ≤ u) :
    (volume : Measure unitInterval).real {v | u < multiplier p v} = (scale p / u) ^ p := by
  have hs : 0 < scale p := scale_pos hp
  have hu0 : 0 < u := hs.trans_le hu
  have hp0 : 0 < p := by linarith
  let q := (scale p / u) ^ p
  have hq : 0 < q := Real.rpow_pos_of_pos (div_pos hs hu0) _
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact Real.rpow_le_one (by positivity) ((div_le_one hu0).mpr hu) hp0.le
  let a : unitInterval := ⟨q, hq.le, hq1⟩
  have hqpow : q ^ (-1 / p) = u / scale p := by
    dsimp [q]
    rw [← Real.rpow_mul (div_pos hs hu0).le]
    have hm : p * (-1 / p) = -1 := by field_simp
    rw [hm, Real.rpow_neg_one, inv_div]
  have haeq : {v : unitInterval | u < multiplier p v} =ᵐ[volume] Iio a := by
    have hne : ∀ᵐ v : unitInterval, v ≠ 0 := volume.ae_ne 0
    filter_upwards [hne] with v hv
    have hv0 : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (by
      intro heq; apply hv; apply Subtype.ext; exact heq.symm)
    apply propext
    change (u < scale p * (v : ℝ) ^ (-1 / p)) ↔ (v : ℝ) < q
    have hueq : u = scale p * q ^ (-1 / p) := by rw [hqpow]; field_simp
    rw [hueq, mul_lt_mul_iff_right₀ hs,
      Real.rpow_lt_rpow_iff_of_neg hq hv0 (div_neg_of_neg_of_pos (by norm_num) hp0)]
  rw [measureReal_congr haeq, measureReal_def, unitInterval.volume_Iio,
    ENNReal.toReal_ofReal hq.le]

lemma multiplier_tail_le {p u : ℝ} (hp : 1 < p) (hu : 0 < u) :
    (volume : Measure unitInterval).real {v | u < multiplier p v} ≤ (scale p / u) ^ p := by
  by_cases hs : scale p ≤ u
  · exact le_of_eq (multiplier_tail hp hs)
  · have hsu : 1 ≤ (scale p / u) ^ p := Real.one_le_rpow
      ((le_div_iff₀ hu).mpr (by linarith : 1 * u ≤ scale p)) (by linarith)
    exact (measureReal_le_one).trans hsu

abbrev pairedMeasure : Measure (unitInterval × unitInterval) :=
  (volume : Measure unitInterval).prod volume

def difference (p : ℝ) (v : unitInterval × unitInterval) : ℝ :=
  multiplier p v.1 - multiplier p v.2

lemma measurable_difference (p : ℝ) : Measurable (difference p) :=
  ((measurable_multiplier p).comp measurable_fst).sub
    ((measurable_multiplier p).comp measurable_snd)

lemma integrable_difference {p : ℝ} (hp : 1 < p) :
    Integrable (difference p) pairedMeasure := by
  exact ((measurePreserving_fst.integrable_comp
    (integrable_multiplier hp).aestronglyMeasurable).mpr (integrable_multiplier hp)).sub
    ((measurePreserving_snd.integrable_comp
    (integrable_multiplier hp).aestronglyMeasurable).mpr (integrable_multiplier hp))

lemma difference_symmetric (p : ℝ) :
    IdentDistrib (difference p) (fun v => -difference p v) pairedMeasure pairedMeasure := by
  have hcomp : (fun v => -difference p v) = difference p ∘ Prod.swap := by
    funext v
    simp [difference, sub_eq_add_neg, add_comm]
  refine ⟨(measurable_difference p).aemeasurable,
    (measurable_difference p).neg.aemeasurable, ?_⟩
  rw [hcomp, ← Measure.map_map (measurable_difference p) measurable_swap, Measure.prod_swap]

lemma difference_tail_upper {p u : ℝ} (hp : 1 < p) (hu : 0 < u) :
    pairedMeasure.real {v | u < |difference p v|} ≤ 2 * (scale p / u) ^ p := by
  let A := {v : unitInterval | u < multiplier p v}
  have hsub : {v | u < |difference p v|} ⊆ (A ×ˢ univ) ∪ (univ ×ˢ A) := by
    intro v hv
    change u < |multiplier p v.1 - multiplier p v.2| at hv
    by_contra hn
    have he : multiplier p v.1 ≤ u ∧ multiplier p v.2 ≤ u := by
      simpa [A] using hn
    have h1 := multiplier_nonneg hp v.1
    have h2 := multiplier_nonneg hp v.2
    have hb : |multiplier p v.1 - multiplier p v.2| ≤ u :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  calc
    _ ≤ pairedMeasure.real ((A ×ˢ univ) ∪ (univ ×ˢ A)) := measureReal_mono hsub
    _ ≤ pairedMeasure.real (A ×ˢ univ) + pairedMeasure.real (univ ×ˢ A) := measureReal_union_le _ _
    _ = 2 * (volume : Measure unitInterval).real A := by
      rw [measureReal_prod_prod, measureReal_prod_prod]
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (multiplier_tail_le hp hu) (by norm_num)

lemma difference_tail_lower {p u : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hu : scale p ≤ u) :
    (1 / 18) * (scale p / u) ^ p ≤ pairedMeasure.real {v | u < |difference p v|} := by
  have hs : 0 < scale p := scale_pos hp
  have hu0 : 0 < u := hs.trans_le hu
  have hp0 : 0 < p := by linarith
  let B := {v : unitInterval | u + 2 * scale p < multiplier p v}
  let C := {v : unitInterval | 2 * scale p < multiplier p v}ᶜ
  have hsub : B ×ˢ C ⊆ {v | u < |difference p v|} := by
    intro v hv
    have hB : u + 2 * scale p < multiplier p v.1 := hv.1
    have hC : multiplier p v.2 ≤ 2 * scale p := le_of_not_gt hv.2
    have hdiff : u < difference p v := by dsimp [difference]; linarith
    exact hdiff.trans_le (le_abs_self _)
  have hB : (volume : Measure unitInterval).real B = (scale p / (u + 2 * scale p)) ^ p :=
    multiplier_tail hp (by linarith)
  have hC : (1 / 2 : ℝ) ≤ (volume : Measure unitInterval).real C := by
    have heq : scale p / (2 * scale p) = (1 / 2 : ℝ) := by field_simp
    have hpow : (1 / 2 : ℝ) ^ p ≤ 1 / 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hp.le
    have hvol : (volume : Measure unitInterval).real univ = 1 := by simp
    dsimp [C]
    rw [measureReal_compl (measurableSet_lt measurable_const (measurable_multiplier p)),
      hvol, multiplier_tail hp (by linarith), heq]
    linarith
  have hB9 : (scale p / u) ^ p ≤ 9 * (volume : Measure unitInterval).real B := by
    rw [hB]
    have hd : (scale p / u) / 3 ≤ scale p / (u + 2 * scale p) := by
      rw [div_div]
      apply (div_le_div_iff₀ (by positivity : 0 < u * 3) (by positivity)).mpr
      nlinarith
    have hpow := Real.rpow_le_rpow (show 0 ≤ (scale p / u) / 3 by positivity) hd hp0.le
    rw [Real.div_rpow (by positivity) (by norm_num)] at hpow
    have h3 : (3:ℝ) ^ p ≤ 9 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
        (show p ≤ 2 by linarith)
      norm_num at h
      exact h
    have hin := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) p)).mp hpow
    have hmul := mul_le_mul_of_nonneg_right h3
      (Real.rpow_nonneg (by positivity : 0 ≤ scale p / (u + 2 * scale p)) p)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hC
    (measureReal_nonneg : 0 ≤ (volume : Measure unitInterval).real B)
  have hm := measureReal_mono (μ := pairedMeasure) hsub
  rw [measureReal_prod_prod] at hm
  nlinarith

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section TailMoments
variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measurable_real_tail (X : Ω → ℝ) : Measurable (fun t : ℝ => μ.real {ω | t < X ω}) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono (fun _ ht => hab.trans_lt ht)

/-- The bounded weighted layer-cake identity used for truncation variances. -/
lemma integral_min_abs_sq {X : Ω → ℝ} (hX : Measurable X) {u : ℝ} (hu : 0 < u) :
    ∫ ω, (min |X ω| u) ^ 2 ∂μ =
      ∫ t in Ioc 0 u, 2 * t * μ.real {ω | t < |X ω|} := by
  let m := fun ω => min |X ω| u
  have hm : Measurable m := hX.abs.min measurable_const
  have hm0 : ∀ ω, 0 ≤ m ω := fun ω => le_min (abs_nonneg _) hu.le
  have hinner : ∀ ω, (∫ t in (0:ℝ)..m ω, 2 * t) = m ω ^ 2 := by
    intro ω
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hlay := lintegral_comp_eq_lintegral_meas_lt_mul μ (ae_of_all _ hm0) hm.aemeasurable
    (fun t ht => (continuous_id.intervalIntegrable 0 t).const_mul (2:ℝ))
    (show ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ 2 * t from
      (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => mul_nonneg (by norm_num) (le_of_lt ht)))
  change (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..m ω, 2 * t) ∂μ) = _ at hlay
  simp only [id_eq] at hlay
  simp_rw [hinner] at hlay
  have hright : (∫⁻ t in Ioi (0:ℝ), μ {ω | t < m ω} * ENNReal.ofReal (2 * t)) =
      ∫⁻ t in Ioc 0 u, ENNReal.ofReal (2 * t * μ.real {ω | t < |X ω|}) := by
    calc
      _ = ∫⁻ t in Ioi (0:ℝ), (Iio u).indicator
          (fun t => ENNReal.ofReal (2 * t * μ.real {ω | t < |X ω|})) t := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change μ {ω | t < m ω} * ENNReal.ofReal (2 * t) = _
        have ht0 : 0 < t := ht
        by_cases htu : t < u
        · rw [Set.indicator_of_mem (show t ∈ Iio u from htu)]
          have he : {ω | t < m ω} = {ω | t < |X ω|} := by
            ext ω
            simp [m, htu]
          rw [he, ENNReal.ofReal_mul (show 0 ≤ 2 * t by positivity), measureReal_def,
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
          exact mul_comm _ _
        · have he : {ω | t < m ω} = ∅ := by
            ext ω
            simp [m, htu]
          rw [he, measure_empty, zero_mul, Set.indicator_of_notMem (show t ∉ Iio u from htu)]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi, restrict_Ioo_eq_restrict_Ioc]
  rw [hright] at hlay
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg (m ω)))
      (hm.pow_const 2).aestronglyMeasurable]
  rw [hlay]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) ht.1.le) measureReal_nonneg
  · exact ((measurable_const.mul measurable_id).mul
      (measurable_real_tail (fun ω => |X ω|))).aestronglyMeasurable

/-- A truncated symmetric summand has second moment controlled using its tail. -/
lemma integral_min_sq_tail_bound {X : Ω → ℝ} (hX : Measurable X)
    {p C u : ℝ} (_hp : 0 < p) (hp2 : p < 2) (_hC : 0 ≤ C) (hu : 0 < u)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < |X ω|} ≤ C * t ^ (-p)) :
    ∫ ω, (min |X ω| u) ^ 2 ∂μ ≤ (2 * C / (2 - p)) * u ^ (2 - p) := by
  rw [integral_min_abs_sq hX hu]
  have hexp : -1 < 1 - p := by linarith
  have hi : IntegrableOn (fun t : ℝ => 2 * C * t ^ (1 - p)) (Ioc 0 u) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hexp).1.const_mul _
  have hle : (∫ t in Ioc 0 u, 2 * t * μ.real {ω | t < |X ω|}) ≤
      ∫ t in Ioc 0 u, 2 * C * t ^ (1 - p) := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (mul_nonneg (by norm_num) ht.1.le) measureReal_nonneg
    · exact hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hbound := mul_le_mul_of_nonneg_left (htail t ht0) (show 0 ≤ 2 * t by positivity)
      convert hbound using 1
      rw [Real.rpow_sub ht0, Real.rpow_one, Real.rpow_neg ht0.le]
      ring
  refine hle.trans_eq ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hu.le,
    integral_rpow (Or.inl hexp), Real.zero_rpow (by linarith : 1 - p + 1 ≠ 0)]
  have he : 1 - p + 1 = 2 - p := by ring
  rw [he]
  ring

def hardTruncate (u x : ℝ) : ℝ := if |x| ≤ u then x else 0

lemma measurable_hardTruncate (u : ℝ) : Measurable (hardTruncate u) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

lemma hardTruncate_neg (u x : ℝ) : hardTruncate u (-x) = -hardTruncate u x := by
  simp only [hardTruncate, abs_neg]
  split_ifs <;> simp

lemma abs_hardTruncate_le {u : ℝ} (hu : 0 ≤ u) (x : ℝ) : |hardTruncate u x| ≤ u := by
  unfold hardTruncate
  split_ifs with h
  · exact h
  · simpa using hu

lemma hardTruncate_sq_le_min_sq {u : ℝ} (_hu : 0 ≤ u) (x : ℝ) :
    (hardTruncate u x) ^ 2 ≤ (min |x| u) ^ 2 := by
  unfold hardTruncate
  split_ifs with h
  · simp [min_eq_left h, sq_abs]
  · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact sq_nonneg _

omit [IsProbabilityMeasure μ] in
lemma integral_hardTruncate_zero [IsProbabilityMeasure μ] {X : Ω → ℝ} {u : ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ) :
    ∫ ω, hardTruncate u (X ω) ∂μ = 0 := by
  have h := (hsym.comp (measurable_hardTruncate u)).integral_eq
  change (∫ ω, hardTruncate u (X ω) ∂μ) = ∫ ω, hardTruncate u (-X ω) ∂μ at h
  simp_rw [hardTruncate_neg] at h
  rw [integral_neg] at h
  linarith

lemma hardTruncate_memLp {X : Ω → ℝ} (hX : Measurable X) {u : ℝ} (hu : 0 ≤ u) :
    MemLp (fun ω => hardTruncate u (X ω)) 2 μ := by
  exact MemLp.of_bound ((measurable_hardTruncate u).comp hX).aestronglyMeasurable u
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using abs_hardTruncate_le hu (X ω)))

lemma hardTruncate_variance_bound {X : Ω → ℝ} (hX : Measurable X)
    {p C u : ℝ} (hp : 0 < p) (hp2 : p < 2) (hC : 0 ≤ C) (hu : 0 < u)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < |X ω|} ≤ C * t ^ (-p)) :
    variance (fun ω => hardTruncate u (X ω)) μ ≤ (2 * C / (2 - p)) * u ^ (2 - p) := by
  refine (variance_le_expectation_sq
    ((measurable_hardTruncate u).comp hX).aestronglyMeasurable).trans ?_
  refine le_trans ?_ (integral_min_sq_tail_bound hX hp hp2 hC hu htail)
  apply integral_mono_of_nonneg (ae_of_all _ (fun ω => sq_nonneg _))
  · refine (integrable_const (u ^ 2)).mono' ((hX.abs.min measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hmin0 : 0 ≤ min |X ω| u := le_min (abs_nonneg _) hu.le
    have hminu := min_le_right |X ω| u
    nlinarith
  · exact ae_of_all _ (fun ω => hardTruncate_sq_le_min_sq hu.le (X ω))

/-- Truncation, the union bound, and Chebyshev, uniformly in the number of summands. -/
lemma independent_symmetric_sum_tail {ι : Type uIota} [Fintype ι]
    (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ)
    {p : ℝ} (hp : 0 < p) (hp2 : p < 2) (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j)
    (htail : ∀ j t, 0 < t → μ.real {ω | t < |X j ω|} ≤ C j * t ^ (-p))
    {u : ℝ} (hu : 0 < u) :
    μ.real {ω | u < |∑ j, X j ω|} ≤
      (1 + 2 / (2 - p)) * (∑ j, C j) * u ^ (-p) := by
  classical
  let T := fun j ω => hardTruncate u (X j ω)
  have hT : ∀ j, MemLp (T j) 2 μ := fun j => hardTruncate_memLp (hX j) hu.le
  have hTi : iIndepFun T μ := hind.comp (fun _ => hardTruncate u) (fun _ => measurable_hardTruncate u)
  have hTzero : ∀ j, ∫ ω, T j ω ∂μ = 0 := fun j => integral_hardTruncate_zero (hsym j)
  let S := fun ω => ∑ j, T j ω
  have hSmem : MemLp S 2 μ := by
    exact memLp_finsetSum _ (fun j _ => hT j)
  have hSzero : ∫ ω, S ω ∂μ = 0 := by
    rw [show S = fun ω => ∑ j, T j ω from rfl, integral_finsetSum _
      (fun j _ => (hT j).integrable (by norm_num))]
    simp [hTzero]
  have hvar : variance S μ = ∑ j, variance (T j) μ := by
    have hSf : S = ∑ j, T j := by ext ω; simp [S]
    rw [hSf]
    exact (IndepFun.variance_sum (s := Finset.univ) (fun j _ => hT j)
        (fun i _ j _ hij => hTi.indepFun hij))
  have hvarbound : variance S μ ≤ (2 / (2 - p)) * (∑ j, C j) * u ^ (2 - p) := by
    rw [hvar]
    calc
      _ ≤ ∑ j, (2 * C j / (2 - p)) * u ^ (2 - p) :=
        Finset.sum_le_sum (fun j _ => hardTruncate_variance_bound (hX j) hp hp2 (hC j) hu (htail j))
      _ = ∑ j, (2 / (2 - p) * C j) * u ^ (2 - p) := by
        apply Finset.sum_congr rfl; intro j hj; ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcheb : μ.real {ω | u < |S ω|} ≤ variance S μ / u ^ 2 := by
    have h := meas_ge_le_variance_div_sq hSmem hu
    rw [hSzero] at h
    simp only [sub_zero] at h
    exact (measureReal_mono (fun ω (hω : u < |S ω|) => hω.le)).trans
      (ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg u)) h)
  have hpow : u ^ (2 - p) / u ^ (2:ℕ) = u ^ (-p) := by
    rw [Real.rpow_sub hu, Real.rpow_two, Real.rpow_neg hu.le]
    field_simp
  have hSbound : μ.real {ω | u < |S ω|} ≤ (2 / (2 - p)) * (∑ j, C j) * u ^ (-p) := by
    refine hcheb.trans ?_
    have h := div_le_div_of_nonneg_right hvarbound (sq_nonneg u)
    simpa only [mul_div_assoc, hpow] using h
  have hunion : μ.real (⋃ j, {ω | u < |X j ω|}) ≤ (∑ j, C j) * u ^ (-p) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    calc
      _ ≤ ∑ j, C j * u ^ (-p) := Finset.sum_le_sum (fun j _ => htail j u hu)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hsub : {ω | u < |∑ j, X j ω|} ⊆ (⋃ j, {ω | u < |X j ω|}) ∪ {ω | u < |S ω|} := by
    intro ω hω
    by_cases he : ∃ j, u < |X j ω|
    · left; exact mem_iUnion.mpr he
    · right
      have hx : ∀ j, hardTruncate u (X j ω) = X j ω := by
        intro j
        exact ite_eq_left (le_of_not_gt (fun hj => he ⟨j, hj⟩))
      simpa [S, T, hx] using hω
  have hb := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  linarith

end TailMoments

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section Signs
variable {ι : Type uIota} [Fintype ι]

def signSum (ε : ι → Bool) (b : ι → ℝ) : ℝ :=
  ∑ j, if ε j then b j else -b j

def signAverage (b : ι → ℝ) : ℝ := by
  classical
  exact (∑ ε : ι → Bool, |signSum ε b|) / Fintype.card (ι → Bool)

lemma norm_le_signAverage (b : ι → ℝ) : ‖b‖ ≤ signAverage b := by
  classical
  have hcard : 0 < (Fintype.card (ι → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  have havg : 0 ≤ signAverage b := div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hcard.le
  apply (pi_norm_le_iff_of_nonneg havg).mpr
  intro j
  let flipFn := fun ε : ι → Bool => Function.update ε j (!(ε j))
  have hinvol : Function.Involutive flipFn := by
    intro ε
    funext i
    by_cases hij : i = j
    · subst i; simp [flipFn]
    · simp [flipFn, Function.update_of_ne hij]
  let flip : (ι → Bool) ≃ (ι → Bool) := ⟨flipFn, flipFn, hinvol, hinvol⟩
  have hdiff : ∀ ε, signSum ε b - signSum (flip ε) b = 2 * (if ε j then b j else -b j) := by
    intro ε
    unfold signSum
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · change (if ε j then b j else -b j) - (if flipFn ε j then b j else -b j) = _
      cases h : ε j <;> simp [flipFn, h] <;> ring
    · intro i hi hij
      change (if ε i then b i else -b i) - (if flipFn ε i then b i else -b i) = 0
      simp [flipFn, Function.update_of_ne hij]
    · simp
  have hpair : ∀ ε, 2 * |b j| ≤ |signSum ε b| + |signSum (flip ε) b| := by
    intro ε
    have he : |signSum ε b - signSum (flip ε) b| = 2 * |b j| := by
      rw [hdiff ε, abs_mul]
      cases ε j <;> simp
    rw [← he]
    simpa only [Real.norm_eq_abs] using norm_sub_le (signSum ε b) (signSum (flip ε) b)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => hpair ε)
  rw [Finset.sum_add_distrib, flip.sum_comp (fun ε => |signSum ε b|)] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  change |b j| ≤ (∑ ε, |signSum ε b|) / (Fintype.card (ι → Bool) : ℝ)
  apply (le_div_iff₀ hcard).mpr
  nlinarith

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma signSum_identDistrib [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X μ) (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ)
    (ε : ι → Bool) :
    IdentDistrib (fun ω => signSum ε (fun j => X j ω)) (fun ω => ∑ j, X j ω) μ μ := by
  let g := fun j (x : ℝ) => if ε j then x else -x
  have hg : ∀ j, Measurable (g j) := by
    intro j; dsimp [g]; cases ε j <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hdist : ∀ j, IdentDistrib (g j ∘ X j) (X j) μ μ := by
    intro j
    cases h : ε j
    · simpa only [g, h, Bool.false_eq_true, ite_false, Function.comp_def] using (hsym j).symm
    · simpa only [g, h, ite_true, Function.comp_def] using IdentDistrib.refl (hX j).aemeasurable
  exact (IdentDistrib.pi hdist (hind.comp g hg) hind).comp
    (show Measurable (fun b : ι → ℝ => ∑ j, b j) by fun_prop)

lemma expected_max_le_expected_abs_sum (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hi : ∀ j, Integrable (X j) μ) (hind : iIndepFun X μ)
    (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ) :
    ∫ ω, ‖fun j => X j ω‖ ∂μ ≤ ∫ ω, |∑ j, X j ω| ∂μ := by
  classical
  have hcard : 0 < (Fintype.card (ι → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsumI : Integrable (fun ω => ∑ j, X j ω) μ := integrable_finsetSum _ (fun j _ => hi j)
  have hsignI : ∀ ε : ι → Bool, Integrable (fun ω => |signSum ε (fun j => X j ω)|) μ := by
    intro ε
    exact ((signSum_identDistrib X hX hind hsym ε).integrable_iff.mpr hsumI).abs
  have hmean : (∫ ω, signAverage (fun j => X j ω) ∂μ) = ∫ ω, |∑ j, X j ω| ∂μ := by
    unfold signAverage
    rw [integral_div, integral_finsetSum _ (fun ε _ => hsignI ε)]
    have heq : ∀ ε : ι → Bool, (∫ ω, |signSum ε (fun j => X j ω)| ∂μ) =
        ∫ ω, |∑ j, X j ω| ∂μ := by
      intro ε
      simpa only [Real.norm_eq_abs] using (signSum_identDistrib X hX hind hsym ε).norm.integral_eq
    simp_rw [heq]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [← hmean]
  exact integral_mono (integrable_pi_iff.mpr hi).norm
    ((integrable_finsetSum _ (fun ε _ => hsignI ε)).div_const _)
    (fun ω => norm_le_signAverage (fun j => X j ω))

lemma one_sub_exp_neg_ge_half {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    v / 2 ≤ 1 - Real.exp (-v) := by
  rw [Real.exp_neg]
  have hb : 1 / Real.exp v ≤ 1 - v / 2 := by
    apply (div_le_iff₀ (Real.exp_pos v)).mpr
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp v)
      (show 0 ≤ 1 - v / 2 by linarith)
    nlinarith
  rw [one_div] at hb
  linarith

lemma independent_max_tail_lower (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X μ) {u : ℝ} (hu : 0 ≤ u) (b : ι → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hb1 : ∑ j, b j ≤ 1)
    (htail : ∀ j, b j ≤ μ.real {ω | u < |X j ω|}) :
    (∑ j, b j) / 2 ≤ μ.real {ω | u < ‖fun j => X j ω‖} := by
  classical
  have hpi : μ.real {ω | ‖fun j => X j ω‖ ≤ u} =
      ∏ j, μ.real {ω | |X j ω| ≤ u} := by
    have h := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => {x : ℝ | |x| ≤ u})
      (fun _ _ => measurableSet_le measurable_abs measurable_const)
    have hset : {ω | ‖fun j => X j ω‖ ≤ u} =
        ⋂ j ∈ (Finset.univ : Finset ι), X j ⁻¹' {x : ℝ | |x| ≤ u} := by
      ext ω
      simp only [Finset.mem_univ, iInter_true, mem_ofPred_eq, mem_iInter, mem_preimage]
      simpa only [Real.norm_eq_abs] using pi_norm_le_iff_of_nonneg (x := fun j => X j ω) hu
    rw [measureReal_def, hset, h, ENNReal.toReal_prod]
    rfl
  have hcomp : ∀ j, μ.real {ω | |X j ω| ≤ u} = 1 - μ.real {ω | u < |X j ω|} := by
    intro j
    have hset : {ω | |X j ω| ≤ u} = {ω | u < |X j ω|}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_lt measurable_const (hX j).abs)]
    simp
  have hallcomp : μ.real {ω | u < ‖fun j => X j ω‖} = 1 -
      μ.real {ω | ‖fun j => X j ω‖ ≤ u} := by
    have hset : {ω | u < ‖fun j => X j ω‖} = {ω | ‖fun j => X j ω‖ ≤ u}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_le
      (Measurable.of_eval hX).norm measurable_const)]
    simp
  have hprod : (∏ j, μ.real {ω | |X j ω| ≤ u}) ≤ Real.exp (-(∑ j, b j)) := by
    calc
      _ ≤ ∏ j, Real.exp (-b j) := by
        apply Finset.prod_le_prod (fun _ _ => measureReal_nonneg)
        intro j hj
        rw [hcomp]
        have he := Real.add_one_le_exp (-b j)
        have ht := htail j
        linarith
      _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hallcomp, hpi]
  exact (one_sub_exp_neg_ge_half (Finset.sum_nonneg (fun j _ => hb j)) hb1).trans
    (sub_le_sub_left hprod 1)

lemma integrable_real_tail {X : Ω → ℝ} (hX : Integrable X μ) (hX0 : 0 ≤ᵐ[μ] X) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t < X ω}) (Ioi 0) volume := by
  refine ⟨(measurable_real_tail X).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => measureReal_nonneg))).mpr ?_⟩
  have heq : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (μ.real {ω | t < X ω})) =
      ∫⁻ t in Ioi (0:ℝ), μ {ω | t < X ω} := by
    apply lintegral_congr
    intro t
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [heq, ← lintegral_eq_lintegral_meas_lt μ hX0 hX.aemeasurable]
  exact hX.lintegral_lt_top

lemma expectation_lower_from_power_tail {X : Ω → ℝ} (hX : Integrable X μ)
    (hX0 : 0 ≤ᵐ[μ] X) {p c d : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (hd : 0 < d)
    (htail : ∀ t, d ≤ t → c * t ^ (-p) ≤ μ.real {ω | t < X ω}) :
    c * d ^ (1 - p) / (p - 1) ≤ ∫ ω, X ω ∂μ := by
  have hi := integrable_real_tail hX hX0
  have hsub : Ioi d ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hd.le
  have hinonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ μ.real {ω | t < X ω} :=
    ae_of_all _ (fun _ => measureReal_nonneg)
  rw [hX.integral_eq_integral_meas_lt hX0]
  calc
    _ = ∫ t in Ioi d, c * t ^ (-p) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hd]
      have he : -p + 1 = 1 - p := by ring
      rw [he]
      field_simp [show p - 1 ≠ 0 by linarith, show 1 - p ≠ 0 by linarith]
      ring
    _ ≤ ∫ t in Ioi d, μ.real {ω | t < X ω} := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hc (Real.rpow_nonneg (hd.trans ht).le _)
      · exact hi.mono_set hsub
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact htail t ht.le
    _ ≤ _ := setIntegral_mono_set hi hinonneg (ae_of_all _ (fun t ht => hsub ht))

end Signs

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section HeavySums
variable {ι : Type uIota} [Fintype ι]

def coefficientNorm (p : ℝ) (a : ι → ℝ) : ℝ := (∑ j, |a j| ^ p) ^ (1 / p)

lemma coefficientNorm_nonneg (p : ℝ) (a : ι → ℝ) : 0 ≤ coefficientNorm p a :=
  Real.rpow_nonneg (Finset.sum_nonneg
    (fun index _ => Real.rpow_nonneg (abs_nonneg (a index)) _)) _

lemma coefficientNorm_rpow {p : ℝ} (hp : 0 < p) (a : ι → ℝ) :
    coefficientNorm p a ^ p = ∑ j, |a j| ^ p := by
  unfold coefficientNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _))]
  have he : (1 / p) * p = 1 := by field_simp
  rw [he, Real.rpow_one]

lemma abs_le_coefficientNorm {p : ℝ} (hp : 0 < p) (a : ι → ℝ) (j : ι) :
    |a j| ≤ coefficientNorm p a := by
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) (coefficientNorm_nonneg p a) hp).mp
  rw [coefficientNorm_rpow hp a]
  exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (abs_nonneg _) p) (Finset.mem_univ j)

lemma sum_scaled_coefficients {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) (a : ι → ℝ) :
    ∑ j, (s * |a j|) ^ p = (s * coefficientNorm p a) ^ p := by
  rw [Real.mul_rpow hs (coefficientNorm_nonneg p a), coefficientNorm_rpow hp a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact Real.mul_rpow hs (abs_nonneg _)

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma difference_law_tail [IsProbabilityMeasure μ] {Y : Ω → ℝ} {p u : ℝ}
    (hY : IdentDistrib Y (difference p) μ pairedMeasure) :
    μ.real {ω | u < |Y ω|} = pairedMeasure.real {v | u < |difference p v|} := by
  exact congrArg ENNReal.toReal (hY.measure_mem_eq
    (measurableSet_lt measurable_const measurable_abs))

lemma scaled_difference_tail_upper {Y : Ω → ℝ} {p u : ℝ}
    (hp : 1 < p) (hY : IdentDistrib Y (difference p) μ pairedMeasure)
    (a : ℝ) (hu : 0 < u) :
    μ.real {ω | u < |a * Y ω|} ≤ 2 * (scale p * |a|) ^ p * u ^ (-p) := by
  by_cases ha : a = 0
  · subst a
    simp [hu.not_gt, Real.zero_rpow (by linarith : p ≠ 0)]
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have hevent : {ω | u < |a * Y ω|} = {ω | u / |a| < |Y ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [abs_mul, div_lt_iff₀ ha0, mul_comm |a|]
  rw [hevent, difference_law_tail hY]
  refine (difference_tail_upper hp (div_pos hu ha0)).trans_eq ?_
  have hdiv : scale p / (u / |a|) = (scale p * |a|) / u := by field_simp
  rw [hdiv, Real.div_rpow (by positivity [scale_pos hp]) hu.le, Real.rpow_neg hu.le]
  ring

lemma scaled_difference_tail_lower {Y : Ω → ℝ} {p u : ℝ}
    (hp : 1 < p) (hpmax : p ≤ 3 / 2) (hY : IdentDistrib Y (difference p) μ pairedMeasure)
    (a : ℝ) (hu : 0 < u) (husa : scale p * |a| ≤ u) :
    (1 / 18) * (scale p * |a|) ^ p * u ^ (-p) ≤ μ.real {ω | u < |a * Y ω|} := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have hevent : {ω | u < |a * Y ω|} = {ω | u / |a| < |Y ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [abs_mul, div_lt_iff₀ ha0, mul_comm |a|]
  rw [hevent, difference_law_tail hY]
  have hlow := difference_tail_lower hp hpmax ((le_div_iff₀ ha0).mpr husa)
  have hdiv : scale p / (u / |a|) = (scale p * |a|) / u := by field_simp
  rw [hdiv, Real.div_rpow (by positivity [scale_pos hp]) hu.le] at hlow
  rw [Real.rpow_neg hu.le]
  convert hlow using 1
  ring

omit [IsProbabilityMeasure μ] in
lemma scaled_difference_symmetric [IsProbabilityMeasure μ] {Y : Ω → ℝ} {p : ℝ}
    (hY : IdentDistrib Y (difference p) μ pairedMeasure) (a : ℝ) :
    IdentDistrib (fun ω => a * Y ω) (fun ω => -(a * Y ω)) μ μ := by
  have hs := (hY.trans (difference_symmetric p)).trans hY.neg.symm
  have ha := hs.const_mul a
  simpa only [Pi.neg_apply, mul_neg] using ha

theorem heavy_tail_upper (Y : ι → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hlaw : ∀ j, IdentDistrib (Y j) (difference p) μ pairedMeasure)
    (a : ι → ℝ) {u : ℝ} (hu : 0 < u) :
    μ.real {ω | u < |∑ j, a j * Y j ω|} ≤
      10 * (scale p * coefficientNorm p a / u) ^ p := by
  have hs := scale_pos hp
  have hp0 : 0 < p := by linarith
  have hp2 : p < 2 := by linarith
  have hind' := hind.comp (fun j x => a j * x) (fun j => measurable_const.mul measurable_id)
  have hb := independent_symmetric_sum_tail (fun j ω => a j * Y j ω)
    (fun j => (hY j).const_mul _) hind' (fun j => scaled_difference_symmetric (hlaw j) (a j))
    hp0 hp2 (fun j => 2 * (scale p * |a j|) ^ p) (fun j => by positivity)
    (fun j t ht => scaled_difference_tail_upper hp (hlaw j) (a j) ht) hu
  rw [← Finset.mul_sum, sum_scaled_coefficients hp0 hs.le a] at hb
  have hconst : 2 / (2 - p) ≤ 4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hconst' : (1 + 2 / (2 - p)) * 2 ≤ 10 := by linarith
  have hm := mul_le_mul_of_nonneg_right hconst'
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg hs.le (coefficientNorm_nonneg p a)) p)
      (Real.rpow_nonneg hu.le (-p)))
  rw [Real.div_rpow (mul_nonneg hs.le (coefficientNorm_nonneg p a)) hu.le]
  rw [Real.rpow_neg hu.le] at hm hb
  simp only [div_eq_mul_inv] at *
  nlinarith

lemma scaled_difference_max_tail (Y : ι → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hlaw : ∀ j, IdentDistrib (Y j) (difference p) μ pairedMeasure)
    (a : ι → ℝ) {u : ℝ} (hu : 0 < u) (hud : scale p * coefficientNorm p a ≤ u) :
    (1 / 36) * (scale p * coefficientNorm p a / u) ^ p ≤
      μ.real {ω | u < ‖fun j => a j * Y j ω‖} := by
  have hs := scale_pos hp
  have hp0 : 0 < p := by linarith
  let b := fun j => (1 / 18) * (scale p * |a j|) ^ p * u ^ (-p)
  have hb0 : ∀ j, 0 ≤ b j := by intro j; dsimp [b]; positivity
  have hsum : ∑ j, b j = (1 / 18) * (scale p * coefficientNorm p a / u) ^ p := by
    dsimp [b]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_scaled_coefficients hp0 hs.le a,
      Real.div_rpow (mul_nonneg hs.le (coefficientNorm_nonneg p a)) hu.le,
      Real.rpow_neg hu.le]
    ring
  have hb1 : ∑ j, b j ≤ 1 := by
    rw [hsum]
    have hr : (scale p * coefficientNorm p a / u) ^ p ≤ 1 :=
      Real.rpow_le_one (div_nonneg (mul_nonneg hs.le (coefficientNorm_nonneg p a)) hu.le)
        ((div_le_one hu).mpr hud) hp0.le
    linarith
  have hind' := hind.comp (fun j x => a j * x) (fun j => measurable_const.mul measurable_id)
  have hb := independent_max_tail_lower (fun j ω => a j * Y j ω)
    (fun j => (hY j).const_mul _) hind' hu.le b hb0 hb1 (fun j =>
      scaled_difference_tail_lower hp hpmax (hlaw j) (a j) hu
        ((mul_le_mul_of_nonneg_left (abs_le_coefficientNorm hp0 a j) hs.le).trans hud))
  rw [hsum] at hb
  convert hb using 1
  ring

theorem heavy_tail_lower (Y : ι → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hlaw : ∀ j, IdentDistrib (Y j) (difference p) μ pairedMeasure)
    (a : ι → ℝ) :
    coefficientNorm p a / 54 ≤ ∫ ω, |∑ j, a j * Y j ω| ∂μ := by
  have hs := scale_pos hp
  have hp0 : 0 < p := by linarith
  have hA0 := coefficientNorm_nonneg p a
  by_cases hAeq : coefficientNorm p a = 0
  · rw [hAeq, zero_div]
    exact integral_nonneg (fun ω => abs_nonneg _)
  have hA : 0 < coefficientNorm p a := lt_of_le_of_ne hA0 (Ne.symm hAeq)
  let d := scale p * coefficientNorm p a
  have hd : 0 < d := mul_pos hs hA
  have hi : ∀ j, Integrable (fun ω => a j * Y j ω) μ := by
    intro j
    exact ((hlaw j).integrable_iff.mpr (integrable_difference hp)).const_mul _
  have hmaxi : Integrable (fun ω => ‖fun j => a j * Y j ω‖) μ := (integrable_pi_iff.mpr hi).norm
  have ht : ∀ t, d ≤ t → ((1 / 36) * d ^ p) * t ^ (-p) ≤
      μ.real {ω | t < ‖fun j => a j * Y j ω‖} := by
    intro t htd
    have ht0 := hd.trans_le htd
    have h := scaled_difference_max_tail Y hY hind hp hpmax hlaw a ht0 htd
    change (1 / 36) * (d / t) ^ p ≤ _ at h
    rw [Real.div_rpow hd.le ht0.le] at h
    rw [Real.rpow_neg ht0.le]
    convert h using 1
    ring
  have hEL := expectation_lower_from_power_tail hmaxi (ae_of_all _ (fun ω => norm_nonneg _))
    hp (show 0 ≤ (1 / 36 : ℝ) * d ^ p by positivity) hd ht
  have hid : ((1 / 36) * d ^ p) * d ^ (1 - p) / (p - 1) = coefficientNorm p a / (36 * p) := by
    rw [mul_assoc, ← Real.rpow_add hd, show p + (1 - p) = 1 by ring, Real.rpow_one]
    dsimp [d, scale]
    field_simp [hp0.ne', show p - 1 ≠ 0 by linarith]
  rw [hid] at hEL
  have h54 : coefficientNorm p a / 54 ≤ coefficientNorm p a / (36 * p) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith
  have hind' := hind.comp (fun j x => a j * x) (fun j => measurable_const.mul measurable_id)
  exact h54.trans (hEL.trans (expected_max_le_expected_abs_sum
    (fun j ω => a j * Y j ω) (fun j => (hY j).const_mul _) hi hind'
    (fun j => scaled_difference_symmetric (hlaw j) (a j))))

theorem heavy_tail (Y : ι → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y μ) {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hlaw : ∀ j, IdentDistrib (Y j) (difference p) μ pairedMeasure) (a : ι → ℝ) :
    (∫ v : unitInterval, multiplier p v = 1) ∧
    (∀ u : ℝ, 0 < u → μ.real {ω | u < |∑ j, a j * Y j ω|} ≤
      10 * (scale p * coefficientNorm p a / u) ^ p) ∧
    coefficientNorm p a / 54 ≤ ∫ ω, |∑ j, a j * Y j ω| ∂μ := by
  exact ⟨integral_multiplier hp, fun u hu => heavy_tail_upper Y hY hind hp hpmax hlaw a hu,
    heavy_tail_lower Y hY hind hp hpmax hlaw a⟩

end HeavySums

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section ProductModels

abbrev cube (ι : Type uIota) := ι → unitInterval
abbrev cubeMeasure (ι : Type uIota) [Fintype ι] : Measure (cube ι) :=
  Measure.pi (fun _ => (volume : Measure unitInterval))
abbrev pairCubeMeasure (ι : Type uIota) [Fintype ι] : Measure (ι → unitInterval × unitInterval) :=
  Measure.pi (fun _ => pairedMeasure)
abbrev arrayMeasure (κ : Type uKappa) (ι : Type uIota) [Fintype κ] [Fintype ι] :
    Measure (κ → cube ι) :=
  Measure.pi (fun _ => cubeMeasure ι)
abbrev pairedArrayMeasure (κ : Type uKappa) (ι : Type uIota) [Fintype κ] [Fintype ι] :
    Measure (κ → ι → unitInterval × unitInterval) :=
  Measure.pi (fun _ => pairCubeMeasure ι)

lemma mp_integral {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (μ.map f) := hf.map_eq.symm ▸ hg
  exact (integral_map hf.aemeasurable hm).symm.trans (congrArg (fun P => ∫ y, g y ∂P) hf.map_eq)

lemma mp_ident {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → γ} (hg : Measurable g) : IdentDistrib (g ∘ f) g μ ν := by
  refine ⟨(hg.comp hf.measurable).aemeasurable, hg.aemeasurable, ?_⟩
  rw [← Measure.map_map hg hf.measurable, hf.map_eq]

variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

def rowSum (p : ℝ) (a : ι → ℝ) (v : cube ι) : ℝ := ∑ j, a j * multiplier p (v j)

def diffRowSum (p : ℝ) (a : ι → ℝ) (v : ι → unitInterval × unitInterval) : ℝ :=
  ∑ j, a j * difference p (v j)

lemma measurable_rowSum (p : ℝ) (a : ι → ℝ) : Measurable (rowSum p a) := by
  unfold rowSum
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul ((measurable_multiplier p).comp (measurable_pi_apply j)))

lemma measurable_diffRowSum (p : ℝ) (a : ι → ℝ) : Measurable (diffRowSum p a) := by
  unfold diffRowSum
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul ((measurable_difference p).comp (measurable_pi_apply j)))

lemma integrable_rowSum {p : ℝ} (hp : 1 < p) (a : ι → ℝ) :
    Integrable (rowSum p a) (cubeMeasure ι) := by
  apply integrable_finsetSum
  intro j _
  exact ((measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) j).integrable_comp (integrable_multiplier hp).aestronglyMeasurable
    |>.mpr (integrable_multiplier hp)).const_mul _

lemma integrable_diffRowSum {p : ℝ} (hp : 1 < p) (a : ι → ℝ) :
    Integrable (diffRowSum p a) (pairCubeMeasure ι) := by
  apply integrable_finsetSum
  intro j _
  exact ((measurePreserving_eval (fun _ : ι => pairedMeasure) j).integrable_comp (integrable_difference hp).aestronglyMeasurable
    |>.mpr (integrable_difference hp)).const_mul _

lemma diffRowSum_lower {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2) (a : ι → ℝ) :
    coefficientNorm p a / 54 ≤ ∫ v, |diffRowSum p a v| ∂pairCubeMeasure ι := by
  apply heavy_tail_lower (μ := pairCubeMeasure ι) (fun j v => difference p (v j))
    (fun j => (measurable_difference p).comp (measurable_pi_apply j))
    (iIndepFun_pi (fun _ => (measurable_difference p).aemeasurable)) hp hpmax
  intro j
  exact mp_ident (measurePreserving_eval (fun _ : ι => pairedMeasure) j) (measurable_difference p)

lemma diffRowSum_tail {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2) (a : ι → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (pairCubeMeasure ι).real {v | r < |diffRowSum p a v|} ≤
      10 * (scale p * coefficientNorm p a / r) ^ p := by
  apply heavy_tail_upper (μ := pairCubeMeasure ι) (fun j v => difference p (v j))
    (fun j => (measurable_difference p).comp (measurable_pi_apply j))
    (iIndepFun_pi (fun _ => (measurable_difference p).aemeasurable)) hp hpmax
    (fun j => mp_ident (measurePreserving_eval (fun _ : ι => pairedMeasure) j) (measurable_difference p)) a hr

/-- Select, independently at every row, one of each pair of resampled coordinates. -/
def selectRows (b : κ → Bool) (v : κ → ι → unitInterval × unitInterval) : κ → cube ι :=
  fun k j => if b k then (v k j).2 else (v k j).1

lemma measurePreserving_selectRows (b : κ → Bool) :
    MeasurePreserving (selectRows (ι := ι) b) (pairedArrayMeasure κ ι) (arrayMeasure κ ι) := by
  unfold selectRows
  apply measurePreserving_pi (fun _ : κ => pairCubeMeasure ι) (fun _ : κ => cubeMeasure ι)
    (f := fun k v j => if b k then (v j).2 else (v j).1)
  intro k
  apply measurePreserving_pi (fun _ : ι => pairedMeasure) (fun _ : ι => (volume : Measure unitInterval))
    (f := fun _ v => if b k then v.2 else v.1)
  intro j
  by_cases hb : b k = true
  · simpa [selectRows, hb] using (measurePreserving_snd :
      MeasurePreserving Prod.snd pairedMeasure (volume : Measure unitInterval))
  · simpa [selectRows, hb] using (measurePreserving_fst :
      MeasurePreserving Prod.fst pairedMeasure (volume : Measure unitInterval))

end ProductModels
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section ProductModels
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

/-- The representation used in the whole-ball argument. -/
def enlargedFunction (p : ℝ) (x : B → ℝ) (u : κ → B → ℝ) (a : κ → ι → ℝ)
    (z : B × (κ → cube ι)) : ℝ :=
  x z.1 + ∑ k, u k z.1 * rowSum p (a k) (z.2 k)

lemma measurable_enlargedFunction (p : ℝ) {x : B → ℝ} {u : κ → B → ℝ}
    (hx : Measurable x) (hu : ∀ k, Measurable (u k)) (a : κ → ι → ℝ) :
    Measurable (enlargedFunction p x u a) := by
  apply (hx.comp measurable_fst).add
  exact Finset.measurable_sum _ (fun k _ => (hu k |>.comp measurable_fst).mul
    ((measurable_rowSum p (a k)).comp ((measurable_pi_apply k).comp measurable_snd)))

omit [IsProbabilityMeasure μ] in
lemma integrable_enlargedFunction [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 < p) {x : B → ℝ} {u : κ → B → ℝ}
    (hx : Integrable x μ) (hu : ∀ k, Integrable (u k) μ) (a : κ → ι → ℝ) :
    Integrable (enlargedFunction p x u a) (μ.prod (arrayMeasure κ ι)) := by
  apply ((measurePreserving_fst.integrable_comp hx.aestronglyMeasurable).mpr hx).add
  apply integrable_finsetSum
  intro k _
  exact (hu k).mul_prod ((measurePreserving_eval (fun _ : κ => cubeMeasure ι) k).integrable_comp
    (integrable_rowSum hp (a k)).aestronglyMeasurable |>.mpr (integrable_rowSum hp (a k)))

omit [MeasurableSpace B] in
lemma resampling_difference [MeasurableSpace B] [DecidableEq κ]
    (p : ℝ) (x : B → ℝ) (u : κ → B → ℝ) (a : κ → ι → ℝ)
    (k : κ) (z : B × (κ → ι → unitInterval × unitInterval)) :
    enlargedFunction p x u a (z.1, selectRows (fun _ => false) z.2) -
      enlargedFunction p x u a (z.1, selectRows (fun l => decide (l = k)) z.2) =
    u k z.1 * diffRowSum p (a k) (z.2 k) := by
  classical
  simp only [enlargedFunction, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp [selectRows, rowSum, diffRowSum, difference, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub]
  · intro l _ hl
    have heq : selectRows (fun _ => false) z.2 l = selectRows (fun t => decide (t = k)) z.2 l := by
      funext j
      simp [selectRows, hl]
    rw [heq, sub_self]
  · simp

/-- Resampling controls the coefficients of EVERY representation of a point of the new unit ball. -/
theorem coefficient_bound_108 {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    {x : B → ℝ} {u : κ → B → ℝ} (hx : Integrable x μ)
    (hu : ∀ k, Integrable (u k) μ) (hun : ∀ k, ∫ b, |u k b| ∂μ = 1)
    (a : κ → ι → ℝ)
    (hg : ∫ z, |enlargedFunction p x u a z| ∂(μ.prod (arrayMeasure κ ι)) ≤ 1)
    (k : κ) : coefficientNorm p (a k) ≤ 108 := by
  classical
  let g := enlargedFunction p x u a
  have hgi : Integrable g (μ.prod (arrayMeasure κ ι)) := integrable_enlargedFunction hp hx hu a
  let f₁ := Prod.map (id : B → B) (selectRows (ι := ι) (fun _ : κ => false))
  let f₂ := Prod.map (id : B → B) (selectRows (ι := ι) (fun l : κ => decide (l = k)))
  have hm₁ : MeasurePreserving f₁ (μ.prod (pairedArrayMeasure κ ι)) (μ.prod (arrayMeasure κ ι)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_selectRows _)
  have hm₂ : MeasurePreserving f₂ (μ.prod (pairedArrayMeasure κ ι)) (μ.prod (arrayMeasure κ ι)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_selectRows _)
  have hi₁ : Integrable (fun z => g (f₁ z)) (μ.prod (pairedArrayMeasure κ ι)) :=
    (hm₁.integrable_comp hgi.aestronglyMeasurable).mpr hgi
  have hi₂ : Integrable (fun z => g (f₂ z)) (μ.prod (pairedArrayMeasure κ ι)) :=
    (hm₂.integrable_comp hgi.aestronglyMeasurable).mpr hgi
  have hdiff : (∫ z, |g (f₁ z) - g (f₂ z)| ∂(μ.prod (pairedArrayMeasure κ ι))) ≤ 2 := by
    calc
      _ ≤ ∫ z, |g (f₁ z)| + |g (f₂ z)| ∂(μ.prod (pairedArrayMeasure κ ι)) :=
        integral_mono (hi₁.sub hi₂).abs (hi₁.abs.add hi₂.abs)
          (fun z => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_sub_le (g (f₁ z)) (g (f₂ z)))
      _ = 2 * ∫ z, |g z| ∂(μ.prod (arrayMeasure κ ι)) := by
        rw [integral_add hi₁.abs hi₂.abs, mp_integral hm₁ hgi.abs.aestronglyMeasurable,
          mp_integral hm₂ hgi.abs.aestronglyMeasurable]
        ring
      _ ≤ 2 := by dsimp [g]; linarith
  have hid : (∫ z, |g (f₁ z) - g (f₂ z)| ∂(μ.prod (pairedArrayMeasure κ ι))) =
      ∫ v, |diffRowSum p (a k) v| ∂pairCubeMeasure ι := by
    simp only [g, f₁, f₂, Prod.map_def, id_eq, resampling_difference, abs_mul]
    rw [integral_prod_mul (μ := μ) (ν := pairedArrayMeasure κ ι)
      (fun b => |u k b|) (fun v => |diffRowSum p (a k) (v k)|), hun k, one_mul]
    exact mp_integral (measurePreserving_eval (fun _ : κ => pairCubeMeasure ι) k) (integrable_diffRowSum hp (a k)).abs.aestronglyMeasurable
  rw [hid] at hdiff
  have hl := diffRowSum_lower hp hpmax (a k)
  linarith

/-- Averaging over the resampled copy produces a deterministic center. -/
lemma concentration_center {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {z : R → ℝ} (hz : Measurable z) {r q : ℝ}
    (h : (ν.prod ν).real {v | r < |z v.1 - z v.2|} < q) :
    ∃ c : ℝ, ν.real {v | r < |z v - c|} < q := by
  let S : Set (R × R) := {v | r < |z v.1 - z v.2|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    ((hz.comp measurable_fst).sub (hz.comp measurable_snd)).abs
  have hi : Integrable (S.indicator (1 : R × R → ℝ)) (ν.prod ν) :=
    (integrable_const 1).indicator hS
  have hinner (y : R) : (∫ x, S.indicator (1 : R × R → ℝ) (x, y) ∂ν) =
      ν.real {x | r < |z x - z y|} := by
    have heq : (fun x => S.indicator (1 : R × R → ℝ) (x, y)) =
        {x | r < |z x - z y|}.indicator (1 : R → ℝ) := by
      funext x
      simp [S, Set.indicator_apply]
    rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hz.sub_const (z y)).abs)]
  have htotal : (ν.prod ν).real S = ∫ y, ν.real {x | r < |z x - z y|} ∂ν := by
    rw [← integral_indicator_one hS, integral_prod_symm _ hi]
    simp_rw [hinner]
  by_contra hn
  push Not at hn
  have hint : Integrable (fun y => ν.real {x | r < |z x - z y|}) ν := by
    simpa only [hinner] using hi.integral_prod_right
  have hq := integral_mono (integrable_const q) hint (fun y => hn (z y))
  simp only [integral_const, probReal_univ, one_smul] at hq
  rw [← htotal] at hq
  exact (not_lt_of_ge hq) h

lemma diffRowSum_prod_tail (p : ℝ) (a : ι → ℝ) (r : ℝ) :
    ((cubeMeasure ι).prod (cubeMeasure ι)).real {v | r < |rowSum p a v.1 - rowSum p a v.2|} =
      (pairCubeMeasure ι).real {v | r < |diffRowSum p a v|} := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow unitInterval unitInterval ι
  have he : MeasurePreserving e (pairCubeMeasure ι) ((cubeMeasure ι).prod (cubeMeasure ι)) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ _ _
  have heq := he.measure_preimage (s := {v | r < |rowSum p a v.1 - rowSum p a v.2|}) (measurableSet_lt measurable_const
    (((measurable_rowSum p a).comp measurable_fst).sub
      ((measurable_rowSum p a).comp measurable_snd)).abs).nullMeasurableSet
  have hset : e ⁻¹' {v | r < |rowSum p a v.1 - rowSum p a v.2|} =
      {v | r < |diffRowSum p a v|} := by
    ext v
    change (r < |rowSum p a (fun j => (v j).1) - rowSum p a (fun j => (v j).2)|) ↔ _
    simp [rowSum, diffRowSum, difference, Finset.sum_sub_distrib, mul_sub]
  simp only [measureReal_def, ← heq, hset]

lemma rowSum_concentration {p r q : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    (hr : 0 < r) (hpq : 10 * (108 * scale p / r) ^ p < q)
    (a : ι → ℝ) (ha : coefficientNorm p a ≤ 108) :
    ∃ c : ℝ, (cubeMeasure ι).real {v | r < |rowSum p a v - c|} < q := by
  apply concentration_center (measurable_rowSum p a)
  rw [diffRowSum_prod_tail]
  apply lt_of_le_of_lt (diffRowSum_tail hp hpmax a hr)
  apply lt_of_le_of_lt _ hpq
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow
  · exact div_nonneg (mul_nonneg (scale_pos hp).le (coefficientNorm_nonneg p a)) hr.le
  · apply div_le_div_of_nonneg_right _ hr.le
    nlinarith [scale_pos hp]
  · linarith

lemma abs_add_lower (a b : ℝ) : |a| + |b| - 2 * min |a| |b| ≤ |a + b| := by
  have h₁ : |a| ≤ |a + b| + |b| := by
    simpa only [Real.norm_eq_abs, add_neg_cancel_right, abs_neg] using (norm_add_le (a + b) (-b))
  have h₂ : |b| ≤ |a| + |a + b| := by
    simpa only [Real.norm_eq_abs, neg_add_cancel_left, abs_neg] using (norm_add_le (-a) (a + b))
  rcases le_total |a| |b| with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

end ProductModels
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section ProductModels
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

/-- Near-disjointness from every old unit vector, using only the new scalar tail. -/
lemma near_additivity {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {w u : B → ℝ} {f : R → ℝ}
    (hw : Integrable w μ) (hu : Integrable u μ) (hf : Integrable f ν)
    (hfm : Measurable f) (hf0 : ∀ v, 0 ≤ f v)
    (hw1 : ∫ b, |w b| ∂μ = 1) (hu1 : ∫ b, |u b| ∂μ = 1)
    (hf1 : ∫ v, f v ∂ν = 1) {c : ℝ} (hc : 0 ≤ c) :
    2 - 2 * (ν.real {v | c < f v} + c) ≤
      ∫ z : B × R, |w z.1 + u z.1 * f z.2| ∂(μ.prod ν) := by
  let S := {v | c < f v}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hfm
  let W : B × R → ℝ := fun z => w z.1
  let V : B × R → ℝ := fun z => u z.1 * f z.2
  let A : B × R → ℝ := fun z => |w z.1| * S.indicator (1 : R → ℝ) z.2
  let C : B × R → ℝ := fun z => c * |u z.1|
  have hW : Integrable W (μ.prod ν) := (measurePreserving_fst.integrable_comp hw.aestronglyMeasurable).mpr hw
  have hV : Integrable V (μ.prod ν) := hu.mul_prod hf
  have hA : Integrable A (μ.prod ν) := hw.abs.mul_prod ((integrable_const 1).indicator hS)
  have hC : Integrable C (μ.prod ν) :=
    ((measurePreserving_fst.integrable_comp hu.abs.aestronglyMeasurable).mpr hu.abs).const_mul c
  have hpoint (z : B × R) : |W z| + |V z| - 2 * (A z + C z) ≤ |W z + V z| := by
    apply le_trans _ (abs_add_lower _ _)
    have hmin : min |W z| |V z| ≤ A z + C z := by
      by_cases hz : z.2 ∈ S
      · simp only [A, Set.indicator_of_mem hz, Pi.one_apply, mul_one, C]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right (mul_nonneg hc (abs_nonneg _)))
      · have hfz : f z.2 ≤ c := le_of_not_gt hz
        simp only [A, Set.indicator_of_notMem hz, mul_zero, zero_add, C]
        apply (min_le_right _ _).trans
        dsimp [V]
        rw [abs_mul, abs_of_nonneg (hf0 _), mul_comm c]
        exact mul_le_mul_of_nonneg_left hfz (abs_nonneg _)
    linarith
  have hineq := integral_mono ((hW.abs.add hV.abs).sub ((hA.add hC).const_mul 2))
    (hW.add hV).abs hpoint
  have hWi : (∫ z, |W z| ∂(μ.prod ν)) = 1 :=
    (mp_integral measurePreserving_fst hw.abs.aestronglyMeasurable).trans hw1
  have hVi : (∫ z, |V z| ∂(μ.prod ν)) = 1 := by
    simp only [V, abs_mul, abs_of_nonneg (hf0 _)]
    rw [integral_prod_mul (fun b => |u b|) f, hu1, hf1, one_mul]
  have hAi : (∫ z, A z ∂(μ.prod ν)) = ν.real S := by
    rw [show A = (fun z : B × R => |w z.1| * S.indicator (1 : R → ℝ) z.2) from rfl,
      integral_prod_mul (fun b => |w b|) (S.indicator (1 : R → ℝ)), hw1, one_mul, integral_indicator_one hS]
  have hCi : (∫ z, C z ∂(μ.prod ν)) = c := by
    dsimp [C]
    rw [integral_const_mul, mp_integral measurePreserving_fst hu.abs.aestronglyMeasurable, hu1, mul_one]
  simp only [Pi.sub_apply, Pi.add_apply] at hineq
  rw [integral_sub (f := fun z => |W z| + |V z|) (g := fun z => 2 * (A z + C z)) (hW.abs.add hV.abs) ((hA.add hC).const_mul 2),
    integral_add hW.abs hV.abs, integral_const_mul, integral_add hA hC, hWi, hVi, hAi, hCi] at hineq
  simpa only [W, V, S, show (1 : ℝ) + 1 = 2 by norm_num] using hineq

/-- Radial retraction to the old L1 unit ball, pointwise on representatives. -/
def normalizeFunction (μ : Measure B) (f : B → ℝ) (b : B) : ℝ :=
  f b / max 1 (∫ b, |f b| ∂μ)

omit [IsProbabilityMeasure μ] in
lemma integrable_normalizeFunction [IsProbabilityMeasure μ]
    {f : B → ℝ} (hf : Integrable f μ) :
    Integrable (normalizeFunction μ f) μ := hf.div_const _

omit [IsProbabilityMeasure μ] in
lemma normalizeFunction_bounds [IsProbabilityMeasure μ]
    {f : B → ℝ} (_hf : Integrable f μ) {R : ℝ}
    (hR : 1 ≤ R) (hN : (∫ b, |f b| ∂μ) ≤ R) :
    (∫ b, |normalizeFunction μ f b| ∂μ) ≤ 1 ∧
    (∫ b, |f b - normalizeFunction μ f b| ∂μ) ≤ R - 1 := by
  let N := ∫ b, |f b| ∂μ
  have hN0 : 0 ≤ N := integral_nonneg (fun b => abs_nonneg _)
  by_cases hN1 : N ≤ 1
  · have heq : normalizeFunction μ f = f := by
      funext b
      change f b / max 1 N = f b
      rw [max_eq_left hN1, div_one]
    rw [heq]
    constructor
    · exact hN1
    · simp only [sub_self, abs_zero, integral_zero]
      linarith
  · have hNpos : 0 < N := by linarith
    have hNgt : 1 < N := lt_of_not_ge hN1
    have heq : normalizeFunction μ f = fun b => f b / N := by
      funext b
      change f b / max 1 N = f b / N
      rw [max_eq_right hNgt.le]
    rw [heq]
    constructor
    · simp only [abs_div, abs_of_pos hNpos]
      rw [integral_div]
      change N / N ≤ 1
      simp [hNpos.ne']
    · have hpoint (b : B) : |f b - f b / N| = ((N - 1) / N) * |f b| := by
        have he : f b - f b / N = ((N - 1) / N) * f b := by field_simp
        rw [he, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hNgt.le) hNpos.le)]
      simp_rw [hpoint]
      rw [integral_const_mul]
      change (N - 1) / N * N ≤ R - 1
      rw [div_mul_cancel₀ _ hNpos.ne']
      exact sub_le_sub_right hN 1

/-- Markov's inequality after discarding a small exceptional set. -/
lemma restricted_markov {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsFiniteMeasure ν] {f b : R → ℝ} (hf : Integrable f ν) (hb : Integrable b ν)
    (hf0 : ∀ v, 0 ≤ f v) (hb0 : ∀ v, 0 ≤ b v)
    {D : Set R} (hD : MeasurableSet D) (hdom : ∀ v ∈ D, f v ≤ b v)
    {h : ℝ} (hh : 0 < h) :
    ν.real {v | h < f v} ≤ ν.real Dᶜ + (∫ v, b v ∂ν) / h := by
  classical
  let T := D.indicator f
  have hT : Integrable T ν := hf.indicator hD
  have hT0 : ∀ v, 0 ≤ T v := fun v => Set.indicator_nonneg (fun v _ => hf0 v) v
  have hTb (v : R) : T v ≤ b v := by
    by_cases hv : v ∈ D
    · simpa only [T, Set.indicator_of_mem hv] using hdom v hv
    · simpa only [T, Set.indicator_of_notMem hv] using hb0 v
  have hbound := (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hT0) hT h).trans
    (integral_mono hT hb hTb)
  have hprob : ν.real {v | h ≤ T v} ≤ (∫ v, b v ∂ν) / h := by
    apply (le_div_iff₀ hh).mpr
    simpa only [mul_comm] using hbound
  have hsub : {v | h < f v} ⊆ Dᶜ ∪ {v | h ≤ T v} := by
    intro v hv
    change h < f v at hv
    by_cases hvD : v ∈ D
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq, T, Set.indicator_of_mem hvD] using hv.le)
    · exact Or.inl hvD
  exact (measureReal_mono (μ := ν) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl hprob))

/-- Fubini on the good event controls the old approximant before normalization. -/
lemma old_norm_on_good_set {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {g : B × R → ℝ} {ψ U : B → ℝ}
    (hg : Integrable g (μ.prod ν)) (hψ : Integrable ψ μ) (hU : Integrable U μ)
    (_hU0 : ∀ b, 0 ≤ U b) {m r : ℝ} (hm : ∫ b, U b ∂μ = m) (_hr : 0 ≤ r)
    (hg1 : ∫ z, |g z| ∂(μ.prod ν) ≤ 1)
    {D : Set R} (hD : MeasurableSet D) (hDpos : 0 < ν.real D)
    (hgood : ∀ b v, v ∈ D → |g (b, v) - ψ b| ≤ r * U b) :
    (∫ b, |ψ b| ∂μ) ≤ r * m + 1 / ν.real D := by
  let J := D.indicator (1 : R → ℝ)
  have hJ : Integrable J ν := (integrable_const 1).indicator hD
  have hA : Integrable (fun z : B × R => |ψ z.1| * J z.2) (μ.prod ν) := hψ.abs.mul_prod hJ
  have hC : Integrable (fun z : B × R => (r * U z.1) * J z.2) (μ.prod ν) := (hU.const_mul r).mul_prod hJ
  have hpoint (z : B × R) : |ψ z.1| * J z.2 ≤ |g z| + (r * U z.1) * J z.2 := by
    by_cases hz : z.2 ∈ D
    · simp only [J, Set.indicator_of_mem hz, Pi.one_apply, mul_one]
      have ht : |ψ z.1| ≤ |g z| + |g z - ψ z.1| := by
        simpa only [Real.norm_eq_abs, sub_sub_cancel] using norm_sub_le (g z) (g z - ψ z.1)
      exact ht.trans (add_le_add le_rfl (hgood z.1 z.2 hz))
    · simp only [J, Set.indicator_of_notMem hz, mul_zero, add_zero]
      exact abs_nonneg _
  have hineq := integral_mono hA (hg.abs.add hC) hpoint
  simp only [Pi.add_apply] at hineq
  rw [integral_prod_mul (fun b => |ψ b|) J, integral_add hg.abs hC,
    integral_prod_mul (fun b => r * U b) J, integral_const_mul, hm,
    show (∫ v, J v ∂ν) = ν.real D from integral_indicator_one hD] at hineq
  have hlin : ((∫ b, |ψ b| ∂μ) - r * m) * ν.real D ≤ 1 := by nlinarith
  have hdiv := (le_div_iff₀ hDpos).mpr hlin
  linarith

end ProductModels
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

section ProductModels
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

lemma whole_ball_estimate {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {g : B × R → ℝ} {ψ U : B → ℝ}
    (hg : Integrable g (μ.prod ν)) (hψ : Integrable ψ μ) (hU : Integrable U μ)
    (hU0 : ∀ b, 0 ≤ U b) {m r q h : ℝ} (hm : ∫ b, U b ∂μ = m)
    (hm0 : 0 ≤ m) (hr : 0 ≤ r) (hq : 0 ≤ q) (hmq : m * q < 1) (hh : 0 < h)
    (hg1 : ∫ z, |g z| ∂(μ.prod ν) ≤ 1)
    {D : Set R} (hD : MeasurableSet D) (hDprob : 1 - m * q ≤ ν.real D)
    (hgood : ∀ b v, v ∈ D → |g (b, v) - ψ b| ≤ r * U b) :
    (∫ b, |normalizeFunction μ ψ b| ∂μ) ≤ 1 ∧
    (μ.prod ν).real {z | h < |g z - normalizeFunction μ ψ z.1|} ≤
      m * q + h⁻¹ * (2 * m * r + (1 - m * q)⁻¹ - 1) := by
  have hL : 0 < 1 - m * q := sub_pos.mpr hmq
  have hDpos := hL.trans_le hDprob
  have hN := old_norm_on_good_set hg hψ hU hU0 hm hr hg1 hD hDpos hgood
  have hinv : 1 / ν.real D ≤ 1 / (1 - m * q) := one_div_le_one_div_of_le hL hDprob
  have hR : 1 ≤ r * m + (1 - m * q)⁻¹ := by
    have hinv1 : 1 ≤ (1 - m * q)⁻¹ := by
      apply (one_le_inv₀ hL).mpr
      nlinarith
    nlinarith
  have hNb : (∫ b, |ψ b| ∂μ) ≤ r * m + (1 - m * q)⁻¹ := by
    simp only [one_div] at hinv hN
    linarith
  obtain ⟨hnorm, hcost⟩ := normalizeFunction_bounds hψ hR hNb
  refine ⟨hnorm, ?_⟩
  let ψ₀ := normalizeFunction μ ψ
  have hψ₀ : Integrable ψ₀ μ := integrable_normalizeFunction hψ
  let f : B × R → ℝ := fun z => |g z - ψ₀ z.1|
  let bnd : B × R → ℝ := fun z => r * U z.1 + |ψ z.1 - ψ₀ z.1|
  have hψpull : Integrable (fun z : B × R => ψ₀ z.1) (μ.prod ν) :=
    (measurePreserving_fst.integrable_comp hψ₀.aestronglyMeasurable).mpr hψ₀
  have hf : Integrable f (μ.prod ν) := (hg.sub hψpull).abs
  have hbi : Integrable bnd (μ.prod ν) :=
    ((measurePreserving_fst.integrable_comp hU.aestronglyMeasurable).mpr hU |>.const_mul r).add
      ((measurePreserving_fst.integrable_comp (hψ.sub hψ₀).abs.aestronglyMeasurable).mpr (hψ.sub hψ₀).abs)
  have hbint : (∫ z, bnd z ∂(μ.prod ν)) ≤ 2 * m * r + (1 - m * q)⁻¹ - 1 := by
    dsimp [bnd]
    rw [integral_add (f := fun z : B × R => r * U z.1)
      (g := fun z => |ψ z.1 - ψ₀ z.1|)
      (((measurePreserving_fst.integrable_comp hU.aestronglyMeasurable).mpr hU).const_mul r)
      ((measurePreserving_fst.integrable_comp (hψ.sub hψ₀).abs.aestronglyMeasurable).mpr (hψ.sub hψ₀).abs),
      integral_const_mul, mp_integral measurePreserving_fst hU.aestronglyMeasurable, hm,
      mp_integral (g := fun b => |ψ b - ψ₀ b|) measurePreserving_fst (hψ.sub hψ₀).abs.aestronglyMeasurable]
    dsimp [ψ₀] at *
    linarith
  have hmark := restricted_markov hf hbi (fun z => abs_nonneg _)
    (fun z => add_nonneg (mul_nonneg hr (hU0 _)) (abs_nonneg _))
    (hD.preimage measurable_snd) (fun z hz => by
      dsimp [f, bnd]
      exact (abs_sub_le (g z) (ψ z.1) (ψ₀ z.1)).trans
        (add_le_add (hgood z.1 z.2 hz) le_rfl)) hh
  have hcompl : (μ.prod ν).real (Prod.snd ⁻¹' D)ᶜ ≤ m * q := by
    rw [← Set.preimage_compl]
    have heq := (measurePreserving_snd : MeasurePreserving (@Prod.snd B R) (μ.prod ν) ν).measure_preimage hD.compl.nullMeasurableSet
    rw [measureReal_def, heq, ← measureReal_def, probReal_compl_eq_one_sub hD]
    linarith
  apply hmark.trans
  have hdiv := div_le_div_of_nonneg_right hbint hh.le
  apply add_le_add hcompl
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

def oldCombination (x : B → ℝ) (u : κ → B → ℝ) (c : κ → ℝ) (b : B) : ℝ :=
  x b + ∑ k, c k * u k b

omit [IsProbabilityMeasure μ] in
lemma integrable_oldCombination [IsProbabilityMeasure μ] {x : B → ℝ} {u : κ → B → ℝ}
    (hx : Integrable x μ) (hu : ∀ k, Integrable (u k) μ) (c : κ → ℝ) :
    Integrable (oldCombination x u c) μ := by
  exact hx.add (integrable_finsetSum _ (fun k _ => (hu k).const_mul (c k)))

/-- Whole-ball approximation for arbitrary coefficients, after fixing the multiplier law,
    and before choosing the number of copies. -/
theorem whole_ball_approximation {p r q h : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    (hr : 0 < r) (hq : 0 < q) (hh : 0 < h)
    (hmq : (Fintype.card κ : ℝ) * q < 1)
    (herr : (Fintype.card κ : ℝ) * q + h⁻¹ *
      (2 * (Fintype.card κ : ℝ) * r + (1 - (Fintype.card κ : ℝ) * q)⁻¹ - 1) < h)
    (hpq : 10 * (108 * scale p / r) ^ p < q)
    {x : B → ℝ} {u : κ → B → ℝ} (hx : Integrable x μ) (hu : ∀ k, Integrable (u k) μ)
    (hun : ∀ k, ∫ b, |u k b| ∂μ = 1) (a : κ → ι → ℝ)
    (hg : ∫ z, |enlargedFunction p x u a z| ∂(μ.prod (arrayMeasure κ ι)) ≤ 1) :
    ∃ c : κ → ℝ,
      (∫ b, |normalizeFunction μ (oldCombination x u c) b| ∂μ) ≤ 1 ∧
      (μ.prod (arrayMeasure κ ι)).real
        {z | h < |enlargedFunction p x u a z - normalizeFunction μ (oldCombination x u c) z.1|} < h := by
  classical
  have hcoeff : ∀ k, coefficientNorm p (a k) ≤ 108 := coefficient_bound_108 hp hpmax hx hu hun a hg
  choose c hc using (fun k => rowSum_concentration hp hpmax hr hpq (a k) (hcoeff k))
  let D : Set (κ → cube ι) := ⋂ k, {v | |rowSum p (a k) (v k) - c k| ≤ r}
  have hD : MeasurableSet D := MeasurableSet.iInter (fun k => measurableSet_le
    (((measurable_rowSum p (a k)).comp (measurable_pi_apply k)).sub_const (c k)).abs measurable_const)
  have htail (k : κ) : (arrayMeasure κ ι).real {v | r < |rowSum p (a k) (v k) - c k|} < q := by
    have he := (measurePreserving_eval (fun _ : κ => cubeMeasure ι) k).measureReal_preimage
      (measurableSet_lt (measurable_const (a := r)) ((measurable_rowSum p (a k)).sub_const (c k)).abs).nullMeasurableSet
    simpa only [Set.preimage_ofPred_eq] using he.trans_lt (hc k)
  have hDprob : 1 - (Fintype.card κ : ℝ) * q ≤ (arrayMeasure κ ι).real D := by
    have heq : Dᶜ = ⋃ k, {v | r < |rowSum p (a k) (v k) - c k|} := by
      ext v
      simp only [D, Set.mem_compl_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_iUnion,
        not_forall, not_le]
    have hb := measureReal_iUnion_fintype_le (μ := arrayMeasure κ ι)
      (fun k => {v | r < |rowSum p (a k) (v k) - c k|})
    have hb' := hb.trans (Finset.sum_le_sum (fun k _ => (htail k).le))
    rw [← heq, probReal_compl_eq_one_sub hD] at hb'
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hb'
    linarith
  let U : B → ℝ := fun b => ∑ k, |u k b|
  have hU : Integrable U μ := integrable_finsetSum _ (fun k _ => (hu k).abs)
  have hU0 : ∀ b, 0 ≤ U b := fun b => Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hUm : (∫ b, U b ∂μ) = (Fintype.card κ : ℝ) := by
    rw [integral_finsetSum _ (fun k _ => (hu k).abs)]
    simp only [hun, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hgood (b : B) (v : κ → cube ι) (hv : v ∈ D) :
      |enlargedFunction p x u a (b, v) - oldCombination x u c b| ≤ r * U b := by
    have heq : enlargedFunction p x u a (b, v) - oldCombination x u c b =
        ∑ k, u k b * (rowSum p (a k) (v k) - c k) := by
      simp only [enlargedFunction, oldCombination, add_sub_add_left_eq_sub,
        mul_sub, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq]
    calc
      _ ≤ ∑ k, |u k b * (rowSum p (a k) (v k) - c k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |u k b| * r := Finset.sum_le_sum (fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (Set.mem_iInter.mp hv k) (abs_nonneg _))
      _ = r * U b := by dsimp [U]; rw [← Finset.sum_mul]; ring
  obtain ⟨hn, ht⟩ := whole_ball_estimate (integrable_enlargedFunction hp hx hu a)
    (integrable_oldCombination hx hu c) hU hU0 hUm (by positivity : (0:ℝ) ≤ Fintype.card κ)
    hr.le hq.le hmq hh hg hD hDprob hgood
  exact ⟨c, hn, ht.trans_lt herr⟩

lemma enlargement_parameters {m h : ℝ} (_hm : 0 < m) (hh : 0 < h) (_hh1 : h < 1) :
    ∃ c r q p : ℝ, 0 < c ∧ c < h / 4 ∧ 0 < r ∧ 0 < q ∧ 1 < p ∧ p ≤ 3/2 ∧
      m * q < 1 ∧ m * q + h⁻¹ * (2 * m * r + (1 - m * q)⁻¹ - 1) < h ∧
      scale p < c ∧ 2 * ((scale p / c) ^ p + c) < h ∧ 10 * (108 * scale p / r) ^ p < q := by
  let c := h / 8
  have hc : 0 < c := by dsimp [c]; positivity
  have hc4 : c < h / 4 := by dsimp [c]; linarith
  have hc2 : 2 * c < h := by dsimp [c]; linarith
  let err := fun v : ℝ => m * v + h⁻¹ * (2 * m * v + (1 - m * v)⁻¹ - 1)
  have herrc : ContinuousAt err 0 := by
    dsimp [err]
    fun_prop (disch := norm_num)
  have herr0 : err 0 = 0 := by simp [err]
  have hevent : ∀ᶠ v in 𝓝 (0 : ℝ), m * v < 1 ∧ err v < h := by
    apply Filter.Eventually.and
    · exact (show ContinuousAt (fun v : ℝ => m * v) 0 by fun_prop).tendsto
        |>.eventually (Iio_mem_nhds (by norm_num))
    · exact herrc.tendsto.eventually (Iio_mem_nhds (by simpa only [herr0] using hh))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : dist r 0 < δ := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using (show r < δ by dsimp [r]; linarith)
  obtain ⟨hmr, herr⟩ := hball hrd
  have hs : ContinuousAt scale 1 := by unfold scale; fun_prop (disch := norm_num)
  have hs1 : scale 1 = 0 := by norm_num [scale]
  have hpowc : ContinuousAt (fun p : ℝ => (scale p / c) ^ p) 1 := by
    apply ContinuousAt.rpow (hs.div_const c) continuousAt_id
    right; norm_num
  have hpowr : ContinuousAt (fun p : ℝ => (108 * scale p / r) ^ p) 1 := by
    apply ContinuousAt.rpow ((hs.const_mul 108).div_const r) continuousAt_id
    right; norm_num
  have hpEv : ∀ᶠ p in 𝓝 (1 : ℝ), p < 3/2 ∧ scale p < c ∧
      2 * ((scale p / c) ^ p + c) < h ∧ 10 * (108 * scale p / r) ^ p < r := by
    filter_upwards [eventually_lt_nhds (by norm_num : (1 : ℝ) < 3/2),
      hs.tendsto.eventually (Iio_mem_nhds (by simpa only [hs1] using hc)),
      ((hpowc.add_const c).const_mul 2).tendsto.eventually (Iio_mem_nhds (by simpa [hs1] using hc2)),
      (hpowr.const_mul 10).tendsto.eventually (Iio_mem_nhds (by simpa [hs1] using hr))]
      with p hp₁ hp₂ hp₃ hp₄
    exact ⟨hp₁, hp₂, hp₃, hp₄⟩
  obtain ⟨ε, hε, hpball⟩ := Metric.eventually_nhds_iff.mp hpEv
  let p := 1 + ε / 2
  have hp : 1 < p := by dsimp [p]; linarith
  have hpd : dist p 1 < ε := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hp)]
    dsimp [p]; linarith
  obtain ⟨hpmax, hpc, hpc2, hpq⟩ := hpball hpd
  exact ⟨c, r, r, p, hc, hc4, hr, hr, hp, hpmax.le, hmr, herr, hpc, hpc2, hpq⟩

end ProductModels

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

abbrev infiniteCube := ℕ → unitInterval
abbrev infiniteCubeMeasure : Measure infiniteCube :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

lemma infinite_coordinate_mp (i : ℕ) :
    MeasurePreserving (fun ω : infiniteCube => ω i) infiniteCubeMeasure volume :=
  ⟨measurable_pi_apply i, Measure.infinitePi_map_eval _ i⟩

lemma finite_coordinates_mp {ι : Type uIota} [Fintype ι] (c : ι → ℕ) (hc : Function.Injective c) :
    MeasurePreserving (fun ω : infiniteCube => fun i => ω (c i)) infiniteCubeMeasure (cubeMeasure ι) := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj hc, Measure.infinitePi_eq_pi]

/-- The number of copies can be chosen arbitrarily late, after the whole-ball parameters.
    This is Mathlib's L1 strong law, applied to the exact Pareto multiplier. -/
lemma multiplier_averages {p h : ℝ} (hp : 1 < p) (hh : 0 < h) :
    ∃ n : ℕ, 0 < n ∧
      (∫ v : cube (Fin n), |(n : ℝ)⁻¹ * (∑ j, multiplier p (v j)) - 1|
        ∂cubeMeasure (Fin n)) < h := by
  let X : ℕ → infiniteCube → ℝ := fun i ω => multiplier p (ω i)
  have hXi (i : ℕ) : Integrable (X i) infiniteCubeMeasure :=
    ((infinite_coordinate_mp i).integrable_comp (integrable_multiplier hp).aestronglyMeasurable).mpr
      (integrable_multiplier hp)
  have hdist (i : ℕ) : IdentDistrib (X i) (multiplier p) infiniteCubeMeasure volume :=
    mp_ident (infinite_coordinate_mp i) (measurable_multiplier p)
  have hind : iIndepFun X infiniteCubeMeasure := iIndepFun_infinitePi (fun _ => measurable_multiplier p)
  have hmean : (∫ ω, X 0 ω ∂infiniteCubeMeasure) = 1 :=
    (hdist 0).integral_eq.trans (integral_multiplier hp)
  have hLLN := strong_law_Lp (by norm_num : (1 : ℝ≥0∞) ≤ 1) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    X (memLp_one_iff_integrable.mpr (hXi 0)) (fun i j hij => hind.indepFun hij) (fun i => (hdist i).trans (hdist 0).symm)
  have hreal := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp hLLN
  simp only [ENNReal.toReal_zero, hmean, smul_eq_mul] at hreal
  have havg (n : ℕ) : Integrable
      (fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - 1) infiniteCubeMeasure :=
    ((integrable_finsetSum _ (fun i _ => hXi i)).const_mul _).sub (integrable_const 1)
  have hevent : ∀ᶠ n : ℕ in atTop,
      (∫ ω, |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - 1| ∂infiniteCubeMeasure) < h := by
    convert hreal.eventually (Iio_mem_nhds hh) using 1
    ext n
    simp only [Function.comp_apply]
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm (havg n).aestronglyMeasurable]
    rfl
  obtain ⟨n, hn, hn'⟩ := ((eventually_gt_atTop 0).and hevent).exists
  refine ⟨n, hn, ?_⟩
  have hmp := finite_coordinates_mp (fun j : Fin n => (j : ℕ)) Fin.val_injective
  have heq := mp_integral hmp
    (((integrable_rowSum hp (fun _ : Fin n => 1)).const_mul (n : ℝ)⁻¹).sub (integrable_const 1)).abs.aestronglyMeasurable
  simp only [rowSum, one_mul, Pi.sub_apply] at heq
  rw [← heq]
  have hefin (ω : infiniteCube) : (∑ j : Fin n, multiplier p (ω j)) =
      ∑ i ∈ Finset.range n, X i ω := Fin.sum_univ_eq_sum_range (fun j => multiplier p (ω j)) n
  simp only [hefin]
  exact hn'

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW

instance kwMeasure_probability : IsProbabilityMeasure kwMeasure := by
  unfold kwMeasure
  infer_instance

abbrev KWL1 := Lp ℝ 1 kwMeasure

/-- Coordinate restriction induces an actual L1 linear isometry. -/
def coordinatesL1 {ι : Type uIota} [Fintype ι] (c : ι → ℕ) (hc : Function.Injective c) :
    Lp ℝ 1 (cubeMeasure ι) →ₗᵢ[ℝ] KWL1 :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (finite_coordinates_mp c hc)

/-- A common finite family of coordinates determines the whole subspace. -/
def FiniteCoordinates (G : Submodule ℝ KWL1) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℕ) (hc : Function.Injective c),
    G ≤ (coordinatesL1 c hc).toLinearMap.range

lemma extend_coordinates {ι : Type uIota} {κ : Type uKappa} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (hc : Function.Injective c) :
    ∃ d : ι ⊕ κ → ℕ, Function.Injective d ∧ ∀ i, d (Sum.inl i) = c i := by
  classical
  let N := (Finset.univ.sup c) + 1
  have hbound (i : ι) : c i < N := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  let d : ι ⊕ κ → ℕ := Sum.elim c (fun j => N + (Fintype.equivFin κ j).val)
  refine ⟨d, ?_, fun i => rfl⟩
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (hc hij)
    | inr j =>
      have := hbound i
      change c i = N + (Fintype.equivFin κ j).val at hij
      omega
  | inr i =>
    cases j with
    | inl j =>
      have := hbound j
      change N + (Fintype.equivFin κ i).val = c j at hij
      omega
    | inr j =>
      apply congrArg Sum.inr
      apply (Fintype.equivFin κ).injective
      apply Fin.ext
      exact Nat.add_left_cancel hij

lemma curry_mp {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι] :
    MeasurePreserving (fun v : cube (κ × ι) => fun k j => v (k,j))
      (cubeMeasure (κ × ι)) (arrayMeasure κ ι) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.infinitePi_map_curry (fun _ : κ => fun _ : ι => (volume : Measure unitInterval))
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_curry] at h
  exact h

def splitCoordinates {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota}
    (v : cube (β ⊕ (κ × ι))) : cube β × (κ → cube ι) :=
  (fun b => v (Sum.inl b), fun k j => v (Sum.inr (k,j)))

lemma splitCoordinates_mp {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota}
    [Fintype β] [Fintype κ] [Fintype ι] :
    MeasurePreserving (splitCoordinates : cube (β ⊕ (κ × ι)) → cube β × (κ → cube ι))
      (cubeMeasure (β ⊕ (κ × ι))) ((cubeMeasure β).prod (arrayMeasure κ ι)) := by
  exact ((MeasurePreserving.id (cubeMeasure β)).prod curry_mp).comp
    (measurePreserving_sumPiEquivProdPi (fun _ : β ⊕ (κ × ι) => (volume : Measure unitInterval)))

section L1Tools
variable {B : Type uB} {R : Type uR} [MeasurableSpace B] [MeasurableSpace R]
  {μ : Measure B} {ν : Measure R}

def integrableL1 (f : B → ℝ) (hf : Integrable f μ) : Lp ℝ 1 μ :=
  (memLp_one_iff_integrable.mpr hf).toLp f

lemma integrableL1_ae (f : B → ℝ) (hf : Integrable f μ) :
    integrableL1 f hf =ᵐ[μ] f := MemLp.coeFn_toLp _

lemma L1_norm_of_ae (f : Lp ℝ 1 μ) {g : B → ℝ} (hg : f =ᵐ[μ] g) :
    ‖f‖ = ∫ b, |g b| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hg.fun_comp abs)

lemma norm_integrableL1 (f : B → ℝ) (hf : Integrable f μ) :
    ‖integrableL1 f hf‖ = ∫ b, |f b| ∂μ := L1_norm_of_ae _ (integrableL1_ae _ _)

lemma coeFn_L1_sum {ι : Type uIota} (s : Finset ι) (f : ι → Lp ℝ 1 μ) :
    (∑ i ∈ s, f i : Lp ℝ 1 μ) =ᵐ[μ] fun b => ∑ i ∈ s, f i b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 1 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with b hb hb'
    simpa only [Pi.add_apply, hb'] using hb

lemma coeFn_L1_smul_sum {ι : Type uIota} [Fintype ι] (a : ι → ℝ) (f : ι → Lp ℝ 1 μ) :
    (∑ i, a i • f i : Lp ℝ 1 μ) =ᵐ[μ] fun b => ∑ i, a i * f i b := by
  filter_upwards [coeFn_L1_sum Finset.univ (fun i => a i • f i),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (f i))] with b hb hbi
  rw [hb]
  exact Finset.sum_congr rfl (fun i _ => by simpa using hbi i)

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def oldL1 : Lp ℝ 1 μ →ₗᵢ[ℝ] Lp ℝ 1 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

omit [IsProbabilityMeasure μ] in
lemma oldL1_ae [IsProbabilityMeasure μ] (f : Lp ℝ 1 μ) :
    oldL1 (ν := ν) f =ᵐ[μ.prod ν] fun z => f z.1 := Lp.coeFn_compMeasurePreserving f _

end L1Tools
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW
section ProductAtoms
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

def arrayMultiplier (p : ℝ) (k : κ) (j : ι) (v : κ → cube ι) : ℝ := multiplier p (v k j)

lemma array_coordinate_mp (k : κ) (j : ι) :
    MeasurePreserving (fun v : κ → cube ι => v k j) (arrayMeasure κ ι) volume :=
  (measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) j).comp
    (measurePreserving_eval (fun _ : κ => cubeMeasure ι) k)

lemma integrable_arrayMultiplier {p : ℝ} (hp : 1 < p) (k : κ) (j : ι) :
    Integrable (arrayMultiplier p k j) (arrayMeasure κ ι) :=
  ((array_coordinate_mp k j).integrable_comp (integrable_multiplier hp).aestronglyMeasurable).mpr
    (integrable_multiplier hp)

lemma integral_arrayMultiplier {p : ℝ} (hp : 1 < p) (k : κ) (j : ι) :
    (∫ v, arrayMultiplier p k j v ∂arrayMeasure κ ι) = 1 :=
  (mp_integral (array_coordinate_mp k j) (integrable_multiplier hp).aestronglyMeasurable).trans
    (integral_multiplier hp)

omit [Fintype κ] [Fintype ι] in
lemma measurable_arrayMultiplier [Fintype κ] [Fintype ι] (p : ℝ) (k : κ) (j : ι) :
    Measurable (arrayMultiplier p k j) :=
  (measurable_multiplier p).comp (by fun_prop)

lemma arrayMultiplier_tail {p c : ℝ} (hp : 1 < p) (hc : scale p ≤ c) (k : κ) (j : ι) :
    (arrayMeasure κ ι).real {v | c < arrayMultiplier p k j v} = (scale p / c)^p := by
  have he := (array_coordinate_mp k j).measureReal_preimage
    (measurableSet_lt (measurable_const (a := c)) (measurable_multiplier p)).nullMeasurableSet
  exact he.trans (multiplier_tail hp hc)

def atomL1 {p : ℝ} (hp : 1 < p) (u : Lp ℝ 1 μ) (k : κ) (j : ι) :
    Lp ℝ 1 (μ.prod (arrayMeasure κ ι)) :=
  integrableL1 (fun z => u z.1 * arrayMultiplier p k j z.2)
    ((L1.integrable_coeFn u).mul_prod (integrable_arrayMultiplier hp k j))

omit [IsProbabilityMeasure μ] in
lemma atomL1_ae [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : Lp ℝ 1 μ) (k : κ) (j : ι) :
    atomL1 hp u k j =ᵐ[μ.prod (arrayMeasure κ ι)]
      fun z => u z.1 * arrayMultiplier p k j z.2 := integrableL1_ae _ _

lemma norm_atomL1 {p : ℝ} (hp : 1 < p) (u : Lp ℝ 1 μ) (k : κ) (j : ι) :
    ‖atomL1 hp u k j‖ = ‖u‖ := by
  rw [L1_norm_of_ae _ (atomL1_ae hp u k j)]
  simp only [abs_mul, arrayMultiplier, abs_of_nonneg (multiplier_nonneg hp _) ]
  change (∫ z : B × (κ → cube ι), |u z.1| * arrayMultiplier p k j z.2 ∂μ.prod (arrayMeasure κ ι)) = ‖u‖
  rw [integral_prod_mul (fun b => |u b|) (arrayMultiplier p k j), integral_arrayMultiplier hp,
    mul_one, L1.norm_eq_integral_norm]
  rfl

lemma atomL1_near_additive {p c h : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (hpc : scale p ≤ c)
    (herr : 2 * ((scale p / c)^p + c) < h) {w u : Lp ℝ 1 μ}
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (k : κ) (j : ι) :
    2 - h ≤ ‖oldL1 w + atomL1 hp u k j‖ := by
  have hn := near_additivity (L1.integrable_coeFn w) (L1.integrable_coeFn u)
    (integrable_arrayMultiplier hp k j) (measurable_arrayMultiplier p k j)
    (fun _ => multiplier_nonneg hp _) (by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm w).symm.trans hw)
    (by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm u).symm.trans hu)
    (integral_arrayMultiplier hp k j) hc
  rw [arrayMultiplier_tail hp hpc k j] at hn
  have hae : (oldL1 w + atomL1 hp u k j : Lp ℝ 1 (μ.prod (arrayMeasure κ ι))) =ᵐ[μ.prod (arrayMeasure κ ι)]
      fun z => w z.1 + u z.1 * arrayMultiplier p k j z.2 := by
    filter_upwards [Lp.coeFn_add (oldL1 w) (atomL1 hp u k j), oldL1_ae w, atomL1_ae hp u k j] with z h₁ h₂ h₃
    simpa only [Pi.add_apply, h₂, h₃] using h₁
  rw [L1_norm_of_ae _ hae]
  linarith

end ProductAtoms

section LinearCombinations
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

def matrixCombination (v : κ → ι → X) : (κ → ι → ℝ) →ₗ[ℝ] X where
  toFun a := ∑ k, ∑ j, a k j • v k j
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

end LinearCombinations

section ProductOperator
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

def productOperator {p : ℝ} (hp : 1 < p) (u : κ → Lp ℝ 1 μ) :
    (Lp ℝ 1 μ × (κ → ι → ℝ)) →ₗ[ℝ] Lp ℝ 1 (μ.prod (arrayMeasure κ ι)) :=
  oldL1.toLinearMap.coprod (matrixCombination (fun k j => atomL1 hp (u k) k j))

lemma productOperator_ae {p : ℝ} (hp : 1 < p) (x : Lp ℝ 1 μ) (u : κ → Lp ℝ 1 μ) (a : κ → ι → ℝ) :
    productOperator hp u (x,a) =ᵐ[μ.prod (arrayMeasure κ ι)]
      enlargedFunction p x (fun k => (u k : B → ℝ)) a := by
  have hrows (k : κ) : (∑ j, a k j • atomL1 hp (u k) k j : Lp ℝ 1 (μ.prod (arrayMeasure κ ι)))
      =ᵐ[μ.prod (arrayMeasure κ ι)] fun z => u k z.1 * rowSum p (a k) (z.2 k) := by
    filter_upwards [coeFn_L1_smul_sum (a k) (fun j => atomL1 hp (u k) k j),
      ae_all_iff.mpr (fun j => atomL1_ae hp (u k) k j)] with z hz hzj
    rw [hz]
    simp only [rowSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hzj j]
    dsimp [arrayMultiplier]
    ring
  filter_upwards [Lp.coeFn_add (oldL1 x) (matrixCombination (fun k j => atomL1 hp (u k) k j) a),
    oldL1_ae x, coeFn_L1_sum Finset.univ (fun k => ∑ j, a k j • atomL1 hp (u k) k j),
    ae_all_iff.mpr hrows] with z hz hzx hzs hzrow
  change (oldL1 x + matrixCombination (fun k j => atomL1 hp (u k) k j) a : Lp ℝ 1 (μ.prod (arrayMeasure κ ι))) z = _
  rw [hz]
  simp only [Pi.add_apply, hzx, enlargedFunction]
  congr 1
  change (∑ k, ∑ j, a k j • atomL1 hp (u k) k j : Lp ℝ 1 (μ.prod (arrayMeasure κ ι))) z = _
  rw [hzs]
  exact Finset.sum_congr rfl (fun k _ => hzrow k)

omit [IsProbabilityMeasure μ] in
lemma productOperator_zero_coeff [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : κ → Lp ℝ 1 μ) (x : Lp ℝ 1 μ) :
    productOperator (ι := ι) hp u (x,0) = oldL1 x := by
  simp [productOperator, matrixCombination]

end ProductOperator
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli
section MeasureMetric
variable {B : Type uB} {R : Type uR} [MeasurableSpace B] [MeasurableSpace R]
  {μ : Measure B} {ν : Measure R} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
lemma measureDistance_le_of_tail [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) {h : ℝ} (hh : 0 < h)
    (ht : μ.real {b | h < |f b - g b|} < h) : measureDistance μ f g ≤ h :=
  csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨hh, ht⟩

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma measureDistance_pullback [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : B → R} (hF : MeasurePreserving F μ ν) (f g : Lp ℝ 1 ν) :
    measureDistance μ (Lp.compMeasurePreserving F hF f) (Lp.compMeasurePreserving F hF g) =
      measureDistance ν f g := by
  have ht (h : ℝ) :
      μ.real {b | h < |Lp.compMeasurePreserving F hF f b - Lp.compMeasurePreserving F hF g b|} =
      ν.real {r | h < |f r - g r|} := by
    have hae : {b | h < |Lp.compMeasurePreserving F hF f b - Lp.compMeasurePreserving F hF g b|} =ᵐ[μ]
        F ⁻¹' {r | h < |f r - g r|} := by
      filter_upwards [Lp.coeFn_compMeasurePreserving f hF, Lp.coeFn_compMeasurePreserving g hF] with b hb hb'
      change (h < |Lp.compMeasurePreserving F hF f b - Lp.compMeasurePreserving F hF g b|) =
          (h < |f (F b) - g (F b)|)
      simp only [hb, hb', Function.comp_apply]
    rw [measureReal_congr hae]
    exact hF.measureReal_preimage (measurableSet_lt measurable_const
      ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable).abs).nullMeasurableSet
  simp only [measureDistance, ht]

end MeasureMetric
end ExactModuli

namespace ExactModuli.KW
section ProductAverages
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} [Fintype κ]

lemma atoms_average_norm {p : ℝ} (hp : 1 < p) {n : ℕ} (u : Lp ℝ 1 μ) (hu : ‖u‖ = 1) (k : κ) :
    ‖oldL1 u - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp u k j‖ =
      ∫ v : cube (Fin n), |(n : ℝ)⁻¹ * (∑ j, multiplier p (v j)) - 1| ∂cubeMeasure (Fin n) := by
  let A : (κ → cube (Fin n)) → ℝ := fun v => 1 - (n : ℝ)⁻¹ * ∑ j, multiplier p (v k j)
  have hae : (oldL1 u - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp u k j : Lp ℝ 1 (μ.prod (arrayMeasure κ (Fin n))))
      =ᵐ[μ.prod (arrayMeasure κ (Fin n))] fun z => u z.1 * A z.2 := by
    filter_upwards [Lp.coeFn_sub (oldL1 u) ((n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp u k j),
      oldL1_ae u, Lp.coeFn_smul (n : ℝ)⁻¹ (∑ j : Fin n, atomL1 hp u k j),
      coeFn_L1_sum Finset.univ (fun j : Fin n => atomL1 hp u k j),
      ae_all_iff.mpr (fun j : Fin n => atomL1_ae hp u k j)] with z hz hu' hs hsum hj
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu', hs, hsum] at hz
    rw [hz]
    simp only [hj, arrayMultiplier, ← Finset.mul_sum, A]
    ring
  rw [L1_norm_of_ae _ hae]
  simp only [abs_mul]
  rw [integral_prod_mul (fun b => |u b|) (fun v => |A v|)]
  have hun : (∫ b, |u b| ∂μ) = 1 := (L1.norm_eq_integral_norm u).symm.trans hu
  rw [hun, one_mul]
  have heq := mp_integral (measurePreserving_eval (fun _ : κ => cubeMeasure (Fin n)) k)
    (((integrable_rowSum hp (fun _ : Fin n => 1)).const_mul (n : ℝ)⁻¹).sub (integrable_const 1)).abs.aestronglyMeasurable
  simp only [rowSum, one_mul, Pi.sub_apply] at heq
  dsimp [A]
  simp_rw [abs_sub_comm (1 : ℝ)]
  exact heq

end ProductAverages

section Normalize
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B}

def normalizeL1 (f : Lp ℝ 1 μ) : Lp ℝ 1 μ := (max 1 ‖f‖)⁻¹ • f

lemma normalizeL1_mem (G : Submodule ℝ (Lp ℝ 1 μ)) {f : Lp ℝ 1 μ} (hf : f ∈ G) :
    normalizeL1 f ∈ G := G.smul_mem _ hf

lemma normalizeL1_norm (f : Lp ℝ 1 μ) : ‖normalizeL1 f‖ ≤ 1 := by
  have hm : 0 < max 1 ‖f‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [normalizeL1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  rw [← div_eq_inv_mul, div_le_one hm]
  exact le_max_right _ _

lemma normalizeL1_ae (f : Lp ℝ 1 μ) {g : B → ℝ} (hfg : f =ᵐ[μ] g) :
    normalizeL1 f =ᵐ[μ] normalizeFunction μ g := by
  have hn := L1_norm_of_ae f hfg
  filter_upwards [Lp.coeFn_smul (max 1 ‖f‖)⁻¹ f, hfg] with b hb hb'
  dsimp [normalizeL1]
  rw [hb]
  simp only [Pi.smul_apply, smul_eq_mul, hb', hn, normalizeFunction, div_eq_mul_inv, mul_comm]

lemma oldCombination_ae (x : Lp ℝ 1 μ) {κ : Type uKappa} [Fintype κ]
    (u : κ → Lp ℝ 1 μ) (c : κ → ℝ) :
    (x + ∑ k, c k • u k : Lp ℝ 1 μ) =ᵐ[μ] oldCombination x (fun k => (u k : B → ℝ)) c := by
  filter_upwards [Lp.coeFn_add x (∑ k, c k • u k), coeFn_L1_smul_sum c u] with b hb hb'
  simpa only [Pi.add_apply, hb', oldCombination] using hb

end Normalize

section WholeBallL1
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

lemma productOperator_control {p r q h : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    (hr : 0 < r) (hq : 0 < q) (hh : 0 < h)
    (hmq : (Fintype.card κ : ℝ) * q < 1)
    (herr : (Fintype.card κ : ℝ) * q + h⁻¹ *
      (2 * (Fintype.card κ : ℝ) * r + (1 - (Fintype.card κ : ℝ) * q)⁻¹ - 1) < h)
    (hpq : 10 * (108 * scale p / r)^p < q)
    (G : Submodule ℝ (Lp ℝ 1 μ)) (x : G) (u : κ → G) (hu : ∀ k, ‖u k‖ = 1)
    (a : κ → ι → ℝ) (hg : ‖productOperator hp (fun k => (u k : Lp ℝ 1 μ)) (x,a)‖ ≤ 1) :
    ∃ ψ : G, ‖ψ‖ ≤ 1 ∧
      measureDistance (μ.prod (arrayMeasure κ ι))
        (productOperator hp (fun k => (u k : Lp ℝ 1 μ)) (x,a)) (oldL1 (ψ : Lp ℝ 1 μ)) ≤ h := by
  classical
  have he := productOperator_ae hp (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) a
  have hgn : (∫ z, |enlargedFunction p (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) a z|
      ∂μ.prod (arrayMeasure κ ι)) ≤ 1 := (L1_norm_of_ae _ he) ▸ hg
  obtain ⟨c, hc, htail⟩ := whole_ball_approximation hp hpmax hr hq hh hmq herr hpq
    (L1.integrable_coeFn (x : Lp ℝ 1 μ)) (fun k => L1.integrable_coeFn (u k : Lp ℝ 1 μ))
    (fun k => by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm (u k : Lp ℝ 1 μ)).symm.trans (hu k)) a hgn
  let ψ : G := ⟨normalizeL1 ((x : Lp ℝ 1 μ) + ∑ k, c k • (u k : Lp ℝ 1 μ)),
    normalizeL1_mem G (G.add_mem x.property (G.sum_mem (fun k _ => G.smul_mem _ (u k).property)))⟩
  refine ⟨ψ, normalizeL1_norm _, measureDistance_le_of_tail _ _ hh ?_⟩
  have hψ : (ψ : Lp ℝ 1 μ) =ᵐ[μ]
      normalizeFunction μ (oldCombination (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) c) :=
    normalizeL1_ae _ (oldCombination_ae _ _ _)
  have hψpull := (measurePreserving_fst (μ := μ) (ν := arrayMeasure κ ι)).quasiMeasurePreserving.ae_eq_comp hψ
  have hevent : {z | h < |productOperator hp (fun k => (u k : Lp ℝ 1 μ)) (x,a) z - oldL1 (ν := arrayMeasure κ ι) (ψ : Lp ℝ 1 μ) z|}
      =ᵐ[μ.prod (arrayMeasure κ ι)] {z | h < |enlargedFunction p (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) a z -
        normalizeFunction μ (oldCombination (x : Lp ℝ 1 μ) (fun k => (u k : Lp ℝ 1 μ)) c) z.1|} := by
    filter_upwards [he, oldL1_ae (ν := arrayMeasure κ ι) (ψ : Lp ℝ 1 μ), hψpull] with z hz hz' hψz
    simp only [Function.comp_apply] at hψz
    change (h < _) = (h < _)
    rw [hz, hz', hψz]
  rw [measureReal_congr hevent]
  exact htail

end WholeBallL1
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli.KW
section CoordinateJoining
variable {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota} [Fintype β] [Fintype κ] [Fintype ι]

def joinedCoordinates (d : β ⊕ (κ × ι) → ℕ) (ω : KWOmega) : cube β × (κ → cube ι) :=
  splitCoordinates (fun i => ω (d i))

lemma joinedCoordinates_mp (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    MeasurePreserving (joinedCoordinates d) kwMeasure ((cubeMeasure β).prod (arrayMeasure κ ι)) :=
  splitCoordinates_mp.comp (finite_coordinates_mp d hd)

def joinedL1 (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    Lp ℝ 1 ((cubeMeasure β).prod (arrayMeasure κ ι)) →ₗᵢ[ℝ] KWL1 :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (joinedCoordinates_mp d hd)

lemma joinedL1_range (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    (joinedL1 d hd).toLinearMap.range ≤ (coordinatesL1 d hd).toLinearMap.range := by
  rintro g ⟨f, rfl⟩
  refine ⟨Lp.compMeasurePreserving splitCoordinates splitCoordinates_mp f, ?_⟩
  exact (Lp.compMeasurePreserving_comp_apply f splitCoordinates_mp (finite_coordinates_mp d hd)).symm

lemma joinedL1_old (c : β → ℕ) (hc : Function.Injective c)
    (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) (hdc : ∀ b, d (Sum.inl b) = c b)
    (f : Lp ℝ 1 (cubeMeasure β)) :
    joinedL1 d hd (oldL1 f) = coordinatesL1 c hc f := by
  change (Lp.compMeasurePreserving (joinedCoordinates d) (joinedCoordinates_mp d hd))
      ((Lp.compMeasurePreserving Prod.fst measurePreserving_fst) f) = _
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_fst (joinedCoordinates_mp d hd)]
  have he : Prod.fst ∘ joinedCoordinates d = (fun ω : KWOmega => fun b => ω (c b)) := by
    funext ω b
    simp only [Function.comp_apply, joinedCoordinates, splitCoordinates, hdc]
  simp only [he]
  rfl

lemma joinedL1_measureDistance (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d)
    (f g : Lp ℝ 1 ((cubeMeasure β).prod (arrayMeasure κ ι))) :
    measureDistance kwMeasure (joinedL1 d hd f) (joinedL1 d hd g) =
      measureDistance ((cubeMeasure β).prod (arrayMeasure κ ι)) f g :=
  measureDistance_pullback (joinedCoordinates_mp d hd) f g

end CoordinateJoining

section Model
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma finiteDimensional_model (L : X →ₗᵢ[ℝ] Y) (G : Submodule ℝ Y) [FiniteDimensional ℝ G] :
    FiniteDimensional ℝ (G.comap L.toLinearMap) := by
  let T : G.comap L.toLinearMap →ₗ[ℝ] G :=
    (L.toLinearMap.domRestrict (G.comap L.toLinearMap)).codRestrict G (fun x => x.property)
  apply FiniteDimensional.of_injective T
  intro x y h
  apply Subtype.ext
  apply L.injective
  exact congrArg Subtype.val h

end Model

section ProductBasis
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

omit [IsProbabilityMeasure μ] in
lemma productOperator_single [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : κ → Lp ℝ 1 μ) (k : κ) (j : ι) :
    ∃ a : κ → ι → ℝ, productOperator hp u (0,a) = atomL1 hp (u k) k j := by
  classical
  refine ⟨fun k' j' => if k' = k then (if j' = j then 1 else 0) else 0, ?_⟩
  simp [productOperator, matrixCombination, ite_smul]

end ProductBasis
end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

structure EnlargementData {κ : Type} [Fintype κ] (G : Submodule ℝ KWL1)
    (u : κ → KWL1) (h : ℝ) where
  space : Submodule ℝ KWL1
  contains : G ≤ space
  finiteDimensional : FiniteDimensional ℝ space
  finiteCoordinates : FiniteCoordinates space
  copies : ℕ
  copies_pos : 0 < copies
  vectors : κ → Fin copies → KWL1
  vectors_mem : ∀ k j, vectors k j ∈ space
  vectors_unit : ∀ k j, ‖vectors k j‖ = 1
  additive : ∀ w ∈ G, ‖w‖ = 1 → ∀ k j, 2 - h ≤ ‖w + vectors k j‖
  averages : ∀ k, ‖u k - (copies : ℝ)⁻¹ • ∑ j, vectors k j‖ ≤ h
  wholeBall : ∀ g ∈ space, ‖g‖ ≤ 1 →
    ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h

/-- The complete quantitative Kadets–Werner finite-dimensional enlargement. -/
theorem finite_dimensional_enlargement {κ : Type} [Fintype κ] [Nonempty κ]
    (G : Submodule ℝ KWL1) [FiniteDimensional ℝ G] (_hG : G ≠ ⊥)
    (hcoords : FiniteCoordinates G) (u : κ → G) (hu : ∀ k, ‖u k‖ = 1)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    Nonempty (EnlargementData G (fun k => (u k : KWL1)) h) := by
  classical
  obtain ⟨β, hβ, c, hc, hGrange⟩ := hcoords
  let : Fintype β := hβ
  let M : Submodule ℝ (Lp ℝ 1 (cubeMeasure β)) := G.comap (coordinatesL1 c hc).toLinearMap
  let : FiniteDimensional ℝ M := finiteDimensional_model (coordinatesL1 c hc) G
  choose u₀ hu₀ using (fun k => hGrange (u k).property)
  change ∀ k, coordinatesL1 c hc (u₀ k) = (u k : KWL1) at hu₀
  let um : κ → M := fun k => ⟨u₀ k, by
    change coordinatesL1 c hc (u₀ k) ∈ G
    rw [hu₀ k]
    exact (u k).property⟩
  have hum (k : κ) : ‖um k‖ = 1 := by
    change ‖u₀ k‖ = 1
    rw [← (coordinatesL1 c hc).norm_map (u₀ k), hu₀ k]
    exact hu k
  have hcard : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  obtain ⟨C, r, q, p, hC, hCh, hr, hq, hp, hpmax, hmq, herr, hpC, hpCh, hpq⟩ :=
    enlargement_parameters hcard hh hh1
  obtain ⟨n, hn, havg⟩ := multiplier_averages hp hh
  obtain ⟨d, hd, hdc⟩ := extend_coordinates (κ := κ × Fin n) c hc
  let J := joinedL1 d hd
  let A : (M × (κ → Fin n → ℝ)) →ₗ[ℝ] (Lp ℝ 1 (cubeMeasure β) × (κ → Fin n → ℝ)) :=
    M.subtype.prodMap LinearMap.id
  let T : (M × (κ → Fin n → ℝ)) →ₗ[ℝ] KWL1 :=
    J.toLinearMap.comp ((productOperator hp u₀).comp A)
  let G' : Submodule ℝ KWL1 := T.range
  have hcontain : G ≤ G' := by
    intro x hx
    obtain ⟨x₀, hx₀⟩ := hGrange hx
    change coordinatesL1 c hc x₀ = x at hx₀
    have hxM : x₀ ∈ M := by change coordinatesL1 c hc x₀ ∈ G; rw [hx₀]; exact hx
    refine ⟨(⟨x₀, hxM⟩, 0), ?_⟩
    change J (productOperator hp u₀ (x₀,0)) = x
    rw [productOperator_zero_coeff]
    exact (joinedL1_old c hc d hd hdc x₀).trans hx₀
  have hfinite : FiniteDimensional ℝ G' := by dsimp [G']; infer_instance
  have hcoords' : FiniteCoordinates G' := by
    refine ⟨β ⊕ (κ × Fin n), inferInstance, d, hd, ?_⟩
    rintro g ⟨z, rfl⟩
    apply joinedL1_range d hd
    exact ⟨productOperator hp u₀ ((z.1 : Lp ℝ 1 (cubeMeasure β)),z.2), rfl⟩
  let v : κ → Fin n → KWL1 := fun k j => J (atomL1 hp (u₀ k) k j)
  have hvMem (k : κ) (j : Fin n) : v k j ∈ G' := by
    obtain ⟨a, ha⟩ := productOperator_single hp u₀ k j
    refine ⟨(0,a), ?_⟩
    change J (productOperator hp u₀ (0,a)) = J (atomL1 hp (u₀ k) k j)
    rw [ha]
  have hvUnit (k : κ) (j : Fin n) : ‖v k j‖ = 1 := by
    dsimp [v]
    rw [J.norm_map, norm_atomL1]
    exact hum k
  have hvAdd : ∀ w ∈ G, ‖w‖ = 1 → ∀ k j, 2 - h ≤ ‖w + v k j‖ := by
    intro w hw hwunit k j
    obtain ⟨w₀, hw₀⟩ := hGrange hw
    change coordinatesL1 c hc w₀ = w at hw₀
    have hwn : ‖w₀‖ = 1 := by rw [← (coordinatesL1 c hc).norm_map w₀, hw₀, hwunit]
    calc
      2 - h ≤ ‖oldL1 w₀ + atomL1 hp (u₀ k) k j‖ :=
        atomL1_near_additive hp hC.le hpC.le hpCh hwn (hum k) k j
      _ = ‖J (oldL1 w₀ + atomL1 hp (u₀ k) k j)‖ := (J.norm_map _).symm
      _ = ‖w + v k j‖ := by
        rw [map_add]
        change ‖joinedL1 d hd (oldL1 w₀) + v k j‖ = _
        rw [joinedL1_old c hc d hd hdc w₀, hw₀]
  have hvAvg (k : κ) : ‖(u k : KWL1) - (n : ℝ)⁻¹ • ∑ j, v k j‖ ≤ h := by
    have huJ : J (oldL1 (u₀ k)) = (u k : KWL1) := (joinedL1_old c hc d hd hdc _).trans (hu₀ k)
    calc
      _ = ‖J (oldL1 (u₀ k) - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp (u₀ k) k j)‖ := by
        rw [map_sub, map_smul, map_sum, huJ]
      _ = ‖oldL1 (u₀ k) - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp (u₀ k) k j‖ := J.norm_map _
      _ = ∫ v : cube (Fin n), |(n : ℝ)⁻¹ * (∑ j, multiplier p (v j)) - 1|
          ∂cubeMeasure (Fin n) := atoms_average_norm hp (u₀ k) (hum k) k
      _ ≤ h := havg.le
  have hvControl : ∀ g ∈ G', ‖g‖ ≤ 1 →
      ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h := by
    rintro g ⟨⟨x,a⟩, rfl⟩ hg
    have hPg : ‖productOperator hp (fun k => (um k : Lp ℝ 1 (cubeMeasure β))) (x,a)‖ ≤ 1 := by
      change ‖J (productOperator hp u₀ ((x : Lp ℝ 1 (cubeMeasure β)),a))‖ ≤ 1 at hg
      rw [J.norm_map] at hg
      exact hg
    obtain ⟨ψ, hψnorm, hψdist⟩ := productOperator_control hp hpmax hr hq hh hmq herr hpq M x um hum a hPg
    refine ⟨coordinatesL1 c hc (ψ : Lp ℝ 1 (cubeMeasure β)), ψ.property, ?_, ?_⟩
    · rw [(coordinatesL1 c hc).norm_map]
      exact hψnorm
    · change measureDistance kwMeasure (J (productOperator hp u₀ ((x : Lp ℝ 1 (cubeMeasure β)),a)))
        (coordinatesL1 c hc (ψ : Lp ℝ 1 (cubeMeasure β))) ≤ h
      rw [← joinedL1_old c hc d hd hdc (ψ : Lp ℝ 1 (cubeMeasure β))]
      exact (joinedL1_measureDistance d hd _ _).symm ▸ hψdist
  exact ⟨⟨G', hcontain, hfinite, hcoords', n, hn, v, hvMem, hvUnit, hvAdd, hvAvg, hvControl⟩⟩

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measureDistance_self (f : Lp ℝ 1 μ) : measureDistance μ f f = 0 := by
  apply le_antisymm _ (measureDistance_nonneg f f)
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [zero_add] using (measureDistance_le_of_tail f f hε (by simpa [not_lt_of_ge hε.le] using hε))

omit [IsProbabilityMeasure μ] in
lemma measureDistance_symm [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) :
    measureDistance μ f g = measureDistance μ g f := by
  simp only [measureDistance, abs_sub_comm (f _) (g _)]

lemma measureDistance_triangle (f g k : Lp ℝ 1 μ) :
    measureDistance μ f k ≤ measureDistance μ f g + measureDistance μ g k := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let a := measureDistance μ f g + ε / 2
  let b := measureDistance μ g k + ε / 2
  have ha : 0 < a := by dsimp [a]; linarith [measureDistance_nonneg f g]
  have hb : 0 < b := by dsimp [b]; linarith [measureDistance_nonneg g k]
  have hfa := tail_lt_of_measureDistance_lt f g (show measureDistance μ f g < a by dsimp [a]; linarith)
  have hgb := tail_lt_of_measureDistance_lt g k (show measureDistance μ g k < b by dsimp [b]; linarith)
  have hsub : {ω | a + b < |f ω - k ω|} ⊆
      {ω | a < |f ω - g ω|} ∪ {ω | b < |g ω - k ω|} := by
    intro ω hω
    by_contra hh
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hh
    have ht : |f ω - k ω| ≤ |f ω - g ω| + |g ω - k ω| := abs_sub_le _ _ _
    exact (not_lt_of_ge (ht.trans (add_le_add hh.1 hh.2))) hω
  have htail : μ.real {ω | a + b < |f ω - k ω|} < a + b :=
    (measureReal_mono hsub).trans_lt ((measureReal_union_le _ _).trans_lt (add_lt_add hfa hgb))
  have hh := measureDistance_le_of_tail f k (add_pos ha hb) htail
  dsimp [a,b] at hh
  linarith

/-- Markov's norm-to-measure estimate, in a form avoiding an unnecessary metric instance. -/
lemma measureDistance_le_of_norm_sub_lt_sq (f g : Lp ℝ 1 μ) {ε : ℝ} (hε : 0 < ε)
    (hfg : ‖f - g‖ < ε ^ 2) : measureDistance μ f g ≤ ε := by
  have hi : Integrable (fun ω => |f ω - g ω|) μ :=
    ((L1.integrable_coeFn f).sub (L1.integrable_coeFn g)).abs
  have hint : (∫ ω, |f ω - g ω| ∂μ) = ‖f - g‖ := by
    exact (KW.L1_norm_of_ae (f-g) (Lp.coeFn_sub f g)).symm
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun ω => abs_nonneg (f ω-g ω))) hi ε
  rw [hint] at hm
  have hle : μ.real {ω | ε ≤ |f ω - g ω|} < ε := by nlinarith
  apply measureDistance_le_of_tail f g hε
  exact (measureReal_mono (μ := μ) (show {ω | ε < |f ω-g ω|} ⊆ {ω | ε ≤ |f ω-g ω|} from by
    intro ω hω
    change ε < |f ω-g ω| at hω
    change ε ≤ |f ω-g ω|
    exact hω.le)).trans_lt hle

end ExactModuli

namespace ExactModuli.KW

lemma normalizeL1_approx {B : Type uB} [MeasurableSpace B] {μ : Measure B}
    (x y : Lp ℝ 1 μ) (hx : ‖x‖ ≤ 1) :
    ‖x - normalizeL1 y‖ ≤ 2 * ‖x-y‖ := by
  by_cases hy : ‖y‖ ≤ 1
  · simp only [normalizeL1, max_eq_left hy, inv_one, one_smul]
    linarith [norm_nonneg (x-y)]
  have hyp : 0 < ‖y‖ := by linarith
  have hinv : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hyp).mpr (le_of_not_ge hy)
  have hcost : ‖y - normalizeL1 y‖ = ‖y‖ - 1 := by
    calc
      _ = ‖(1 - ‖y‖⁻¹) • y‖ := by
        rw [normalizeL1, max_eq_right (le_of_not_ge hy), sub_smul, one_smul]
      _ = (1 - ‖y‖⁻¹) * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hinv)]
      _ = ‖y‖ - 1 := by rw [sub_mul, one_mul, inv_mul_cancel₀ hyp.ne']
  calc
    ‖x - normalizeL1 y‖ ≤ ‖x-y‖ + ‖y-normalizeL1 y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x-y‖ := by
      rw [hcost]
      have ht := norm_sub_norm_le y x
      rw [norm_sub_rev] at ht
      linarith

lemma sphere_normalize_approx {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x y : X) (hx : ‖x‖ = 1) (hy : y ≠ 0) :
    ‖x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x-y‖ := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hcost : ‖y - ‖y‖⁻¹ • y‖ = |‖y‖ - 1| := by
    calc
      _ = ‖(1 - ‖y‖⁻¹) • y‖ := by rw [sub_smul, one_smul]
      _ = |(1 - ‖y‖⁻¹) * ‖y‖| := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg y)]
      _ = |‖y‖ - 1| := by rw [sub_mul, one_mul, inv_mul_cancel₀ hyp.ne']
  calc
    ‖x - ‖y‖⁻¹ • y‖ ≤ ‖x-y‖ + ‖y-‖y‖⁻¹ • y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x-y‖ := by
      rw [hcost, ← hx]
      have ht := abs_norm_sub_norm_le y x
      rw [norm_sub_rev] at ht
      linarith

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

/-- One finite-coordinate stage of the construction. -/
structure ConstructionStage where
  space : Submodule ℝ KWL1
  finiteDimensional : FiniteDimensional ℝ space
  finiteCoordinates : FiniteCoordinates space
  nonzero : space ≠ ⊥

/-- All estimates propagated from one stage to the next. -/
structure StepEstimates (G H : Submodule ℝ KWL1) (h : ℝ) : Prop where
  proper : G < H
  wholeBall : ∀ g ∈ H, ‖g‖ ≤ 1 →
    ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h
  averages : ∀ u ∈ G, ‖u‖ = 1 → ∃ n : ℕ, 0 < n ∧ ∃ v : Fin n → KWL1,
    (∀ j, v j ∈ H ∧ ‖v j‖ = 1) ∧
    ‖u - (n : ℝ)⁻¹ • ∑ j, v j‖ ≤ 2 * h ∧
    ∀ w ∈ G, ‖w‖ = 1 → ∀ j, 2 - h ≤ ‖w + v j‖

lemma stage_enlargement (G : ConstructionStage) {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    ∃ H : ConstructionStage, StepEstimates G.space H.space h := by
  classical
  let : FiniteDimensional ℝ G.space := G.finiteDimensional
  let : Nontrivial G.space := Submodule.nontrivial_iff_ne_bot.mpr G.nonzero
  obtain ⟨t, hts, htfin, hcover⟩ := (isCompact_sphere (0 : G.space) 1).finite_cover_balls hh
  have hex : ∃ z : G.space, ‖z‖ = 1 := exists_norm_eq G.space (by norm_num : (0:ℝ) ≤ 1)
  have htne : t.Nonempty := by
    obtain ⟨z,hz⟩ := hex
    have hzcover := hcover (show z ∈ Metric.sphere (0:G.space) 1 by simpa using hz)
    simp only [Set.mem_iUnion] at hzcover
    obtain ⟨b,hb,_⟩ := hzcover
    exact ⟨b,hb⟩
  let : Fintype t := htfin.fintype
  let : Nonempty t := htne.to_subtype
  let u : t → G.space := fun z => z.val
  have hu (z : t) : ‖u z‖ = 1 := by simpa [u] using hts z.property
  obtain ⟨A⟩ := finite_dimensional_enlargement G.space G.nonzero G.finiteCoordinates u hu hh hh1
  have hproper : G.space < A.space := by
    apply lt_of_le_of_ne A.contains
    intro heq
    let k : t := Classical.choice inferInstance
    let j : Fin A.copies := ⟨0,A.copies_pos⟩
    have hv : A.vectors k j ∈ G.space := by simpa only [heq] using A.vectors_mem k j
    have hhfar := A.additive (-A.vectors k j) (G.space.neg_mem hv)
      (by simpa using A.vectors_unit k j) k j
    simp only [neg_add_cancel, norm_zero] at hhfar
    linarith
  let H : ConstructionStage := ⟨A.space, A.finiteDimensional, A.finiteCoordinates,
    ne_bot_of_gt hproper⟩
  refine ⟨H, ⟨hproper, A.wholeBall, ?_⟩⟩
  intro x hx hxu
  have hxcover := hcover (show (⟨x,hx⟩ : G.space) ∈ Metric.sphere 0 1 by simpa using hxu)
  simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hxcover
  obtain ⟨b,hb,hxb⟩ := hxcover
  let k : t := ⟨b,hb⟩
  refine ⟨A.copies, A.copies_pos, A.vectors k, fun j => ⟨A.vectors_mem k j, A.vectors_unit k j⟩, ?_, ?_⟩
  · have ha := A.averages k
    have hxb' : ‖x - (u k : KWL1)‖ < h := hxb
    calc
      _ ≤ ‖x - (u k : KWL1)‖ + ‖(u k : KWL1) - (A.copies : ℝ)⁻¹ • ∑ j, A.vectors k j‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * h := by linarith
  · exact fun w hw hw1 j => A.additive w hw hw1 k j

/-- The constant-one vector, so the initial stage is literally span{1}. -/
def oneVector : KWL1 := Lp.const 1 kwMeasure (1:ℝ)

lemma oneVector_norm : ‖oneVector‖ = 1 := by
  simp [oneVector, Lp.norm_const]

lemma oneVector_finiteCoordinates : FiniteCoordinates (Submodule.span ℝ {oneVector}) := by
  let c : Fin 0 → ℕ := Fin.elim0
  have hc : Function.Injective c := fun i => Fin.elim0 i
  refine ⟨Fin 0, inferInstance, c, hc, Submodule.span_le.mpr ?_⟩
  intro x hx
  have hx' : x = oneVector := Set.mem_singleton_iff.mp hx
  subst x
  refine ⟨Lp.const 1 (cubeMeasure (Fin 0)) (1:ℝ), ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.const 1 (cubeMeasure (Fin 0)) (1:ℝ))
      (finite_coordinates_mp c hc),
    (finite_coordinates_mp c hc).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_const 1 (cubeMeasure (Fin 0)) (1:ℝ)),
    Lp.coeFn_const 1 kwMeasure (1:ℝ)] with ω hω hω' hω''
  exact hω.trans (hω'.trans hω''.symm)

def initialStage : ConstructionStage where
  space := Submodule.span ℝ {oneVector}
  finiteDimensional := inferInstance
  finiteCoordinates := oneVector_finiteCoordinates
  nonzero := by
    intro heq
    have hmem : oneVector ∈ (⊥ : Submodule ℝ KWL1) := heq ▸ Submodule.subset_span (Set.mem_singleton oneVector)
    have hz : oneVector = 0 := hmem
    have hn := oneVector_norm
    rw [hz, norm_zero] at hn
    norm_num at hn

def stageError (n : ℕ) : ℝ := (1/2)^(n+1)

lemma stageError_pos (n : ℕ) : 0 < stageError n := by unfold stageError; positivity

lemma stageError_lt_one (n : ℕ) : stageError n < 1 := by
  unfold stageError
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

lemma stageError_succ (n : ℕ) : 2 * stageError (n+1) = stageError n := by
  simp only [stageError, pow_succ]
  ring

def nextStage (n : ℕ) (G : ConstructionStage) : ConstructionStage :=
  Classical.choose (stage_enlargement G (stageError_pos n) (stageError_lt_one n))

lemma nextStage_estimates (n : ℕ) (G : ConstructionStage) :
    StepEstimates G.space (nextStage n G).space (stageError n) :=
  Classical.choose_spec (stage_enlargement G (stageError_pos n) (stageError_lt_one n))

def stages : ℕ → ConstructionStage
  | 0 => initialStage
  | n+1 => nextStage n (stages n)

def stageSpace (n : ℕ) : Submodule ℝ KWL1 := (stages n).space

instance stageSpace_finite (n : ℕ) : FiniteDimensional ℝ (stageSpace n) :=
  (stages n).finiteDimensional

lemma stageSpace_nonzero (n : ℕ) : stageSpace n ≠ ⊥ := (stages n).nonzero

lemma step_estimates (n : ℕ) : StepEstimates (stageSpace n) (stageSpace (n+1)) (stageError n) :=
  nextStage_estimates n (stages n)

lemma stageSpace_strictMono : StrictMono stageSpace :=
  strictMono_nat_of_lt_succ (fun n => (step_estimates n).proper)

lemma stageSpace_mono : Monotone stageSpace := stageSpace_strictMono.monotone

def unionSpace : Submodule ℝ KWL1 := ⨆ n, stageSpace n

def constructedSpace : Submodule ℝ KWL1 := unionSpace.topologicalClosure

lemma stageSpace_le_constructed (n : ℕ) : stageSpace n ≤ constructedSpace :=
  (le_iSup stageSpace n).trans unionSpace.le_topologicalClosure

lemma constructedSpace_closed : IsClosed (constructedSpace : Set KWL1) :=
  unionSpace.isClosed_topologicalClosure

lemma constructedSpace_nonzero : constructedSpace ≠ ⊥ :=
  ne_bot_of_le_ne_bot (stageSpace_nonzero 0) (stageSpace_le_constructed 0)

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

lemma constructedSpace_infiniteDimensional : ¬ FiniteDimensional ℝ constructedSpace := by
  intro hfinite
  let : FiniteDimensional ℝ constructedSpace := hfinite
  have hstrict : StrictMono (fun n => Module.finrank ℝ (stageSpace n)) := by
    intro n m hnm
    exact Submodule.finrank_lt_finrank_of_lt (stageSpace_strictMono hnm)
  have hle := hstrict.id_le (Module.finrank ℝ constructedSpace + 1)
  have hbound := Submodule.finrank_mono (stageSpace_le_constructed (Module.finrank ℝ constructedSpace + 1))
  change Module.finrank ℝ constructedSpace + 1 ≤ Module.finrank ℝ (stageSpace (Module.finrank ℝ constructedSpace + 1)) at hle
  omega

lemma constructed_union_approx {x : KWL1} (hx : x ∈ constructedSpace)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y ∈ stageSpace n, ‖x-y‖ < ε := by
  have hx' : x ∈ closure (unionSpace : Set KWL1) := hx
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx' ε hε
  obtain ⟨n,hn⟩ := (Submodule.mem_iSup_of_directed stageSpace stageSpace_mono.directed_le).mp hy
  exact ⟨max n N, le_max_right _ _, y, stageSpace_mono (le_max_left _ _) hn, by simpa [dist_eq_norm] using hxy⟩

lemma constructed_ball_approx {x : KWL1} (hx : x ∈ constructedSpace) (hxn : ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y ∈ stageSpace n, ‖y‖ ≤ 1 ∧ ‖x-y‖ < ε := by
  obtain ⟨n,hn,y,hy,hxy⟩ := constructed_union_approx hx (half_pos hε) N
  refine ⟨n,hn,normalizeL1 y,normalizeL1_mem _ hy,normalizeL1_norm _,?_⟩
  exact (normalizeL1_approx x y hxn).trans_lt (by linarith)

lemma constructed_sphere_approx {x : KWL1} (hx : x ∈ constructedSpace) (hxn : ‖x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y ∈ stageSpace n, ‖y‖ = 1 ∧ ‖x-y‖ < ε := by
  obtain ⟨n,hn,y,hy,hxy⟩ := constructed_union_approx hx (lt_min (half_pos hε) (by norm_num : (0:ℝ)<1/2)) N
  have hy0 : y ≠ 0 := by
    intro hy0
    rw [hy0, sub_zero, hxn] at hxy
    have hh := hxy.trans_le (min_le_right _ _)
    norm_num at hh
  refine ⟨n,hn,‖y‖⁻¹ • y,(stageSpace n).smul_mem _ hy,norm_smul_inv_norm hy0,?_⟩
  exact (sphere_normalize_approx x y hxn hy0).trans_lt (by linarith [hxy.trans_le (min_le_left _ _)])

lemma stageError_tendsto : Tendsto stageError atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_const (1/2:ℝ)
  change Tendsto (fun n : ℕ => (1/2:ℝ)^(n+1)) atTop (𝓝 0)
  simpa only [zero_mul, pow_succ] using h

lemma stageError_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, stageError n < ε :=
  eventually_atTop.mp (stageError_tendsto.eventually_lt_const hε)

/-- The exact telescoping finite-stage error; the remaining tail equals 2 h_b. -/
lemma stage_ball_control (b a : ℕ) (hba : b ≤ a) :
    ∀ g ∈ stageSpace a, ‖g‖ ≤ 1 → ∃ ψ ∈ stageSpace b, ‖ψ‖ ≤ 1 ∧
      measureDistance kwMeasure g ψ ≤ 2 * stageError b - 2 * stageError a := by
  induction a, hba using Nat.le_induction with
  | base =>
    intro g hg hgn
    exact ⟨g,hg,hgn,by simp [measureDistance_self]⟩
  | succ a hba ih =>
    intro g hg hgn
    obtain ⟨y,hy,hyn,hgy⟩ := (step_estimates a).wholeBall g hg hgn
    obtain ⟨ψ,hψ,hψn,hyψ⟩ := ih y hy hyn
    refine ⟨ψ,hψ,hψn,?_⟩
    have ht := measureDistance_triangle g y ψ
    rw [stageError_succ]
    linarith

lemma stage_ball_control_uniform (b a : ℕ) (g : KWL1) (hg : g ∈ stageSpace a) (hgn : ‖g‖ ≤ 1) :
    ∃ ψ ∈ stageSpace b, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ 2 * stageError b := by
  by_cases hba : b ≤ a
  · obtain ⟨ψ,hψ,hψn,hgψ⟩ := stage_ball_control b a hba g hg hgn
    exact ⟨ψ,hψ,hψn,hgψ.trans (by linarith [stageError_pos a])⟩
  · exact ⟨g,stageSpace_mono (le_of_not_ge hba) hg,hgn,by rw [measureDistance_self]; exact (mul_pos (by norm_num) (stageError_pos b)).le⟩

lemma constructed_ball_stage_control (b : ℕ) (x : KWL1) (hx : x ∈ constructedSpace) (hxn : ‖x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ ψ ∈ stageSpace b, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure x ψ ≤ 2 * stageError b + η := by
  obtain ⟨a,ha,y,hy,hyn,hxy⟩ := constructed_ball_approx hx hxn (sq_pos_of_pos hη) 0
  obtain ⟨ψ,hψ,hψn,hyψ⟩ := stage_ball_control_uniform b a y hy hyn
  refine ⟨ψ,hψ,hψn,?_⟩
  have hd := measureDistance_le_of_norm_sub_lt_sq x y hη hxy
  have ht := measureDistance_triangle x y ψ
  linarith

lemma constructedSpace_measurePrecompact : MeasurePrecompactBall kwMeasure constructedSpace := by
  classical
  intro ε hε
  obtain ⟨b,hb⟩ := stageError_eventually_small (show 0 < ε/8 by positivity)
  have hb' := hb b le_rfl
  obtain ⟨t,hts,htfin,hcover⟩ := (isCompact_closedBall (0 : stageSpace b) 1).finite_cover_balls
    (sq_pos_of_pos (show 0 < ε/4 by positivity))
  refine ⟨htfin.toFinset.image (fun z : stageSpace b => (z : KWL1)), ?_⟩
  intro x hxn
  obtain ⟨ψ,hψ,hψn,hxψ⟩ := constructed_ball_stage_control b x x.property hxn (show 0 < ε/4 by positivity)
  have hcov := hcover (show (⟨ψ,hψ⟩ : stageSpace b) ∈ Metric.closedBall 0 1 by simpa using hψn)
  simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hcov
  obtain ⟨z,hz,hψz⟩ := hcov
  refine ⟨(z : KWL1),Finset.mem_image.mpr ⟨z,htfin.mem_toFinset.mpr hz,rfl⟩,?_⟩
  have hd := measureDistance_le_of_norm_sub_lt_sq ψ (z : KWL1) (show 0 < ε/4 by positivity) hψz
  have ht := measureDistance_triangle (x : KWL1) ψ (z : KWL1)
  linarith

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


namespace ExactModuli

lemma unit_in_nonempty_slice {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
    (ell : X →L[ℝ] ℝ) (α : ℝ) (hs : ∃ x : X, ‖x‖ ≤ 1 ∧ α < ell x) :
    ∃ u : X, ‖u‖ = 1 ∧ α < ell u := by
  obtain ⟨x,hxn,hα⟩ := hs
  by_cases hxpos : 0 < ell x
  · have hx0 : x ≠ 0 := by intro hx; simp [hx] at hxpos
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    refine ⟨‖x‖⁻¹ • x,norm_smul_inv_norm hx0,?_⟩
    rw [map_smul, smul_eq_mul]
    exact hα.trans_le (le_mul_of_one_le_left hxpos.le ((one_le_inv₀ hnx).mpr hxn))
  · have hα0 : α < 0 := hα.trans_le (le_of_not_gt hxpos)
    obtain ⟨u,hu⟩ := exists_norm_eq X (by norm_num : (0:ℝ)≤1)
    by_cases hu0 : 0 ≤ ell u
    · exact ⟨u,hu,hα0.trans_le hu0⟩
    · exact ⟨-u,by simpa using hu,by simpa using hα0.trans (neg_pos.mpr (lt_of_not_ge hu0))⟩

end ExactModuli

namespace ExactModuli.KW

lemma constructedSpace_unitSlice : UnitSliceProperty constructedSpace := by
  classical
  let : Nontrivial constructedSpace := Submodule.nontrivial_iff_ne_bot.mpr constructedSpace_nonzero
  intro w hwn ell α hs ρ hρ
  obtain ⟨u,hun,hα⟩ := unit_in_nonempty_slice ell α hs
  let η : ℝ := min (ρ/4) ((ell u - α) / (8 * (‖ell‖ + 1)))
  have hden : 0 < 8 * (‖ell‖ + 1) := by positivity
  have hη : 0 < η := lt_min (by positivity) (div_pos (sub_pos.mpr hα) hden)
  have hηρ : η ≤ ρ/4 := min_le_left _ _
  have hηell : η * (8 * (‖ell‖ + 1)) ≤ ell u - α :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨N,hN⟩ := stageError_eventually_small hη
  obtain ⟨nu,hnu,us,hus,husn,huus⟩ := constructed_sphere_approx u.property hun hη N
  obtain ⟨nw,hnw,ws,hws,hwsn,hwws⟩ := constructed_sphere_approx w.property hwn hη N
  let b := max nu nw
  have husb : us ∈ stageSpace b := stageSpace_mono (le_max_left _ _) hus
  have hwsb : ws ∈ stageSpace b := stageSpace_mono (le_max_right _ _) hws
  have hb : stageError b < η := hN b (hnu.trans (le_max_left _ _))
  obtain ⟨n,hn,v,hv,husv,hadd⟩ := (step_estimates b).averages us husb husn
  let V : Fin n → constructedSpace := fun j => ⟨v j,stageSpace_le_constructed (b+1) (hv j).1⟩
  let a : constructedSpace := (n : ℝ)⁻¹ • ∑ j, V j
  have haVal : (a : KWL1) = (n : ℝ)⁻¹ • ∑ j, v j := by simp [a,V]
  have hua : ‖u-a‖ ≤ η + 2 * stageError b := by
    change ‖(u : KWL1) - (a : KWL1)‖ ≤ _
    rw [haVal]
    exact (norm_sub_le_norm_sub_add_norm_sub _ us _).trans (add_le_add huus.le husv)
  have hdiff : |ell u - ell a| ≤ ‖ell‖ * (η + 2 * stageError b) := by
    calc
      _ = ‖ell (u-a)‖ := by rw [map_sub, Real.norm_eq_abs]
      _ ≤ ‖ell‖ * ‖u-a‖ := ell.le_opNorm _
      _ ≤ ‖ell‖ * (η + 2 * stageError b) := mul_le_mul_of_nonneg_left hua (norm_nonneg ell)
  have herror : ‖ell‖ * (η + 2 * stageError b) < ell u - α := by
    have he := mul_le_mul_of_nonneg_left (show η + 2 * stageError b ≤ 3*η by linarith) (norm_nonneg ell)
    have hLη : 0 ≤ ‖ell‖ * η := mul_nonneg (norm_nonneg ell) hη.le
    nlinarith
  have haα : α < ell a := by linarith [le_abs_self (ell u - ell a)]
  have hnℝ : (0:ℝ) < n := by exact_mod_cast hn
  have haell : ell a = (∑ j, ell (V j)) / (n:ℝ) := by
    simp [a, map_sum, div_eq_mul_inv, mul_comm]
  have hj : ∃ j, α < ell (V j) := by
    by_contra hh
    push Not at hh
    have hsum : (∑ j, ell (V j)) ≤ (n:ℝ) * α := by
      calc
        _ ≤ ∑ j : Fin n, α := Finset.sum_le_sum (fun j _ => hh j)
        _ = (n:ℝ) * α := by simp
    have hale : ell a ≤ α := by
      rw [haell]
      exact (div_le_iff₀ hnℝ).mpr (by simpa only [mul_comm] using hsum)
    linarith
  obtain ⟨j,hj⟩ := hj
  refine ⟨V j,(hv j).2,hj,?_⟩
  have hnear := hadd ws hwsb hwsn j
  have htri : ‖ws + v j‖ ≤ ‖(w:KWL1)-ws‖ + ‖(w:KWL1)+v j‖ := by
    have ht := norm_add_le (ws-(w:KWL1)) ((w:KWL1)+v j)
    have heq : ws-(w:KWL1)+((w:KWL1)+v j) = ws+v j := by abel
    rw [heq, norm_sub_rev] at ht
    exact ht
  change 2 - ρ ≤ ‖(w:KWL1)+v j‖
  linarith

lemma constructedSpace_daugavet : Daugavet constructedSpace := by
  let : Nontrivial constructedSpace := Submodule.nontrivial_iff_ne_bot.mpr constructedSpace_nonzero
  exact unitSlice_daugavet constructedSpace_unitSlice

end ExactModuli.KW

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli

theorem kadets_werner_existence_oai :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E := by
  exact ⟨KW.constructedSpace, KW.constructedSpace_closed, KW.constructedSpace_infiniteDimensional,
    KW.constructedSpace_measurePrecompact, KW.constructedSpace_unitSlice, KW.constructedSpace_daugavet⟩

end ExactModuli

namespace ExactModuli

theorem exact_example :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
        H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
        D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
      (∀ t : ℝ, 0 < t →
        averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
        oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
      (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  let := KW.kwMeasure_probability
  obtain ⟨E,hclosed,hdim,hcompact,hslice,hdaugavet⟩ := kadets_werner_existence_oai
  obtain ⟨hpoint,hcenters,hrenorm⟩ := exact_main kwMeasure E hclosed hdim hcompact hdaugavet
  exact ⟨E,hclosed,hdim,hcompact,hslice,hdaugavet,hpoint,hcenters,hrenorm⟩

end ExactModuli

end

end OAI
end
end

theorem solution : type_of% @OAI.ExactModuli.kadets_werner_existence_oai := @OAI.ExactModuli.kadets_werner_existence_oai
