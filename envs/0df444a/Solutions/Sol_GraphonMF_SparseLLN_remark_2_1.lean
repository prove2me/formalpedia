-- Prove2me | solution 1 for GraphonMF.SparseLLN.remark_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:35:44.370695+00:00
-- url     : https://prove2.me/submissions/1f96139b-b827-432b-8e9a-4038f840c016

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting
import Definitions.Def_GraphonMF_SparseLLN_Setting
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SSGM
open Function

section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

lemma amul {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]

lemma lemG {k : α → ℝ} (hkm : Measurable k) (hk : Integrable k μ) {d : ℝ}
    (hd : ∀ S : Set α, MeasurableSet S → |∫ x in S, k x ∂μ| ≤ d)
    (a : α → ℝ) (hab : ∀ x, |a x| ≤ 1) (ham : AEStronglyMeasurable a μ) :
    |∫ x, a x * k x ∂μ| ≤ 2 * d := by
  have h1 : |∫ x, a x * k x ∂μ| ≤ ∫ x, |k x| ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) (fun x => a x * k x)
    refine this.trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hk.norm
      (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    nlinarith [hab x, abs_nonneg (k x)]
  have hSp : MeasurableSet {x | 0 < k x} := measurableSet_lt measurable_const hkm
  have hSn : MeasurableSet {x | k x < 0} := measurableSet_lt hkm measurable_const
  have h2 : ∀ x, |k x| = ({x | 0 < k x}.indicator k x) - ({x | k x < 0}.indicator k x) := by
    intro x
    rcases lt_trichotomy (k x) 0 with h | h | h
    · simp [Set.indicator, h, abs_of_neg h, not_lt.mpr h.le]
    · simp [Set.indicator, h]
    · simp [Set.indicator, h, abs_of_pos h, not_lt.mpr h.le]
  have h3 : ∫ x, |k x| ∂μ = (∫ x in {x | 0 < k x}, k x ∂μ) - ∫ x in {x | k x < 0}, k x ∂μ := by
    simp_rw [h2]
    rw [integral_sub (hk.indicator hSp) (hk.indicator hSn), integral_indicator hSp,
      integral_indicator hSn]
  have := hd _ hSp
  have := hd _ hSn
  rw [h3] at h1
  have e1 := le_abs_self (∫ x in {x | 0 < k x}, k x ∂μ)
  have e2 := neg_abs_le (∫ x in {x | k x < 0}, k x ∂μ)
  linarith

lemma boundedInt {F : α → ℝ} (hm : Measurable F) (hb : ∀ x, |F x| ≤ 1) : Integrable F μ :=
  Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun x => by simpa using hb x)

lemma swapS (F : α → α → ℝ) (hF : Measurable (uncurry F)) (hb : ∀ u v, |F u v| ≤ 1)
    (S : Set α) :
    ∫ u, ∫ v in S, F u v ∂μ ∂μ = ∫ v in S, ∫ u, F u v ∂μ ∂μ := by
  have hint : Integrable (uncurry F) (μ.prod (μ.restrict S)) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (Eventually.of_forall fun p => by simpa [uncurry] using hb p.1 p.2)
  exact integral_integral_swap hint

lemma meas_right (F : α → α → ℝ) (hF : Measurable (uncurry F)) (S : Set α) :
    Measurable fun u => ∫ v in S, F u v ∂μ := by
  have := (hF.stronglyMeasurable.integral_prod_right' (ν := μ.restrict S))
  exact this.measurable

lemma meas_left (F : α → α → ℝ) (hF : Measurable (uncurry F)) :
    Measurable fun v => ∫ u, F u v ∂μ := by
  have := (hF.stronglyMeasurable.integral_prod_left' (μ := μ))
  exact this.measurable

lemma abs_int_le {F : α → ℝ} (hb : ∀ x, |F x| ≤ 1) (S : Set α) :
    |∫ x in S, F x ∂μ| ≤ 1 := by
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := S) (f := F) (C := 1)
    (measure_lt_top μ S) (fun x _ => by simpa using hb x)
  have h2 : μ.real S ≤ 1 := by
    have := prob_le_one (μ := μ) (s := S)
    simpa [Measure.real] using ENNReal.toReal_mono (by simp) this
  simpa using this.trans (by simpa using h2)

lemma core (W : α → α → ℝ) (hW : Measurable (uncurry W)) (hb : ∀ u v, |W u v| ≤ 1) (c : ℝ)
    (hc : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      |∫ u in A, ∫ v in B, W u v ∂μ ∂μ| ≤ c)
    (g : α → ℝ) (hg : Measurable g) (hgb : ∀ v, |g v| ≤ 1) :
    ∫ u, |∫ v, W u v * g v ∂μ| ∂μ ≤ 4 * c := by
  set h : α → ℝ := fun u => ∫ v, W u v * g v ∂μ with hh
  have hWg : Measurable (uncurry fun u v => W u v * g v) :=
    hW.mul (hg.comp measurable_snd)
  have hm : Measurable h := by
    have := (hWg.stronglyMeasurable.integral_prod_right' (ν := μ))
    exact this.measurable
  set s : α → ℝ := fun u => if 0 ≤ h u then 1 else -1 with hs
  have hsm : Measurable s := Measurable.ite (measurableSet_le measurable_const hm)
    measurable_const measurable_const
  have hsb : ∀ u, |s u| ≤ 1 := by intro u; simp only [hs]; split_ifs <;> simp
  have hsh : ∀ u, |h u| = s u * h u := by
    intro u; simp only [hs]; split_ifs with H
    · simp [abs_of_nonneg H]
    · have := not_le.mp H; simp [abs_of_neg this]
  -- step 1
  have step1 : ∫ u, |h u| ∂μ = ∫ v, g v * (∫ u, s u * W u v ∂μ) ∂μ := by
    have e1 : ∫ u, |h u| ∂μ = ∫ u, ∫ v, s u * (W u v * g v) ∂μ ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show |h u| = ∫ v, s u * (W u v * g v) ∂μ
      rw [hsh u]
      exact (integral_const_mul (s u) (fun v => W u v * g v)).symm
    have hF : Measurable (uncurry fun u v => s u * (W u v * g v)) :=
      (hsm.comp measurable_fst).mul hWg
    have e2 := swapS (μ := μ) (fun u v => s u * (W u v * g v)) hF
      (fun u v => amul (hsb u) (amul (hb u v) (hgb v))) Set.univ
    simp only [Measure.restrict_univ] at e2
    rw [e1, e2]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    show ∫ u, s u * (W u v * g v) ∂μ = g v * ∫ u, s u * W u v ∂μ
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    ring
  have hmm : Measurable fun v => ∫ u, s u * W u v ∂μ :=
    meas_left (μ := μ) (fun u v => s u * W u v) ((hsm.comp measurable_fst).mul hW)
  have hmb : ∀ v, |∫ u, s u * W u v ∂μ| ≤ 1 := by
    intro v
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => s u * W u v) (C := 1)
      (Eventually.of_forall fun u => by
        simpa only [Real.norm_eq_abs] using amul (hsb u) (hb u v))
    simpa using this
  have hmi : Integrable (fun v => ∫ u, s u * W u v ∂μ) μ := boundedInt hmm hmb
  have step2 : ∀ S : Set α, MeasurableSet S → |∫ v in S, (∫ u, s u * W u v ∂μ) ∂μ| ≤ 2 * c := by
    intro S hS
    have hF : Measurable (uncurry fun u v => s u * W u v) := (hsm.comp measurable_fst).mul hW
    have e := swapS (μ := μ) (fun u v => s u * W u v) hF
      (fun u v => amul (hsb u) (hb u v)) S
    rw [← e]
    have e3 : ∫ u, ∫ v in S, s u * W u v ∂μ ∂μ = ∫ u, s u * ∫ v in S, W u v ∂μ ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show ∫ v in S, s u * W u v ∂μ = s u * ∫ v in S, W u v ∂μ
      rw [integral_const_mul]
    rw [e3]
    have hkm := meas_right (μ := μ) W hW S
    have hkb : ∀ u, |∫ v in S, W u v ∂μ| ≤ 1 := fun u => abs_int_le (fun v => hb u v) S
    exact lemG hkm (boundedInt hkm hkb) (fun A hA => by
      have := hc A S hA hS
      simpa using this) s hsb hsm.aestronglyMeasurable
  have := lemG (μ := μ) hmm hmi step2 g hgb hg.aestronglyMeasurable
  rw [step1]
  calc _ ≤ |∫ v, g v * (∫ u, s u * W u v ∂μ) ∂μ| := le_abs_self _
    _ ≤ 2 * (2 * c) := this
    _ = 4 * c := by ring
end


variable {α : Type*} [MeasurableSpace α] in
lemma le_cut (φ : Set α → Set α → ℝ) (hφ : ∀ S U, φ S U ≤ 1) (h0 : ∀ S U, 0 ≤ φ S U)
    (S U : Set α) (hS : MeasurableSet S) (hU : MeasurableSet U) :
    φ S U ≤ ⨆ (S : Set α) (U : Set α) (_ : MeasurableSet S ∧ MeasurableSet U), φ S U := by
  have b3 : ∀ S U, (⨆ (_ : MeasurableSet S ∧ MeasurableSet U), φ S U) ≤ 1 :=
    fun S U => Real.iSup_le (fun _ => hφ S U) zero_le_one
  have b2 : ∀ S, (⨆ (U : Set α) (_ : MeasurableSet S ∧ MeasurableSet U), φ S U) ≤ 1 :=
    fun S => Real.iSup_le (fun U => b3 S U) zero_le_one
  have bdd3 : BddAbove (Set.range fun (_ : MeasurableSet S ∧ MeasurableSet U) => φ S U) :=
    ⟨φ S U, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have bdd2 : BddAbove (Set.range fun (U : Set α) =>
      ⨆ (_ : MeasurableSet S ∧ MeasurableSet U), φ S U) :=
    ⟨1, by rintro _ ⟨U, rfl⟩; exact b3 S U⟩
  have bdd1 : BddAbove (Set.range fun (S : Set α) =>
      ⨆ (U : Set α) (_ : MeasurableSet S ∧ MeasurableSet U), φ S U) :=
    ⟨1, by rintro _ ⟨S, rfl⟩; exact b2 S⟩
  refine le_trans ?_ (le_ciSup bdd1 S)
  refine le_trans ?_ (le_ciSup bdd2 U)
  exact le_ciSup bdd3 ⟨hS, hU⟩


open GraphonMF.Stability in
lemma opNorm_le (W : I → I → ℝ) (hW : Measurable (uncurry W)) (hb : ∀ u v, |W u v| ≤ 1) (c : ℝ)
    (hc : ∀ A B : Set I, MeasurableSet A → MeasurableSet B →
      |∫ u in A, ∫ v in B, W u v| ≤ c) : opNorm W ≤ 4 * c := by
  have h0 : 0 ≤ 4 * c := by
    have := hc ∅ ∅ MeasurableSet.empty MeasurableSet.empty
    have := abs_nonneg (∫ u in (∅ : Set I), ∫ v in (∅ : Set I), W u v)
    linarith
  unfold opNorm
  exact Real.iSup_le (fun g => Real.iSup_le (fun hg => core W hW hb c hc g hg.1 hg.2) h0) h0

open GraphonMF.Stability in
lemma opNorm_nonneg' (W : I → I → ℝ) : 0 ≤ opNorm W := by
  unfold opNorm
  exact Real.iSup_nonneg (fun g => Real.iSup_nonneg (fun _ => integral_nonneg fun u => abs_nonneg _))

open GraphonMF.Stability in
lemma diff_meas (G H : I → I → ℝ) (hG : IsGraphon G) (hH : IsGraphon H) :
    Measurable (uncurry fun u v => H u v - G u v) := hH.1.sub hG.1

open GraphonMF.Stability in
lemma diff_bd (G H : I → I → ℝ) (hG : IsGraphon G) (hH : IsGraphon H) (u v : I) :
    |H u v - G u v| ≤ 1 := by
  have h1 := hG.2.2 u v
  have h2 := hH.2.2 u v
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

open GraphonMF.Stability in
lemma iter_eq (W : I → I → ℝ) (hW : Measurable (uncurry W)) (hb : ∀ u v, |W u v| ≤ 1)
    (A B : Set I) :
    ∫ p in A ×ˢ B, W p.1 p.2 = ∫ u in A, ∫ v in B, W u v := by
  rw [Measure.volume_eq_prod]
  exact setIntegral_prod _ ((boundedInt (μ := (volume : Measure I).prod volume)
    (F := fun p : I × I => W p.1 p.2) hW (fun p => hb p.1 p.2)).integrableOn)

open GraphonMF.Stability in
lemma sp_cut (W : I → I → ℝ) (hW : Measurable (uncurry W)) (hb : ∀ u v, |W u v| ≤ 1)
    (A B : Set I) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |∫ u in A, ∫ v in B, W u v| ≤ GraphonMF.SparseLLN.cutNorm W := by
  unfold GraphonMF.SparseLLN.cutNorm
  exact le_cut (fun S U => |∫ u in S, ∫ v in U, W u v|)
    (fun S U => (abs_int_le (μ := (volume : Measure I))
      (F := fun u => ∫ v in U, W u v) (fun u => abs_int_le (fun v => hb u v) U) S))
    (fun S U => abs_nonneg _) A B hA hB

open GraphonMF.Stability in
lemma sp_main (G : I → I → ℝ) (Gs : ℕ → I → I → ℝ)
    (hG : IsGraphon G) (hGs : ∀ n, IsGraphon (Gs n))
    (hcut : Tendsto (fun n => GraphonMF.SparseLLN.cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0)) :
    Tendsto (fun n => opNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => opNorm_nonneg' _) (fun n => ?_)
    (by simpa using hcut.const_mul 4)
  exact opNorm_le _ (diff_meas G _ hG (hGs n)) (diff_bd G _ hG (hGs n)) _
    (fun A B hA hB => sp_cut _ (diff_meas G _ hG (hGs n)) (diff_bd G _ hG (hGs n)) A B hA hB)

end SSGM

theorem solution (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
    (hG : GraphonMF.Stability.IsGraphon G) (hGs : ∀ n, GraphonMF.Stability.IsGraphon (Gs n))
    (hcut : Tendsto (fun n => GraphonMF.SparseLLN.cutNorm (fun u v => Gs n u v - G u v))
      atTop (𝓝 0)) :
    Tendsto (fun n => GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0) :=
  SSGM.sp_main G Gs hG hGs hcut
