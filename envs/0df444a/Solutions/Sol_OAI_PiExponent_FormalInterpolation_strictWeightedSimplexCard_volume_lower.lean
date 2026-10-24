-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:30:45.4209+00:00
-- url     : https://prove2.me/submissions/45fd7459-5e4c-455b-b53a-f0b1c3917e0f

import Mathlib
import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex

open MeasureTheory
open scoped BigOperators Pointwise

namespace PXSc

def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (Finset.univ.sum fun i : Fin n => x i) ≤ c}

lemma image_eq (n : ℕ) (a : ℝ) :
    (fun y : Fin n → ℝ => fun i => a * y i) '' S n 1 = a • S n 1 := by
  rw [← Set.image_smul]; rfl

lemma S_eq_smul (n : ℕ) (c : ℝ) (hc : 0 ≤ c) : S n c = c • S n 1 := by
  ext x
  constructor
  · rintro ⟨h0, hs⟩
    rcases hc.eq_or_lt with rfl | hc'
    · refine ⟨0, ⟨fun i => le_rfl, by simp⟩, ?_⟩
      have hx : ∀ i, x i = 0 := by
        intro i
        have hle : x i ≤ ∑ j, x j :=
          Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
        exact le_antisymm (hle.trans hs) (h0 i)
      funext i; simp [hx i]
    · refine ⟨c⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hc) (h0 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hc']; simpa using hs
      · simp [smul_smul, hc'.ne']
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (h0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      simpa using mul_le_mul_of_nonneg_left hs hc

lemma vol_smul (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S n 1) = ENNReal.ofReal (a ^ n) * volume (S n 1) := by
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg ha n)]


lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := by
  unfold S
  rw [Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const

lemma S_neg (n : ℕ) (c : ℝ) (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h0
  exact lt_of_lt_of_le hc (Finset.sum_nonneg (fun i _ => h0 i))

lemma vol_S (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n) * volume (S n 1) := by
  rw [S_eq_smul n c hc]; exact vol_smul n c hc

end PXSc

namespace PXSl

lemma slice (m : ℕ) (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    volume s = ∫⁻ t, volume {y : Fin m → ℝ | Fin.cons t y ∈ s} := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have hs' : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ⁻¹' s) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurable hs
  rw [← hp.measure_preimage hs.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hs']
  refine lintegral_congr (fun t => ?_)
  congr 1
  ext y
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

end PXSl

namespace PXSV
open PXSc

lemma slice_S (n : ℕ) (t : ℝ) :
    {y : Fin n → ℝ | Fin.cons t y ∈ S (n + 1) 1} =
      (if t ∈ Set.Icc (0:ℝ) 1 then S n (1 - t) else ∅) := by
  ext y
  simp only [S, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · rw [if_pos ht]
    simp only [S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨ht.1, h1⟩, by linarith⟩
  · rw [if_neg ht]
    simp only [Set.mem_empty_iff_false, iff_false, not_and, not_le]
    rintro ⟨h0, h1⟩
    have hs : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => h1 i)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · exact absurd h0 (not_le.2 ht)
    · linarith

lemma integral_pow (n : ℕ) :
    ∫⁻ t in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) = ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ n)]
    simp [integral_pow]
  · exact (continuous_const.sub continuous_id |>.pow n).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_nonneg (by linarith [ht.2]) n

theorem succ (n : ℕ) :
    volume (S (n + 1) 1) = ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) * volume (S n 1) := by
  rw [PXSl.slice n _ (S_meas _ _)]
  simp_rw [slice_S]
  have : ∀ t, volume (if t ∈ Set.Icc (0:ℝ) 1 then S n (1 - t) else ∅)
      = Set.indicator (Set.Icc (0:ℝ) 1) (fun t => ENNReal.ofReal ((1 - t) ^ n) * volume (S n 1)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0:ℝ) 1
    · rw [if_pos ht, Set.indicator_of_mem ht, vol_S n _ (by linarith [ht.2])]
    · rw [if_neg ht, Set.indicator_of_notMem ht]; simp
  simp_rw [this]
  rw [lintegral_indicator measurableSet_Icc, lintegral_mul_const _ (by fun_prop), integral_pow]

end PXSV

namespace PXSV
open PXSc

theorem vol_one (n : ℕ) : volume (S n 1) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  induction n with
  | zero =>
    have : S 0 1 = Set.univ := by
      ext x; simp [S]
    rw [this, volume_pi, Measure.pi_of_empty (x := fun i => (Fin.elim0 i : ℝ))]
    simp
  | succ n ih =>
    rw [succ, ih, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    field_simp

end PXSV

namespace PXDg

lemma image_vol {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (s : Set (Fin m → ℝ)) :
    volume ((fun y : Fin m → ℝ => fun i => y i / w i) '' s)
      = ENNReal.ofReal (∏ i, (w i)⁻¹) * volume s := by
  have hf : (fun y : Fin m → ℝ => fun i => y i / w i)
      = ⇑(Matrix.toLin' (Matrix.diagonal fun i => (w i)⁻¹)) := by
    funext y i
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal, div_eq_inv_mul]
  rw [hf, Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_diagonal,
    abs_of_pos (Finset.prod_pos (fun i _ => inv_pos.2 (hw i)))]

lemma weighted_eq {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (B : ℝ) :
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B}
      = (fun y : Fin m → ℝ => fun i => y i / w i) '' PXSc.S m B := by
  ext x
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨fun i => w i * x i, ⟨fun i => mul_nonneg (hw i).le (h0 i), hs⟩, ?_⟩
    funext i; field_simp [(hw i).ne']
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => div_nonneg (h0 i) (hw i).le, ?_⟩
    have : ∀ i, w i * (y i / w i) = y i := fun i => by field_simp [(hw i).ne']
    simp only [this]; exact hs

end PXDg

theorem PXDg_vol_formula {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B}).toReal =
      B ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  rw [PXDg.weighted_eq w hw B, PXDg.image_vol w hw, PXSc.vol_S m B hB.le, PXSV.vol_one]
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => (inv_pos.2 (hw i)).le)),
    ENNReal.toReal_ofReal (pow_nonneg hB.le m), ENNReal.toReal_ofReal (by positivity),
    Finset.prod_inv_distrib]
  field_simp
namespace PXUB

lemma box_eq {m : ℕ} (a : Fin m → ℕ) :
    {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}
      = Set.univ.pi (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)) := by
  ext x; simp [Set.mem_pi]

lemma box_vol {m : ℕ} (a : Fin m → ℕ) :
    MeasureTheory.volume {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1} = 1 := by
  rw [box_eq, Real.volume_pi_Ico]
  simp

lemma box_meas {m : ℕ} (a : Fin m → ℕ) :
    MeasurableSet {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1} := by
  rw [box_eq]; exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)

lemma box_disj {m : ℕ} (s : Finset (Fin m → ℕ)) :
    (s : Set (Fin m → ℕ)).PairwiseDisjoint
      (fun a => {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) := by
  intro a _ b _ hab
  rw [Function.onFun, Set.disjoint_left]
  intro x hxa hxb
  apply hab
  funext i
  have h1 := hxa i; have h2 := hxb i

  have : (a i : ℝ) < b i + 1 := by linarith [h1.1, h2.2]
  have : (b i : ℝ) < a i + 1 := by linarith [h2.1, h1.2]
  have e1 : a i < b i + 1 := by exact_mod_cast ‹(a i : ℝ) < b i + 1›
  have e2 : b i < a i + 1 := by exact_mod_cast ‹(b i : ℝ) < a i + 1›
  omega

lemma union_vol {m : ℕ} (s : Finset (Fin m → ℕ)) :
    MeasureTheory.volume
      (⋃ a ∈ s, {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) = s.card := by
  rw [MeasureTheory.measure_biUnion_finset (box_disj s) (fun a _ => box_meas a)]
  simp [box_vol]

end PXUB

namespace S105SW
open OAI.PiExponent.FormalInterpolation

noncomputable def F {n : ℕ} (w : Fin n → ℝ) (T : ℝ) : Finset (Fin n → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊T / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) < T)

lemma mem_F {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (T : ℝ) (a : Fin n → ℕ) :
    a ∈ F w T ↔ ∑ i, w i * (a i : ℝ) < T := by
  classical
  unfold F
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
  intro hs i
  have hle : w i * (a i : ℝ) ≤ ∑ j, w j * (a j : ℝ) :=
    Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  have : (a i : ℝ) ≤ T / w i := by rw [le_div_iff₀ (hw i)]; linarith
  have := Nat.le_floor this
  omega

lemma vol_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (T' T : ℝ) (hT : T' < T) :
    MeasureTheory.volume {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) ≤ T'}
      ≤ (F w T).card := by
  classical
  rw [← PXUB.union_vol]
  apply MeasureTheory.measure_mono
  rintro x ⟨h0, hs⟩
  set a : Fin n → ℕ := fun i => ⌊x i⌋₊ with ha
  have hax : ∀ i, (a i : ℝ) ≤ x i := fun i => Nat.floor_le (h0 i)
  have hsa : ∑ i, w i * (a i : ℝ) ≤ ∑ i, w i * x i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hax i) (hw i).le)
  have hmem : a ∈ F w T := (mem_F w hw T a).2 (by linarith)
  simp only [Set.mem_iUnion]
  exact ⟨a, hmem, fun i => ⟨hax i, Nat.lt_floor_add_one (x i)⟩⟩

lemma fin_main {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (T : ℝ) (hT : 0 < T) :
    T ^ n ≤ (n.factorial : ℝ) * (∏ i, w i) * ((F w T).card : ℝ) := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have key : ∀ T', 0 < T' → T' < T → T' ^ n ≤ (n.factorial : ℝ) * (∏ i, w i) * ((F w T).card : ℝ) := by
    intro T' h0 h1
    have h := vol_le w hw T' T h1
    have hv := PXDg_vol_formula w T' hw h0
    have h2 : (MeasureTheory.volume {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) ≤ T'}).toReal
        ≤ (F w T).card := by
      have := ENNReal.toReal_mono (by simp) h
      simpa using this
    rw [hv] at h2
    rw [div_div, div_le_iff₀ (by positivity)] at h2
    linarith
  -- limit T' → T⁻
  have hc : ContinuousAt (fun t : ℝ => t ^ n) T := (continuous_pow n).continuousAt
  have ht : Filter.Tendsto (fun t : ℝ => t ^ n) (nhdsWithin T (Set.Iio T)) (nhds (T ^ n)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht' using key t ht'.1 ht'.2

end S105SW

open OAI.PiExponent OAI.PiExponent.FormalInterpolation in
theorem solution
    {ι : Type*} [Fintype ι] (v : ι → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T) :
    Finite (strictWeightedSimplex v T) ∧
      T ^ Fintype.card ι ≤
        ((Fintype.card ι).factorial : Real) * (∏ i, (v i : Real)) *
          (strictWeightedSimplexCard v T : Real) := by
  classical
  set n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let w : Fin n → ℝ := fun i => (v (e.symm i) : ℝ)
  have hw : ∀ i, 0 < w i := fun i => hv _
  have hsum : ∀ a : ι → ℕ, (∑ i, (v i : ℝ) * (a i : ℝ)) = ∑ i, w i * ((a ∘ e.symm) i : ℝ) := by
    intro a
    exact (Fintype.sum_equiv e _ _ (fun i => by simp [w])).trans rfl
  let E : strictWeightedSimplex v T ≃ {a // a ∈ S105SW.F w T} :=
    { toFun := fun a => ⟨a.1 ∘ e.symm, (S105SW.mem_F w hw T _).2 (by rw [← hsum]; exact a.2)⟩
      invFun := fun a => ⟨a.1 ∘ e, by
        show (∑ i, (v i : ℝ) * ((a.1 ∘ e) i : ℝ)) < T
        rw [hsum]; simpa [Function.comp_def] using (S105SW.mem_F w hw T _).1 a.2⟩
      left_inv := fun a => Subtype.ext (by funext i; simp)
      right_inv := fun a => by ext i; simp }
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  have hcard : strictWeightedSimplexCard v T = (S105SW.F w T).card := by
    unfold strictWeightedSimplexCard
    rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hprod : (∏ i, (v i : ℝ)) = ∏ i, w i :=
    Fintype.prod_equiv e _ _ (fun i => by simp [w])
  rw [hcard, hprod]
  exact S105SW.fin_main w hw T hT
