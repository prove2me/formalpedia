-- Prove2me | solution 1 for MohriFoML.OnlineToBatch.online_to_batch_averaged_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @ShouqiaoWang
-- created : 2026-10-30T12:47:48.383982+00:00
-- url     : https://prove2.me/submissions/6f8961ca-9369-47f5-84e6-a933673e73d4

import Mathlib
import Definitions.Def_MohriFoML_OnlineToBatch_genError
import Definitions.Def_MohriFoML_OnlineToBatch_OnlineAlgorithm
import Definitions.Def_MohriFoML_OnlineToBatch_hypSeq
import Definitions.Def_MohriFoML_OnlineToBatch_avgHyp
import Definitions.Def_MohriFoML_OnlineToBatch_regret
import Theorems.Thm_MohriFoML_OnlineToBatch_avg_genError_le_avg_loss

set_option autoImplicit false
open MeasureTheory MohriFoML.OnlineToBatch

namespace OTCPrivate

lemma measure_gap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (d : ENNReal)
    (h : ∀ ε : ℝ, 0 < ε → μ {x | g x + ε < f x} ≤ d) :
    μ {x | g x < f x} ≤ d := by
  let E : ℕ → Set Ω := fun n => {x | g x + 1 / (n + 1 : ℝ) < f x}
  have hm : Monotone E := by
    intro i j hij x hx
    have hi : (0 : ℝ) < i + 1 := by positivity
    have hij' : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have hdiv := one_div_le_one_div_of_le hi hij'
    dsimp [E] at hx ⊢
    linarith
  have heq : {x | g x < f x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by dsimp [E]; linarith⟩
    · rintro ⟨n, hn⟩
      have hp : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      dsimp [E] at hn
      linarith
  rw [heq, hm.measure_iUnion]
  exact iSup_le fun n => h _ (by positivity)

lemma jensen_risk {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [AddCommGroup E] [Module ℝ E]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (Y' : Set E) (L : E → Y → ℝ) (M : ℝ)
    (hL : ∀ a ∈ Y', ∀ y, 0 ≤ L a y ∧ L a y ≤ M)
    (hconv : ∀ y, ConvexOn ℝ Y' (fun a => L a y))
    (A : OnlineAlgorithm X Y E) (T : ℕ) (hT : 0 < T)
    (S : Fin T → X × Y)
    (hmem : ∀ t x, hypSeq A S t x ∈ Y')
    (hm : ∀ t, Measurable (fun z : X × Y => L (hypSeq A S t z.1) z.2))
    (havg : Measurable (fun z : X × Y => L (avgHyp A S z.1) z.2)) :
    genError D L (avgHyp A S) ≤ (1 / (T : ℝ)) * ∑ t, genError D L (hypSeq A S t) := by
  have hTr : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hw : ∑ _t : Fin T, (1 / (T : ℝ)) = 1 := by simp [hTr]
  have havgmem (x : X) (y : Y) : avgHyp A S x ∈ Y' := by
    simpa only [avgHyp, ← Finset.smul_sum] using
      (hconv y).1.sum_mem (t := Finset.univ) (w := fun _ : Fin T => 1 / (T : ℝ))
        (fun _ _ => by positivity) hw (fun t _ => hmem t x)
  have hpoint (z : X × Y) : L (avgHyp A S z.1) z.2 ≤
      (1 / (T : ℝ)) * ∑ t, L (hypSeq A S t z.1) z.2 := by
    simpa only [avgHyp, ← Finset.smul_sum, smul_eq_mul, ← Finset.mul_sum] using
      (hconv z.2).map_sum_le (t := Finset.univ) (w := fun _ : Fin T => 1 / (T : ℝ))
        (fun _ _ => by positivity) hw (fun t _ => hmem t z.1)
  have hint (t : Fin T) : Integrable (fun z : X × Y => L (hypSeq A S t z.1) z.2) D :=
    Integrable.of_mem_Icc 0 M (hm t).aemeasurable
      (Filter.Eventually.of_forall fun z => hL _ (hmem t z.1) z.2)
  have hiavg : Integrable (fun z : X × Y => L (avgHyp A S z.1) z.2) D :=
    Integrable.of_mem_Icc 0 M havg.aemeasurable
      (Filter.Eventually.of_forall fun z => hL _ (havgmem z.1 z.2) z.2)
  calc
    genError D L (avgHyp A S) ≤ ∫ z, (1 / (T : ℝ)) * ∑ t, L (hypSeq A S t z.1) z.2 ∂D :=
      integral_mono hiavg ((integrable_finset_sum _ fun t _ => hint t).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, integral_finset_sum _ (fun t _ => hint t)]; rfl

lemma fixed_comparator {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (Y' : Set E) (L : E → Y → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hL : ∀ a ∈ Y', ∀ y, 0 ≤ L a y ∧ L a y ≤ M)
    (h : X → E) (hh : ∀ x, h x ∈ Y')
    (hm : Measurable (fun z : X × Y => L (h z.1) z.2))
    (T : ℕ) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin T => D)
      {S | ¬ ((1 / (T : ℝ)) * ∑ t : Fin T, L (h (S t).1) (S t).2 ≤
        genError D L h + M * Real.sqrt (2 * Real.log (1 / δ) / T))} ≤ ENNReal.ofReal δ := by
  let B : OnlineAlgorithm X Y E := fun _ _ => h
  let K : E → Y → ℝ := fun a y => M - L a y
  have hK : ∀ a ∈ Y', ∀ y, 0 ≤ K a y ∧ K a y ≤ M := by
    intro a ha y
    have := hL a ha y
    dsimp [K]
    constructor <;> linarith
  have hBm (t : ℕ) : Measurable (fun p : (Fin t → X × Y) × (X × Y) => K (B t p.1 p.2.1) p.2.2) :=
    measurable_const.sub (hm.comp measurable_snd)
  have hb := avg_genError_le_avg_loss D Y' K M hM hK {h}
    (by intro h' hh'; simpa using (Set.mem_singleton_iff.mp hh') ▸ hh)
    B (by intro t s; exact Set.mem_singleton h) hBm T hT δ hδ
  have hint : Integrable (fun z : X × Y => L (h z.1) z.2) D :=
    Integrable.of_mem_Icc 0 M hm.aemeasurable (Filter.Eventually.of_forall fun z => hL _ (hh z.1) z.2)
  have hr : genError D K h = M - genError D L h := by
    simp only [genError, K]
    rw [integral_sub (integrable_const _) hint]
    simp
  have hTr : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  convert hb using 1
  congr 1
  ext S
  simp only [Set.mem_setOf_eq, hypSeq, B, hr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, K, Finset.sum_sub_distrib]
  have he : (1 / (T : ℝ)) * ((T : ℝ) * M - ∑ t : Fin T, L (h (S t).1) (S t).2) =
      M - (1 / (T : ℝ)) * ∑ t : Fin T, L (h (S t).1) (S t).2 := by field_simp
  rw [he]
  field_simp
  constructor <;> intro hn <;> contrapose! hn <;> linarith

end OTCPrivate

theorem solution {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (Y' : Set E) (L : E → Y → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hL : ∀ a ∈ Y', ∀ y, 0 ≤ L a y ∧ L a y ≤ M)
    (hL_convex : ∀ y, ConvexOn ℝ Y' (fun a => L a y))
    (H : Set (X → E)) (hH : ∀ h ∈ H, ∀ x, h x ∈ Y')
    (hH_meas : ∀ h ∈ H, Measurable (fun z : X × Y => L (h z.1) z.2))
    (A : OnlineAlgorithm X Y E) (hA : ∀ t s, A t s ∈ H)
    (hA_meas : ∀ t : ℕ,
      Measurable (fun p : (Fin t → X × Y) × (X × Y) => L (A t p.1 p.2.1) p.2.2))
    (T : ℕ) (hT : 0 < T)
    (hAvg_meas : ∀ S : Fin T → X × Y,
      Measurable (fun z : X × Y => L (avgHyp A S z.1) z.2))
    (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin T => D)
        {S | ¬ (genError D L (avgHyp A S) ≤
            (1 / (T : ℝ)) * ∑ t : Fin T, L (hypSeq A S t (S t).1) (S t).2 +
              M * Real.sqrt (2 * Real.log (1 / δ) / T))}
      ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin T => D)
        {S | ¬ (genError D L (avgHyp A S) ≤
            (⨅ h : H, genError D L h) + regret H L A S / T +
              2 * M * Real.sqrt (2 * Real.log (2 / δ) / T))}
      ≤ ENNReal.ofReal δ  := by
  classical
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hTr0 : (T : ℝ) ≠ 0 := ne_of_gt hTr
  have hJ (S : Fin T → X × Y) : genError D L (avgHyp A S) ≤
      (1 / (T : ℝ)) * ∑ t, genError D L (hypSeq A S t) :=
    OTCPrivate.jensen_risk D Y' L M hL hL_convex A T hT S
      (fun t x => hH _ (hA _ _) x) (fun t => hH_meas _ (hA _ _)) (hAvg_meas S)
  have hfirst (d : ℝ) (hd : 0 < d) :
      (Measure.pi fun _ : Fin T => D)
        {S | ¬ (genError D L (avgHyp A S) ≤
            (1 / (T : ℝ)) * ∑ t : Fin T, L (hypSeq A S t (S t).1) (S t).2 +
              M * Real.sqrt (2 * Real.log (1 / d) / T))} ≤ ENNReal.ofReal d := by
    refine (measure_mono ?_).trans
      (avg_genError_le_avg_loss D Y' L M hM hL H hH A hA hA_meas T hT d hd)
    intro S hS hh
    exact hS ((hJ S).trans hh)
  refine ⟨hfirst δ hδ, ?_⟩
  letI : Nonempty H := ⟨⟨A 0 Fin.elim0, hA 0 Fin.elim0⟩⟩
  have hrisknonneg (h : H) : 0 ≤ genError D L h :=
    integral_nonneg fun z => (hL _ (hH h h.property z.1) z.2).1
  have hbounded : BddBelow (Set.range (fun h : H => genError D L h)) :=
    ⟨0, by rintro _ ⟨h, rfl⟩; exact hrisknonneg h⟩
  let r : ℝ := ⨅ h : H, genError D L h
  let c : ℝ := M * Real.sqrt (2 * Real.log (2 / δ) / T)
  have hd2 : 0 < δ / 2 := by positivity
  have hhalf := hfirst (δ / 2) hd2
  have hlog : (1 : ℝ) / (δ / 2) = 2 / δ := by field_simp
  rw [hlog] at hhalf
  let μ := Measure.pi fun _ : Fin T => D
  simp only [mul_assoc (2 : ℝ) M]
  change μ {S | ¬ (genError D L (avgHyp A S) ≤ r + regret H L A S / T + 2 * c)} ≤ _
  simp only [not_le]
  apply OTCPrivate.measure_gap
  intro ε hε
  obtain ⟨h, hh⟩ : ∃ h : H, genError D L h < r + ε :=
    exists_lt_of_ciInf_lt (show (⨅ h : H, genError D L h) < r + ε by dsimp [r]; linarith)
  have hfixed := OTCPrivate.fixed_comparator D Y' L M hM hL h
    (hH h h.property) (hH_meas h h.property) T hT (δ / 2) hd2
  rw [hlog] at hfixed
  let B₁ : Set (Fin T → X × Y) := {S | ¬ (genError D L (avgHyp A S) ≤
      (1 / (T : ℝ)) * ∑ t : Fin T, L (hypSeq A S t (S t).1) (S t).2 + c)}
  let B₂ : Set (Fin T → X × Y) := {S | ¬ ((1 / (T : ℝ)) *
      ∑ t : Fin T, L ((h : X → E) (S t).1) (S t).2 ≤ genError D L h + c)}
  have hsubset : {S | r + regret H L A S / T + 2 * c + ε < genError D L (avgHyp A S)} ⊆ B₁ ∪ B₂ := by
    intro S hS
    by_contra hn
    have hgood := not_or.mp hn
    have hg1 : genError D L (avgHyp A S) ≤
        (1 / (T : ℝ)) * ∑ t : Fin T, L (hypSeq A S t (S t).1) (S t).2 + c :=
      not_not.mp hgood.1
    have hg2 : (1 / (T : ℝ)) * ∑ t : Fin T, L ((h : X → E) (S t).1) (S t).2 ≤ genError D L h + c :=
      not_not.mp hgood.2
    have hemp : (⨅ k : H, ∑ t : Fin T, L ((k : X → E) (S t).1) (S t).2) ≤
        ∑ t : Fin T, L ((h : X → E) (S t).1) (S t).2 := by
      apply ciInf_le (f := fun k : H => ∑ t : Fin T, L ((k : X → E) (S t).1) (S t).2) _ h
      exact ⟨0, by rintro _ ⟨k, rfl⟩; exact Finset.sum_nonneg fun t _ => (hL _ (hH k k.property (S t).1) (S t).2).1⟩
    have hempdiv := div_le_div_of_nonneg_right hemp hTr.le
    have hreg : (1 / (T : ℝ)) * ∑ t : Fin T, L (hypSeq A S t (S t).1) (S t).2 =
        regret H L A S / T + (⨅ k : H, ∑ t : Fin T, L ((k : X → E) (S t).1) (S t).2) / T := by
      rw [regret, sub_div]
      ring
    rw [hreg] at hg1
    rw [one_div_mul_eq_div] at hg2
    change r + regret H L A S / T + 2 * c + ε < genError D L (avgHyp A S) at hS
    linarith
  calc
    μ _ ≤ μ (B₁ ∪ B₂) := measure_mono hsubset
    _ ≤ μ B₁ + μ B₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hhalf hfixed
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add hd2.le hd2.le]; congr 1; ring
