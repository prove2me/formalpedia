-- Prove2me | solution 1 for Kyprianou.exercise2_8_AllPartsCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:43:57.355287+00:00
-- url     : https://prove2.me/submissions/a234b3d5-5e00-4e82-b722-7ff3fa000c65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumIsSubordinatorV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyDriftPlusJumpDecompositionV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyPosNegJumpSumsIndepV1

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise28Helpers

private lemma nhdsWithin_Iio_neBot_of_pos {s : ℝ≥0} (hs : 0 < s) :
    (nhdsWithin s (Set.Iio s)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  let y : ℝ≥0 := ⟨max 0 ((s : ℝ) - ε / 2), le_max_left _ _⟩
  refine ⟨y, ?_, ?_⟩
  · change max 0 ((s : ℝ) - ε / 2) < (s : ℝ)
    exact max_lt hs (by linarith)
  · change |(s : ℝ) - (y : ℝ)| < ε
    have hy_le : (y : ℝ) ≤ (s : ℝ) := max_le (NNReal.coe_nonneg s) (by linarith)
    have hy_ge : (s : ℝ) - ε / 2 ≤ (y : ℝ) := le_max_right _ _
    rw [abs_of_nonneg (sub_nonneg.mpr hy_le)]
    linarith

private lemma isLevyProcess_neg
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : ProbabilityTheory.IsLevyProcess X P) :
    ProbabilityTheory.IsLevyProcess (fun t ω => -X t ω) P where
  start_zero := by
    funext ω
    simp [congrFun hX.start_zero ω]
  indep_increments := by
    intro n t ht
    have hcomp :
        (fun k : Fin n => increment (fun s ω => -X s ω) (t k.castSucc) (t k.succ)) =
        (fun k : Fin n => (fun x : ℝ => -x) ∘ increment X (t k.castSucc) (t k.succ)) := by
      funext k ω
      simp [increment]
      ring
    rw [hcomp]
    exact (hX.indep_increments n t ht).comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  stationary_increments := by
    intro s h
    have h1 : increment (fun u ω => -X u ω) s (s + h) =
        (fun x : ℝ => -x) ∘ increment X s (s + h) := by
      funext ω; simp [increment]; ring
    have h2 : increment (fun u ω => -X u ω) 0 h =
        (fun x : ℝ => -x) ∘ increment X 0 h := by
      funext ω; simp [increment]; ring
    rw [h1, h2]
    exact (hX.stationary_increments s h).comp measurable_neg
  cadlag_ae := by
    filter_upwards [hX.cadlag_ae] with ω hω t
    obtain ⟨hrc, l, hl⟩ := hω t
    exact ⟨hrc.neg, -l, hl.neg⟩

private lemma locallyBoundedVariationOn_neg
    {f : ℝ≥0 → ℝ} (hf : LocallyBoundedVariationOn f Set.univ) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 => -f t) Set.univ := by
  intro a b ha hb
  have heq : eVariationOn (fun t : ℝ≥0 => -f t) (Set.univ ∩ Set.Icc a b) =
      eVariationOn f (Set.univ ∩ Set.Icc a b) := by
    unfold eVariationOn
    refine iSup_congr fun ⟨n, u, hu, hus⟩ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact edist_neg_neg (f (u (i + 1))) (f (u i))
  change eVariationOn (fun t : ℝ≥0 => -f t) (Set.univ ∩ Set.Icc a b) ≠ ⊤
  rw [heq]
  exact hf a b ha hb

private lemma iIndepFun_of_ae_eq
    {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
    [(i : ι) → MeasurableSpace (β i)] {P : Measure Ω}
    {f g : (i : ι) → Ω → β i}
    (hf : ProbabilityTheory.iIndepFun f P)
    (hfg : ∀ i, f i =ᵐ[P] g i) :
    ProbabilityTheory.iIndepFun g P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hsets
  have hsingle : ∀ i, g i ⁻¹' sets i =ᵐ[P] f i ⁻¹' sets i := fun i => by
    filter_upwards [hfg i] with ω hω
    exact propext (show g i ω ∈ sets i ↔ f i ω ∈ sets i by rw [hω])
  have hinter : (⋂ i ∈ S, g i ⁻¹' sets i) =ᵐ[P] (⋂ i ∈ S, f i ⁻¹' sets i) := by
    have hall : ∀ᵐ ω ∂P, ∀ i ∈ (S : Set ι), (g i ω ∈ sets i ↔ f i ω ∈ sets i) := by
      rw [ae_ball_iff S.countable_toSet]
      intro i _
      filter_upwards [hfg i] with ω hω
      rw [hω]
    filter_upwards [hall] with ω hω
    exact propext (show (ω ∈ ⋂ i ∈ S, g i ⁻¹' sets i) ↔ (ω ∈ ⋂ i ∈ S, f i ⁻¹' sets i) by
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact forall₂_congr fun i hi => hω i hi)
  rw [measure_congr hinter, hf S hsets]
  refine Finset.prod_congr rfl fun i _ => (measure_congr (hsingle i)).symm

private lemma isLevyProcess_of_ae_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hZ0 : Z 0 = fun _ => 0)
    (hae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = Z t ω) :
    ProbabilityTheory.IsLevyProcess Z P where
  start_zero := hZ0
  indep_increments := by
    intro n t ht
    refine iIndepFun_of_ae_eq (hY.indep_increments n t ht) fun k => ?_
    filter_upwards [hae] with ω hω
    simp [increment, hω]
  stationary_increments := by
    intro s h
    have h1 : increment Y s (s + h) =ᵐ[P] increment Z s (s + h) := by
      filter_upwards [hae] with ω hω; simp [increment, hω]
    have h2 : increment Y 0 h =ᵐ[P] increment Z 0 h := by
      filter_upwards [hae] with ω hω; simp [increment, hω]
    have hst := hY.stationary_increments s h
    exact
      { aemeasurable_fst := hst.aemeasurable_fst.congr h1
        aemeasurable_snd := hst.aemeasurable_snd.congr h2
        map_eq := by rw [← Measure.map_congr h1, ← Measure.map_congr h2, hst.map_eq] }
  cadlag_ae := by
    filter_upwards [hY.cadlag_ae, hae] with ω hω heq
    have hfun : (fun t => Z t ω) = (fun t => Y t ω) := funext fun t => (heq t).symm
    rwa [hfun]

private lemma isLevyProcess_add_linear
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℝ≥0 → Ω → ℝ} (hY : ProbabilityTheory.IsLevyProcess Y P) (c : ℝ) :
    ProbabilityTheory.IsLevyProcess (fun t ω => Y t ω + c * (t : ℝ)) P where
  start_zero := by
    funext ω
    simp [congrFun hY.start_zero ω]
  indep_increments := by
    intro n t ht
    let g : Fin n → ℝ → ℝ := fun k x => x + c * ((t k.succ : ℝ) - (t k.castSucc : ℝ))
    have hcomp :
        (fun k : Fin n => increment (fun s ω => Y s ω + c * (s : ℝ)) (t k.castSucc) (t k.succ)) =
        (fun k : Fin n => g k ∘ increment Y (t k.castSucc) (t k.succ)) := by
      funext k ω
      simp [increment, g]
      ring
    rw [hcomp]
    exact (hY.indep_increments n t ht).comp g (fun k => measurable_id.add measurable_const)
  stationary_increments := by
    intro s h
    let g : ℝ → ℝ := fun x => x + c * (h : ℝ)
    have h1 : increment (fun u ω => Y u ω + c * (u : ℝ)) s (s + h) =
        g ∘ increment Y s (s + h) := by
      funext ω
      simp [increment, g, NNReal.coe_add]
      ring
    have h2 : increment (fun u ω => Y u ω + c * (u : ℝ)) 0 h =
        g ∘ increment Y 0 h := by
      funext ω
      simp [increment, g]
      ring
    rw [h1, h2]
    exact (hY.stationary_increments s h).comp (measurable_id.add measurable_const)
  cadlag_ae := by
    filter_upwards [hY.cadlag_ae] with ω hω t
    obtain ⟨hrc, l, hl⟩ := hω t
    have hlin_cont : Continuous (fun u : ℝ≥0 => c * (u : ℝ)) :=
      continuous_const.mul NNReal.continuous_coe
    refine ⟨hrc.add hlin_cont.continuousWithinAt, l + c * (t : ℝ), ?_⟩
    exact hl.add (hlin_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

private lemma monotone_add_nonneg_linear
    {f : ℝ≥0 → ℝ} (hf : Monotone f) {c : ℝ} (hc : 0 ≤ c) :
    Monotone (fun t : ℝ≥0 => f t + c * (t : ℝ)) := by
  intro s t hst
  exact add_le_add (hf hst) (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) hc)

private lemma iIndepFun_add_linear_pair
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Jpos Jneg : ℝ≥0 → Ω → ℝ}
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Jpos t ω else Jneg t ω) P)
    (c0 c1 : ℝ) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Jpos t ω + c0 * (t : ℝ) else Jneg t ω + c1 * (t : ℝ)) P := by
  let g : Fin 2 → (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun i f t =>
    f t + (if i = 0 then c0 else c1) * (t : ℝ)
  have hg_meas : ∀ i : Fin 2, Measurable (g i) := fun i =>
    measurable_pi_lambda _ fun t => (measurable_pi_apply t).add measurable_const
  have hcomp :
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Jpos t ω + c0 * (t : ℝ) else Jneg t ω + c1 * (t : ℝ)) =
      (fun i : Fin 2 => g i ∘ fun ω t => if i = 0 then Jpos t ω else Jneg t ω) := by
    funext i ω t
    by_cases hi : i = 0 <;> simp [g, hi]
  rw [hcomp]
  exact hind.comp g hg_meas

end Exercise28Helpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    ∃ (Spos Sneg : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess Spos P ∧
      ProbabilityTheory.IsLevyProcess Sneg P ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
      ProbabilityTheory.iIndepFun
        (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then Spos t ω else Sneg t ω) P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω) := by
  let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (X s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
  let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
        X s.1 ω) 0
  let JposNeg : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max ((-X s.1 ω) -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => -X u ω)) 0
  obtain ⟨hJpos_levy, hJpos_mono⟩ :=
    Kyprianou.Ch02.bvLevyPositiveJumpSumIsSubordinatorV1 P X hX hBV
  have hXneg_levy : ProbabilityTheory.IsLevyProcess (fun t ω => -X t ω) P :=
    Exercise28Helpers.isLevyProcess_neg hX
  have hXneg_BV : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => -X t ω) Set.univ := by
    filter_upwards [hBV] with ω hω
    exact Exercise28Helpers.locallyBoundedVariationOn_neg hω
  obtain ⟨hJposNeg_levy, hJposNeg_mono⟩ :=
    Kyprianou.Ch02.bvLevyPositiveJumpSumIsSubordinatorV1 P (fun t ω => -X t ω) hXneg_levy hXneg_BV
  have hJneg_ae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, JposNeg t ω = Jneg t ω := by
    filter_upwards [hX.cadlag_ae] with ω hω t
    dsimp only [JposNeg, Jneg]
    refine tsum_congr fun s => ?_
    have : (nhdsWithin s.1 (Set.Iio s.1)).NeBot :=
      Exercise28Helpers.nhdsWithin_Iio_neBot_of_pos s.2.1
    obtain ⟨_, l, hl⟩ := hω s.1
    have hlim1 : Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) = l :=
      hl.limUnder_eq
    have hlim2 : Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => -X u ω) = -l :=
      hl.neg.limUnder_eq
    rw [hlim1, hlim2]
    congr 1
    ring
  have hJneg0 : Jneg 0 = fun _ => 0 := by
    funext ω
    dsimp only [Jneg]
    have : IsEmpty (Set.Ioc (0 : ℝ≥0) 0) :=
      ⟨fun ⟨_, hx⟩ => not_lt_of_ge hx.2 hx.1⟩
    exact tsum_empty
  have hJneg_levy : ProbabilityTheory.IsLevyProcess Jneg P :=
    Exercise28Helpers.isLevyProcess_of_ae_eq hJposNeg_levy hJneg0 hJneg_ae
  have hJneg_mono : ∀ᵐ ω ∂P, Monotone (fun t => Jneg t ω) := by
    filter_upwards [hJposNeg_mono, hJneg_ae] with ω hmono heq
    have hfun : (fun t => Jneg t ω) = (fun t => JposNeg t ω) := funext fun t => (heq t).symm
    rwa [hfun]
  obtain ⟨d, hd⟩ := Kyprianou.Ch02.bvLevyDriftPlusJumpDecompositionV1 P X hX hBV
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Jpos t ω else Jneg t ω) P :=
    Kyprianou.Ch02.bvLevyPosNegJumpSumsIndepV1 P X hX hBV
  let dpos : ℝ := max d 0
  let dneg : ℝ := max (-d) 0
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => Jpos t ω + dpos * (t : ℝ)
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => Jneg t ω + dneg * (t : ℝ)
  refine ⟨Spos, Sneg,
    Exercise28Helpers.isLevyProcess_add_linear hJpos_levy dpos,
    Exercise28Helpers.isLevyProcess_add_linear hJneg_levy dneg,
    ?_, ?_,
    Exercise28Helpers.iIndepFun_add_linear_pair hind dpos dneg,
    ?_⟩
  · filter_upwards [hJpos_mono] with ω hω
    exact Exercise28Helpers.monotone_add_nonneg_linear hω (le_max_right d 0)
  · filter_upwards [hJneg_mono] with ω hω
    exact Exercise28Helpers.monotone_add_nonneg_linear hω (le_max_right (-d) 0)
  · filter_upwards [hd] with ω hω t
    have hd_split : dpos - dneg = d := by
      dsimp only [dpos, dneg]
      rcases le_total d 0 with hle | hge
      · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
      · rw [max_eq_left hge, max_eq_right (by linarith)]; ring
    dsimp only [Spos, Sneg]
    rw [hω t]
    linear_combination -(t : ℝ) * hd_split
