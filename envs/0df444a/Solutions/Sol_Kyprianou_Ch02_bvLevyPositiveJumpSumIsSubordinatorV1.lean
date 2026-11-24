-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyPositiveJumpSumIsSubordinatorV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T14:02:35.388962+00:00
-- url     : https://prove2.me/submissions/99335cb1-d9e9-459d-a305-126b7f162948
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanSposSnegEqJumpPlusDriftV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumMonotonePointwiseV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Positive jump sum is a subordinator: `Jpos = Spos - dpos·t` via the Jordan↔jump
child; Lévy-ness transfers from proved `Spos` by adding linear drift `-dpos`
then AE-repair; monotonicity from Jordan monotonicity and `dpos ≥ 0`.
-/

private lemma iIndepFun_of_ae_eq
    {Ω ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
    [(i : ι) → MeasurableSpace (β i)] {P : Measure Ω}
    {f g : (i : ι) → Ω → β i}
    (hf : iIndepFun f P) (hfg : ∀ i, f i =ᵐ[P] g i) :
    iIndepFun g P := by
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
    exact propext
      (show (ω ∈ ⋂ i ∈ S, g i ⁻¹' sets i) ↔ (ω ∈ ⋂ i ∈ S, f i ⁻¹' sets i) by
        simp only [Set.mem_iInter, Set.mem_preimage]
        exact forall₂_congr fun i hi => hω i hi)
  rw [measure_congr hinter, hf S hsets]
  refine Finset.prod_congr rfl fun i _ => (measure_congr (hsingle i)).symm

private lemma isLevyProcess_of_ae_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : IsLevyProcess Y P) (hZ0 : Z 0 = fun _ => 0)
    (hae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = Z t ω) :
    IsLevyProcess Z P where
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
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsLevyProcess Y P) (c : ℝ) :
    IsLevyProcess (fun t ω => Y t ω + c * (t : ℝ)) P where
  start_zero := by
    funext ω
    simp [congrFun hY.start_zero ω]
  indep_increments := by
    intro n t ht
    let g : Fin n → ℝ → ℝ := fun k x => x + c * ((t k.succ : ℝ) - (t k.castSucc : ℝ))
    have hcomp :
        (fun k : Fin n =>
          increment (fun s ω => Y s ω + c * (s : ℝ)) (t k.castSucc) (t k.succ)) =
          fun k : Fin n => g k ∘ increment Y (t k.castSucc) (t k.succ) := by
      funext k ω
      simp [increment, g]
      ring
    rw [hcomp]
    exact (hY.indep_increments n t ht).comp g (fun _ => measurable_id.add measurable_const)
  stationary_increments := by
    intro s h
    let g : ℝ → ℝ := fun x => x + c * (h : ℝ)
    have h1 :
        increment (fun u ω => Y u ω + c * (u : ℝ)) s (s + h) =
          g ∘ increment Y s (s + h) := by
      funext ω
      simp [increment, g, NNReal.coe_add]
      ring
    have h2 :
        increment (fun u ω => Y u ω + c * (u : ℝ)) 0 h =
          g ∘ increment Y 0 h := by
      funext ω
      simp [increment, g, NNReal.coe_zero]
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

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    ProbabilityTheory.IsLevyProcess Jpos P ∧
    (∀ᵐ ω ∂P, Monotone (fun t => Jpos t ω)) := by
  dsimp only
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (X s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
  obtain ⟨hSposLevy, _⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  obtain ⟨hSposMono, _, _⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  refine Exists.elim
    (Kyprianou.Ch02.bvLevyJordanSposSnegEqJumpPlusDriftV1 P X hX hBV)
    fun dpos hex =>
      Exists.elim hex fun dneg hpack => ?_
  rcases hpack with ⟨hdpos, _, hSposEq, _⟩
  have hJeq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Jpos t ω = Spos t ω - dpos * (t : ℝ) := by
    filter_upwards [hSposEq] with ω hω t
    exact (sub_eq_of_eq_add (hω t)).symm
  have hJ0 : Jpos 0 = fun _ => 0 := by
    funext ω
    have : IsEmpty (Set.Ioc (0 : ℝ≥0) 0) :=
      ⟨fun ⟨_, hx⟩ => (not_lt_of_ge hx.2) hx.1⟩
    exact tsum_empty
  -- Spos - dpos·t = Spos + (-dpos)·t
  have hDrift : IsLevyProcess (fun t ω => Spos t ω + (-dpos) * (t : ℝ)) P :=
    isLevyProcess_add_linear hSposLevy (-dpos)
  have hLevy : IsLevyProcess Jpos P :=
    isLevyProcess_of_ae_eq hDrift hJ0 (by
      filter_upwards [hJeq] with ω hω t
      simpa [sub_eq_add_neg] using (hω t).symm)
  -- Nonnegative summands grow with the time horizon ⇒ pathwise monotone.
  refine ⟨hLevy, Eventually.of_forall fun ω a b hab =>
    Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseV1 X ω a b hab⟩
