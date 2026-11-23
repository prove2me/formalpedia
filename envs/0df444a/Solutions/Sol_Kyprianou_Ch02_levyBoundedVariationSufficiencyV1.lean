-- Prove2me | solution 1 for Kyprianou.Ch02.levyBoundedVariationSufficiencyV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:38:11.947251+00:00
-- url     : https://prove2.me/submissions/d0982f8f-da52-4a58-b86d-0471e4d10ef6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyFiniteVariationMonotoneJordanRepresentationV1
open MeasureTheory ProbabilityTheory Complex Kyprianou
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A real difference of locally bounded-variation paths is locally bounded-variation. -/
private theorem locallyBV_sub
    {α : Type*} [LinearOrder α] {f g : α → ℝ} {s : Set α}
    (hf : LocallyBoundedVariationOn f s)
    (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (fun t => f t - g t) s := by
  intro a b ha hb
  have hfa := hf a b ha hb
  have hga := hg a b ha hb
  have hneg : BoundedVariationOn (fun t => -g t) ((s ∩ Set.Icc a b)) := by
    change eVariationOn (fun t => -g t) ((s ∩ Set.Icc a b)) ≠ ⊤
    have heq : eVariationOn (fun t => -g t) ((s ∩ Set.Icc a b)) =
        eVariationOn g ((s ∩ Set.Icc a b)) := by
      simp only [eVariationOn, edist_neg_neg]
    rw [heq]
    exact hga
  have hle : eVariationOn (fun t => f t + -g t) ((s ∩ Set.Icc a b)) ≤
      eVariationOn f ((s ∩ Set.Icc a b)) +
      eVariationOn (fun t => -g t) ((s ∩ Set.Icc a b)) := by
    apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) +
           edist (-g (u (i + 1))) (-g (u i))) :=
        Finset.sum_le_sum fun _ _ => edist_add_add_le _ _ _ _
      _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range n, edist (-g (u (i + 1))) (-g (u i)) :=
        Finset.sum_add_distrib
      _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)
  have hsum : BoundedVariationOn (fun t => f t + -g t) ((s ∩ Set.Icc a b)) :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfa, hneg⟩) hle
  simpa only [sub_eq_add_neg] using hsum

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) := by
  intro hfin
  have hrep :=
    Kyprianou.Ch02.levyFiniteVariationMonotoneJordanRepresentationV1
      a σ levyMeasure hlevyMeasure P X hX hchar hfin
  filter_upwards [hrep] with ω hω
  obtain ⟨p, q, hp, hq, heq⟩ := hω
  have hvar : LocallyBoundedVariationOn
      (fun t : ℝ≥0 => p t - q t) Set.univ :=
    locallyBV_sub (hp.monotoneOn Set.univ).locallyBoundedVariationOn
      (hq.monotoneOn Set.univ).locallyBoundedVariationOn
  have hpath : (fun t : ℝ≥0 => X t ω) = (fun t => p t - q t) :=
    funext heq
  rw [hpath]
  exact hvar
