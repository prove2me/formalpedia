-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffDifferenceBandV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:33:10.629781+00:00
-- url     : https://prove2.me/submissions/3e1a5ccb-5ba0-4a14-83d2-62deb3e43aa4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegrableAllTimesAEV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The difference of nested cutoffs is the compensated intermediate mark band. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 U V : NNReal → Ω → ℝ) (η ε : ℝ)
    (hη : 0 < η) (hηε : η < ε) (hε : ε < 1)
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X Xleft ω)
    (hU : ∀ t ω, U t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | η < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | η < |x| ∧ |x| < 1}, x ∂ν))
    (hV : ∀ t ω, V t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν)) :
    ∀ᵐ ω ∂P, ∀ t : NNReal, U t ω - V t ω =
      (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | η < |x| ∧ |x| ≤ ε},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | η < |x| ∧ |x| ≤ ε}, x ∂ν) := by
  let B : Set ℝ := {x | η < |x| ∧ |x| < 1}
  let C : Set ℝ := {x | ε < |x| ∧ |x| < 1}
  let D : Set ℝ := {x | η < |x| ∧ |x| ≤ ε}
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hC : MeasurableSet C := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_le measurable_id.abs measurable_const)
  have hfin : ν B < ⊤ := (measure_mono (show B ⊆ {x | η ≤ |x|} from
    fun x hx => hx.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top hη)
  have hCD : C ∪ D = B := by
    ext x
    change (ε < |x| ∧ |x| < 1) ∨ (η < |x| ∧ |x| ≤ ε) ↔ η < |x| ∧ |x| < 1
    constructor
    · rintro (h | h)
      · exact ⟨hηε.trans h.1,h.2⟩
      · exact ⟨h.1,h.2.trans_lt hε⟩
    · intro h
      exact (lt_or_ge ε |x|).elim (fun he => Or.inl ⟨he,h.2⟩)
        (fun he => Or.inr ⟨h.1,he⟩)
  have hdis : Disjoint C D := Set.disjoint_left.mpr fun x hx hy =>
    (not_le_of_gt hx.1) hy.2
  have hCs : C ⊆ B := by rw [← hCD]; exact subset_union_left
  have hDs : D ⊆ B := by rw [← hCD]; exact subset_union_right
  have : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hfin⟩
  have hi : IntegrableOn (fun x : ℝ => x) B ν :=
    Integrable.mono' (integrable_const (1 : ℝ)) measurable_id.aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem hB] with x hx
          rw [Real.norm_eq_abs]
          exact hx.2.le)
  have hsplit : (∫ x in B, x ∂ν) = (∫ x in C, x ∂ν) + ∫ x in D, x ∂ν := by
    rw [← hCD]
    exact setIntegral_union hdis hD (hi.mono_set hCs) (hi.mono_set hDs)
  filter_upwards [hN, Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV1
    P ν N B hB hfin] with ω hω hiω
  have hz : N.N ω (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [hω]
    exact Kyprianou.Ch04.pathJumpMeasureZeroTimeV1 X Xleft ω
  intro t
  let I := Ioc (0 : ℝ) (t : ℝ)
  have hu : I ×ˢ C ∪ I ×ˢ D = I ×ˢ B := by rw [← Set.prod_union, hCD]
  have hd : Disjoint (I ×ˢ C) (I ×ˢ D) :=
    Set.disjoint_left.mpr fun p hp hq => Set.disjoint_left.mp hdis hp.2 hq.2
  have hj := setIntegral_union hd (measurableSet_Ioc.prod hD)
    ((hiω t).mono_set (Set.prod_mono le_rfl hCs))
    ((hiω t).mono_set (Set.prod_mono le_rfl hDs))
  rw [hu] at hj
  change U t ω - V t ω = (∫ z in I ×ˢ D,z.2 ∂(N.N ω)) - (t : ℝ) * ∫ x in D,x ∂ν
  rw [hU, hV]
  change X2 t ω + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B,z.2 ∂(N.N ω)) -
    (t : ℝ) * (∫ x in B,x ∂ν) -
    (X2 t ω + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ C,z.2 ∂(N.N ω)) -
    (t : ℝ) * (∫ x in C,x ∂ν)) = _
  rw [Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 _ hz,
    Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 _ hz, hj, hsplit]
  ring
