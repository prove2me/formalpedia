-- Prove2me | solution 1 for Kyprianou.poissonRandomMeasureExists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:12:41.606825+00:00
-- url     : https://prove2.me/submissions/3d1e4d91-ed93-405a-ac2b-3ec34c434082
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_poissonRandomMeasureExistsGenericCh02V3
import Theorems.Thm_LevyStochCalc_Poisson_indep_of_disjoint_region_families_ch02

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Construct the time-marked PRM from the generic sigma-finite PRM. -/
theorem solution
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        Nonempty (LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0}
          P levyMeasure) := by
  classical
  let m : Measure (ℝ × ℝ) :=
    LevyStochCalc.Poisson.referenceIntensity levyMeasure
  haveI : SigmaFinite m := by
    dsimp [m, LevyStochCalc.Poisson.referenceIntensity]
    infer_instance
  obtain ⟨Ω, measΩ, P, probP, M, hmeas, hnat, hlaw, hinf, hind⟩ :=
    Kyprianou.poissonRandomMeasureExistsGenericCh02V3
      (ℝ × ℝ) m
  letI : MeasurableSpace Ω := measΩ
  letI : IsProbabilityMeasure P := probP
  have hInd : ∀ {ι : Type} [Countable ι]
      (B : ι → Set (ℝ × ℝ)),
      (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      ProbabilityTheory.iIndepFun (fun i ω => M ω (B i)) P :=
    hind
  have hpast : ∀ {s t : ℝ}, 0 ≤ s → s < t →
      ∀ {A : Set ℝ}, MeasurableSet A → levyMeasure A ≠ ⊤ →
      Indep
        (⨆ B ∈ {C : Set (ℝ × ℝ) |
          C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => M ω B) inferInstance)
        (MeasurableSpace.comap
          (fun ω => M ω (Set.Ioc s t ×ˢ A)) inferInstance) P := by
    intro s t hs hst A hA _
    let R : Set (ℝ × ℝ) := Set.Ioc s t ×ˢ A
    have hR : MeasurableSet R := measurableSet_Ioc.prod hA
    have hfull :=
      LevyStochCalc.Poisson.indep_of_disjoint_region_families_ch02
        (P := P) (N := M) (fun {B} hB => hmeas B hB) hInd
        (fun _ : Fin 1 => R) (fun _ => hR)
    have hright :
        (⨆ j : Fin 1,
          MeasurableSpace.comap (fun ω => M ω ((fun _ : Fin 1 => R) j))
            inferInstance) =
        MeasurableSpace.comap (fun ω => M ω R) inferInstance := by
      simp
    rw [hright] at hfull
    have hleft :
        (⨆ B ∈ {C : Set (ℝ × ℝ) |
            C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => M ω B) inferInstance) ≤
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
            (∀ j : Fin 1, Disjoint C ((fun _ : Fin 1 => R) j)) ∧
              MeasurableSet C},
          MeasurableSpace.comap (fun ω => M ω C) inferInstance) := by
      refine iSup₂_le fun C hC => le_iSup₂_of_le C ?_ le_rfl
      refine ⟨?_, hC.2⟩
      intro j
      apply Set.disjoint_left.mpr
      intro z hz hzR
      have htle : z.1 ≤ s := (hC.1 hz).1
      have hts : s < z.1 := hzR.1.1
      exact (not_lt_of_ge htle) hts
    change Indep
        (⨆ B ∈ {C : Set (ℝ × ℝ) |
          C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => M ω B) inferInstance)
        (MeasurableSpace.comap (fun ω => M ω R) inferInstance) P
    exact indep_of_indep_of_le_left hfull hleft
  refine ⟨Ω, measΩ, P, probP, ⟨{
    N := M
    measurable_eval := fun {B} hB => hmeas B hB
    integer_valued := fun {B} hB hfin =>
      hnat B hB (lt_top_iff_ne_top.mpr hfin)
    infinite_at_infinite_intensity := fun {B} hB hinfty =>
      hinf B hB hinfty
    poisson_law := fun {B} hB hfin => by
      simpa only [LevyStochCalc.Poisson.poissonMeasureENN] using
        hlaw B hB (lt_top_iff_ne_top.mpr hfin)
    independent_disjoint := fun B hB hdisj => hInd B hB hdisj
    joint_past_future_independent := hpast
  }⟩⟩
