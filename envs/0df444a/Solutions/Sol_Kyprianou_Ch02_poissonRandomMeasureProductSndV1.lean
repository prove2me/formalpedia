-- Prove2me | solution 1 for Kyprianou.Ch02.poissonRandomMeasureProductSndV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:50:34.494202+00:00
-- url     : https://prove2.me/submissions/085eff3b-1edd-4c42-9ca7-be8a177c7f50

import Theorems.Thm_Kyprianou_Ch02_indepComapSndProductV1
import Theorems.Thm_Kyprianou_Ch02_iIndepFunSndProductV1
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N₂ : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P₂ ν) :
    ∃ N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} (P₁.prod P₂) ν,
      ∀ ω : Ω₁ × Ω₂, N.N ω = N₂.N ω.2 := by
  let P : Measure (Ω₁ × Ω₂) := P₁.prod P₂
  have hP : IsProbabilityMeasure P := inferInstance
  have hmap_fst : P.map Prod.fst = P₁ := by
    simp [P, Measure.map_fst_prod]
  have hmap_snd : P.map Prod.snd = P₂ := by
    simp [P, Measure.map_snd_prod]
  let N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν :=
    { N := fun ω => N₂.N ω.2
      measurable_eval := fun hS => (N₂.measurable_eval hS).comp measurable_snd
      integer_valued := fun hS hfin => Measure.quasiMeasurePreserving_snd.ae (N₂.integer_valued hS hfin)
      infinite_at_infinite_intensity := fun hS hinf =>
        Measure.quasiMeasurePreserving_snd.ae (N₂.infinite_at_infinite_intensity hS hinf)
      poisson_law := fun {S} hS hfin => by
        have hcomp : (fun ω : Ω₁ × Ω₂ => N₂.N ω.2 S) = (fun ω₂ : Ω₂ => N₂.N ω₂ S) ∘ Prod.snd := rfl
        rw [hcomp, ← Measure.map_map (N₂.measurable_eval hS) measurable_snd, hmap_snd]
        exact N₂.poisson_law hS hfin
      independent_disjoint := fun B' hB' hdisj =>
        Kyprianou.Ch02.iIndepFunSndProductV1 P₁ P₂ (N₂.independent_disjoint B' hB' hdisj)
      joint_past_future_independent := fun {s t} hs hst {A} hA hAfin => by
        have hbase := Kyprianou.Ch02.indepComapSndProductV1 P₁ P₂
          (N₂.joint_past_future_independent hs hst hA hAfin)
        have hL : (⨆ C ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
              MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => N₂.N ω.2 C) inferInstance) =
            (⨆ C ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
              MeasurableSpace.comap (fun ω₂ : Ω₂ => N₂.N ω₂ C) inferInstance).comap Prod.snd := by
          simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
          rfl
        have hR : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => N₂.N ω.2 (Set.Ioc s t ×ˢ A)) inferInstance =
            (MeasurableSpace.comap (fun ω₂ : Ω₂ => N₂.N ω₂ (Set.Ioc s t ×ˢ A)) inferInstance).comap Prod.snd := by
          rw [MeasurableSpace.comap_comp]; rfl
        rw [hL, hR]
        exact hbase }
  refine ⟨N, ?_⟩
  intro ω
  rfl

