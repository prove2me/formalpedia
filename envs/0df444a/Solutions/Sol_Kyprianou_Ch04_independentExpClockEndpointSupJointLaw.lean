-- Prove2me | solution 1 for Kyprianou.Ch04.independentExpClockEndpointSupJointLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T07:47:11.174148+00:00
-- url     : https://prove2.me/submissions/43511bb9-6619-4474-b8b7-4c526fbafe2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_Kyprianou_Ch04_independentExpClockPathJointLaw
import Theorems.Thm_Kyprianou_Ch04_cadlagEndpointSupMeasurablePiProxy

open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem rawSup_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ω : Ω) :
    sSup ((fun s : NNReal => L.X s ω) '' Set.Iic t) = runningSup L t ω := by
  rw [(runningSup_eq_rawSup_nonneg L t ω).1]
  change sSup ((fun s : NNReal => L.X s ω) '' Set.Iic t) =
    sSup (Set.range (fun s : Set.Icc (0 : NNReal) t => L.X s.1 ω))
  congr 1
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, zero_le, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.1, s.2.2, rfl⟩

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q)
    (e : Ω → NNReal) (he : Measurable e)
    (hlaw : ∀ t : NNReal, (P {ω | t < e ω}).toReal =
      Real.exp (-q * (t : ℝ)))
    (hi : Indep (MeasurableSpace.comap e inferInstance)
      (MeasurableSpace.comap (fun ω : Ω => fun t : NNReal => L.X t ω)
        inferInstance) P) :
    let S : Ω → ℝ := fun ω =>
      sSup ((fun s : NNReal => L.X s ω) '' Set.Iic (e ω))
    let D : Ω → ℝ := fun ω => L.X (e ω) ω - S ω
    let Sp : Ω × ℝ → ℝ := fun z => runningSup L z.2.toNNReal z.1
    let Dp : Ω × ℝ → ℝ := fun z =>
      L.X z.2.toNNReal z.1 - Sp z
    Measurable D ∧ Measurable S ∧
      Measure.map (fun ω => (D ω, S ω)) P =
        Measure.map (fun z => (Dp z, Sp z)) (P.prod (expMeasure q)) := by
  intro S D Sp Dp
  obtain ⟨G, hG, hG_eval⟩ := cadlagEndpointSupMeasurablePiProxy P F L
  let A : Ω → NNReal × (NNReal → ℝ) :=
    fun ω => (e ω, fun t => L.X t ω)
  let B : Ω × ℝ → NNReal × (NNReal → ℝ) :=
    fun z => (z.2.toNNReal, fun t => L.X t z.1)
  have hpath : Measurable (fun ω : Ω => fun t : NNReal => L.X t ω) :=
    measurable_pi_lambda _ (fun t => L.adapted.measurable)
  have hA : Measurable A := he.prodMk hpath
  have hB : Measurable B :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk (hpath.comp measurable_fst)
  have hGA : G ∘ A = fun ω => (D ω, S ω) := by
    funext ω
    rw [Function.comp_apply, hG_eval]
    dsimp [D, S]
    rw [rawSup_eq]
  have hGB : G ∘ B = fun z => (Dp z, Sp z) := by
    funext z
    exact hG_eval z.2.toNNReal z.1
  have hm : Measurable (fun ω => (D ω, S ω)) := by
    rw [← hGA]
    exact hG.comp hA
  refine ⟨hm.fst, hm.snd, ?_⟩
  rw [← hGA, ← hGB, ← Measure.map_map hG hA, ← Measure.map_map hG hB]
  rw [show P.map A = (P.prod (expMeasure q)).map B from
    independentExpClockPathJointLaw P F L q hq e he hlaw hi]
