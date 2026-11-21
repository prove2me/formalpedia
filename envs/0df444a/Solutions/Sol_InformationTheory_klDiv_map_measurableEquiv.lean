-- Prove2me | solution 1 for InformationTheory.klDiv_map_measurableEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:53.143968+00:00
-- url     : https://prove2.me/submissions/1ab0d314-0b86-4ff4-b43a-975343168aad

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InformationTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace InformationTheory
theorem _root_.solution (e : α ≃ᵐ β) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun]
  by_cases hμν : μ ≪ ν
  · have hmap : μ.map e ≪ ν.map e := e.measurableEmbedding.absolutelyContinuous_map hμν
    simp only [hμν, hmap, ↓reduceIte]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    simp [hx]
  · have hmap : ¬ μ.map e ≪ ν.map e := by
      intro h
      have h' := e.symm.measurableEmbedding.absolutelyContinuous_map h
      exact hμν (by simpa using h')
    simp [hμν, hmap]
end InformationTheory
