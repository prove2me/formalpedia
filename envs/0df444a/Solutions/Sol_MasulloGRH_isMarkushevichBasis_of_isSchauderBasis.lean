-- Prove2me | solution 1 for MasulloGRH.isMarkushevichBasis_of_isSchauderBasis
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:51:49.80084+00:00
-- url     : https://prove2.me/submissions/8e461502-ce13-4e6a-b06e-b568a257fbe1

import Definitions.Def_MasulloGRH_SchauderBases
import Definitions.Def_MarkushevichBasis_Basic

open MasulloGRH Filter Topology

set_option autoImplicit false

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    MarkushevichBasis.IsMarkushevichBasis x f := by
  have : T2Space E := hE.2
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_, ?_⟩
  · simpa using hx.biorthogonal i i
  · simpa [hij] using hx.biorthogonal i j
  · intro u
    apply mem_closure_of_tendsto (hx.expansion u)
    exact Eventually.of_forall fun k =>
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  · intro u hu
    have hLimit : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 u) := by
      simpa [basicProjection, hu] using hx.expansion u
    exact tendsto_nhds_unique hLimit tendsto_const_nhds
