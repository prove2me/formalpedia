-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_has_peak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:51.375669+00:00
-- url     : https://prove2.me/submissions/548c362a-33e8-4e23-88e8-ad07825c96b2

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_mem_clusterUpperSet_self
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_le_one_iff

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularSuperlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_clusterUpperSet_has_peak_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hf : (G.clusterUpperSet ω v).Finite) :
    ∃ y∈G.cluster ω v, G.clusterPeak ω y ∧
      G.peakBound hf.toFinset.card ω y := by
  obtain ⟨y,hy,hmax⟩ := hf.toFinset.exists_max_image (G.stabilizerWeight v)
    ⟨v,hf.mem_toFinset.mpr (G.mem_clusterUpperSet_self ω v)⟩
  have hy' := hf.mem_toFinset.mp hy
  have hbound (z : V) (hz : z∈G.cluster ω v) : G.stabilizerWeight v z ≤ G.stabilizerWeight v y := by
    by_cases h : 1≤G.stabilizerWeight v z
    · exact hmax z (hf.mem_toFinset.mpr ⟨hz,h⟩)
    · exact (le_of_not_ge h).trans hy'.2
  have hpeak : G.clusterPeak ω y := by
    intro z hz
    exact (G.stabilizerWeight_le_one_iff hc hl v y z).mpr (hbound z (hy'.1.trans hz))
  refine ⟨y,hy'.1,hpeak,hf.toFinset,le_rfl,?_⟩
  intro z hz
  apply hf.mem_toFinset.mpr
  refine ⟨hy'.1.trans hz.1,?_⟩
  exact hy'.2.trans ((G.stabilizerWeight_le_one_iff hc hl v z y).mp (hz.2 y hz.1.symm))

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_has_peak_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_has_peak_oai.{u_1, u_2}
