-- Prove2me | solution 1 for GlobalTheory.CentralExponent.exists_cong_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:57.095038+00:00
-- url     : https://prove2.me/submissions/2b9f464e-f3f4-44fc-bc51-c4b160ea064e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CentralExponent
theorem _root_.solution {U : Set (GL n k)} (hU : U ∈ 𝓝 (1 : GL n k)) :
    ∃ (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), ∀ g ∈ cong n γ hγ, g ∈ U := by
  rw [SplitFlip.isEmbedding_val_GL.nhds_eq_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have h1 : (fun A : Matrix n n k => A + 1) ⁻¹' T ∈ 𝓝 (0 : Matrix n n k) :=
    (continuous_add_right _).continuousAt.preimage_mem_nhds (by simpa using hT)
  have h2 : Tendsto (fun p : (ValueGroupWithZero k)ˣ × Matrix n n k =>
      if ∀ i j, valuation k (p.2 i j) < p.1 then p.2 else 0) (atBot ×ˢ ⊤) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [Matrix.zero_apply, (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    filter_upwards [prod_mem_prod (mem_atBot γ) univ_mem] with p hp
    split_ifs with h
    · exact (h i j).trans_le hp.1
    · simp
  obtain ⟨γ, hγ1, hγ⟩ := ((eventually_le_atBot 1).and (mem_prod_top.1 (h2 h1))).exists
  refine ⟨γ, hγ1, fun g hg => hTU ?_⟩
  have := hγ (g.val - 1)
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  rw [Set.mem_preimage, Set.mem_preimage, if_pos hg', sub_add_cancel] at this
  exact this
end GlobalTheory.CentralExponent
