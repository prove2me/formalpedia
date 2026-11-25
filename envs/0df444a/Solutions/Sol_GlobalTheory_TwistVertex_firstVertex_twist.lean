-- Prove2me | solution 1 for GlobalTheory.TwistVertex.firstVertex_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:18.796792+00:00
-- url     : https://prove2.me/submissions/7b0069a3-6ebd-463f-81c1-21d200575305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
import Theorems.Thm_GlobalTheory_TwistVertex_embX_mem_KO
import Theorems.Thm_GlobalTheory_TwistVertex_mem_KO_of_mul_embX
import Theorems.Thm_GlobalTheory_TwistVertex_simpleSum_mem
import Theorems.Thm_GlobalTheory_TwistVertex_mem_level_iff
import Theorems.Thm_GlobalTheory_TwistVertex_level_lam
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp
import Theorems.Thm_GlobalTheory_StepData_mem_prX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TwistVertex
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((twistChain s t κ δ hδ η).lev 0 c H).J 1) : Set (GL (XIx κ t 0) k)) = KO k (XIx κ t 0) ∧ (∀ γ ∈ KO k (XIx κ t 0), ∃ hm : embX c γ ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = 1) ∧ ∀ u ∈ N k (XIx κ t 0) c 1, ∀ hm : u ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  intro k _ _ _ _ ψ hψ s t _ _ κ _ _ δ hδ η c H
  have hJ : ∀ x, x ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J ↔ x ∈ KO k (XIx κ t 0 ⊕ Fin c) :=
    fun x => mem_level_iff (hδ := hδ) (stdOrd κ t 0 c H) x
  have hl : ∀ x, ((twistChain s t κ δ hδ η).lev 0 c H).lam x = 1 :=
    fun x => level_lam (hδ := hδ) (stdOrd κ t 0 c H) x
  refine ⟨?_, fun γ hγ => ⟨(hJ _).2 (embX_mem_KO hγ), by rw [hl]; rfl⟩, fun u _ hm => ?_⟩
  · ext g
    simp only [SetLike.mem_coe, mem_prX, mem_Cgrp, hJ, inv_one, one_mul, mul_one]
    refine ⟨fun ⟨u, hu, _, h⟩ => mem_KO_of_mul_embX hu h, fun hg => ⟨1, one_mem _, ?_, ?_⟩⟩
    · rw [one_mul]; exact (le_sup_left : (embX c).range ≤ R k _ c 1) ⟨g, rfl⟩
    · rw [one_mul]; exact embX_mem_KO hg
  · rw [hl, hψ.eq_one (show _ ∈ cball (1 : kˣ) from simpleSum_mem ((hJ u).1 hm))]; rfl
end GlobalTheory.TwistVertex
