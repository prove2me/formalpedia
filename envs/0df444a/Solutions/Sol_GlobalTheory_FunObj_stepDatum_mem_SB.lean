-- Prove2me | solution 1 for GlobalTheory.FunObj.stepDatum_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:01.527344+00:00
-- url     : https://prove2.me/submissions/051fa2a9-4bd8-424e-a666-16e62349a2a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution {φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ} (j : Fin (G.m - 1))
    (hφ : φ (.theta G.m j) ∈ SB _) : stepDatum hs φ j ∈ SB _ := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have key : ∀ {A B C D : Type} (a : A ≃ C) (b : B ≃ D),
      Topology.IsClosedEmbedding fun z : Matrix A B k => (z.reindex a b)ᵀ := fun a b =>
    Function.LeftInverse.isClosedEmbedding (f := fun z => zᵀ.reindex a.symm b.symm) (fun z => by simp)
      (continuous_id.matrix_transpose.matrix_reindex _ _) (continuous_id.matrix_reindex _ _).matrix_transpose
  exact ⟨hφ.1.comp_continuous (key _ _).continuous, hφ.2.comp_isClosedEmbedding (key _ _)⟩
end GlobalTheory.FunObj
