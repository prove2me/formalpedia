-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.span_adjoin_gen_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:47.592968+00:00
-- url     : https://prove2.me/submissions/5bf0b0a1-ba12-44bb-89bd-1d9b1d23d1d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGen
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_exists_aeval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {K : UQ} (B : InvAlg K) (hP : B.P.Separable) :
    Submodule.span K.E ((Subalgebra.toSubmodule (Algebra.adjoin K.O {B.g}) : Submodule K.O B.A) : Set B.A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, rfl⟩ := Sandwich.exists_aeval B hP x
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show B.g ^ i ∈ Algebra.adjoin K.O {B.g}
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i
end GlobalTheory.UnitLemma.Desc
