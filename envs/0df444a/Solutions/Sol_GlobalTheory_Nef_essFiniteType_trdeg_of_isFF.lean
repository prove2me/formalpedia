-- Prove2me | solution 1 for GlobalTheory.Nef.essFiniteType_trdeg_of_isFF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:51.732802+00:00
-- url     : https://prove2.me/submissions/dba14be5-a7e3-43df-ae85-6cb5e3d6cad3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndE
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open IntermediateField
namespace GlobalTheory.Nef
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F] (h : IsFF k F) :
    Algebra.EssFiniteType k F ∧ Algebra.trdeg k F ≤ 1 := by
  obtain ⟨t, ht, hfin⟩ := h
  have h1 : Algebra.EssFiniteType k k⟮t⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{t}, by simp⟩
  refine ⟨Algebra.EssFiniteType.comp k k⟮t⟯ F, ?_⟩
  open IntermediateField.algebraAdjoinAdjoin in
  have : Algebra.IsAlgebraic (Algebra.adjoin k {t}) F := Algebra.IsAlgebraic.trans _ k⟮t⟯ _
  have hind : AlgebraicIndependent k (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis k (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr (by rwa [Set.range_const])
  rw [← hb.cardinalMk_eq_trdeg]
  simp
end GlobalTheory.Nef
