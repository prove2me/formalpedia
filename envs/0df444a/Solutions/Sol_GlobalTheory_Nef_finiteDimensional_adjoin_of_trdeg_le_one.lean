-- Prove2me | solution 1 for GlobalTheory.Nef.finiteDimensional_adjoin_of_trdeg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:56.719692+00:00
-- url     : https://prove2.me/submissions/2f1d35c9-ec97-4378-a524-b9538fd1fa4b

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
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F ≤ 1) (x : F) (hx : Transcendental k x) :
    FiniteDimensional k⟮x⟯ F := by
  have hind : AlgebraicIndependent k (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis k (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg : Algebra.IsAlgebraic k⟮x⟯ F := by
    have := hb.isAlgebraic_field
    rwa [Set.range_const] at this
  have : Algebra.EssFiniteType k⟮x⟯ F := Algebra.EssFiniteType.of_comp k k⟮x⟯ F
  obtain ⟨S, hS⟩ := IntermediateField.fg_top_iff.mpr this
  have hfin : FiniteDimensional k⟮x⟯ (adjoin k⟮x⟯ (S : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [hS] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := k⟮x⟯) (E := F)).toLinearEquiv
end GlobalTheory.Nef
