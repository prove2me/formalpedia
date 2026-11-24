-- Prove2me | solution 1 for GlobalTheory.Descent.fg_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:10:29.622687+00:00
-- url     : https://prove2.me/submissions/9995f5f2-85d6-4944-a769-f31455513184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory.Descent
theorem _root_.solution {N : Submodule A M} (h : (N.baseChange A').FG) : N.FG := by
  have hinj : Function.Injective (N.subtype.baseChange A') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A') N.subtype N.injective_subtype
  have e : A' ⊗[A] N ≃ₗ[A'] N.baseChange A' := LinearEquiv.ofInjective _ hinj
  have : Module.Finite A' (N.baseChange A') := Module.Finite.iff_fg.mpr h
  have : Module.Finite A' (A' ⊗[A] N) := Module.Finite.equiv e.symm
  exact Module.Finite.iff_fg.mp (finite A')
end GlobalTheory.Descent
