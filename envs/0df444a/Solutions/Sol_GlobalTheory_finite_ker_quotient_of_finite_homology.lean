-- Prove2me | solution 1 for GlobalTheory.finite_ker_quotient_of_finite_homology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:04.238241+00:00
-- url     : https://prove2.me/submissions/995ea99f-c39f-45d7-ade7-46b8580685ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    [Module.Finite R (C.homology j)] :
    Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) := by
  have e := (C.homologyIsoSc' i j k hi hk ≪≫ (C.sc' i j k).moduleCatHomologyIso).toLinearEquiv
  have h : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
    LinearMap.range (C.sc' i j k).moduleCatToCycles) := Module.Finite.equiv e
  refine Module.Finite.equiv (Submodule.quotEquivOfEq
    (LinearMap.range (C.sc' i j k).moduleCatToCycles) _ ?_)
  ext x
  exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩
end GlobalTheory
