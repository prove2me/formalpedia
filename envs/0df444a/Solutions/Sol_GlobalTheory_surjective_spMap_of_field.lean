-- Prove2me | solution 1 for GlobalTheory.surjective_spMap_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:59.868924+00:00
-- url     : https://prove2.me/submissions/7f1d9254-3555-4494-bb7e-963a4290ead2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackFieldOfIrreducibleCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F k : Type} [Field F] [Field k] (f : F →+* k) :
    Surjective (spMap f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Sp k) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩
end GlobalTheory
