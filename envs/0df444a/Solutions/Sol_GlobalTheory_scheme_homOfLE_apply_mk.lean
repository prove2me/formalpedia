-- Prove2me | solution 1 for GlobalTheory.scheme_homOfLE_apply_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:43.576568+00:00
-- url     : https://prove2.me/submissions/604a6693-67a5-4ea2-a64c-cab4be67ecae

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
theorem _root_.solution {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (x : X) (hx : x ∈ V) :
    (X.homOfLE e) ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  apply Subtype.ext
  have h1 : (X.homOfLE e ≫ U.ι) ⟨x, hx⟩ = V.ι ⟨x, hx⟩ := by rw [X.homOfLE_ι]
  simpa using h1
end GlobalTheory
