-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.eq_zero_of_forall_affineOpens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:13.395557+00:00
-- url     : https://prove2.me/submissions/e5dbb577-d698-4c58-a526-a5fe205aee11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (x : Γ(X, ⊤))
    (h : ∀ U : X.affineOpens, X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x = 0) : x = 0 :=
  X.sheaf.eq_of_locally_eq' (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge x 0 fun U ↦ (h U).trans (map_zero _).symm
end GlobalTheory.ProperFunctions
