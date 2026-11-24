-- Prove2me | solution 1 for GlobalTheory.AugCot.finrank_eq_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:05.105489+00:00
-- url     : https://prove2.me/submissions/f852ea12-02c4-49a5-bab9-3df412da3312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)
namespace GlobalTheory.AugCot
theorem _root_.solution [Nontrivial R] [Module.Free A Ω[A⁄R]] :
    Module.finrank R (AugCot ε) = Module.finrank A Ω[A⁄R] := by
  letI : Algebra A R := (ε : A →+* R).toAlgebra
  haveI : Nontrivial A := (ε : A →+* R).domain_nontrivial
  rw [(kaehlerEquiv ε (fun _ => rfl)).finrank_eq, Module.finrank_baseChange]
end GlobalTheory.AugCot
