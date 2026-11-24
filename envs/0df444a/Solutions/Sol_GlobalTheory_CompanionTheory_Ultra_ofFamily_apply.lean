-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.ofFamily_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:23.695785+00:00
-- url     : https://prove2.me/submissions/656c44a0-dae7-4116-afda-5709098ce0d0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
variable {A : ι → Type} [∀ i, CommRing (A i)] {B : Type} [CommRing B]
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution (h : ∀ i, B → A i) (h1 hadd hmul) (b : B) :
    ofFamily U h h1 hadd hmul b = mk U (fun i => h i b) := rfl
end GlobalTheory.CompanionTheory.Ultra
