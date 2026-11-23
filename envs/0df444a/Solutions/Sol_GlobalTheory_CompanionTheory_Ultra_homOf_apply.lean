-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.homOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:34.055824+00:00
-- url     : https://prove2.me/submissions/b064eeec-df69-4d3a-a8b1-f92f3371c14c

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
theorem _root_.solution (h : ∀ i, B → A i) (hh : IsAEHom U h) (b : B) :
    homOf U h hh b = mk U (fun i => h i b) := rfl
end GlobalTheory.CompanionTheory.Ultra
