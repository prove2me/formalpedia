-- Prove2me | solution 1 for GlobalTheory.PMon.homRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:22.226545+00:00
-- url     : https://prove2.me/submissions/d9b86f91-a52b-4d95-b7b6-c7324e364952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.PMon
theorem _root_.solution {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (g : G) :
    homRep ρ₁ ρ₂ g = homUnit (ρ₁ g) (ρ₂ g) := rfl
end GlobalTheory.PMon
