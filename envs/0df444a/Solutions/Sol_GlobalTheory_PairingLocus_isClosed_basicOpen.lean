-- Prove2me | solution 1 for GlobalTheory.PairingLocus.isClosed_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:51.027708+00:00
-- url     : https://prove2.me/submissions/0090d0be-61de-462e-95ce-3827d4afb47d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsClopenOfIsLocallyNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLocus
namespace GlobalTheory.PairingLocus
theorem _root_.solution {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (X.basicOpen e : Set X) := by
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ X.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (X.mem_basicOpen e x trivial).2 h'
      · exact absurd ((X.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl
end GlobalTheory.PairingLocus
