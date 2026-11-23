-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_pt_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:03.970005+00:00
-- url     : https://prove2.me/submissions/10783c39-40fb-48c9-a099-8d7901d0db08

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A]
    (g : Spec (CommRingCat.of A) ⟶ X) (W : X.affineOpens)
    (hW : g (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ W.1) : ∃ p, g = pt W p := by
  have hr : Set.range g ⊆ Set.range W.2.fromSpec := by
    rw [W.2.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hs : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint x
    exact (hs.map g.continuous).mem_open W.1.2 hW
  refine ⟨(Spec.preimage (IsOpenImmersion.lift W.2.fromSpec g hr)).hom, ?_⟩
  simp [pt]
end GlobalTheory.CompanionTheory.Ultra
