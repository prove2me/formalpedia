-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FormalClosed.mem_of_forall_mem_over_closedFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:43.7461+00:00
-- url     : https://prove2.me/submissions/1d6a5e04-8622-4299-97b6-7123cc9b528a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsIsoOfIsClosedImmersionOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalClosed
open GlobalTheory.ThickeningClosed
namespace GlobalTheory.CompanionTheory.FormalClosed
theorem _root_.solution {R : Type} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {W : Set X} (hW : IsOpen W)
    (h : ∀ x, I ≤ (f x).asIdeal → x ∈ W) (x : X) : x ∈ W := by
  by_contra hx
  have hZ : IsClosed (f '' Wᶜ) := f.isClosedMap _ hW.isClosed_compl
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (f x).asIdeal (f x).isPrime.ne_top
  let p : PrimeSpectrum (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have h1 : p ∈ closure ({f x} : Set (PrimeSpectrum (CommRingCat.of R))) :=
    (PrimeSpectrum.le_iff_mem_closure (f x) p).1 hle
  have hfx : f x ∈ f '' Wᶜ := ⟨x, hx, rfl⟩
  have hp : p ∈ f '' Wᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hfx) hZ h1
  obtain ⟨z, hz, hzp⟩ := hp
  apply hz
  apply h z
  rw [hzp]
  show I ≤ m
  refine hI.trans ?_
  unfold Ideal.jacobson
  exact sInf_le ⟨bot_le, hm⟩
end GlobalTheory.CompanionTheory.FormalClosed
