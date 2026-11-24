-- Prove2me | solution 1 for GlobalTheory.isClosed_torusZariski_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:28.249418+00:00
-- url     : https://prove2.me/submissions/a6274374-d333-4df8-9ca9-207cc27968ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]
namespace GlobalTheory
theorem _root_.solution (H : Set (Multiplicative X →* Rˣ)) :
    IsClosed[torusZariski R X] H ↔
      ∃ S : Set (AddMonoidAlgebra R X), ∀ t, t ∈ H ↔ ∀ f ∈ S, torusEval t f = 0 := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).1 hZ
    exact ⟨S, fun t => by simp [Set.subset_def]⟩
  · rintro ⟨S, hS⟩
    refine ⟨PrimeSpectrum.zeroLocus S, PrimeSpectrum.isClosed_zeroLocus S, ?_⟩
    ext t
    simp [Set.subset_def, hS]
end GlobalTheory
