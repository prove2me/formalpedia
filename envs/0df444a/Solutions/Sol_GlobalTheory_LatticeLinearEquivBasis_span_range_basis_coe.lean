-- Prove2me | solution 1 for GlobalTheory.LatticeLinearEquivBasis.span_range_basis_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:58.951998+00:00
-- url     : https://prove2.me/submissions/271f9ef5-cb63-4048-8a64-efadb0ddc62a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsLinearEquivMapLatticeEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.LatticeLinearEquivBasis
open Module
namespace GlobalTheory.LatticeLinearEquivBasis
theorem _root_.solution {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (A : Submodule R V) (b : Basis ι R A) :
    Submodule.span R (Set.range fun i => (b i : V)) = A := by
  have h : Set.range (fun i => (b i : V)) = A.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
end GlobalTheory.LatticeLinearEquivBasis
