-- Prove2me | solution 1 for GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:03.206851+00:00
-- url     : https://prove2.me/submissions/def70807-7f61-4db0-a88d-c2a6fc02550f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftEqMapOfSpanningLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftEqMapOfSpanningLatticeStatement
import Theorems.Thm_GlobalTheory_charpoly_mulLeft_eq_map_of_spanning_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R F A S : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A] [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S] [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A), Function.Injective ι → Submodule.span F (Set.range ι) = ⊤ → ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly = ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  first | exact @GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | exact GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | (intros; apply GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice <;> assumption)
end _root_.GlobalTheory.T
