-- Prove2me | solution 1 for GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:08.106597+00:00
-- url     : https://prove2.me/submissions/c96353dc-f6b6-4a19-937c-0929b3f6113f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFiniteStatement
import Theorems.Thm_GlobalTheory_UnitLemma_OrbitFinite_orbits_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.OrbitFinite.orbits_finite | exact GlobalTheory.UnitLemma.OrbitFinite.orbits_finite | (intros; apply GlobalTheory.UnitLemma.OrbitFinite.orbits_finite <;> assumption)
end _root_.GlobalTheory.T
