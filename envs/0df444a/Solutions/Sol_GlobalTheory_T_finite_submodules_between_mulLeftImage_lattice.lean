-- Prove2me | solution 1 for GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:22:18.983526+00:00
-- url     : https://prove2.me/submissions/dc4c74e9-a45b-41e0-a42f-692e6c0b6e63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Theorems.Thm_GlobalTheory_UnitLemma_finite_between_mulLat


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  first | exact @GlobalTheory.UnitLemma.finite_between_mulLat | exact GlobalTheory.UnitLemma.finite_between_mulLat | (intros; apply GlobalTheory.UnitLemma.finite_between_mulLat <;> assumption)
end _root_.GlobalTheory.T
