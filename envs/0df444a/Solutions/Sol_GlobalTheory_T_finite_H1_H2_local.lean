-- Prove2me | solution 1 for GlobalTheory.T.finite_H1_H2_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:51.250583+00:00
-- url     : https://prove2.me/submissions/03750a06-b5a6-46d0-82a5-720ccbf1ede4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteH1H2Local
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteH1H2LocalStatement
import Theorems.Thm_GlobalTheory_finite_H1_H2_of_localTateDuality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.GaloisCohomology ReciprocityTheory.Gal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  first | exact @GlobalTheory.finite_H1_H2_of_localTateDuality | exact GlobalTheory.finite_H1_H2_of_localTateDuality | (intros; apply GlobalTheory.finite_H1_H2_of_localTateDuality <;> assumption)
end _root_.GlobalTheory.T
