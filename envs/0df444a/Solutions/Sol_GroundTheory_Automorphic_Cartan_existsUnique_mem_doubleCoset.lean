-- Prove2me | solution 1 for GroundTheory.Automorphic.Cartan.existsUnique_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:19.388494+00:00
-- url     : https://prove2.me/submissions/4d99bebd-cc2a-49f7-9ecd-9f8ccb37df22

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulLeftCancelOfDetNeZero
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix
open GroundTheory.Automorphic.Cartan
open ValuativeRel GLnLocal DoubleCoset
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Cartan
theorem _root_.solution (g : GL (Fin n) F) :
    ∃! μ : Fin n → ℤ, IsDominant μ ∧
      g ∈ doubleCoset (diagPow F n μ) (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) := by
  obtain ⟨μ, hμ, h⟩ := exists_eq_mul_diagPow_mul F n g
  exact ⟨μ, ⟨hμ, (mem_doubleCoset_diagPow F n).mpr h⟩,
    fun ν hν => (eq_of_mem_doubleCoset F n hν.1 hμ hν.2 ((mem_doubleCoset_diagPow F n).mpr h))⟩
end GroundTheory.Automorphic.Cartan
