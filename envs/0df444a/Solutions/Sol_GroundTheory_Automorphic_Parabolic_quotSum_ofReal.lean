-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.quotSum_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:05.037142+00:00
-- url     : https://prove2.me/submissions/aecb1d37-1532-4528-8785-bcc0d37f791e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotSum_def


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out) :
    quotSum H (fun g => (Φ g : ℂ)) = ((quotSum H Φ : ℝ) : ℂ) := by
  rw [quotSum_def, quotSum_def]
  exact (map_finsum Complex.ofRealHom hfin).symm
end GroundTheory.Automorphic.Parabolic
