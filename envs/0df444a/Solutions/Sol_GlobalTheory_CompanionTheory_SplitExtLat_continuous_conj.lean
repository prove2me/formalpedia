-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitExtLat.continuous_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:49.28693+00:00
-- url     : https://prove2.me/submissions/beb17569-ee0c-48ef-884e-82b2a46fb600

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_splitHomeo_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply

set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]
namespace GlobalTheory.CompanionTheory.SplitExtLat
theorem _root_.solution [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) :
    Continuous fun z : G₁ × π.ker => MulAut.conjNormal (ι z.1) z.2 := by
  refine Continuous.subtype_mk (f := fun z : G₁ × π.ker => ι z.1 * (z.2 : P) * (ι z.1)⁻¹) ?_ _
  fun_prop
end GlobalTheory.CompanionTheory.SplitExtLat
