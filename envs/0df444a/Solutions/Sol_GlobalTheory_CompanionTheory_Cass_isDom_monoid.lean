-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cass.isDom_monoid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:14.592726+00:00
-- url     : https://prove2.me/submissions/0c9ea0a1-7ff3-4b31-b62f-fe8a97779408

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsDomMonoid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep PositivityTheory.SphericalProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cass
namespace GlobalTheory.CompanionTheory.Cass
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), D.IsDom 1 ∧ ∀ t t' : D.T, D.IsDom t → D.IsDom t' → D.IsDom (t * t') := by
  intro G _ _ _ D
  refine ⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn,
    fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩
  rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · have h := h1 _ (h1' n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := h2' _ (h2 n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3 _ (h3' x hx).1).1
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3' _ (h3 x hx).2).2
    rw [Subgroup.coe_mul]
    convert h using 1
    group
end GlobalTheory.CompanionTheory.Cass
