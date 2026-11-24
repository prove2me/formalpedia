-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:54.159623+00:00
-- url     : https://prove2.me/submissions/767d04f3-120b-4caf-9fd6-a9ff72bae9a5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProjMemFixedPiN

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
theorem _root_.solution (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : fixed π D.J) : D.proj π (v : V) ∈ fixed (D.piN π) D.JT := by
  intro t
  have ht : ((t : D.T) : G) ∈ D.J := Subgroup.mem_comap.mp t.2
  have hv : π ((t : D.T) : G) (v : V) = (v : V) := by
    have h := v.2 ⟨((t : D.T) : G), ht⟩
    simpa using h
  have hq : (D.piN π) (t : D.T) (D.proj π (v : V)) = D.proj π (π ((t : D.T) : G) (v : V)) := rfl
  rw [hq, hv, MonoidHom.one_apply, Units.val_one, one_smul]
end GlobalTheory.CompanionTheory.Cass
