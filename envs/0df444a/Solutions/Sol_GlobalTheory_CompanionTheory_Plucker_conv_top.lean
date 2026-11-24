-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.conv_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:13.419244+00:00
-- url     : https://prove2.me/submissions/b5e1e61a-6b85-4cda-8697-8aaa2a1fae7d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution {G : Type} [Group G] (Γ P : Subgroup G) (hP : P = ⊤) (l : G → ℝ) : Conv Γ P l := by
  subst hP
  intro g
  haveI : Subsingleton (Cos (⊤ : Subgroup G) Γ) := ⟨fun a b => by
    induction a using Quotient.inductionOn with | _ x => ?_
    induction b using Quotient.inductionOn with | _ y => ?_
    refine Quotient.sound ?_
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
    trivial⟩
  exact summable_of_finite_support (Set.toFinite _)
end GlobalTheory.CompanionTheory.Plucker
