-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StdLattice.exists_nhds_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:49:16.202614+00:00
-- url     : https://prove2.me/submissions/995a5b1e-10eb-4549-8da0-11da2a89c945

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
namespace GlobalTheory.CompanionTheory.StdLattice
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {f : G → ℂ}
    (hf : f ∈ SB G) : ∀ᶠ u in 𝓝 (0 : G), ∀ y ∈ tsupport f, f (y + u) = f y := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  obtain ⟨hlc, hcs⟩ := hf'
  have hg : IsLocallyConstant (fun z : G × G => f (z.2 + z.1)) :=
    hlc.comp_continuous (continuous_snd.add continuous_fst)
  have hg2 : IsLocallyConstant (fun z : G × G => f z.2) := hlc.comp_continuous continuous_snd
  refine hcs.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
  filter_upwards [hg.eventually_eq (0, y), hg2.eventually_eq (0, y)] with z hz1 hz2
  exact hz1.trans ((congrArg f (add_zero y)).trans hz2.symm)
end GlobalTheory.CompanionTheory.StdLattice
