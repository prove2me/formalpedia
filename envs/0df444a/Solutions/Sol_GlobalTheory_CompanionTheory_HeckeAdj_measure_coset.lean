-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeAdj.measure_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:38.902426+00:00
-- url     : https://prove2.me/submissions/7ebd7c0f-80e6-474c-a852-795d659b0a21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HeckeAdj
theorem _root_.solution (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (q : G ⧸ K) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) = μ (K : Set G) := by
  have e : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q} = (fun h => q.out⁻¹ * h) ⁻¹' (K : Set G) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  rw [e, measure_preimage_mul]
end GlobalTheory.CompanionTheory.HeckeAdj
