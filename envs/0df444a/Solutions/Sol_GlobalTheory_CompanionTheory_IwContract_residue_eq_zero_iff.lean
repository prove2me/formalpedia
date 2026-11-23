-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.residue_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:36.313057+00:00
-- url     : https://prove2.me/submissions/9331261c-0a33-4487-8338-380b1df06dc5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ valuation F (algebraMap 𝒪[F] F x) < 1 := by
  have hv := Valuation.integer.integers (valuation F)
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    hv.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => ne_of_lt h⟩
end GlobalTheory.CompanionTheory.IwContract
