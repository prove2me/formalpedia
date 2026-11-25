-- Prove2me | solution 1 for GlobalTheory.exists_mem_genericPoints_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:02.88343+00:00
-- url     : https://prove2.me/submissions/0f9572ec-d324-4363-9433-980606c711f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (w : T) : ∃ w₀ ∈ genericPoints T, w₀ ⤳ w :=
  ⟨_, (genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents w⟩).2,
    (genericPoints.isGenericPoint_ofComponent
      ⟨_, irreducibleComponent_mem_irreducibleComponents w⟩).specializes mem_irreducibleComponent⟩
end GlobalTheory
