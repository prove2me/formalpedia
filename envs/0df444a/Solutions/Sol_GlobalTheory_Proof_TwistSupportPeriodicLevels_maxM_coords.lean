-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.maxM_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:49.766962+00:00
-- url     : https://prove2.me/submissions/e921e12f-fff4-45a8-9ea6-3d93c7a62cb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {y : Matrix Y Y' k} (h : MaxM y) : MaxM (F.coords F' y) := by
  have hM : MaxM ((F.bas⁻¹).val * y * F'.bas.val) :=
    ((mem_KO.mp hF).2.mul_maxM h).mul_intM (intM_of_mem_KO hF')
  show MaxM (((F.bas⁻¹).val * y * F'.bas.val).submatrix F.ord F'.ord)
  exact fun i j => hM (F.ord i) (F'.ord j)
end GlobalTheory.Proof.TwistSupportPeriodicLevels
