-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.intM_of_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:15.93617+00:00
-- url     : https://prove2.me/submissions/a03414e1-48b0-469a-89cc-fdd479c77262

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
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
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by
  have hM : IntM ((F.bas⁻¹).val * x * F'.bas.val) := fun a b => by
    have := h (F.ord.symm a) (F'.ord.symm b)
    simp only [LatFrame.coords, Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    exact this
  have hx : F.bas.val * ((F.bas⁻¹).val * x * F'.bas.val) * (F'.bas⁻¹).val = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [← hx]
  exact ((intM_of_mem_KO hF).mul hM).mul (mem_KO.mp hF').2
end GlobalTheory.Proof.TwistSupportPeriodicLevels
