-- Prove2me | solution 1 for GlobalTheory.SharpGradient.norm_Wm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:55.927462+00:00
-- url     : https://prove2.me/submissions/a4615f30-e092-4410-91d4-e29b9a58780a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SharpGradient
theorem _root_.solution {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (m : Fin (r - X.p0))
    (b : Fin X.p0) :
    ‖ExF.Wm X z τ m b‖ ^ 2 ≤ ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0 := by
  have hlt : Fin.castLE X.p0_le b < ExF.qI X m := by
    rw [Fin.lt_def]
    have := b.isLt
    simp only [ExF.qI, Fin.val_castLE]
    omega
  have h := Finset.single_le_sum (f := fun e : Ent X =>
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0) (fun e _ => by split_ifs <;> positivity)
      (Finset.mem_univ (⟨τ, ⟨(ExF.qI X m, Fin.castLE X.p0_le b), hlt⟩⟩ : Ent X))
  refine le_trans (le_of_eq ?_) h
  have hc : ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 ∧ X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) :=
    ⟨b.isLt, by simp [ExF.qI]⟩
  simp only [if_pos hc]
  simp [ExF.Wm, ExF.nM, mat, nmat, hlt]
end GlobalTheory.SharpGradient
