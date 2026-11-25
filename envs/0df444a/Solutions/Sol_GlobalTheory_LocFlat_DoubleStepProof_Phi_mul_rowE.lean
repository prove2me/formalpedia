-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.Phi_mul_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:13.988732+00:00
-- url     : https://prove2.me/submissions/1ac9aba4-776b-4126-a4be-0824bbe82e32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_P2M_GlobalTheory_LocFlat_DoubleStepProof_det_rowE__5b352327b95b
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_rowE_mem_lev
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_laws


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution (hP : S.Pattern t) (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (hc : c = 2 * r)
    (u : XIx (Fin κ) t (j + 1) → k) (hu : u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1))) :
    ∃ a : ℂ, ∀ y, (S.T t).Phi (j + 1) (c + 1) H (y * (rowE (c + 1 + 1) (r + 1) u).val) =
      a * (S.T t).Phi (j + 1) (c + 1) H y := by
  have hL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  have hm := rowE_mem_lev S t hP j c H r hc u hu
  have h1 := (hL.1 (j + 1) (c + 1) H).1 ⟨_, hm⟩
  refine ⟨((((S.T t).lev (j + 1) (c + 1 + 1) (by omega)).lam ⟨_, hm⟩ : ℂˣ) : ℂ), fun y => ?_⟩
  have h2 := congrFun h1 y
  simp only [om, det_rowE', map_one, inv_one, Units.val_one, nabs_one, Real.one_rpow, Complex.ofReal_one, one_mul,
    Matrix.one_mul, Pi.smul_apply, smul_eq_mul] at h2
  exact h2
end GlobalTheory.LocFlat.DoubleStepProof
