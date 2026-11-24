-- Prove2me | solution 1 for GlobalTheory.OmAStab.isOpen_omA_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:02.973979+00:00
-- url     : https://prove2.me/submissions/453ab244-e751-4b6b-ac22-fe3b12917831

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
import Theorems.Thm_GlobalTheory_OmAStab_isLocallyConstant_of_isOpen_ker
import Theorems.Thm_GlobalTheory_OmAStab_isLocallyConstant_comp_invT
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM
open GlobalTheory GlobalTheory.OmAStab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.OmAStab
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  intro k _ _ _ _ a d ν β hβ Φ hΦ
  have hb : IsLocallyConstant fun h : GL (Fin d) k => β (gdet h) :=
    (isLocallyConstant_of_isOpen_ker β hβ).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hn : IsLocallyConstant fun h : GL (Fin d) k => GlobalTheory.SplitWeil.nabs k (gdet h) :=
    (GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hc : IsLocallyConstant fun h : GL (Fin d) k => omA ν β 1 h Φ := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
    filter_upwards [hb.eventually_eq h0, hn.eventually_eq h0,
      (isLocallyConstant_comp_invT hΦ).eventually_eq h0] with h e1 e2 e3
    funext X
    have e4 := congrFun e3 X
    simp only [omA, apow, inv_one, Units.val_one, Matrix.one_mul, e1, e2, e4]
  exact hc.isOpen_fiber Φ
end GlobalTheory.OmAStab
