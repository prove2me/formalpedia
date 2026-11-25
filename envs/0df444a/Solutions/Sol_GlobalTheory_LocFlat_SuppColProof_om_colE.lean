-- Prove2me | solution 1 for GlobalTheory.LocFlat.SuppColProof.om_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:03.723498+00:00
-- url     : https://prove2.me/submissions/70f10629-e29e-4ea1-bec9-713ed76ff311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPosition
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul


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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.SuppColProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LocFlat.SuppColProof
theorem _root_.solution {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (μ : kˣ →* ℂˣ) (g h : GL (n ⊕ Fin c) k) (hg : Matrix.GeneralLinearGroup.det g = 1)
    (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    (fun z => om μ 1 h Φ (g.val * z)) = om μ 1 (g⁻¹ * h) Φ := by
  rw [show om μ 1 (g⁻¹ * h) Φ = om μ (1 * 1) (g⁻¹ * h) Φ by rw [mul_one], om_mul]
  funext z
  have hi : Matrix.GeneralLinearGroup.det g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  simp [om, hi, nabs_one]
end GlobalTheory.LocFlat.SuppColProof
