-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.isCompact_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:51.176367+00:00
-- url     : https://prove2.me/submissions/5cc89d4d-000e-45c6-acf7-133adbf84811

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ValueGroupWithZero k) :
    IsCompact {g : GL ι k | Bd γ g.val ∧ Bd γ (g⁻¹).val} := by
  haveI := t2Space k
  have hB : IsCompact {x : Matrix ι ι k | Bd γ x} := by
    have := isCompact_univ_pi (fun _ : ι => isCompact_univ_pi
      (fun _ : ι => IsNonarchimedeanLocalField.isCompact_closedBall k γ))
    have e : {x : Matrix ι ι k | Bd γ x} =
        (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => {x : k | valuation k x ≤ γ} : Set (ι → ι → k)) := by
      ext x
      exact ⟨fun h r _ s _ => h r s, fun h r s => h r trivial s trivial⟩
    rw [e]
    exact this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix ι ι k)).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  convert this using 1
  ext g
  refine and_congr_right fun _ => ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
  rintro ⟨x, hx, e⟩
  obtain rfl : x = (g⁻¹).val := MulOpposite.op_injective e
  exact hx
end GlobalTheory.RootEx.Supp
