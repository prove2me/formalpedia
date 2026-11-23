-- Prove2me | solution 1 for GlobalTheory.KuennethOne.exists_isDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:37.62489+00:00
-- url     : https://prove2.me/submissions/f4dbc54e-63a3-44ab-b380-262696179f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_glue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.KuennethOne
variable {Z : Scheme.{0}}
variable {I : Type} (V : I → Z.Opens) (φ : ∀ a b, Γ(Z, V a ⊓ V b))
variable {V φ}
namespace GlobalTheory.KuennethOne
theorem _root_.solution (hV : ⨆ a, V a = ⊤) {O O' P : Z.Opens} {ψ : ∀ a, Γ(Z, O ⊓ V a)}
    {ψ' : ∀ a, Γ(Z, O' ⊓ V a)} (h : Splits V φ O ψ) (h' : Splits V φ O' ψ')
    (hO : P ≤ O) (hO' : P ≤ O') : ∃ c : Γ(Z, P), IsDiff V ψ ψ' hO hO' c := by
  obtain ⟨c, hc⟩ := glue P (fun a => P ⊓ V a) (fun a => inf_le_left)
    (by rw [← inf_iSup_eq, hV]; simp)
    (fun a => rs (inf_le_inf_right _ hO) (ψ a) - rs (inf_le_inf_right _ hO') (ψ' a)) (by
      intro a b
      have hP : P ⊓ V a ⊓ (P ⊓ V b) ≤ P := inf_le_left.trans inf_le_left
      have ha : P ⊓ V a ⊓ (P ⊓ V b) ≤ V a := inf_le_left.trans inf_le_right
      have hb : P ⊓ V a ⊓ (P ⊓ V b) ≤ V b := inf_le_right.trans inf_le_right
      have e1 := h a b _ (hP.trans hO) ha hb
      have e2 := h' a b _ (hP.trans hO') ha hb
      simp only [map_sub, rs_rs]
      linear_combination e2 - e1)
  refine ⟨c, fun a M hM ha => ?_⟩
  have := congrArg (rs (le_inf hM ha)) (hc a)
  simpa only [map_sub, rs_rs] using this
end GlobalTheory.KuennethOne
