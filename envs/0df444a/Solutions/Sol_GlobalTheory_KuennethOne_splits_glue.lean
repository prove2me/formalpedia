-- Prove2me | solution 1 for GlobalTheory.KuennethOne.splits_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:37.74056+00:00
-- url     : https://prove2.me/submissions/3a7478f8-aef1-41e2-9ca4-8a8f24f6e98d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_glue
import Theorems.Thm_GlobalTheory_KuennethOne_loc
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
theorem _root_.solution {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (g : ∀ j, Γ(Z, O j))
    (hg : ∀ j k a (M : Z.Opens) (hj : M ≤ O j) (hk : M ≤ O k) (ha : M ≤ V a),
      rs (le_inf hj ha) (ψ j a) - rs (le_inf hk ha) (ψ k a) = rs hj (g j) - rs hk (g k))
    (O₀ : Z.Opens) (hc : O₀ ≤ iSup O) : ∃ χ, Splits V φ O₀ χ := by
  have key : ∀ a, ∃ χ : Γ(Z, O₀ ⊓ V a), ∀ j,
      rs (inf_le_left : O₀ ⊓ V a ⊓ O j ≤ O₀ ⊓ V a) χ =
        rs (le_inf inf_le_right (inf_le_left.trans inf_le_right)) (ψ j a) -
          rs inf_le_right (g j) := by
    intro a
    refine glue (O₀ ⊓ V a) (fun j => O₀ ⊓ V a ⊓ O j) (fun j => inf_le_left) ?_ _ ?_
    · rw [← inf_iSup_eq]
      exact le_inf le_rfl (inf_le_left.trans hc)
    · intro j k
      have e := hg j k a (O₀ ⊓ V a ⊓ O j ⊓ (O₀ ⊓ V a ⊓ O k)) (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans inf_le_right))
      simp only [map_sub, rs_rs]
      linear_combination e
  choose χ hχ using key
  refine ⟨χ, fun a b N hO ha hb => loc O (hO.trans hc) _ _ fun j => ?_⟩
  have e1 := congrArg (rs (inf_le_inf_right (O j) (le_inf hO ha))) (hχ a j)
  have e2 := congrArg (rs (inf_le_inf_right (O j) (le_inf hO hb))) (hχ b j)
  have e3 := h j a b (N ⊓ O j) inf_le_right (inf_le_left.trans ha) (inf_le_left.trans hb)
  simp only [map_sub, rs_rs] at e1 e2 ⊢
  linear_combination e3 - e1 + e2
end GlobalTheory.KuennethOne
