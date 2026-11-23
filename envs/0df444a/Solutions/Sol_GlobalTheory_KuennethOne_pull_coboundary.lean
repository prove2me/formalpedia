-- Prove2me | solution 1 for GlobalTheory.KuennethOne.pull_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:38.138451+00:00
-- url     : https://prove2.me/submissions/f6c83a77-bae6-4b5e-8db3-0c2c8549b4f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_loc
import Theorems.Thm_GlobalTheory_KuennethOne_exists_isDiff
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
theorem _root_.solution (hV : ⨆ a, V a = ⊤) {T : Scheme.{0}} (f : T ⟶ Z)
    (ρ : ∀ a, Γ(T, f ⁻¹ᵁ V a))
    (hρ : ∀ a b, (f.app (V a ⊓ V b)).hom (φ a b) =
      rs (f.preimage_mono inf_le_left) (ρ a) - rs (f.preimage_mono inf_le_right) (ρ b))
    {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (N : J → T.Opens) (hN : ∀ j, N j ≤ f ⁻¹ᵁ O j) :
    ∃ x : ∀ j, Γ(T, N j), ∀ j k (P : Z.Opens) (hj : P ≤ O j) (hk : P ≤ O k) (c : Γ(Z, P)),
      IsDiff V (ψ j) (ψ k) hj hk c → ∀ (M : T.Opens) (hMj : M ≤ N j) (hMk : M ≤ N k)
        (hM : M ≤ f ⁻¹ᵁ P), (f.appLE P M hM).hom c = rs hMj (x j) - rs hMk (x k) := by
  have hV' : ⨆ a, f ⁻¹ᵁ V a = ⊤ := by rw [← f.preimage_iSup, hV]; rfl
  let φ' : ∀ a b, Γ(T, f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b) := fun a b =>
    (f.appLE (V a ⊓ V b) _ (by rw [f.preimage_inf])).hom (φ a b)
  let ρ' : ∀ a, Γ(T, ⊤ ⊓ f ⁻¹ᵁ V a) := fun a => rs inf_le_right (ρ a)
  have h1 : Splits (fun a => f ⁻¹ᵁ V a) φ' ⊤ ρ' := by
    intro a b M _ ha hb
    have hM : M ≤ f ⁻¹ᵁ (V a ⊓ V b) := by rw [f.preimage_inf]; exact le_inf ha hb
    have := congrArg (rs hM) (hρ a b)
    rw [f.app_eq_appLE] at this
    simpa only [φ', ρ', rs_appLE, rs_rs, map_sub] using this
  let ψ' : ∀ j a, Γ(T, N j ⊓ f ⁻¹ᵁ V a) := fun j a =>
    (f.appLE (O j ⊓ V a) _ (by rw [f.preimage_inf]; exact inf_le_inf_right _ (hN j))).hom (ψ j a)
  have h2 : ∀ j, Splits (fun a => f ⁻¹ᵁ V a) φ' (N j) (ψ' j) := by
    intro j a b M hj ha hb
    have hM : M ≤ f ⁻¹ᵁ (O j ⊓ (V a ⊓ V b)) := by
      rw [f.preimage_inf, f.preimage_inf]; exact le_inf (hj.trans (hN j)) (le_inf ha hb)
    have := congrArg (f.appLE _ M hM).hom (h j a b (O j ⊓ (V a ⊓ V b)) inf_le_left
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
    simpa only [φ', ψ', rs_appLE, appLE_rs, map_sub] using this
  choose x hx using fun j => exists_isDiff hV' (h2 j) h1 le_rfl le_top
  refine ⟨x, fun j k P hj hk c hc M hMj hMk hM => loc (fun a => f ⁻¹ᵁ V a) (by rw [hV']; exact le_top)
    _ _ fun a => ?_⟩
  have e1 := hx j a (M ⊓ f ⁻¹ᵁ V a) (inf_le_left.trans hMj) inf_le_right
  have e2 := hx k a (M ⊓ f ⁻¹ᵁ V a) (inf_le_left.trans hMk) inf_le_right
  have hM' : M ⊓ f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ (P ⊓ V a) := by
    rw [f.preimage_inf]; exact inf_le_inf_right _ hM
  have e3 := congrArg (f.appLE _ _ hM').hom (hc a (P ⊓ V a) inf_le_left inf_le_right)
  simp only [ψ', ρ', rs_appLE, appLE_rs, map_sub, rs_rs] at e1 e2 e3 ⊢
  linear_combination e3 - e1 + e2
end GlobalTheory.KuennethOne
