-- Prove2me | solution 1 for GroundTheory.GroupCoh.associator_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:26.003286+00:00
-- url     : https://prove2.me/submissions/aa0e2728-9764-41b4-8f0c-e5c47191aaf9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_add
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_prefix
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
import Theorems.Thm_GroundTheory_GroupCoh_associator_hom_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupₗ_apply
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {C : Rep k G} {r m l : ℕ} (h₁ : p + q = m) (h₂ : m + r = n)
    (h₃ : q + r = l) (h₄ : p + l = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B)
    (e : (Fin r → G) → C) (x : Fin n → G) :
    (α_ A B C).hom.hom (cupCochain h₂ (cupCochain h₁ f g) e x) =
      cupCochain h₄ f (cupCochain h₃ g e) x := by
  subst h₁ h₂ h₃
  simp only [cupCochain_apply]
  rw [associator_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply,
    ← map_mul, ← partialProd_add x (fun j : Fin (q + r) => x ⟨p + j, by omega⟩) (by omega)
      (fun j => rfl) (by omega), partialProd_prefix x (by omega) (by omega)]
  have hE : (fun j : Fin r => x ⟨p + (q + j), by omega⟩) = fun j : Fin r => x ⟨p + q + j, by omega⟩ :=
    funext fun j => congrArg x (Fin.ext (by simp only; omega))
  rw [hE]
end GroundTheory.GroupCoh
