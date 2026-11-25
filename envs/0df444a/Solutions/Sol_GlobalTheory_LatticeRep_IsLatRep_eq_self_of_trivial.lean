-- Prove2me | solution 1 for GlobalTheory.LatticeRep.IsLatRep.eq_self_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:36.321259+00:00
-- url     : https://prove2.me/submissions/3d6ff556-f7af-4842-a6bf-5ee22d6e0d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSelfOfTrivial
import Theorems.Thm_GlobalTheory_LatticeRep_transl_induction
import Theorems.Thm_GlobalTheory_LatticeRep_IsLatRep_fix_of_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeRep
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}
namespace GlobalTheory.LatticeRep
namespace IsLatRep
theorem _root_.solution (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) {g : Γ}
    (hg : ∀ x, ρ g x = x) (m : M) : Om g m = m := by
  refine transl_induction h.2.2.2.1 (p := fun m => Om g m = m) (fun x v hv => ?_) (map_zero _)
    (fun a b ha hb => by rw [map_add, ha, hb]) (fun c a ha => by rw [map_smul, ha]) m
  rw [hO.1, hg, hO.fix_of_map_le h _ hv]
  rintro _ ⟨a, ha, rfl⟩
  rw [hg]; exact ha
end IsLatRep
end GlobalTheory.LatticeRep
