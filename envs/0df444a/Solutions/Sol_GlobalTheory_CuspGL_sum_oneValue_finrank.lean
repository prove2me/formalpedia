-- Prove2me | solution 1 for GlobalTheory.CuspGL.sum_oneValue_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:14.036823+00:00
-- url     : https://prove2.me/submissions/7b103a1d-1219-4fe3-b529-e8892d919a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Theorems.Thm_GlobalTheory_QBinomialSum_sum_gaussian_mul_prod
import Theorems.Thm_GlobalTheory_T_card_subspaces_of_finrank_mul_card_bases


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, oneValue (Nat.card F) (Module.finrank F W) = (Module.finrank F V : ℂ) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := GlobalTheory.QBinomialSum.sum_gaussian_mul_prod (Nat.card F) (Module.finrank F V)
    (fun a => Nat.card {W : Submodule F V // Module.finrank F W = a}) hq
    (fun a ha => GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha)
  rw [← h, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Icc 0 (Module.finrank F V))
    (g := fun W : Submodule F V => Module.finrank F W)
    (fun W _ => Finset.mem_Icc.2 ⟨Nat.zero_le _, W.finrank_le⟩)]
  have h2 : ∀ a : ℕ, ∑ W ∈ Finset.univ.filter (fun W : Submodule F V => Module.finrank F W = a),
      oneValue (Nat.card F) (Module.finrank F W) =
      (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * oneValue (Nat.card F) a := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => oneValue (Nat.card F) a)
      (fun W hW => by rw [(Finset.mem_filter.1 hW).2]), Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = a}), Fintype.card_subtype]
  simp only [h2]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) ?_ ?_
  · intro a ha
    have : a = 0 := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]
  · intro a ha
    have : a ≠ 0 := by
      simp only [Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]
end GlobalTheory.CuspGL
