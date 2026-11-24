-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_one_eq_oneValue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:13.347465+00:00
-- url     : https://prove2.me/submissions/d2aa41a5-2abf-4ec9-b362-9ee9c0f835ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Theorems.Thm_GlobalTheory_CuspGL_sum_oneValue_finrank
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq


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
theorem _root_.solution (F : Type) [Field F] [Finite F] (s : F[X] → ℂ)
    (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = n →
      psi s V 1 = oneValue (Nat.card F) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn
    classical
    haveI : Finite V := Module.finite_of_finite F
    haveI : Fintype (Submodule F V) := Fintype.ofFinite _
    have hc : LinearMap.charpoly (1 : Module.End F V) = (X - C 1) ^ n := by
      rw [LinearMap.charpoly_one, hn, C_1]
    rw [psi_eq, hc, hs]
    have h1 : ∀ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, (1 : Module.End F V) x ∈ W},
        psi s W.1 ((1 : Module.End F V).restrict W.2.2) = oneValue (Nat.card F) (Module.finrank F W.1) := by
      intro W
      have : (1 : Module.End F V).restrict W.2.2 = (1 : Module.End F W.1) := by
        ext x
        rfl
      rw [this]
      exact ih _ (hn ▸ Submodule.finrank_lt W.2.1) _ rfl
    rw [finsum_congr h1, finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (Finset.univ.erase (⊤ : Submodule F V)) (by intro W; simp)
        (fun W : Submodule F V => oneValue (Nat.card F) (Module.finrank F W))]
    have h2 := sum_oneValue_finrank F V
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊤ : Submodule F V)), finrank_top, hn] at h2
    rw [← h2]
    ring
end GlobalTheory.CuspGL
