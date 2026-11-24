-- Prove2me | solution 1 for GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:36.605814+00:00
-- url     : https://prove2.me/submissions/73b65afa-0ad3-4658-8208-53e14eba2d7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_succ


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
open Polynomial
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F]
    (s : F[X] → ℂ) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V']
      [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V' (e.conj g) =
        _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e g
    rw [_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ,
      e.charpoly_conj]
    congr 1
    let σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃
        {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W} :=
      (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by
        change _ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧
          ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))
        refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
        · exact ((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm
        · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
          simpa [LinearEquiv.conj_apply] using
            Submodule.mem_map_of_mem (f := (e : V →ₗ[F] V')) (h x hx)
        · have := h (e x) (Submodule.mem_map_of_mem hx)
          simpa [LinearEquiv.conj_apply, Submodule.mem_map_equiv] using this
    rw [← finsum_comp_equiv σ]
    refine finsum_congr fun W => ?_
    rw [← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]
    show _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _
    congr 1
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
