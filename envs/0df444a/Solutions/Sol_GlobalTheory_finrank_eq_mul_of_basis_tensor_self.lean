-- Prove2me | solution 1 for GlobalTheory.finrank_eq_mul_of_basis_tensor_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:40.626304+00:00
-- url     : https://prove2.me/submissions/5bfb0ae7-07bc-417d-be5b-80c4387fa814

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Theorems.Thm_GlobalTheory_nonempty_basis_of_basis_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory
open TensorProduct Module
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (k B A : Type) [Field k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Finite k A] (r : ℕ)
    (hinj : Function.Injective (algebraMap B A))
    (hb : Nonempty (Module.Basis (Fin r) A (TensorProduct B A A))) :
    Module.finrank k A = r * Module.finrank k B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Subsingleton A := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_zero (algebraMap B A), ← map_one (algebraMap B A), Subsingleton.elim (0 : B) 1]
    simp [Module.finrank_zero_of_subsingleton]
  haveI : Module.Finite k B :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom k B A).toLinearMap hinj
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite k B A
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  obtain ⟨β⟩ := _root_.GlobalTheory.nonempty_basis_of_basis_baseChange (M := A) hinj hb.some
  haveI : Module.Free B A := Module.Free.of_basis β
  rw [← Module.finrank_mul_finrank k B A, finrank_eq_card_basis β, Fintype.card_fin, mul_comm]
end _root_.GlobalTheory
end GlobalTheory
