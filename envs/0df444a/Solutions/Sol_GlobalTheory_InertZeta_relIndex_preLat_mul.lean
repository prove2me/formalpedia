-- Prove2me | solution 1 for GlobalTheory.InertZeta.relIndex_preLat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:52.354533+00:00
-- url     : https://prove2.me/submissions/2a3d6112-477a-4ad6-b997-0ef6964f9c79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
import Theorems.Thm_GlobalTheory_InertZeta_intV_vecMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {A D a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (ea : a' * a = 1)
    (hpre : ∀ r, r ∈ preLat A ↔ r ᵥ* a ∈ preLat D) :
    (intV L n).relIndex (preLat A) = (intV L n).relIndex (preLat D) := by
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hf : ∀ r, f r = r ᵥ* a := fun r => rfl
  have hsurj : Function.Surjective f := fun y => ⟨y ᵥ* a', by rw [hf, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : preLat A = (preLat D).comap f := by
    ext r; rw [AddSubgroup.mem_comap, hf]; exact hpre r
  have h2 : intV L n = (intV L n).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hf]
    refine ⟨fun h => intV_vecMul h ha, fun h => ?_⟩
    have := intV_vecMul h ha'
    rwa [Matrix.vecMul_vecMul, ea2, Matrix.vecMul_one] at this
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj, ← h2]
end GlobalTheory.InertZeta
