-- Prove2me | solution 1 for GlobalTheory.ClassParam.exists_unit_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:31.701745+00:00
-- url     : https://prove2.me/submissions/b03342fd-ee0b-4bb1-9235-22b61756d2ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_inclPlus_injective
import Theorems.Thm_GlobalTheory_ClassParam_star_fixed_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution (hP : IsPPol c r P) {x : AdjoinRoot P ⊗[F] k} (hu : IsUnit x)
    (hx : starLk k hP x = x) : ∃ x₀ : (Lplus hP ⊗[F] k)ˣ, inclPlus k hP x₀ = x := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨w, hw⟩ := (star_fixed_iff k hP _).1 hx
  have h2 : starLk k hP ((u⁻¹ : _ˣ) : AdjoinRoot P ⊗[F] k) = (u⁻¹ : _ˣ) := by
    apply Units.eq_inv_of_mul_eq_one_left
    rw [← hx, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨w', hw'⟩ := (star_fixed_iff k hP _).1 h2
  have h3 : w * w' = 1 := inclPlus_injective k hP (by rw [map_mul, hw, hw', map_one, Units.mul_inv])
  exact ⟨Units.mkOfMulEqOne w w' h3, hw⟩
end GlobalTheory.ClassParam
