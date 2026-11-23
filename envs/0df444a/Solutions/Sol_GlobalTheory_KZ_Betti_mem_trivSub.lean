-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.mem_trivSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:49.808924+00:00
-- url     : https://prove2.me/submissions/4aa07750-daa2-4ef4-aace-e109ac3b89bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti
variable {R : Type} [CommRing R]
variable {w : ℕ} {Γ : Subgroup SL(2, ℤ)}
namespace GlobalTheory.KZ.Betti
theorem _root_.solution {F : ℂ → MvPolynomial (Fin 2) R} : F ∈ trivSub R w Γ ↔ F ∈ Triv R w Γ := by exact Iff.rfl
end GlobalTheory.KZ.Betti
