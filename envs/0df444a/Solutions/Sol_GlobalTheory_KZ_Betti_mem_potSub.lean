-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.mem_potSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:49.214857+00:00
-- url     : https://prove2.me/submissions/6c810f85-d267-4b1d-8a11-0a9630e107de

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
theorem _root_.solution {F : ℂ → MvPolynomial (Fin 2) R} : F ∈ potSub R w Γ ↔ F ∈ Pot R w Γ := by exact Iff.rfl
end GlobalTheory.KZ.Betti
