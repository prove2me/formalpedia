-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.exists_isDiam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:47.468799+00:00
-- url     : https://prove2.me/submissions/45af98b2-5ee2-4b22-9ad3-5b1eda694a65

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
namespace GlobalTheory.KZ.Betti
theorem _root_.solution {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : ∃ γ, IsDiam N l d γ := by
  have : NeZero (N * l) := ⟨Nat.mul_ne_zero hN hl⟩
  have hNl : N ∣ N * l := Dvd.intro l rfl
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNl (ZMod.unitOfCoprime d hd)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  have hdet : (!![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ),
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)] :=
    ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨γ, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · have hcast : (((u : ZMod (N * l)).val : ℕ) : ZMod N) = d := by
      rw [ZMod.natCast_val, ← ZMod.unitsMap_val hNl, hu, ZMod.coe_unitOfCoprime]
    simpa [en, hγ] using hcast
end GlobalTheory.KZ.Betti
