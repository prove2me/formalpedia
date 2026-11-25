-- Prove2me | solution 1 for GlobalTheory.encard_fiber_orbit_mul_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:37.487549+00:00
-- url     : https://prove2.me/submissions/1fd2b33f-625e-4188-a11c-783c08a62f51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory
open MulAction
namespace GlobalTheory
theorem _root_.solution {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) (x : L) (y : Y) (g : Γ)
    (hg : g • π x = y) :
    ({z : L | π z = y ∧ z ∈ orbit Γ x}).encard * (stabilizer Γ x : Set Γ).encard
      = (stabilizer Γ y : Set Γ).encard := by
  classical
  have hx0 : π (g • x) = y := by rw [hπ, hg]
  have hset : (orbit (stabilizer Γ y) (g • x) : Set L) = {z : L | π z = y ∧ z ∈ orbit Γ x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      have hh : (h : Γ) • y = y := mem_stabilizer_iff.mp h.2
      refine ⟨?_, (h : Γ) * g, ?_⟩
      · show π ((h : Γ) • g • x) = y
        rw [hπ, hx0, hh]
      · show ((h : Γ) * g) • x = (h : Γ) • g • x
        rw [mul_smul]
    · rintro ⟨hz, k, rfl⟩
      have hk : k * g⁻¹ ∈ stabilizer Γ y := by
        rw [mem_stabilizer_iff]
        calc (k * g⁻¹) • y = (k * g⁻¹) • g • π x := by rw [hg]
          _ = π (k • x) := by rw [mul_smul, inv_smul_smul, hπ]
          _ = y := hz
      exact ⟨⟨k * g⁻¹, hk⟩, show (k * g⁻¹) • g • x = k • x by rw [mul_smul, inv_smul_smul]⟩
  have e : stabilizer (stabilizer Γ y) (g • x) ≃ stabilizer Γ x :=
    { toFun := fun s => ⟨g⁻¹ * ((s : stabilizer Γ y) : Γ) * g, by
        have hs : ((s : stabilizer Γ y) : Γ) • g • x = g • x := mem_stabilizer_iff.mp s.2
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hs, inv_smul_smul]⟩
      invFun := fun t => ⟨⟨g * (t : Γ) * g⁻¹, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          rw [mem_stabilizer_iff, ← hg, mul_smul, mul_smul, inv_smul_smul, ← hπ, ht]⟩, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          show (g * (t : Γ) * g⁻¹) • g • x = g • x
          rw [mul_smul, mul_smul, inv_smul_smul, ht]⟩
      left_inv := fun s => by
        apply Subtype.ext; apply Subtype.ext
        show g * (g⁻¹ * ((s : stabilizer Γ y) : Γ) * g) * g⁻¹ = ((s : stabilizer Γ y) : Γ)
        group
      right_inv := fun t => by
        apply Subtype.ext
        show g⁻¹ * (g * (t : Γ) * g⁻¹) * g = (t : Γ)
        group }
  have key := ENat.card_congr
    (Subgroup.groupEquivQuotientProdSubgroup (s := stabilizer (stabilizer Γ y) (g • x)))
  rw [ENat.card_prod, ← ENat.card_congr (orbitEquivQuotientStabilizer (stabilizer Γ y) (g • x)),
    ENat.card_congr e] at key
  rw [← hset]
  exact key.symm
end GlobalTheory
