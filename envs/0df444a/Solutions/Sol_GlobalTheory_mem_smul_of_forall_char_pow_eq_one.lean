-- Prove2me | solution 1 for GlobalTheory.mem_smul_of_forall_char_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:29.828797+00:00
-- url     : https://prove2.me/submissions/e393d52b-d03c-4f30-b20e-06817038bb6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSmulOfForallCharPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (k : ℕ) (hk : (k : F) ≠ 0) (d : X)
    (hd : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd d) = 1) :
    ∃ z : X, d = k • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  by_contra hne
  push_neg at hne
  have hex : ∃ i, ¬ (k : ℤ) ∣ b.repr d i := by
    by_contra h
    push_neg at h
    apply hne (∑ i, (b.repr d i / k) • b i)
    apply b.repr.injective
    ext j
    rw [← natCast_zsmul]
    simp [map_sum, Finsupp.single_apply, Int.mul_ediv_cancel' (h j)]
  obtain ⟨i, hi⟩ := hex
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (by simp)
  haveI : NeZero (k : F) := ⟨hk⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk0
  let u : Fˣ := Units.mk0 ζ hζ0
  have hu : IsPrimitiveRoot u k := IsPrimitiveRoot.coe_units_iff.mp (by simpa [u] using hζ)
  let τ : Multiplicative X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hτ : ∀ x : X, τ (Multiplicative.ofAdd x) = u ^ (b.repr x i) := by
    intro x; simp [τ]
  have hτk : τ ^ k = 1 := by
    ext x
    show (τ x ^ k : Fˣ).val = (1 : Fˣ).val
    congr 1
    rw [← ofAdd_toAdd x, hτ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hu.pow_eq_one, one_zpow]
  have h1 := hd τ hτk
  rw [hτ] at h1
  exact hi ((hu.zpow_eq_one_iff_dvd _).1 h1)
end GlobalTheory
