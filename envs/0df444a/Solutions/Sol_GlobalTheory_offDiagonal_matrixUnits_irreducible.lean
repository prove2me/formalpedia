-- Prove2me | solution 1 for GlobalTheory.offDiagonal_matrixUnits_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:20.966262+00:00
-- url     : https://prove2.me/submissions/74e9a3cf-cf29-48f0-934f-20c2c00ba3e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OffDiagonalMatrixUnitsIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ),
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
        (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) := by
  intro r p hp hpr W h
  have hs : ∀ (j k : Fin r) (v : Fin r → ℂ),
      (Matrix.single j k (1 : ℂ)).mulVec v = v k • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j k v
    ext i
    rw [Matrix.single_mulVec]
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have key : ∀ (j k : Fin r) (v : Fin r → ℂ), v k ≠ 0 →
      (Matrix.single j k (1 : ℂ)).mulVec v ∈ W → (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro j k v hv hm
    rw [hs] at hm
    exact (W.smul_mem_iff hv).1 hm
  have up : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v k ≠ 0 →
      (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvk => key j k v hvk (h j k hj hk v hv).1
  have down : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v j ≠ 0 →
      (Pi.single k (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvj => key k j v hvj (h j k hj hk v hv).2
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : v k ≠ 0 := hk
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨p, hpr⟩
  have ha : (a : ℕ) < p := hp
  have hb : p ≤ (b : ℕ) := le_rfl
  have hbW : (Pi.single b (1 : ℂ) : Fin r → ℂ) ∈ W := by
    rcases lt_or_ge (k : ℕ) p with hkp | hkp
    · exact down k b v hkp hb hv hk'
    · exact down a b _ ha hb (up a k v ha hkp hv hk') (by simp)
  have haW : (Pi.single a (1 : ℂ) : Fin r → ℂ) ∈ W := up a b _ ha hb hbW (by simp)
  have hall : ∀ i : Fin r, (Pi.single i (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro i
    rcases lt_or_ge (i : ℕ) p with hi | hi
    · exact up i b _ hi hb hbW (by simp)
    · exact down a i _ ha hi haW (by simp)
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)
end GlobalTheory
