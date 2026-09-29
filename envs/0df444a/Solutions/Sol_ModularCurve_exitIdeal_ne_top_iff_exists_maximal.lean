-- Prove2me | solution 1 for ModularCurve.exitIdeal_ne_top_iff_exists_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2adb56e5-1337-5d9a-9095-fecc08a27c69

import Mathlib
import Definitions.Def_ModularCurve_SupportTransfer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exitIdeal_ne_top_iff_exists_maximal

theorem exitIdeal_le_iff_aux (N : ℕ) [NeZero N] (W : WeierstrassCurve ℤ) (p : ℕ)
    {𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N})} :
    ModularCurve.exitIdeal N W p ≤ 𝔪₁ ↔
      ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) ∈ 𝔪₁ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), W.IsGoodPrimeFor ℓ → ℓ ≠ p →
        ModularCurve.exitGen N W ℓ hℓ hℓN ∈ 𝔪₁ := by
  rw [ModularCurve.exitIdeal, Ideal.span_le]
  constructor
  · intro h
    exact ⟨h (Set.mem_insert _ _),
      fun ℓ hℓ hℓN hgood hℓp => h (Set.mem_insert_of_mem _ ⟨ℓ, hℓ, hℓN, hgood, hℓp, rfl⟩)⟩
  · rintro ⟨hp, hgen⟩ x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨ℓ, hℓ, hℓN, hgood, hℓp, rfl⟩
    · exact hp
    · exact hgen ℓ hℓ hℓN hgood hℓp

theorem solution (N : ℕ) [NeZero N] (W : WeierstrassCurve ℤ) (p : ℕ) :
    ModularCurve.exitIdeal N W p ≠ ⊤ ↔
      ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}), 𝔪₁.IsMaximal ∧
        ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) ∈ 𝔪₁ ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), W.IsGoodPrimeFor ℓ → ℓ ≠ p →
          ModularCurve.exitGen N W ℓ hℓ hℓN ∈ 𝔪₁ := by
  constructor
  · intro h
    obtain ⟨𝔪₁, h𝔪₁, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨hp, hgen⟩ := (exitIdeal_le_iff_aux N W p).mp hle
    exact ⟨𝔪₁, h𝔪₁, hp, hgen⟩
  · rintro ⟨𝔪₁, h𝔪₁, hp, hgen⟩ htop
    exact h𝔪₁.ne_top (top_le_iff.mp (htop ▸ (exitIdeal_le_iff_aux N W p).mpr ⟨hp, hgen⟩))

end S_ModularCurve_exitIdeal_ne_top_iff_exists_maximal
end P2MW
export P2MW.S_ModularCurve_exitIdeal_ne_top_iff_exists_maximal (solution)
