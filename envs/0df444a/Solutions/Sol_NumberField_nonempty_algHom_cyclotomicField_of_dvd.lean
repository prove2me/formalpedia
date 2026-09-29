-- Prove2me | solution 1 for NumberField.nonempty_algHom_cyclotomicField_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:48:44.249326+00:00
-- url     : https://prove2.me/submissions/67d07833-3a7a-4192-a038-9901a4c285ba

import Mathlib.NumberTheory.Cyclotomic.Basic

open Polynomial

theorem solution {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hdvd : m ∣ k) : Nonempty (CyclotomicField m ℚ →ₐ[ℚ] CyclotomicField k ℚ) := by
  have : NeZero ((k : ℕ) : ℚ) := ⟨by exact_mod_cast hk.ne'⟩
  have : NeZero k := ⟨hk.ne'⟩
  have hc := CyclotomicField.isCyclotomicExtension k ℚ
  obtain ⟨ζ, hζ⟩ := hc.exists_isPrimitiveRoot (Set.mem_singleton k) (NeZero.ne _)
  obtain ⟨c, rfl⟩ := hdvd
  have hζ' : IsPrimitiveRoot (ζ ^ c) m := hζ.pow hk (mul_comm m c)
  refine ⟨SplittingField.lift (cyclotomic m ℚ) ?_⟩
  rw [map_cyclotomic]
  exact (X_pow_sub_one_splits hζ').of_dvd (X_pow_sub_C_ne_zero hm _)
    (by simpa using cyclotomic.dvd_X_pow_sub_one m (CyclotomicField (m * c) ℚ))

