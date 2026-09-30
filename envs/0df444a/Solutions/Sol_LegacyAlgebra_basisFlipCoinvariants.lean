-- Prove2me | solution 1 for LegacyAlgebra.basisFlipCoinvariants
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:00:11.494977+00:00
-- url     : https://prove2.me/submissions/072b5d21-f905-4a1f-9d3d-0f57630da8ff

import Mathlib

set_option autoImplicit false

theorem solution
    (k G V ι : Type*) [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (b : Module.Basis ι k V)
    (hTwo : (2 : k) ≠ 0)
    (hFlip : ∀ i : ι, ∃ g : G, ρ g (b i) = -(b i)) :
    Representation.Coinvariants.ker ρ = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  obtain ⟨g, hg⟩ := hFlip i
  have h := Representation.Coinvariants.sub_mem_ker (ρ := ρ) g (b i)
  rw [hg] at h
  have hscale := (Representation.Coinvariants.ker ρ).smul_mem (-(2 : k)⁻¹) h
  have heq : (-(2 : k)⁻¹) • (-(b i) - b i) = b i := by
    calc
      (-(2 : k)⁻¹) • (-(b i) - b i) =
          (-(2 : k)⁻¹) • ((-(2 : k)) • b i) := by
            congr 1
            module
      _ = b i := by simp [smul_smul, hTwo]
  rwa [heq] at hscale
