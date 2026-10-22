-- Prove2me | solution 1 for GeomDL.Sets.eq_13_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:36:38.60457+00:00
-- url     : https://prove2.me/submissions/0adef564-0dc6-4023-aaa2-84fa932c066e

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

open GeomDL.Sets

theorem solution {n d d' : ℕ}
    (φ : (Fin d → ℝ) → Multiset (Fin d → ℝ) → (Fin d' → ℝ)) :
    IsGraphPermEquivariant (localLayer φ : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin d') ℝ) := by
  intro σ X A
  have hN : ∀ u, neighbourhoodFeatures (permRows σ X) (permAdj σ A) u =
      neighbourhoodFeatures X A (σ.symm u) := by
    intro u
    unfold neighbourhoodFeatures neighbourhood
    have hset : (Finset.univ.filter (fun v => permAdj σ A u v ≠ 0 ∨ permAdj σ A v u ≠ 0)).map
        σ.symm.toEmbedding =
        Finset.univ.filter (fun v => A (σ.symm u) v ≠ 0 ∨ A v (σ.symm u) ≠ 0) := by
      ext w
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.coe_toEmbedding, permAdj, Matrix.submatrix_apply]
      constructor
      · rintro ⟨v, hv, rfl⟩; simpa using (Finset.mem_filter.mp hv).2
      · intro hw; exact ⟨σ w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hw⟩, by simp⟩
    rw [← hset, Finset.map_val, Multiset.map_map]
    rfl
  ext u j
  simp only [localLayer, Matrix.of_apply, hN]
  rfl
