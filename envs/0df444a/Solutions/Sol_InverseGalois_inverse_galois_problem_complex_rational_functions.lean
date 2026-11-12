-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_complex_rational_functions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T21:07:25.577336+00:00
-- url     : https://prove2.me/submissions/4c6f03cd-09a4-4438-aa2c-d5c72b524d14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InverseGalois_realizability
import Theorems.Thm_InverseGalois_fundamentalGroup_punctured_plane_free
import Theorems.Thm_InverseGalois_riemann_existence_realizable_complex

open InverseGalois

theorem solution {G : Type*} [Fintype G] [Group G] : IsRealizable (RatFunc ℂ) G := by
  classical
  -- puncture the plane at `card G` points, with a basepoint off the punctures
  set n := Fintype.card G with hn
  set S : Finset ℂ := (Finset.range n).image (fun k : ℕ => (k : ℂ)) with hS
  have hinj : Function.Injective (fun k : ℕ => (k : ℂ)) :=
    fun _ _ h => Nat.cast_injective h
  have hcard : S.card = n := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hx : (n : ℂ) ∉ (S : Set ℂ) := by
    simp only [hS, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    rintro ⟨k, hk, hk'⟩
    exact absurd (hinj hk') (by omega)
  -- the fundamental group of the punctured plane is free on `card G` generators
  obtain ⟨e⟩ := fundamentalGroup_punctured_plane_free S (n : ℂ) hx
  -- a free group on `card G` generators surjects onto `G`
  let eq : Fin S.card ≃ G := (finCongr hcard).trans (Fintype.equivFin G).symm
  have hψ : Function.Surjective (FreeGroup.lift eq : FreeGroup (Fin S.card) →* G) := by
    intro g
    exact ⟨FreeGroup.of (eq.symm g), by simp⟩
  -- Riemann existence turns that surjection into a Galois extension of `ℂ(t)`
  exact riemann_existence_realizable_complex S (n : ℂ) hx
    ((FreeGroup.lift eq).comp e.toMonoidHom) (hψ.comp e.surjective)
