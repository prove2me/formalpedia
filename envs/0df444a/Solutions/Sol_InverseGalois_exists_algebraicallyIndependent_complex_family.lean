-- Prove2me | solution 1 for InverseGalois.exists_algebraicallyIndependent_complex_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T01:35:37.375564+00:00
-- url     : https://prove2.me/submissions/95aa2a62-cf4e-4ec0-bdf6-5ae06bb48fa2

import Mathlib

theorem solution (I : Type) [Fintype I] :
    ∃ x : I → ℂ, AlgebraicIndependent ℚ x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hcard : Cardinal.mk ℂ = Cardinal.mk s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      (v' := ((↑) : s → ℂ)) hs (by simp)
        (by simpa only [Cardinal.mk_complex] using Cardinal.aleph0_lt_continuum)
  have hlt : Cardinal.mk I < Cardinal.mk s := by
    calc
      Cardinal.mk I < Cardinal.aleph0 := Cardinal.lt_aleph0_of_finite I
      _ < Cardinal.mk ℂ := by
        simpa only [Cardinal.mk_complex] using Cardinal.aleph0_lt_continuum
      _ = Cardinal.mk s := hcard
  obtain ⟨e⟩ : Nonempty (I ↪ s) :=
    Cardinal.lift_mk_le'.mp (by simpa using hlt.le)
  exact ⟨fun i ↦ (e i : ℂ), hs.1.comp e e.injective⟩
