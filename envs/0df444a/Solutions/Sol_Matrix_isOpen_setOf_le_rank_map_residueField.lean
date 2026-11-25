-- Prove2me | solution 1 for Matrix.isOpen_setOf_le_rank_map_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:11:53.723042+00:00
-- url     : https://prove2.me/submissions/535a5a4a-5816-4a9d-a7dc-8f5c20c86195

import Mathlib

set_option autoImplicit false

open Module

theorem solution {A : Type*} [CommRing A] {m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix m n A) (s : ℕ) :
    IsOpen {p : PrimeSpectrum A | s ≤ (M.map (algebraMap A p.asIdeal.ResidueField)).rank} := by
  classical
  -- over a field: `s ≤ rank N` iff some `s × s` minor of `N` is nonzero
  have key : ∀ {k : Type _} [Field k] (N : Matrix m n k),
      s ≤ N.rank ↔ ∃ (a : Fin s → m) (c : Fin s → n), (N.submatrix a c).det ≠ 0 := by
    intro k _ N
    constructor
    · intro hs
      obtain ⟨a, ha⟩ : ∃ a : Fin N.rank → m, LinearIndependent k (N.row ∘ a) := by
        obtain ⟨κ, b, hb, hspan, hli⟩ := exists_linearIndependent' k N.row
        have : Finite κ := Finite.of_injective b hb
        have := Fintype.ofFinite κ
        have hcard : Fintype.card κ = N.rank := by
          rw [N.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
        let e : Fin N.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
        exact ⟨b ∘ e, hli.comp e e.injective⟩
      let a' : Fin s → m := a ∘ Fin.castLE hs
      have ha' : LinearIndependent k (N.submatrix a' id).row :=
        ha.comp (Fin.castLE hs) (Fin.castLE_injective hs)
      obtain ⟨c, hc⟩ : ∃ c : Fin s → n, ((N.submatrix a' id).submatrix id c).det ≠ 0 := by
        obtain ⟨κ, b, hb, hspan, hli⟩ := exists_linearIndependent' k (N.submatrix a' id).col
        have : Finite κ := Finite.of_injective b hb
        have := Fintype.ofFinite κ
        have hcard : Fintype.card κ = s := by
          rw [← finrank_span_eq_card hli, hspan, ← (N.submatrix a' id).rank_eq_finrank_span_cols,
            ha'.rank_matrix, Fintype.card_fin]
        let e : Fin s ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
        refine ⟨b ∘ e, ?_⟩
        have hcol : LinearIndependent k ((N.submatrix a' id).submatrix id (b ∘ e)).col :=
          hli.comp e e.injective
        exact ((Matrix.isUnit_iff_isUnit_det _).1
          (Matrix.linearIndependent_cols_iff_isUnit.1 hcol)).ne_zero
      refine ⟨a', c, ?_⟩
      rwa [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at hc
    · rintro ⟨a, c, h⟩
      have := Matrix.rank_of_det_ne_zero h
      rw [Fintype.card_fin] at this
      rw [← this]
      exact Matrix.rank_submatrix_le N a c
  have e : {p : PrimeSpectrum A | s ≤ (M.map (algebraMap A p.asIdeal.ResidueField)).rank} =
      ⋃ (a : Fin s → m) (c : Fin s → n),
        (PrimeSpectrum.basicOpen (M.submatrix a c).det : Set (PrimeSpectrum A)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    rw [key]
    refine exists₂_congr fun a c => ?_
    rw [← Ideal.algebraMap_residueField_eq_zero, RingHom.map_det]
    rfl
  rw [e]
  exact isOpen_iUnion fun a => isOpen_iUnion fun c => PrimeSpectrum.isOpen_basicOpen

