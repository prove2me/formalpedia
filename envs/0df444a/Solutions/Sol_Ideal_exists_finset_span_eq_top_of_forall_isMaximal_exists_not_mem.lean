-- Prove2me | solution 1 for Ideal.exists_finset_span_eq_top_of_forall_isMaximal_exists_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5314ad6e-2d2e-5ca9-85a9-f8bb9f6046fc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_finset_span_eq_top_of_forall_isMaximal_exists_not_mem

set_option autoImplicit false

theorem solution
    {S : Type} [CommRing S] (P : S → Prop)
    (h : ∀ 𝔭 : PrimeSpectrum S, 𝔭.asIdeal.IsMaximal → ∃ g : S, g ∉ 𝔭.asIdeal ∧ P g) :
    ∃ (k : ℕ) (g : Fin k → S), Ideal.span (Set.range g) = ⊤ ∧ ∀ i, P (g i) := by
  classical
  have htop : Ideal.span {g : S | P g} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg𝔪, hPg⟩ := h ⟨𝔪, h𝔪.isPrime⟩ h𝔪
    exact hg𝔪 (hle (Ideal.subset_span hPg))
  have h1 : (1 : S) ∈ Ideal.span {g : S | P g} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun i => ((T.equivFin.symm i : ↥T) : S), ?_, fun i => hTsub (T.equivFin.symm i).2⟩
  have hrange : Set.range (fun i : Fin T.card => ((T.equivFin.symm i : ↥T) : S)) = (↑T : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro hx
      exact ⟨T.equivFin ⟨x, hx⟩, by simp only [Equiv.symm_apply_apply]⟩
  rw [hrange, Ideal.eq_top_iff_one]
  exact h1T

end S_Ideal_exists_finset_span_eq_top_of_forall_isMaximal_exists_not_mem
end P2MW
export P2MW.S_Ideal_exists_finset_span_eq_top_of_forall_isMaximal_exists_not_mem (solution)
