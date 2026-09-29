-- Prove2me | solution 1 for Ideal.exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/04fbb04f-16c4-57e7-b789-4f63beb3b9ad

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem

set_option autoImplicit false

universe u

theorem solution
    {B : Type u} [CommRing B] (P : B → Prop)
    (hloc : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∃ f : B, f ∉ 𝔭 ∧ P f) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, P (f i) := by
  classical

  have htop : Ideal.span {f : B | P f} = ⊤ := by
    by_contra h
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf𝔪, hPf⟩ := hloc 𝔪 h𝔪.isPrime
    exact hf𝔪 (hle (Ideal.subset_span hPf))

  have h1 : (1 : B) ∈ Ideal.span {f : B | P f} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨↥T, inferInstance, fun t => t.1, ?_, fun t => hTsub t.2⟩
  rw [Ideal.eq_top_iff_one]
  have : Set.range (fun t : ↥T => (t.1 : B)) = (T : Set B) := by
    ext b; simp
  rw [this]
  exact h1T

end S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
end P2MW
export P2MW.S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem (solution)
