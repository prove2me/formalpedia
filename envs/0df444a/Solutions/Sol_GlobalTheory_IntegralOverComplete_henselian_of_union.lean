-- Prove2me | solution 1 for GlobalTheory.IntegralOverComplete.henselian_of_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:51:57.03891+00:00
-- url     : https://prove2.me/submissions/62c50d19-2d13-402b-8870-40e3ede47826

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.IntegralOverComplete
open IsLocalRing Polynomial
namespace GlobalTheory.IntegralOverComplete
theorem _root_.solution (W R : Type) [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (h : ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsLocalRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ IsLocalHom W'.val.toRingHom) :
    HenselianLocalRing R := by
  classical
  refine ⟨fun f hf a₀ h0 hu => ?_⟩
  obtain ⟨V, _, hs, hc, hl⟩ := h (insert a₀ f.coeffs ∪ {0})
  let i : V →+* R := V.val.toRingHom
  have hlift : f ∈ lifts i := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : f.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨f.coeff n, hs (by simp [coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hf
  obtain ⟨b, rfl⟩ : ∃ b : V, i b = a₀ := ⟨⟨a₀, hs (by simp)⟩, rfl⟩
  subst hg
  rw [eval_map, eval₂_at_apply] at h0
  rw [derivative_map, eval_map, eval₂_at_apply] at hu
  have h0' : g.eval b ∈ maximalIdeal V := fun hu' => h0 (hu'.map i)
  have hu' : IsUnit (g.derivative.eval b) := IsLocalHom.map_nonunit _ hu
  obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian (I := maximalIdeal V) g hgm b h0' (hu'.map _)
  refine ⟨i a, ?_, ?_⟩
  · rw [IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact fun hh => hab (IsLocalHom.map_nonunit _ hh)
end GlobalTheory.IntegralOverComplete
