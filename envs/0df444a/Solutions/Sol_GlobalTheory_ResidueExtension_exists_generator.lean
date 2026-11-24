-- Prove2me | solution 1 for GlobalTheory.ResidueExtension.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:39.134456+00:00
-- url     : https://prove2.me/submissions/effe23a3-8be8-43b7-bab5-29c330874f84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
namespace GlobalTheory.ResidueExtension
theorem _root_.solution (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) {π : O}
    (hπ : Irreducible π) :
    ∃ G : O[X], (G.Monic ∨ G = 0) ∧ G.eval₂ r a = 0 ∧
      ∀ f : O[X], f.eval₂ r a = 0 → ∃ g h, f = G * g + C π * h := by
  let rb : ResidueField O →+* Ω :=
    Ideal.Quotient.lift (maximalIdeal O) r fun x hx => by rwa [← hr] at hx
  let _ : Algebra (ResidueField O) Ω := rb.toAlgebra
  have hev : ∀ f : O[X], aeval a (f.map (residue O)) = f.eval₂ r a := by
    intro f
    rw [aeval_def, eval₂_map]
    rfl
  obtain ⟨G, hG, hG'⟩ : ∃ G : O[X], (G.Monic ∨ G = 0) ∧
      G.map (residue O) = minpoly (ResidueField O) a := by
    by_cases h : IsIntegral (ResidueField O) a
    · obtain ⟨G, h1, -, h2⟩ := lifts_and_degree_eq_and_monic
        ((mem_lifts _).mpr (map_surjective (residue O) residue_surjective _)) (minpoly.monic h)
      exact ⟨G, Or.inl h2, h1⟩
    · exact ⟨0, Or.inr rfl, by rw [minpoly.eq_zero h, Polynomial.map_zero]⟩
  refine ⟨G, hG, by rw [← hev, hG', minpoly.aeval], fun f hf => ?_⟩
  rw [← hev] at hf
  obtain ⟨g', hg'⟩ := minpoly.dvd _ _ hf
  obtain ⟨g, rfl⟩ := map_surjective (residue O) residue_surjective g'
  have h1 : f - G * g ∈ RingHom.ker (mapRingHom (residue O)) := by
    rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hG', hg', sub_self]
  rw [ker_mapRingHom, ker_residue, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h1
  obtain ⟨h, hh⟩ := h1
  exact ⟨g, h, by rw [← hh]; ring⟩
end GlobalTheory.ResidueExtension
