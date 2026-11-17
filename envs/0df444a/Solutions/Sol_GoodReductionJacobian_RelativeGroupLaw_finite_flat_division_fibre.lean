-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.finite_flat_division_fibre
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:13.041206+00:00
-- url     : https://prove2.me/submissions/2fd3784a-5103-47e3-a05f-af6ac9d2b027

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

/-- Every division fibre over a section of an abelian scheme is finite flat,
including when the multiplication integer equals the residue characteristic. -/
theorem _root_.solution
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hB : AbelianSchemePropertyBundle R f)
    (hc : L.IsCommutative) (n : ℕ) (hn : 0 < n)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    IsFinite (pullback.snd (L.schemeNsmul n) S.1) ∧
      Flat (pullback.snd (L.schemeNsmul n) S.1) := by
  obtain ⟨hfin, hflat⟩ := L.isFinite_and_flat_schemeNsmul hB hc n hn
  letI := hfin
  letI := hflat
  exact ⟨inferInstance, inferInstance⟩

end GoodReductionJacobian.RelativeGroupLaw
