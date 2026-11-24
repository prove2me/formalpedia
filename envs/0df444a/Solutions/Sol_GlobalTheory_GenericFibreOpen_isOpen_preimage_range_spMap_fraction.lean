-- Prove2me | solution 1 for GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:21.490871+00:00
-- url     : https://prove2.me/submissions/bcd6cbaa-3cb8-4220-9e7c-aec08676b119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpen
import Theorems.Thm_GlobalTheory_GenericFibreOpen_range_spMap_algebraMap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GenericFibreOpen
namespace GlobalTheory.GenericFibreOpen
theorem _root_.solution :
    ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R]
      [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  intro O K R _ _ _ _ _ _ _ g
  rw [range_spMap_algebraMap_eq O K]
  have hc : Continuous g.base := g.base.hom.continuous
  set c : Sp R := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  have hle : ∀ x : Sp R, ((g.base x : Sp O) : PrimeSpectrum O).asIdeal ≤ ((g.base c : Sp O) : PrimeSpectrum O).asIdeal := by
    intro x
    have hs : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
    exact (PrimeSpectrum.le_iff_specializes _ _).2 (hs.map hc)
  by_cases hp : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal = ⊥
  · have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_bot_iff.1 (hp ▸ hle x)
    exact this ▸ isOpen_univ
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    have hmax : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
      ((g.base c : Sp O) : PrimeSpectrum O).isPrime.isMaximal hp
    have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} =
        (fun x : Sp R => g.base x) ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum O)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h hx
        rw [h, Ideal.mem_bot] at hx
        exact ha0 hx
      · intro hx
        by_contra hne
        have hq : ((g.base x : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
          ((g.base x : Sp O) : PrimeSpectrum O).isPrime.isMaximal hne
        have heq := hq.eq_of_le hmax.ne_top (hle x)
        exact hx (heq ▸ ha)
    rw [this]
    exact (PrimeSpectrum.basicOpen a).isOpen.preimage hc
end GlobalTheory.GenericFibreOpen
