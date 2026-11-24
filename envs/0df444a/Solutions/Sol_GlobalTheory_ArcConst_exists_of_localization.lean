-- Prove2me | solution 1 for GlobalTheory.ArcConst.exists_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:12.1296+00:00
-- url     : https://prove2.me/submissions/20a09c24-0205-4911-a2d0-20585cba4f04

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_AlgZ_map
import Theorems.Thm_GlobalTheory_ArcConst_isIntegralElem_of_isAlgebraic_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
namespace GlobalTheory.ArcConst
theorem _root_.solution {K R S : Type} [Field K] [CharZero K] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) (f : K →+* R)
    {s : S} (hs : AlgZ s) : ∃ r : R, algebraMap R S r = s ∧ AlgZ r := by
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have h1 : ((algebraMap R S).comp f).IsIntegralElem s := isIntegralElem_of_isAlgebraic_int _ hs
  have h2 : IsIntegral R s := by
    obtain ⟨p, hp, hp0⟩ := h1
    exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hp0⟩
  let g : S →ₐ[R] FractionRing R := IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId R (FractionRing R))
    (fun y => IsLocalization.map_units (M := nonZeroDivisors R) (FractionRing R) ⟨y.1, hM y.2⟩)
  have hg : Function.Injective g := by
    let : Algebra S (FractionRing R) := g.toRingHom.toAlgebra
    have : IsScalarTower R S (FractionRing R) := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
    have : IsFractionRing S (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S (FractionRing R)
    exact IsFractionRing.injective S (FractionRing R)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h2.map g)
  have hrs : algebraMap R S r = s := hg (by rw [g.commutes]; exact hr)
  refine ⟨r, hrs, ?_⟩
  rw [← hrs] at hs
  exact (isAlgebraic_algHom_iff (algebraMap R S).toIntAlgHom hinj).1 hs
end GlobalTheory.ArcConst
