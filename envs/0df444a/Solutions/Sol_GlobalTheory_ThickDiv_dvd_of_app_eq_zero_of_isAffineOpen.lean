-- Prove2me | solution 1 for GlobalTheory.ThickDiv.dvd_of_app_eq_zero_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:50.874596+00:00
-- url     : https://prove2.me/submissions/09ce6e63-e4d1-465f-84de-008f2192cfa6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
import Theorems.Thm_GlobalTheory_ThickDiv_thick_appTop
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_app_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickDiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
private theorem ker_thick_appTop_le_span_pow_succ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (e : ℕ) :
    RingHom.ker (thick V (maximalIdeal V) e).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (ϖ ^ (e + 1))} := by
  intro x hx
  obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b = x :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x, by simp⟩
  rw [RingHom.mem_ker, thick_appTop] at hx
  have hb : Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)) b = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ maximalIdeal V ^ (e + 1)))).hom.hom hx
  rw [Ideal.Quotient.eq_zero_iff_mem, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact Ideal.mem_span_singleton.2 ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c, map_mul _ _ _⟩
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
end GlobalTheory.ThickDiv
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickDiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace GlobalTheory.ThickDiv
theorem _root_.solution (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (hf : ((fstG (maximalIdeal V) e X).left.app U).hom f = 0) : constFn X.hom U (ϖ ^ (e + 1)) ∣ f := by
  have hm := GlobalTheory.ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback X.hom (thick V (maximalIdeal V) e)) hU f hf
  have hm2 := Ideal.map_mono (ker_thick_appTop_le_span_pow_succ hϖ e) hm
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm2
  exact hm2
end GlobalTheory.ThickDiv
