-- Prove2me | solution 1 for GlobalTheory.isRegularRing_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:24.961569+00:00
-- url     : https://prove2.me/submissions/02718709-0e5e-4920-80d0-e9cb75ec1a2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private theorem isRegularLocalRing_atPrime_of_etale' (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (h : IsRegularLocalRing (Localization.AtPrime (q.under R))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmax : (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hsf : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank := by
    have heq : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
      rw [← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
    rw [heq]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing
  have hht : (q.under R).height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast hsf
    _ = ringKrullDim (Localization.AtPrime (q.under R)) := h.spanFinrank_maximalIdeal
    _ = ((q.under R).height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _
    _ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ = ringKrullDim (Localization.AtPrime q) :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R S : Type*) [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isRegularRing_iff.mpr fun q _ => isRegularLocalRing_atPrime_of_etale' R S q inferInstance
end GlobalTheory
