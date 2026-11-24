-- Prove2me | solution 1 for GlobalTheory.PushInv.stalkSpecializes_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:31.450897+00:00
-- url     : https://prove2.me/submissions/feace3d2-11d0-47ea-9034-82bf24889687

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
import Theorems.Thm_GlobalTheory_PushInv_gs_id
import Theorems.Thm_GlobalTheory_PushInv_gs_specializes
import Theorems.Thm_GlobalTheory_PushInv_exists_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.PushInv
theorem _root_.solution {x y : X} (h : y ⤳ x) [IsDomain (X.presheaf.stalk x)] :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨A, hA, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  have hy : y ∈ A := h.mem_open A.2 hx
  obtain ⟨a, b, hb, e⟩ := exists_frac hA hx t
  have ha : gs (𝟙 X) y A a = 0 := by
    rw [← gs_specializes (𝟙 X) h A hx, ← e, map_mul, ht, zero_mul]
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : A)
  have hl := hA.isLocalization_stalk ⟨y, hy⟩
  rw [gs_id y A hy] at ha
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (hA.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) a).1 ha
  have hu : IsUnit (gs (𝟙 X) y A c) := by
    rw [gs_id y A hy]
    exact IsLocalization.map_units (X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) c
  have hne : gs (𝟙 X) x A c ≠ 0 := fun h0 => by
    rw [← gs_specializes (𝟙 X) h A hx, h0, map_zero] at hu
    exact not_isUnit_zero hu
  have h0 : gs (𝟙 X) x A c * gs (𝟙 X) x A a = 0 := by
    rw [← gs_mul _ _ _ hx, hc, gs_id x A hx, map_zero]
  rw [(mul_eq_zero.1 h0).resolve_left hne] at e
  exact (hb.mul_left_eq_zero).1 e
end GlobalTheory.PushInv
