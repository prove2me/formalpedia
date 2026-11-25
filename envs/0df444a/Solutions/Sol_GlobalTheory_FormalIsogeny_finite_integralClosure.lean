-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finite_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:20.894736+00:00
-- url     : https://prove2.me/submissions/ea87fc10-5278-4676-bc78-fb1e43677a11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_map
import Theorems.Thm_GlobalTheory_finite_quotient_span_of_birational
import Theorems.Thm_GlobalTheory_krullAkizuki
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_faithful


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
include K
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution : Module.Finite R (integralClosure R L) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful R K L
  have hinj := FaithfulSMul.algebraMap_injective R L
  set B := integralClosure R L
  have hBn : IsNoetherianRing B := (krullAkizuki K B).1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : (maximalIdeal R).map (algebraMap R B) = Ideal.span {algebraMap R B π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have : IsHausdorff ((maximalIdeal R).map (algebraMap R B)) B := by
    refine IsHausdorff.of_isDomain _ ?_
    obtain ⟨n, hn⟩ := Ideal.exists_maximal B
    refine ne_top_of_le_ne_top hn.ne_top (Ideal.map_le_iff_le_comap.2 ?_)
    exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).ge
  have halg : Algebra.IsAlgebraic R L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := K) (C := L)).mpr inferInstance
  obtain ⟨s, hsT, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := K) (B : Set L)).mp
    (IsNoetherian.noetherian _)
  let C := Algebra.adjoin R (s : Set L)
  have hCB : C ≤ B := Algebra.adjoin_le hsT
  have hCf : Module.Finite R C :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet fun x hx => hsT hx
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  have hCd : Ring.DimensionLEOne C := Ring.DimensionLEOne.of_isIntegral R C
  letI : Algebra C B := (Subalgebra.inclusion hCB).toAlgebra
  have : IsScalarTower R C B := .of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Subalgebra.inclusion_injective hCB)
  have hfin : Module.Finite C (B ⧸ Ideal.span {algebraMap C B (algebraMap R C π)}) := by
    refine finite_quotient_span_of_birational (fun x => ?_) fun h => ?_
    · have h1 : (x : L) ∈ Submodule.span K (s : Set L) := hs ▸ Submodule.subset_span x.2
      obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ _ h1
      refine ⟨algebraMap R C d, fun h => ?_, ⟨_, Algebra.span_le_adjoin R _ hd⟩, Subtype.ext ?_⟩
      · have h3 : algebraMap R L d = 0 := congrArg Subtype.val h
        exact nonZeroDivisors.coe_ne_zero d (hinj (h3.trans (map_zero _).symm))
      · change algebraMap R L d * x = (d : R) • (x : L)
        rw [Algebra.smul_def]
    · have h3 : algebraMap R L π = 0 := congrArg Subtype.val h
      exact hπ.ne_zero (hinj (h3.trans (map_zero _).symm))
  have : Module.Finite R (B ⧸ (maximalIdeal R).map (algebraMap R B)) := by
    rw [hm, IsScalarTower.algebraMap_apply R C B]
    exact .trans C _
  exact finite_of_finite_quotient_map (maximalIdeal R)
end GlobalTheory.FormalIsogeny
