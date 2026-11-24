-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.exists_localHom_of_overLa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:10.136376+00:00
-- url     : https://prove2.me/submissions/12d8bb4e-bcb9-48c2-afcb-d5e50552e700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_algebraMap_lt_one_iff
import Theorems.Thm_GlobalTheory_PlaceCompletion_exists_algebraMap_eq_of_valV_le_one
import Theorems.Thm_GlobalTheory_PlaceCompletion_mem_atPrime_iff
import Theorems.Thm_GlobalTheory_PlaceCompletion_isUnit_atPrime_iff
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_eq_pow_of_overLa
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.PlaceCompletion
open scoped WithZero
section Val
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
end Val
section Place
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
private theorem valuation_lt_one_of_mem_maximalIdeal' (x : la.valuationSubringAtPrime K)
    (hx : x ∈ IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) : la.valuation K (x : K) < 1 :=
  lt_of_le_of_ne ((mem_atPrime_iff la (x : K)).1 x.2)
    (fun h => ((IsLocalRing.mem_maximalIdeal x).1 hx) ((isUnit_atPrime_iff la x).2 h))
end Place
end GlobalTheory.PlaceCompletion
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
namespace GlobalTheory.PlaceCompletion
theorem _root_.solution {j : K →+* K'} {e : ℕ} (ho : OverLa la V j e) :
    ∃ o : la.valuationSubringAtPrime K →+* V, (∀ x, algebraMap V K' (o x) = j x) ∧
      ∀ x ∈ IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K),
        o x ∈ IsLocalRing.maximalIdeal V := by
  have he : 0 < e := by
    have h' := ho
    unfold OverLa at h'
    exact h'.1
  have hint : ∀ x : la.valuationSubringAtPrime K, j x ∈ (algebraMap V K').range := fun x =>
    RingHom.mem_range.2 (exists_algebraMap_eq_of_valV_le_one (by
      rw [valV_eq_pow_of_overLa ho]
      exact pow_le_one₀ zero_le ((mem_atPrime_iff la (x : K)).1 x.2)))
  have finj : Function.Injective (algebraMap V K') := IsFractionRing.injective V K'
  let E := RingEquiv.ofBijective (algebraMap V K').rangeRestrict
    ⟨fun a b hab => finj (congrArg Subtype.val hab), (algebraMap V K').rangeRestrict_surjective⟩
  let r := (j.comp (la.valuationSubringAtPrime K).subtype).codRestrict _ hint
  have hE : ∀ x, algebraMap V K' (E.symm (r x)) = j x := fun x =>
    congrArg Subtype.val (E.apply_symm_apply (r x))
  refine ⟨E.symm.toRingHom.comp r, hE, fun x hx => ?_⟩
  rw [← valV_algebraMap_lt_one_iff (K' := K')]
  change valV V (algebraMap V K' (E.symm (r x))) < 1
  rw [hE, valV_eq_pow_of_overLa ho]
  exact pow_lt_one₀ zero_le (valuation_lt_one_of_mem_maximalIdeal' x hx) he.ne'
end GlobalTheory.PlaceCompletion
