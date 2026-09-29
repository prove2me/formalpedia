-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_cover_of_affineChart_nodes_of_baseSmoothPointStalks_of_coeffEmb_mem_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6f8fff5a-1479-53b6-80fc-001b82a703c5

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_isCurveOver_and_essFiniteType_of_exists_transcendental
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_cover_of_affineChart_nodes_of_baseSmoothPointStalks_of_coeffEmb_mem_of_eq_two_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

noncomputable section

namespace CoverLiftEd2Aux

theorem coe_inv_mem_of_isUnit {K : Type*} [Field K] (A : ValuationSubring K) {x : K} (hx : x ∈ A)
    (h : IsUnit (⟨x, hx⟩ : A)) : x⁻¹ ∈ A := by
  by_cases hx0 : x = 0
  · rw [hx0, inv_zero]; exact zero_mem _
  obtain ⟨u, hu⟩ := h
  have hmul : (((u⁻¹ : Aˣ) : A) : K) * x = 1 := by
    have := congrArg (fun z : A => (z : K)) u.inv_mul
    simpa [hu] using this
  rw [← eq_inv_of_mul_eq_one_left hmul]
  exact SetLike.coe_mem _

theorem valuation_eq_one_of_mem_of_inv_mem {K : Type*} [Field K] (A : ValuationSubring K) {x : K}
    (hx : x ∈ A) (hxi : x⁻¹ ∈ A) (hx0 : x ≠ 0) : A.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : A) :=
    ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxi⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
  exact (A.valuation_eq_one_iff _).mp hu

section EvalAt

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.evalAt f = 0 := by
  rw [Place.evalAt, dif_neg hf]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  simpa using v.evalAt_algebraMap_eq (0 : K)

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add v hv hf (neg_mem hg), evalAt_neg v hv hg, ← sub_eq_add_neg]

theorem evalAt_eq_zero_iff (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = 0 ↔ (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hf]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact v.algebraMap_residueField_injective (by rw [h, map_zero])

theorem isUnit_iff_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.evalAt f ≠ 0 := by
  rw [Ne, evalAt_eq_zero_iff v hv hf]
  exact ⟨fun hu hm => (IsLocalRing.mem_maximalIdeal _).mp hm hu,
    fun h => by
      by_contra hu
      exact h ((IsLocalRing.mem_maximalIdeal _).mpr hu)⟩

theorem inv_mem_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    f⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨u, hu⟩ := (isUnit_iff_evalAt_ne_zero v hv hf).mpr h
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h (evalAt_zero v)
  have hmul : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 * f = 1 := by
    have := congrArg (fun z : v.toValuationSubring => (z : F)) u.inv_mul
    simpa [hu] using this
  have heq : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 = f⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  rw [← heq]
  exact ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2

theorem evalAt_inv_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h (evalAt_zero v)
  have hmul := v.evalAt_mul_of_mem hv hf (inv_mem_of_evalAt_ne_zero v hv hf h)
  rw [mul_inv_cancel₀ hf0, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · rw [h0, v.ord_zero]
  · exact (v.mem_iff_ord_nonneg h0).mp hf

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  by_cases h0 : f = 0
  · rw [h0]; exact zero_mem _
  · exact v.mem_toValuationSubring_of_ord_nonneg_alt h0 h

end EvalAt

section Composite

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def compositeVS (v : Place K F) (hv : v.IsRational) (A : ValuationSubring K) : ValuationSubring F where
  carrier := {f | f ∈ v.toValuationSubring ∧ v.evalAt f ∈ A}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨mul_mem ha hb, by rw [v.evalAt_mul_of_mem hv ha hb]; exact mul_mem ha' hb'⟩
  one_mem' := ⟨one_mem _, by rw [v.evalAt_one]; exact one_mem _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, by rw [evalAt_add v hv ha hb]; exact add_mem ha' hb'⟩
  zero_mem' := ⟨zero_mem _, by rw [evalAt_zero v]; exact zero_mem _⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨neg_mem ha, by rw [evalAt_neg v hv ha]; exact neg_mem ha'⟩
  mem_or_inv_mem' := by
    intro f
    by_cases hf : f ∈ v.toValuationSubring
    · by_cases hA : v.evalAt f ∈ A
      · exact Or.inl ⟨hf, hA⟩
      · right
        have hne : v.evalAt f ≠ 0 := by
          intro h
          exact hA (h ▸ zero_mem _)
        refine ⟨inv_mem_of_evalAt_ne_zero v hv hf hne, ?_⟩
        rw [evalAt_inv_of_evalAt_ne_zero v hv hf hne]
        exact (A.mem_or_inv_mem _).resolve_left hA
    · right
      have hfi : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
      refine ⟨hfi, ?_⟩

      have hnu : ¬ IsUnit (⟨f⁻¹, hfi⟩ : v.toValuationSubring) := by
        intro hu
        apply hf
        have hne : v.evalAt f⁻¹ ≠ 0 := (isUnit_iff_evalAt_ne_zero v hv hfi).mp hu
        have := inv_mem_of_evalAt_ne_zero v hv hfi hne
        rwa [inv_inv] at this
      have h0 : v.evalAt f⁻¹ = 0 := by
        by_contra hne
        exact hnu ((isUnit_iff_evalAt_ne_zero v hv hfi).mpr hne)
      rw [h0]
      exact zero_mem _

variable (v : Place K F) (hv : v.IsRational) (A : ValuationSubring K)

theorem mem_compositeVS_iff {f : F} :
    f ∈ compositeVS v hv A ↔ f ∈ v.toValuationSubring ∧ v.evalAt f ∈ A := Iff.rfl

theorem algebraMap_mem_compositeVS_iff (c : K) :
    algebraMap K F c ∈ compositeVS v hv A ↔ c ∈ A := by
  rw [mem_compositeVS_iff, v.evalAt_algebraMap_eq]
  exact ⟨fun h => h.2, fun h => ⟨v.algebraMap_mem' c, h⟩⟩

def evalHom : compositeVS v hv A →+* A where
  toFun f := ⟨v.evalAt (f : F), f.2.2⟩
  map_one' := Subtype.ext (by simp [v.evalAt_one])
  map_mul' a b := Subtype.ext (by
    show v.evalAt ((a : F) * (b : F)) = v.evalAt (a : F) * v.evalAt (b : F)
    exact v.evalAt_mul_of_mem hv a.2.1 b.2.1)
  map_zero' := Subtype.ext (by simp [evalAt_zero v])
  map_add' a b := Subtype.ext (by
    show v.evalAt ((a : F) + (b : F)) = v.evalAt (a : F) + v.evalAt (b : F)
    exact evalAt_add v hv a.2.1 b.2.1)

@[scoped simp] theorem coe_evalHom_apply (f : compositeVS v hv A) :
    ((evalHom v hv A f : A) : K) = v.evalAt (f : F) := rfl

theorem isUnit_iff_isUnit_evalHom (f : compositeVS v hv A) :
    IsUnit f ↔ IsUnit (evalHom v hv A f) := by
  constructor
  · intro h
    exact h.map (evalHom v hv A)
  · intro h
    have hne : v.evalAt (f : F) ≠ 0 := by
      intro h0
      apply h.ne_zero
      exact Subtype.ext h0
    have hfi : (f : F)⁻¹ ∈ v.toValuationSubring := inv_mem_of_evalAt_ne_zero v hv f.2.1 hne
    have hval : v.evalAt (f : F)⁻¹ ∈ A := by
      rw [evalAt_inv_of_evalAt_ne_zero v hv f.2.1 hne]
      obtain ⟨u, hu⟩ := h
      have : (v.evalAt (f : F))⁻¹ = (((u⁻¹ : Aˣ) : A) : K) := by
        have hmul : (((u⁻¹ : Aˣ) : A) : K) * v.evalAt (f : F) = 1 := by
          have := congrArg (fun z : A => (z : K)) u.inv_mul
          simpa [hu] using this
        exact (eq_inv_of_mul_eq_one_left hmul).symm
      rw [this]
      exact SetLike.coe_mem _
    have hf0 : (f : F) ≠ 0 := by
      rintro h0
      exact hne (by rw [h0, evalAt_zero v])
    refine ⟨⟨f, ⟨(f : F)⁻¹, ⟨hfi, hval⟩⟩, Subtype.ext (mul_inv_cancel₀ hf0),
      Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

theorem not_isUnit_iff_mem_maximalIdeal (f : compositeVS v hv A) :
    ¬ IsUnit f ↔ evalHom v hv A f ∈ maximalIdeal A := by
  rw [isUnit_iff_isUnit_evalHom, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem mem_maximalIdeal_iff (f : compositeVS v hv A) :
    f ∈ maximalIdeal (compositeVS v hv A) ↔ evalHom v hv A f ∈ maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_isUnit_iff_mem_maximalIdeal]

end Composite

end CoverLiftEd2Aux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_cover_of_affineChart_nodes_of_baseSmoothPointStalks_of_coeffEmb_mem_of_eq_two_of_dvd.CoverLiftEd2Aux"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_cover_of_affineChart_nodes_of_baseSmoothPointStalks_of_coeffEmb_mem_of_eq_two_of_dvd.CoverLiftEd2Aux"

open CoverLiftEd2Aux ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) → (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) → IsDiscreteValuationRing ↥W₀ →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),
        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) → (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg → @Algebra.FinitePresentation ↥Ab ↥B _ _ alg →
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) →
        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) → Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) →
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) →
        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb} ∧
            (∀ a : ↥Ab, ρ (@algebraMap ↥Ab ↥B _ _ alg a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B) (hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) →

      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ (nodes : Finset (Subring ↥F₀)),
          (∀ V : ValuationSubring ↥F₀, (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
              (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
              (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                  ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                  (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                  ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                    residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                    ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥F₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →

        ∀ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sb : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
          (φb : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥Ab →+* ↥(Sb Q)))
          (χb : (Q : Place (ResidueField ↥A) FSS) → (↥(Sb Q) →+* ResidueField ↥A))
          (Db : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          (N.card = q + 1 ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔
            ∀ (b : ↥B) (hb : ((b : ↥B) : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hb⟩ ∈ Q.toValuationSubring) ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (
              (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ Sb Q) ∧

              (∀ a : ↥Ab, ((φb Q (Polynomial.C a) : ↥(Sb Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
              (∀ a : ↥Ab, χb Q (φb Q (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
              χb Q (φb Q Polynomial.X) = 0 ∧

              (∃ _ : IsLocalRing ↥(Sb Q), RingHom.ker (χb Q) = maximalIdeal ↥(Sb Q)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sb Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (φb Q).FormallySmooth ∧ (φb Q).FormallyUnramified ∧ (φb Q).EssFiniteType ∧

              (∃ hSR : ∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ R.integers,
                ∀ f : ↥(Sb Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φb Q (Polynomial.C ϖb) ∣ f) ∧

              (∀ f : ↥(Sb Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χb Q f)) ∧

              (∃ hR : ((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q ↔ ∃ g h : ↥B,
                (∀ hh : ((h : ↥B) : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hh⟩ ∈ Q.toValuationSubring,
                  IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hh⟩, hm⟩ ≠ 0) ∧
                f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (∀ P, P ∈ Db Q ↔ (P.IsRational ∧
                (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))) )) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q → P ∈ Db Q' → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Db Q,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Db Q) = Db (R.resAut τ hτ • Q)))) →

        (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∀ a : A, IsLocalRing.residue A a =
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                  ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                    (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) →
        (∃ O ∈ nodes, (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
          (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
            ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)) ∨
        (∃ Q : Place (ResidueField ↥A) FSS, Q ∉ N ∧ P ∈ Db Q)) := by
  letI instk₀F : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ W₀ hK1 hK2 hW₀dvr hW₀unif hLD B alg halgB hBKF hBfrac hFS hFP hKrull hBW hprime hW₀loc hjB
    hBstab hDrin hRAT nodes hCOVER FSS _instF _instA R hRW N Sb φb χb Db hOUT P hPrat hPs
  letI := alg
  obtain ⟨hNcard, hEnds, hStalk, -, -, -⟩ := hOUT

  have hsrat : (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).IsRational :=
    ((ModularCurve.mem_ssPlaces_iff q M' (ResidueField ↥A)).mp ((hW _).mp s.2)).1

  let VF : ValuationSubring ↥(fieldBar q M') := compositeVS P hPrat A
  let ι : ↥F₀ →+* ↥(fieldBar q M') :=
    { toFun := fun x => (x : ↥(fieldBar q M'))
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let V : ValuationSubring ↥F₀ := VF.comap ι
  have hV : ∀ x : ↥F₀, x ∈ V ↔
      ((x : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (x : ↥(fieldBar q M')) ∈ A) :=
    fun x => Iff.rfl
  let ιV : ↥V →+* ↥VF :=
    { toFun := fun y => ⟨((y : ↥F₀) : ↥(fieldBar q M')), y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have hVunit : ∀ (x : ↥F₀) (hx : x ∈ V),
      IsUnit (⟨x, hx⟩ : ↥V) ↔ IsUnit (⟨(x : ↥(fieldBar q M')), hx⟩ : ↥VF) := by
    intro x hx
    constructor
    · intro h
      exact h.map ιV
    · intro h
      have hne : P.evalAt (x : ↥(fieldBar q M')) ≠ 0 := by
        have h' := (isUnit_iff_isUnit_evalHom P hPrat A _).mp h
        intro h0
        apply h'.ne_zero
        exact Subtype.ext h0
      have hx0 : (x : ↥(fieldBar q M')) ≠ 0 := by
        intro h0
        exact hne (by rw [h0, evalAt_zero])
      have hx0' : x ≠ 0 := fun h0 => hx0 (by rw [h0]; rfl)
      have hinvVF : (x : ↥(fieldBar q M'))⁻¹ ∈ VF := coe_inv_mem_of_isUnit VF _ h
      have hinvV : x⁻¹ ∈ V := by
        show ((x⁻¹ : ↥F₀) : ↥(fieldBar q M')) ∈ VF
        exact hinvVF
      exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinvV⟩, Subtype.ext (mul_inv_cancel₀ hx0'),
        Subtype.ext (inv_mul_cancel₀ hx0')⟩, rfl⟩
  have hVmax : ∀ (x : ↥F₀) (hx : x ∈ V),
      (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔
        (⟨P.evalAt (x : ↥(fieldBar q M')), hx.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hVunit,
      not_isUnit_iff_mem_maximalIdeal P hPrat A]
    rfl

  have hVK : ∀ x : ↥k₀, (x : AlgebraicClosure ℚ) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V := by
    intro x
    rw [hV]
    have : ((algebraMap ↥k₀ ↥F₀ x : ↥F₀) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := rfl
    rw [this]
    exact (algebraMap_mem_compositeVS_iff P hPrat A _).symm

  have hreg : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ P.toValuationSubring := by

    have step : ∀ (g : ↥(modularFunctionFieldBar M')) (hg : g ∈ R₀.integers),
        (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (g : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨g, hg⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle g : fieldBar q M') ∉ P.toValuationSubring →
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨g, hg⟩) = 0 := by
      intro g hg hgreg hgs hgP
      obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective
        ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨g, hg⟩))
      obtain ⟨hA, hm⟩ := hPs g hg hgreg hgs a ha
      have hz : P.evalAt (IntermediateField.inclusion hle g : fieldBar q M') = 0 := evalAt_of_not_mem P hgP
      have : (⟨P.evalAt (IntermediateField.inclusion hle g : fieldBar q M') - (a : AlgebraicClosure ℚ), hA⟩ : ↥A) = -a :=
        Subtype.ext (by simp [hz])
      rw [this] at hm
      rw [← ha, IsLocalRing.residue_eq_zero_iff]
      simpa using hm
    intro f hf hfreg hfs
    by_contra hnot
    have h1 := step f hf hfreg hfs hnot
    have hf1 : f + 1 ∈ R₀.integers := add_mem hf (one_mem _)
    have hf1reg : ∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P'.ord ((f + 1 : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) :=
      fun P' hP' => ord_nonneg_of_mem P' (add_mem (mem_of_ord_nonneg P' (hfreg P' hP')) (one_mem _))
    have hx1 : (R₀.residue ⟨f + 1, hf1⟩ : modularFunctionFieldC (ResidueField A) M') = R₀.residue ⟨f, hf⟩ + 1 := by
      have : (⟨f + 1, hf1⟩ : ↥R₀.integers) = ⟨f, hf⟩ + 1 := Subtype.ext rfl
      rw [this, map_add, map_one]
    have hf1s : (R₀.residue ⟨f + 1, hf1⟩ : modularFunctionFieldC (ResidueField A) M') ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := by
      rw [hx1]
      exact add_mem hfs (one_mem _)
    have hnot1 : (IntermediateField.inclusion hle (f + 1) : fieldBar q M') ∉ P.toValuationSubring := by
      intro h
      apply hnot
      rw [map_add, map_one] at h
      simpa using sub_mem h (one_mem P.toValuationSubring)
    have h2 := step (f + 1) hf1 hf1reg hf1s hnot1
    rw [hx1] at h2
    have e1 := (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).algebraMap_evalAt hsrat hfs
    have e2 := (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).algebraMap_evalAt hsrat
      (add_mem hfs (one_mem _))
    rw [h1, map_zero] at e1
    rw [h2, map_zero] at e2
    have : (⟨R₀.residue ⟨f, hf⟩ + 1, add_mem hfs (one_mem _)⟩ :
        ↥(s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring) =
        ⟨R₀.residue ⟨f, hf⟩, hfs⟩ + 1 := Subtype.ext rfl
    rw [this, map_add, map_one, ← e1, zero_add] at e2
    exact zero_ne_one e2

  have hVs : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
          (⟨_, hF⟩ : ↥F₀) ∈ V ∧
          ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
            ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro g hg hgi hgreg hgs
    have hmemP := hreg _ hgi hgreg hgs
    have hF₀ : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀ :=
      hRAT _ ⟨g, rfl⟩
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective
      ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩))
    obtain ⟨hA₀, -⟩ := hPs _ hgi hgreg hgs a₀ ha₀
    have hvalA : P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ A := by
      have := add_mem hA₀ a₀.2
      simpa using this
    have hgV : (⟨_, hF₀⟩ : ↥F₀) ∈ V := (hV _).mpr ⟨hmemP, hvalA⟩
    refine ⟨hF₀, hgV, ?_⟩
    intro c hc hce
    have hcV : algebraMap ↥k₀ ↥F₀ c ∈ V := (hVK c).mp hc
    have hm : (⟨_, hF₀⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V := sub_mem hgV hcV
    refine ⟨hm, ?_⟩
    obtain ⟨hdA, hdm⟩ := hPs _ hgi hgreg hgs ⟨c, hc⟩ hce
    rw [hVmax]
    have hcst : ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := rfl
    have hev : P.evalAt (((⟨_, hF₀⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) =
        P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) - (c : AlgebraicClosure ℚ) := by
      show P.evalAt ((IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) -
          ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M'))) = _
      rw [hcst, evalAt_sub P hPrat hmemP (P.algebraMap_mem' _), P.evalAt_algebraMap_eq]
    have : (⟨P.evalAt (((⟨_, hF₀⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')), hm.2⟩ : ↥A) =
        ⟨_, hdA⟩ := Subtype.ext hev
    rw [this]
    exact hdm

  rcases hCOVER V hVK hVs with hBV | ⟨O, hOn, hO⟩
  swap
  ·
    left
    refine ⟨O, hOn, fun f hfO => ((hV f).mp (hO f hfO).1).1, fun f hfO hnu => ?_⟩
    have hfV : f ∈ V := (hO f hfO).1
    have hmax : (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V := (hO f hfO).2 hnu hfV
    rw [hVmax] at hmax
    exact ⟨hfV.2, hmax⟩

  right
  have hBVF : ∀ b : ↥B, (b : ↥(fieldBar q M')) ∈ VF := by
    intro b
    obtain ⟨hf, h⟩ := hBV (b : ↥(fieldBar q M')) b.2
    exact (hV _).mp h
  have hBR : ∀ b : ↥B, (b : ↥(fieldBar q M')) ∈ R.integers := by
    intro b
    obtain ⟨hf, hW⟩ := hBW (b : ↥(fieldBar q M')) b.2
    exact (hRW ⟨_, hf⟩).mpr hW

  let inclB : ↥B →+* ↥VF :=
    { toFun := fun b => ⟨(b : ↥(fieldBar q M')), hBVF b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let θ : ↥B →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp ((evalHom P hPrat A).comp inclB)
  have hθ : ∀ b : ↥B, θ b = IsLocalRing.residue ↥A ⟨P.evalAt (b : ↥(fieldBar q M')), (hBVF b).2⟩ :=
    fun b => rfl
  let inclR : ↥B →+* ↥R.integers :=
    { toFun := fun b => ⟨(b : ↥(fieldBar q M')), hBR b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let resB : ↥B →+* FSS := R.residue.comp inclR
  have hresB : ∀ b : ↥B, resB b = R.residue ⟨(b : ↥(fieldBar q M')), hBR b⟩ := fun b => rfl

  have hθconst : ∀ a : ↥Ab, θ (algebraMap ↥Ab ↥B a) =
      IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩ := by
    intro a
    rw [hθ]
    congr 1
    apply Subtype.ext
    show P.evalAt ((algebraMap ↥Ab ↥B a : ↥B) : ↥(fieldBar q M')) = _
    rw [halgB a, P.evalAt_algebraMap_eq]
  have hresBconst : ∀ a : ↥Ab, resB (algebraMap ↥Ab ↥B a) =
      algebraMap (ResidueField ↥A) FSS
        (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) := by
    intro a
    rw [hresB]
    have : (⟨((algebraMap ↥Ab ↥B a : ↥B) : ↥(fieldBar q M')), hBR _⟩ : ↥R.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : AlgebraicClosure ℚ),
          (R.algebraMap_mem_iff _).mpr ((hAb a).mp a.2)⟩ := Subtype.ext (halgB a)
    rw [this]
    exact R.residue_algebraMap ⟨_, (hAb a).mp a.2⟩

  have hconst : ∀ b : ↥B, ∃ a : ↥Ab, θ (algebraMap ↥Ab ↥B a) = θ b := by
    intro b
    obtain ⟨c, hcA, hsub, hm⟩ := hκ (P.evalAt (b : ↥(fieldBar q M'))) (hBVF b).2
    have hcKb : (c : AlgebraicClosure ℚ) ∈ Kb := Kb.algebraMap_mem c
    refine ⟨⟨⟨(c : AlgebraicClosure ℚ), hcKb⟩, (hAb _).mpr hcA⟩, ?_⟩
    rw [hθconst, hθ, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have : (⟨(c : AlgebraicClosure ℚ), hcA⟩ : ↥A) - ⟨P.evalAt (b : ↥(fieldBar q M')), (hBVF b).2⟩ =
        -⟨_, hsub⟩ := Subtype.ext (by simp)
    rw [this]
    exact neg_mem hm

  have hKO : ∀ e : ResidueField ↥A, ∃ b : ↥B, resB b = algebraMap (ResidueField ↥A) FSS e := by
    intro e
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective e
    obtain ⟨c, hcA, hsub, hm⟩ := hκ (a₀ : AlgebraicClosure ℚ) a₀.2
    have hcKb : (c : AlgebraicClosure ℚ) ∈ Kb := Kb.algebraMap_mem c
    refine ⟨algebraMap ↥Ab ↥B ⟨⟨(c : AlgebraicClosure ℚ), hcKb⟩, (hAb _).mpr hcA⟩, ?_⟩
    rw [hresBconst]
    congr 1
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have : (⟨(c : AlgebraicClosure ℚ), hcA⟩ : ↥A) - a₀ = -⟨_, hsub⟩ := Subtype.ext (by simp)
    rw [this]
    exact neg_mem hm

  have hϖA : (⟨((ϖb : ↥Kb) : AlgebraicClosure ℚ), (hAb _).mp ϖb.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hϖm : ϖb ∈ maximalIdeal ↥Ab := hϖb ▸ Ideal.mem_span_singleton_self ϖb
    apply (IsLocalRing.mem_maximalIdeal _).mp hϖm
    have hinvA : (((ϖb : ↥Kb) : AlgebraicClosure ℚ))⁻¹ ∈ A := coe_inv_mem_of_isUnit A _ hu
    have hinvAb : ((ϖb : ↥Kb))⁻¹ ∈ Ab := (hAb _).mpr (by simpa using hinvA)
    have hϖ0 : (ϖb : ↥Kb) ≠ 0 := fun h => hϖb0 (Subtype.ext h)
    exact ⟨⟨ϖb, ⟨_, hinvAb⟩, Subtype.ext (mul_inv_cancel₀ hϖ0), Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩
  have hkerB : ∀ b : ↥B, resB b = 0 → θ b = 0 := by
    intro b hb0
    have hbm : (⟨(b : ↥(fieldBar q M')), hBR b⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers := by
      rw [← R.ker_residue]
      exact hb0
    have hdvd : algebraMap ↥Ab ↥B ϖb ∣ b := by
      by_contra hnd
      by_cases hb00 : (b : ↥(fieldBar q M')) = 0
      · exact hnd (by rw [show b = 0 from Subtype.ext hb00]; exact dvd_zero _)
      obtain ⟨hbF, hbW⟩ := hBW (b : ↥(fieldBar q M')) b.2
      have hbinvF : (b : ↥(fieldBar q M'))⁻¹ ∈ F₀ := inv_mem hbF
      have hbinvW : (⟨(b : ↥(fieldBar q M'))⁻¹, hbinvF⟩ : ↥F₀) ∈ W₀ :=
        (hW₀loc _).mpr ⟨1, b, hnd, by simp [inv_mul_cancel₀ hb00]⟩
      have hbinvR : (b : ↥(fieldBar q M'))⁻¹ ∈ R.integers := (hRW ⟨_, hbinvF⟩).mpr hbinvW
      apply (IsLocalRing.mem_maximalIdeal _).mp hbm
      exact ⟨⟨⟨_, hBR b⟩, ⟨_, hbinvR⟩, Subtype.ext (mul_inv_cancel₀ hb00),
        Subtype.ext (inv_mul_cancel₀ hb00)⟩, rfl⟩
    obtain ⟨b', hb'⟩ := hdvd
    rw [hb', map_mul, hθconst ϖb, (IsLocalRing.residue_eq_zero_iff _).mpr hϖA, zero_mul]

  have hp0 : ∃ p : ↥B, θ p = 0 ∧ resB p ≠ 0 := by
    by_contra hall
    push Not at hall
    have hall' : ∀ Q' : Place (ResidueField ↥A) FSS, Q' ∉ N := by
      intro Q'
      rw [hEnds]
      intro b hb
      obtain ⟨a, ha⟩ := hconst b
      have h0 : θ (b - algebraMap ↥Ab ↥B a) = 0 := by rw [map_sub, ha, sub_self]
      have h1 := hall _ h0
      rw [map_sub, sub_eq_zero] at h1
      have : R.residue ⟨(b : ↥(fieldBar q M')), hb⟩ = resB b := rfl
      rw [this, h1, hresBconst a]
      exact Q'.algebraMap_mem' _
    have hNe : N = ∅ := Finset.eq_empty_of_forall_notMem (fun Q' hQ' => hall' Q' hQ')
    rw [hNe, Finset.card_empty] at hNcard
    omega

  let I' : Ideal ↥resB.range := Ideal.map resB.rangeRestrict (RingHom.ker θ)
  have hI' : I' ≠ ⊤ := by
    intro htop
    have h1 : (1 : ↥resB.range) ∈ I' := htop ▸ Submodule.mem_top
    obtain ⟨p, hp, hp1⟩ := (Ideal.mem_map_iff_of_surjective _ resB.rangeRestrict_surjective).mp h1
    have hp1' : resB p = 1 := by
      have := congrArg Subtype.val hp1
      simpa using this
    have hker : θ (1 - p) = 0 := hkerB _ (by rw [map_sub, map_one, hp1', sub_self])
    rw [map_sub, map_one, (RingHom.mem_ker).mp hp, sub_zero] at hker
    exact one_ne_zero hker
  obtain ⟨O, hDO, hIO⟩ := Ideal.image_subset_nonunits_valuationSubring I' hI'
  have hBO : ∀ b : ↥B, resB b ∈ O := fun b => hDO ⟨b, rfl⟩
  have h𝔭O : ∀ p : ↥B, θ p = 0 → resB p ∈ O.nonunits := fun p hp =>
    hIO ⟨resB.rangeRestrict p, Ideal.mem_map_of_mem _ ((RingHom.mem_ker).mpr hp), rfl⟩
  have hOK : ∀ e : ResidueField ↥A, algebraMap (ResidueField ↥A) FSS e ∈ O := by
    intro e
    obtain ⟨b, hb⟩ := hKO e
    rw [← hb]
    exact hBO b
  have hOKval : ∀ e : ResidueField ↥A, e ≠ 0 → O.valuation (algebraMap (ResidueField ↥A) FSS e) = 1 := by
    intro e he
    refine valuation_eq_one_of_mem_of_inv_mem O (hOK e) ?_ ((map_ne_zero _).mpr he)
    rw [← map_inv₀]
    exact hOK _
  have hOtop : O ≠ ⊤ := by
    obtain ⟨p, hp, hp0⟩ := hp0
    intro htop
    have hnu := h𝔭O p hp
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hnu
    obtain ⟨hmem, hmax⟩ := hnu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    have hinv : (resB p)⁻¹ ∈ O := by rw [htop]; exact ValuationSubring.mem_top _
    exact ⟨⟨⟨_, hmem⟩, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hp0), Subtype.ext (inv_mul_cancel₀ hp0)⟩, rfl⟩

  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hF : ∃ x : ↥(fieldBar q M'), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(fieldBar q M')))
        ↥(fieldBar q M') := by
    haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
      Subgroup.finiteIndex_of_le (CuspForm.Gamma_le_GammaH (q ^ 2 * M') (levelH q M'))
    exact ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _)
  have htr : ∃ t : FSS, Transcendental (ResidueField ↥A) t := by
    have hne : N.Nonempty := by
      rw [← Finset.card_pos, hNcard]
      omega
    obtain ⟨Q₀, -⟩ := hne
    by_contra hno
    push Not at hno
    haveI : Algebra.IsAlgebraic (ResidueField ↥A) FSS :=
      ⟨fun t => by
        have := hno t
        unfold Transcendental at this
        push Not at this
        exact this⟩
    haveI : Algebra.IsIntegral (ResidueField ↥A) FSS := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
    have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := FSS)).2
    apply Q₀.ne_top'
    ext t
    refine ⟨fun _ => ValuationSubring.mem_top _, fun _ => ?_⟩
    obtain ⟨e, rfl⟩ := hsurj t
    exact Q₀.algebraMap_mem' e
  obtain ⟨-, -, xbar, -, hfin⟩ :=
    AlgebraicCurve.RegularProlongation.isCurveOver_and_essFiniteType_of_exists_transcendental hF R htr
  haveI := hfin
  have hPIR : IsPrincipalIdealRing ↥O :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin xbar O hOK hOtop
  obtain ⟨Q, hQO⟩ : ∃ Q : Place (ResidueField ↥A) FSS, Q.toValuationSubring = O :=
    ⟨⟨O, hOK, hOtop, hPIR⟩, rfl⟩
  subst hQO
  have hQN : Q ∉ N := (hEnds Q).mpr (fun b hb => hBO b)
  refine ⟨Q, hQN, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hresQ, -, -, hSloc, hD⟩ := hStalk Q hQN

  have hkey : ∀ g : ↥B, resB g ∈ Q.toValuationSubring.nonunits ↔ θ g = 0 := by
    intro g
    refine ⟨fun hg => ?_, h𝔭O g⟩
    by_contra hne
    obtain ⟨a, ha⟩ := hconst g
    have h0 : θ (g - algebraMap ↥Ab ↥B a) = 0 := by rw [map_sub, ha, sub_self]
    have h1 := h𝔭O _ h0
    rw [map_sub] at h1
    have h2 : resB (algebraMap ↥Ab ↥B a) ∈ Q.toValuationSubring.nonunits := by
      have := sub_mem hg h1
      simpa using this
    rw [hresBconst a, ValuationSubring.mem_nonunits_iff] at h2
    have hne' : IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩ ≠ 0 := by
      rw [← hθconst a, ha]
      exact hne
    exact (ne_of_lt h2) (hOKval _ hne')

  have hfrac : ∀ f : ↥(Sb Q), ∃ g h : ↥B, θ h ≠ 0 ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = g := by
    intro f
    obtain ⟨g, h, hh, hfh⟩ := (hSloc (f : ↥(fieldBar q M'))).mp f.2
    refine ⟨g, h, ?_, hfh⟩
    obtain ⟨hm, hne⟩ := hh (hBR h)
    intro hθ0
    apply hne
    rw [IsLocalRing.residue_eq_zero_iff]
    exact ValuationSubring.coe_mem_nonunits_iff.mp ((hkey h).mpr hθ0)

  have hfP : ∀ (f : ↥(Sb Q)) (g h : ↥B), θ h ≠ 0 →
      (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = g →
      P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ (h : ↥(fieldBar q M')) ≠ 0 ∧
      (h : ↥(fieldBar q M'))⁻¹ ∈ P.toValuationSubring ∧
      (f : ↥(fieldBar q M')) = g * (h : ↥(fieldBar q M'))⁻¹ ∧
      (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧
      P.evalAt (f : ↥(fieldBar q M')) = P.evalAt (g : ↥(fieldBar q M')) * (P.evalAt (h : ↥(fieldBar q M')))⁻¹ ∧
      A.valuation (P.evalAt (h : ↥(fieldBar q M'))) = 1 ∧
      P.evalAt (f : ↥(fieldBar q M')) ∈ A := by
    intro f g h hθh hfh
    have hhval : P.evalAt (h : ↥(fieldBar q M')) ≠ 0 := by
      intro h0
      apply hθh
      rw [hθ, IsLocalRing.residue_eq_zero_iff]
      have : (⟨P.evalAt (h : ↥(fieldBar q M')), (hBVF h).2⟩ : ↥A) = 0 := Subtype.ext h0
      rw [this]
      exact zero_mem _
    have hh0 : (h : ↥(fieldBar q M')) ≠ 0 := fun e => hhval (by rw [e, evalAt_zero])
    have hfeq : (f : ↥(fieldBar q M')) = g * (h : ↥(fieldBar q M'))⁻¹ := by
      rw [← hfh, mul_inv_cancel_right₀ hh0]
    have hginv : (h : ↥(fieldBar q M'))⁻¹ ∈ P.toValuationSubring :=
      inv_mem_of_evalAt_ne_zero P hPrat (hBVF h).1 hhval
    have hfmem : (f : ↥(fieldBar q M')) ∈ P.toValuationSubring := by
      rw [hfeq]
      exact mul_mem (hBVF g).1 hginv
    have hfval : P.evalAt (f : ↥(fieldBar q M')) =
        P.evalAt (g : ↥(fieldBar q M')) * (P.evalAt (h : ↥(fieldBar q M')))⁻¹ := by
      rw [hfeq, P.evalAt_mul_of_mem hPrat (hBVF g).1 hginv, evalAt_inv_of_evalAt_ne_zero P hPrat (hBVF h).1 hhval]
    have hu : IsUnit (⟨P.evalAt (h : ↥(fieldBar q M')), (hBVF h).2⟩ : ↥A) := by
      by_contra hnu
      apply hθh
      rw [hθ, IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hinvA : (P.evalAt (h : ↥(fieldBar q M')))⁻¹ ∈ A := coe_inv_mem_of_isUnit A _ hu
    have hval1 : A.valuation (P.evalAt (h : ↥(fieldBar q M'))) = 1 :=
      valuation_eq_one_of_mem_of_inv_mem A (hBVF h).2 hinvA hhval
    refine ⟨hhval, hh0, hginv, hfeq, hfmem, hfval, hval1, ?_⟩
    rw [hfval]
    exact mul_mem (hBVF g).2 hinvA
  refine (hD P).mpr ⟨hPrat, fun f => ?_, fun f => ?_⟩
  · obtain ⟨g, h, hθh, hfh⟩ := hfrac f
    obtain ⟨-, -, -, -, hfmem, -, -, hfA⟩ := hfP f g h hθh hfh
    exact ⟨hfmem, hfA⟩
  · obtain ⟨g, h, hθh, hfh⟩ := hfrac f
    obtain ⟨hhval, hh0, hginv, hfeq, hfmem, hfval, hval1, hfA⟩ := hfP f g h hθh hfh

    have hL : A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ θ g = 0 := by
      rw [hfval, map_mul, map_inv₀, hval1, inv_one, mul_one, hθ, IsLocalRing.residue_eq_zero_iff,
        ValuationSubring.valuation_lt_one_iff]

    obtain ⟨hfR, hfm, hfres⟩ := hresQ f
    have hresBh1 : Q.toValuationSubring.valuation (resB h) = 1 := by
      have hnot : resB h ∉ Q.toValuationSubring.nonunits := fun hh => hθh ((hkey h).mp hh)
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at hnot
      exact le_antisymm (Q.toValuationSubring.valuation_le_one_iff _ |>.mpr (hBO h)) hnot
    have hresBh0 : resB h ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hresBh1
      exact zero_ne_one hresBh1
    have hprod : R.residue ⟨(f : ↥(fieldBar q M')), hfR⟩ * resB h = resB g := by
      rw [hresB, hresB, ← map_mul]
      congr 1
      exact Subtype.ext hfh
    have hR : χb Q f = 0 ↔ θ g = 0 := by
      rw [← hkey g, ValuationSubring.mem_nonunits_iff, ← hprod, map_mul, hresBh1, mul_one,
        ← ValuationSubring.mem_nonunits_iff]
      constructor
      · intro hχ
        rw [hχ, map_zero, IsLocalRing.residue_eq_zero_iff] at hfres
        exact ValuationSubring.coe_mem_nonunits_iff.mpr hfres
      · intro hnu
        have := (ValuationSubring.coe_mem_nonunits_iff (a := (⟨R.residue ⟨(f : ↥(fieldBar q M')), hfR⟩, hfm⟩ : ↥Q.toValuationSubring))).mp hnu
        rw [← IsLocalRing.residue_eq_zero_iff] at this
        have hfres' := hfres
        rw [this] at hfres'
        exact (algebraMap (ResidueField ↥A) Q.ResidueField).injective (by rw [map_zero]; exact hfres'.symm)
    rw [hL, hR]

end S_ModularCurve_FullLevel_supersingularProlongation_cover_of_affineChart_nodes_of_baseSmoothPointStalks_of_coeffEmb_mem_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_cover_of_affineChart_nodes_of_baseSmoothPointStalks_of_coeffEmb_mem_of_eq_two_of_dvd (solution)
