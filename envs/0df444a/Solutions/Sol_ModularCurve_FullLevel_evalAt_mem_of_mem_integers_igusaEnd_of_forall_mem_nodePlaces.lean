-- Prove2me | solution 1 for ModularCurve.FullLevel.evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a0369d61-274d-54f2-8bda-de7e5b8ddb28

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
import Theorems.Thm_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

namespace TubeMaxGlue

open scoped TensorProduct

theorem exists_sum_of_mem_range_productMap
    {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F] [Algebra E F]
    [IsScalarTower k E F]
    (F₀ : IntermediateField k F) (O : Subring ↥F₀)
    (hfrac : ∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g)
    (t : E ⊗[k] ↥F₀) :
    ∃ (n : ℕ) (c : Fin n → E) (a : Fin n → ↥O) (b : ↥O), ((b : ↥F₀) : F) ≠ 0 ∧
      (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k E F) F₀.val t) * ((b : ↥F₀) : F) =
        ∑ i, c i • (((a i : ↥O) : ↥F₀) : F) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, 1, ?_, ?_⟩
    · simp
    · simp
  | tmul e g =>
    obtain ⟨g', h, hg', hh, hh0, hgh⟩ := hfrac g
    refine ⟨1, fun _ => e, fun _ => ⟨g', hg'⟩, ⟨h, hh⟩, ?_, ?_⟩
    · simpa using hh0
    · simp only [Algebra.TensorProduct.productMap_apply_tmul, IsScalarTower.coe_toAlgHom',
        IntermediateField.coe_val, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      have : ((g : F) * (h : F)) = (g' : F) := by
        have := congrArg (fun z : ↥F₀ => (z : F)) hgh
        simpa using this
      rw [Algebra.smul_def, mul_assoc, this]
  | add t₁ t₂ ih₁ ih₂ =>
    obtain ⟨n₁, c₁, a₁, b₁, hb₁, h₁⟩ := ih₁
    obtain ⟨n₂, c₂, a₂, b₂, hb₂, h₂⟩ := ih₂
    refine ⟨n₁ + n₂, Fin.append c₁ c₂, Fin.append (fun i => a₁ i * b₂) (fun i => a₂ i * b₁), b₁ * b₂, ?_, ?_⟩
    · simp only [Subring.coe_mul, IntermediateField.coe_mul]
      exact mul_ne_zero hb₁ hb₂
    · rw [map_add, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Subring.coe_mul, IntermediateField.coe_mul]
      have e1 : ∀ i : Fin n₁, c₁ i • ((((a₁ i : ↥O) : ↥F₀) : F) * (((b₂ : ↥O) : ↥F₀) : F)) =
          (c₁ i • (((a₁ i : ↥O) : ↥F₀) : F)) * (((b₂ : ↥O) : ↥F₀) : F) := fun i => by
        rw [smul_mul_assoc]
      have e2 : ∀ i : Fin n₂, c₂ i • ((((a₂ i : ↥O) : ↥F₀) : F) * (((b₁ : ↥O) : ↥F₀) : F)) =
          (c₂ i • (((a₂ i : ↥O) : ↥F₀) : F)) * (((b₁ : ↥O) : ↥F₀) : F) := fun i => by
        rw [smul_mul_assoc]
      simp only [e1, e2, ← Finset.sum_mul, ← h₁, ← h₂]
      ring

theorem hgen_of_sup_eq_top
    {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F] [Algebra E F]
    [IsScalarTower k E F] [Algebra.IsAlgebraic k E]
    (F₀ : IntermediateField k F)
    (htop : IntermediateField.adjoin k (Set.range (algebraMap E F)) ⊔ F₀ = ⊤)
    (O : Subring ↥F₀)
    (hfrac : ∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) (f : F) :
    ∃ (n : ℕ) (c : Fin n → E) (a : Fin n → ↥O) (b : ↥O), ((b : ↥F₀) : F) ≠ 0 ∧
      f * ((b : ↥F₀) : F) = ∑ i, c i • (((a i : ↥O) : ↥F₀) : F) := by
  classical
  set φ : E →ₐ[k] F := IsScalarTower.toAlgHom k E F with hφ

  have hint : ∀ x ∈ Set.range (algebraMap E F), IsIntegral k x := by
    rintro _ ⟨e, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := k) e).map φ
  haveI : Algebra.IsAlgebraic k ↥(IntermediateField.adjoin k (Set.range (algebraMap E F))) :=
    IntermediateField.isAlgebraic_adjoin hint
  have hE : (IntermediateField.adjoin k (Set.range (algebraMap E F))).toSubalgebra = φ.range := by
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx => (hint x hx).isAlgebraic)]
    apply le_antisymm
    · exact Algebra.adjoin_le (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
    · rintro _ ⟨e, rfl⟩
      exact Algebra.subset_adjoin ⟨e, rfl⟩
  have hmem : f ∈ (Algebra.TensorProduct.productMap φ F₀.val).range := by
    rw [Algebra.TensorProduct.productMap_range, ← hE, IntermediateField.range_val,
      ← IntermediateField.sup_toSubalgebra_of_isAlgebraic_left, htop]
    trivial
  obtain ⟨t, rfl⟩ := hmem
  exact exists_sum_of_mem_range_productMap F₀ O hfrac t

end TubeMaxGlue

namespace TubeMaxGlue

theorem linearIndependent_bot_of_linearIndependent_map
    {k E : Type*} [Field k] [Field E] [Algebra k E]
    (A₀ : ValuationSubring k) {n : ℕ} (c : Fin n → E)
    (hli : LinearIndependent ↥(A₀.toSubring.map (algebraMap k E)) c) :
    LinearIndependent ↥(⊥ : IntermediateField k E) c := by
  classical
  rw [linearIndependent_iff'] at hli ⊢
  intro s g hsum i hi

  have hg : ∀ j, ∃ t : k, algebraMap k E t = (g j : E) := fun j =>
    (IntermediateField.mem_bot.mp (g j).2)
  choose t ht using hg

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ↥A₀) s t
  have hd0 : ((d : ↥A₀) : k) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero d
    exact fun h => this (Subtype.ext h)

  have hr : ∀ j ∈ s, ∃ r : ↥A₀, (r : k) = (d : ↥A₀) * t j := fun j hj => by
    obtain ⟨r, hr⟩ := hd j hj
    refine ⟨r, ?_⟩
    have : (algebraMap (↥A₀) k) r = (r : k) := rfl
    rw [← this, hr, Submonoid.smul_def, Algebra.smul_def]
    rfl
  choose! r hr' using hr
  let g' : Fin n → ↥(A₀.toSubring.map (algebraMap k E)) := fun j =>
    ⟨algebraMap k E (r j : k), Subring.mem_map.mpr ⟨(r j : k), (r j).2, rfl⟩⟩
  have hsum' : ∑ j ∈ s, g' j • c j = 0 := by
    have : ∑ j ∈ s, g' j • c j = algebraMap k E ((d : ↥A₀) : k) * ∑ j ∈ s, g j • c j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      show algebraMap k E (r j : k) * c j = algebraMap k E ((d : ↥A₀) : k) * ((g j : E) * c j)
      rw [hr' j hj, map_mul, ← ht j, mul_assoc]
    rw [this, hsum, mul_zero]
  have h0 := hli s g' hsum' i hi
  have h1 : algebraMap k E (r i : k) = 0 := congrArg Subtype.val h0
  have h2 : (r i : k) = 0 := (map_eq_zero _).mp h1
  have h3 : t i = 0 := by
    have := hr' i hi
    rw [h2] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hd0
  apply Subtype.ext
  show (g i : E) = 0
  rw [← ht i, h3, map_zero]

theorem isAlgebraic_subring_of_charZero {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] [Algebra.IsAlgebraic ℚ E]
    (C : Subring E) (a : E) : IsAlgebraic ↥C a := by
  have hQ : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hZ : IsAlgebraic ℤ a := by
    have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).mpr inferInstance
    exact this.isAlgebraic a
  have hinj : Function.Injective (algebraMap ℤ ↥C) := by
    intro m n h
    have : ((m : ↥C) : E) = ((n : ↥C) : E) := by
      have := congrArg (fun z : ↥C => (z : E)) h
      simpa using this
    exact_mod_cast this
  exact hZ.extendScalars hinj

end TubeMaxGlue

open IsLocalRing

namespace TubeMaxGlue

def comapToVal {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) :
    ↥(A.comap (algebraMap K L)) →+* ↥A where
  toFun x := ⟨algebraMap K L (x : K), (ValuationSubring.mem_comap).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem valuationSubring_eq_of_henselian_comap
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L)
    [HenselianLocalRing ↥(A.comap (algebraMap K L))] [IsDiscreteValuationRing ↥(A.comap (algebraMap K L))]
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (π₀ : K) (hπ₀A : algebraMap K L π₀ ∈ A) (hπ₀0 : π₀ ≠ 0)
    (V : ValuationSubring L) (hCV : ∀ x : K, algebraMap K L x ∈ A → algebraMap K L x ∈ V)
    (hπV : algebraMap K L π₀ ∈ V.nonunits) : V = A := by
  classical
  letI : Algebra ↥(A.comap (algebraMap K L)) ↥A := (comapToVal A).toAlgebra
  have hcompat : ∀ x : ↥(A.comap (algebraMap K L)),
      ((algebraMap ↥(A.comap (algebraMap K L)) ↥A x : ↥A) : L) = algebraMap K L (x : K) := fun x => rfl
  obtain ⟨-, hint⟩ := ValuationSubring.faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap A hcompat

  let g : ↥(A.comap (algebraMap K L)) →+* ↥V :=
    { toFun := fun x => ⟨algebraMap K L (x : K), hCV x ((ValuationSubring.mem_comap).mp x.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }

  have hAV : ∀ a : L, a ∈ A → a ∈ V := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := hint.isIntegral (⟨a, ha⟩ : ↥A)
    have h1 : Polynomial.eval₂ (algebraMap K L |>.comp (A.comap (algebraMap K L)).subtype) a p = 0 := by
      have := congrArg (fun z : ↥A => (z : L)) hpa
      simp only [ZeroMemClass.coe_zero] at this
      rw [← this, Polynomial.eval₂_def, Polynomial.eval₂_def, Polynomial.sum_def, Polynomial.sum_def]
      simp only [AddSubmonoidClass.coe_finsetSum, RingHom.coe_comp, Function.comp_apply]
      rfl
    have h2 : (algebraMap K L).comp (A.comap (algebraMap K L)).subtype = V.subtype.comp g := by
      ext x; rfl
    rw [h2, ← Polynomial.eval₂_map] at h1
    have hI : IsIntegral ↥V a := ⟨p.map g, hp.map g, by
      rw [Polynomial.eval₂_def] at h1 ⊢
      convert h1 using 2
      all_goals rfl⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := L)).mp hI
    rw [← hy]
    exact y.2

  refine le_antisymm ?_ (fun a ha => hAV a ha)
  intro v hv
  by_contra hvA
  have hv0 : v ≠ 0 := by rintro rfl; exact hvA A.zero_mem
  have hvi : v⁻¹ ∈ A := (A.mem_or_inv_mem v).resolve_left hvA
  have hvim : (⟨v⁻¹, hvi⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hvA
    have : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = v := by
      have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A).1 * v⁻¹ = 1 := by
        have := congrArg (fun z : ↥A => (z : L)) u.inv_mul
        rw [hu] at this
        simpa using this
      field_simp at h1
      linear_combination h1
    rw [← this]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have hb0 : (⟨algebraMap K L π₀, hπ₀A⟩ : ↥A) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥A => (z : L)) h
    simp only [ZeroMemClass.coe_zero, map_eq_zero] at this
    exact hπ₀0 this
  obtain ⟨n, w, hw⟩ := hrk ⟨v⁻¹, hvi⟩ ⟨algebraMap K L π₀, hπ₀A⟩ hvim hb0
  have hwL : (v⁻¹) ^ n = algebraMap K L π₀ * (w : L) := by
    have := congrArg (fun z : ↥A => (z : L)) hw
    simpa using this

  obtain ⟨hπVmem, hπVmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hπV
  apply (mem_maximalIdeal _).mp hπVmax
  refine IsUnit.of_mul_eq_one ⟨(w : L) * v ^ n, mul_mem (hAV _ w.2) (pow_mem hv n)⟩ ?_
  apply Subtype.ext
  show algebraMap K L π₀ * ((w : L) * v ^ n) = 1
  rw [← mul_assoc, ← hwL, ← mul_pow, inv_mul_cancel₀ hv0, one_pow]

end TubeMaxGlue

open IsLocalRing AlgebraicCurve

namespace TubeMaxGlue

theorem isUnit_iff_inv_mem {K : Type*} [Field K] (V : ValuationSubring K) (x : K) (hx : x ∈ V) :
    IsUnit (⟨x, hx⟩ : ↥V) ↔ x ≠ 0 ∧ x⁻¹ ∈ V := by
  constructor
  · rintro ⟨u, hu⟩
    have hx0 : x ≠ 0 := by
      intro h0
      apply u.ne_zero
      rw [hu]
      exact Subtype.ext h0
    refine ⟨hx0, ?_⟩
    have : ((u⁻¹ : (↥V)ˣ) : ↥V).1 = x⁻¹ := by
      have h1 := congrArg (fun z : ↥V => (z : K)) u.mul_inv
      rw [hu] at h1
      have h1' : x * ((u⁻¹ : (↥V)ˣ) : ↥V).1 = 1 := h1
      field_simp at h1' ⊢
      linear_combination h1'
    rw [← this]
    exact ((u⁻¹ : (↥V)ˣ) : ↥V).2
  · rintro ⟨hx0, hinv⟩
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem mem_maximalIdeal_iff_not {K : Type*} [Field K] (V : ValuationSubring K) (x : K) (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_inv_mem]
  tauto

theorem mem_nonunits_iff' {K : Type*} [Field K] (V : ValuationSubring K) (x : K) :
    x ∈ V.nonunits ↔ x ∈ V ∧ (x = 0 ∨ x⁻¹ ∉ V) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨h, hm⟩; exact ⟨h, (mem_maximalIdeal_iff_not V x h).mp hm⟩
  · rintro ⟨h, hm⟩; exact ⟨h, (mem_maximalIdeal_iff_not V x h).mpr hm⟩

theorem mem_maximalIdeal_comap_iff {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (x : ↥(A.comap (algebraMap K L))) :
    x ∈ maximalIdeal ↥(A.comap (algebraMap K L)) ↔
      (⟨algebraMap K L (x : K), (ValuationSubring.mem_comap).mp x.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
  have hx : (⟨(x : K), x.2⟩ : ↥(A.comap (algebraMap K L))) = x := rfl
  rw [← hx, mem_maximalIdeal_iff_not, mem_maximalIdeal_iff_not, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

theorem algebraMap_mem_nonunits_of_mem_maximalIdeal
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (a : ↥A) (ha : a ∈ maximalIdeal ↥A) :
    algebraMap L F (a : L) ∈ R.integers.nonunits := by
  have ha' : (⟨(a : L), a.2⟩ : ↥A) = a := rfl
  rw [← ha', mem_maximalIdeal_iff_not] at ha
  rw [mem_nonunits_iff', R.algebraMap_mem_iff, map_eq_zero, ← map_inv₀, R.algebraMap_mem_iff]
  exact ⟨a.2, ha⟩

theorem mem_maximalIdeal_iff_coe_mem_nonunits
    {k F : Type*} [Field k] [Field F] [Algebra k F] {F₀ : IntermediateField k F}
    (W' : ValuationSubring ↥F₀) (R' : ValuationSubring F)
    (htr : ∀ f : ↥F₀, ((f : F) ∈ R' ↔ f ∈ W')) (g : ↥F₀) (hg : g ∈ W') :
    (⟨g, hg⟩ : ↥W') ∈ maximalIdeal ↥W' ↔ ((g : ↥F₀) : F) ∈ R'.nonunits := by
  rw [mem_maximalIdeal_iff_not, mem_nonunits_iff', htr]
  have h1 : ((g : ↥F₀) : F)⁻¹ = ((g⁻¹ : ↥F₀) : F) := by simp
  rw [h1, htr]
  simp only [ZeroMemClass.coe_eq_zero]
  tauto

theorem isRational_of_isCurveOver {L F : Type*} [Field L] [IsAlgClosed L] [Field F] [Algebra L F]
    [IsCurveOver L F] (P : Place L F) : P.IsRational := by
  haveI : Module.Finite L P.ResidueField := IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral L P.ResidueField := Algebra.IsIntegral.of_finite L P.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := P.ResidueField)).2

theorem isDiscreteValuationRing_of_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] (e : R ≃+* S) : IsDiscreteValuationRing S := by
  haveI : IsPrincipalIdealRing S := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  haveI : IsLocalRing S := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro h
  apply IsDiscreteValuationRing.not_a_field' (R := R)
  rw [eq_bot_iff] at h ⊢
  intro r hr
  have : e r ∈ maximalIdeal S := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    rwa [isUnit_map_iff]
  have h0 := h this
  rw [Ideal.mem_bot] at h0 ⊢
  simpa using h0

end TubeMaxGlue

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 48000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (W₀ : ValuationSubring ↥F₀),

      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →

    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ((cy : ↥F₀) ∈ W₀) → (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
      (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) →

    ∀ (Wx : ValuationSubring ↥F₀),
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) →
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) →
                IsDiscreteValuationRing ↥Wx →
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) →
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →

    ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →

    ∀ (FI : Type) [Field FI] [Algebra (ResidueField ↥A) FI] (Rx : RegularProlongation A ↥(fieldBar q M') FI),
      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ Wx)) →

    ∀ (S : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
        (∀ f : ↥F₀, f ∈ O → ((f : ↥(fieldBar q M')) ∈ P.toValuationSubring)) ∧
        (∀ f : ↥O, ¬ IsUnit f → ∃ h : P.evalAt (((f : ↥F₀)) : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) →

    ∀ f : ↥(fieldBar q M'), f ∈ Rx.integers → f ∈ R.integers → (∀ P ∈ S, f ∈ P.toValuationSubring) →
      ∀ P ∈ S, P.evalAt f ∈ A := by
  intro F₀ hK1 hLD W₀ hW₀ O instLoc instNoeth hOW₀ hOk₀ hOres hOfrac E₀ hE₀ hπO cx cy u ι γU γV hxy
    hιconst hιcx hιcy hcyW₀ hcyW₀m hcxW₀m Wx hOWx hWxk₀ hWxdvr hWxunif hcxWxm hcyWxm FSS instF1 instA1 R hR
    FI instF2 instA2 Rx hRx S hS f hfRx hfR hfS P hP
  classical
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
  have hST : IsScalarTower ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdvr
  haveI := hhens

  obtain ⟨hcurve, hess⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
    (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := hcurve
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(fieldBar q M') := hess

  have hπ₀A₀ : π₀ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := (ValuationSubring.mem_comap).mpr hπ
  have hπ₀max : (⟨π₀, hπ₀A₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [hunif]; exact Ideal.mem_span_singleton_self _
  have hπ₀ne : (π₀ : ↥k₀) ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field' (R := ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    rw [hunif, Ideal.span_singleton_eq_bot]
    exact Subtype.ext h0
  have hπ₀Qne : (π₀ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h; apply hπ₀ne; exact_mod_cast h
  have hirr₀ : Irreducible (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  have hπ₀maxA : (⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ : ↥A) ∈ maximalIdeal ↥A :=
    (TubeMaxGlue.mem_maximalIdeal_comap_iff A ⟨π₀, hπ₀A₀⟩).mp hπ₀max
  have hCmem_iff : ∀ c : AlgebraicClosure ℚ, c ∈ ((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↔ ∃ x : ↥k₀, (x : AlgebraicClosure ℚ) ∈ A ∧ (x : AlgebraicClosure ℚ) = c := by
    intro c
    rw [Subring.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, (ValuationSubring.mem_comap).mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, (ValuationSubring.mem_comap).mpr hx, rfl⟩
  have hC : ∀ c : AlgebraicClosure ℚ, c ∈ ((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → c ∈ A := by
    intro c hc; obtain ⟨x, hx, rfl⟩ := (hCmem_iff c).mp hc; exact hx
  let eC : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ≃+* ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.equivMapOfInjective (algebraMap ↥k₀ (AlgebraicClosure ℚ))
    (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have heC_apply : ∀ x : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ((eC x : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ) = ((x : ↥k₀) : AlgebraicClosure ℚ) := fun x => rfl
  haveI : IsDiscreteValuationRing ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := TubeMaxGlue.isDiscreteValuationRing_of_ringEquiv eC
  let ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := eC ⟨π₀, hπ₀A₀⟩
  have hϖval : ((ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ) = (π₀ : AlgebraicClosure ℚ) := rfl
  have hϖ0 : ((ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ) ≠ 0 := by rw [hϖval]; exact hπ₀Qne
  have hϖ : ∀ d : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsLocalRing.residue ↥A ⟨(d : AlgebraicClosure ℚ), hC d d.2⟩ = 0 ↔ ∃ d' : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))), d = ϖ * d' := by
    intro d
    obtain ⟨x, rfl⟩ := eC.surjective d
    rw [IsLocalRing.residue_eq_zero_iff]
    have h1 : (⟨((eC x : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ), hC _ (eC x).2⟩ : ↥A) =
        ⟨algebraMap ↥k₀ (AlgebraicClosure ℚ) (x : ↥k₀), (ValuationSubring.mem_comap).mp x.2⟩ := rfl
    rw [h1, ← TubeMaxGlue.mem_maximalIdeal_comap_iff A x, hunif, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨eC y, ?_⟩
      rw [← map_mul, hy]
    · rintro ⟨d', hd'⟩
      obtain ⟨y, rfl⟩ := eC.surjective d'
      refine ⟨y, ?_⟩
      apply eC.injective
      rw [hd', map_mul]
  have halg : ∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a := fun a _ =>
    TubeMaxGlue.isAlgebraic_subring_of_charZero ((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a
  have hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n := by
    intro a b ha hb
    rcases eq_or_ne a 0 with rfl | ha0
    · exact ⟨1, by simp⟩
    · exact ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal A (q := q) hA b hb a ha ha0
  have hκ' : ∀ a : ↥A, ∃ c : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a - ⟨(c : AlgebraicClosure ℚ), hC c c.2⟩ ∈ maximalIdeal ↥A := by
    intro a
    obtain ⟨c, hcA, h, hm⟩ := hκ (a : AlgebraicClosure ℚ) a.2
    refine ⟨⟨(c : AlgebraicClosure ℚ), (hCmem_iff _).mpr ⟨c, hcA, rfl⟩⟩, ?_⟩
    convert hm
    all_goals try rfl
  have huniq : ∀ V : ValuationSubring (AlgebraicClosure ℚ), (∀ c : AlgebraicClosure ℚ, c ∈ ((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → c ∈ V) →
      ((ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ) ∈ V.nonunits → V = A := by
    intro V hCV hϖV
    refine TubeMaxGlue.valuationSubring_eq_of_henselian_comap (K := ↥k₀) A hrk π₀ hπ hπ₀ne V ?_ hϖV
    intro x hx
    exact hCV _ ((hCmem_iff _).mpr ⟨x, hx, rfl⟩)

  obtain ⟨eO, heO_apply⟩ : ∃ eO : ↥O ≃+* ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))),
      ∀ g : ↥O, ((eO g : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) = ((g : ↥F₀) : ↥(fieldBar q M')) :=
    ⟨O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective,
      fun g => rfl⟩
  have hmemN0 : ∀ f : ↥(fieldBar q M'), f ∈ (O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) ↔ ∃ g : ↥F₀, g ∈ O ∧ (g : ↥(fieldBar q M')) = f := by
    intro f; rw [Subring.mem_map]; rfl
  haveI : IsLocalRing ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) := IsLocalRing.of_surjective' eO.toRingHom eO.surjective
  haveI : IsNoetherianRing ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) := isNoetherianRing_of_ringEquiv ↥O eO
  have hCmem : ∀ c : AlgebraicClosure ℚ, c ∈ ((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ (O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) := by
    intro c hc
    obtain ⟨x, hxA, rfl⟩ := (hCmem_iff c).mp hc
    rw [hmemN0]
    exact ⟨algebraMap ↥k₀ ↥F₀ x, (hOk₀ x).mp hxA, rfl⟩
  have hϖN0 : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ), hCmem ϖ ϖ.2⟩ : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) =
      eO ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩ := by
    apply Subtype.ext; rw [heO_apply]; rfl
  have hSne : ∀ PP : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), PP ∈ S ↔
      (∀ g : ↥(fieldBar q M'), g ∈ (O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) → g ∈ PP.toValuationSubring) ∧
      (∀ g : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))), ¬ IsUnit g → ∃ h : PP.evalAt (g : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) := by
    intro PP
    rw [hS PP]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · obtain ⟨g₀, hg₀, rfl⟩ := (hmemN0 g).mp hg
        exact h1 g₀ hg₀
      · obtain ⟨g₀, rfl⟩ := eO.surjective g
        have hg' : ¬ IsUnit g₀ := fun hu => hg ((isUnit_map_iff eO g₀).mpr hu)
        rw [heO_apply]
        exact h2 g₀ hg'
    · rintro ⟨h1, h2⟩
      refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · exact h1 _ ((hmemN0 _).mpr ⟨g, hg, rfl⟩)
      · have hg' : ¬ IsUnit (eO g) := fun hu => hg ((isUnit_map_iff eO g).mp hu)
        have := h2 (eO g) hg'
        rwa [heO_apply] at this
  have hrat : ∀ PP ∈ S, Place.IsRational PP := fun PP _ => TubeMaxGlue.isRational_of_isCurveOver PP
  have hgen : ∀ g : ↥(fieldBar q M'), ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) (b : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))),
      (b : ↥(fieldBar q M')) ≠ 0 ∧ g * (b : ↥(fieldBar q M')) = ∑ i, c i • ((a i : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) := by
    intro g
    obtain ⟨n, c, a, b, hb, hsum⟩ := @TubeMaxGlue.hgen_of_sup_eq_top ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') _ _ _ _ instAlg _ hST _ F₀ hK1 O hOfrac g
    refine ⟨n, c, fun i => eO (a i), eO b, ?_, ?_⟩
    · rw [heO_apply]; exact hb
    · simp only [heO_apply]; exact hsum
  have hld : ∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))), LinearIndependent ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))) c →
      ∑ i, c i • ((a i : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) = 0 → ∀ i, a i = 0 := by
    intro n c a hli hsum i
    have hli' := TubeMaxGlue.linearIndependent_bot_of_linearIndependent_map (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) c hli
    have hmem : ∀ j, ((a j : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) ∈
        IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) ''
          (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀ := by
      intro j
      obtain ⟨g₀, hg₀, hg₀eq⟩ := (hmemN0 _).mp (a j).2
      have hF₀ : ((a j : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) ∈ F₀ := by rw [← hg₀eq]; exact g₀.2
      exact (le_sup_right : F₀ ≤ _ ⊔ F₀) hF₀
    have hsum' : ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c j) * ((a j : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) = 0 := by
      rw [← hsum]; simp_rw [Algebra.smul_def]
    have := hLD ⊥ inferInstance n c (fun j => ((a j : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M'))) hmem hli' hsum' i
    exact Subtype.ext this
  have hres : ∀ g : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))), ∃ o : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ¬ IsUnit (g - ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (o : AlgebraicClosure ℚ), hCmem o o.2⟩) := by
    intro g
    obtain ⟨g₀, rfl⟩ := eO.surjective g
    obtain ⟨x, hx, hxA, hnu⟩ := hOres (g₀ : ↥F₀) g₀.2
    refine ⟨⟨(x : AlgebraicClosure ℚ), (hCmem_iff _).mpr ⟨x, hxA, rfl⟩⟩, ?_⟩
    intro hu
    apply hnu
    have hc' : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ),
        hCmem _ ((hCmem_iff _).mpr ⟨x, hxA, rfl⟩)⟩ : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) = eO ⟨algebraMap ↥k₀ ↥F₀ x, hx⟩ :=
      Subtype.ext (by rw [heO_apply]; rfl)
    rw [hc', ← map_sub] at hu
    exact (isUnit_map_iff eO _).mp hu

  have h₁ : ∀ g : ↥(fieldBar q M'), g ∈ (O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) → g ∈ R.integers := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := (hmemN0 g).mp hg
    exact (hR g₀).mpr (hOW₀ g₀ hg₀)
  have h₂ : ∀ g : ↥(fieldBar q M'), g ∈ (O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) → g ∈ Rx.integers := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := (hmemN0 g).mp hg
    exact (hRx g₀).mpr (hOWx g₀ hg₀)
  have hϖ₁ : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ) ∈ R.integers.nonunits :=
    TubeMaxGlue.algebraMap_mem_nonunits_of_mem_maximalIdeal R ⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ hπ₀maxA
  have hϖ₂ : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ : ↥((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : AlgebraicClosure ℚ) ∈ Rx.integers.nonunits :=
    TubeMaxGlue.algebraMap_mem_nonunits_of_mem_maximalIdeal Rx ⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ hπ₀maxA
  have hcxW₀ : (cx : ↥F₀) ∈ W₀ := hOW₀ _ cx.2
  have hcxWx : (cx : ↥F₀) ∈ Wx := hOWx _ cx.2
  have hcyWx : (cy : ↥F₀) ∈ Wx := hOWx _ cy.2
  have hx₁ : ((eO cx : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) ∉ R.integers.nonunits := by
    rw [heO_apply, ← TubeMaxGlue.mem_maximalIdeal_iff_coe_mem_nonunits W₀ R.integers hR (cx : ↥F₀) hcxW₀]
    exact hcxW₀m hcxW₀
  have hx₂ : ((eO cx : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) ∈ Rx.integers.nonunits := by
    rw [heO_apply, ← TubeMaxGlue.mem_maximalIdeal_iff_coe_mem_nonunits Wx Rx.integers hRx (cx : ↥F₀) hcxWx]
    exact hcxWxm hcxWx
  have hy₁ : ((eO cy : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) ∈ R.integers.nonunits := by
    rw [heO_apply, ← TubeMaxGlue.mem_maximalIdeal_iff_coe_mem_nonunits W₀ R.integers hR (cy : ↥F₀) hcyW₀]
    exact hcyW₀m hcyW₀
  have hy₂ : ((eO cy : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) : ↥(fieldBar q M')) ∉ Rx.integers.nonunits := by
    rw [heO_apply, ← TubeMaxGlue.mem_maximalIdeal_iff_coe_mem_nonunits Wx Rx.integers hRx (cy : ↥F₀) hcyWx]
    exact hcyWxm hcyWx

  obtain ⟨instDom, instDVR, instCpl, hirr, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hirr₀
  obtain ⟨ê, hê⟩ := IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv eO
  obtain ⟨ι', hι'⟩ : ∃ ι' : AdicCompletion (maximalIdeal ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀),
      ∀ z, ι' z = ι (ê.symm z) := ⟨ê.symm.trans ι, fun z => rfl⟩
  have hêê : ∀ w, ê.symm (ê w) = w := fun w => ê.symm_apply_apply w
  have hι'ι' : ∀ w, ι' (ι'.symm w) = w := fun w => ι'.apply_symm_apply w
  obtain ⟨σ, hconst'⟩ : ∃ σ : AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* AdicCompletion (maximalIdeal ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M'))),
      ∀ o, ι' (σ o) = const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) o :=
    ⟨ι'.symm.toRingHom.comp (constHom ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)), fun o => hι'ι' _⟩

  refine (AlgebraicCurve.NodeAnnulusEngine.isIntegral_and_evalAt_mem_of_mem_ends_of_forall_mem_toValuationSubring
    A S hrat _ hSne hgen _ hC hCmem ϖ hϖ hϖ0 halg hld hrk hres
    (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
      (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩)
    hirr σ ?_ E₀ hE₀ ι' hconst' hκ' huniq
    R.integers Rx.integers h₁ h₂ hϖ₁ hϖ₂ (eO cx) (eO cy) γU γV ?_ ?_ hx₁ hx₂ hy₁ hy₂ f hfR hfRx hfS).2 P hP
  ·
    apply ι'.injective
    rw [hconst', hϖN0, hι', ← hê ⟨algebraMap ↥k₀ ↥F₀ π₀, hπO⟩, hêê]
    exact (hιconst π₀ hπ hπO).symm
  · rw [hι', ← hê cx, hêê]; exact hιcx
  · rw [hι', ← hê cy, hêê]; exact hιcy

end S_ModularCurve_FullLevel_evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces
end P2MW
export P2MW.S_ModularCurve_FullLevel_evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces (solution)
