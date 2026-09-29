-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/384a7cc8-103d-5e6e-b499-1019dbaa9a0c

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_ModularCurve_UVCrossingModel_moduleFinite_quotient_of_not_le_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_prod_norm_quotient_of_forall_iff_evalAt_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

universe u

p2m_open "AlgebraicCurve IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero.IsLocalRing ModularCurve~UVCrossingModel.U_mul_V P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero.ModularCurve ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const constHom_apply mk_surjective S moduleFinite_quotient_of_not_le_span_pair maximalIdeal_eq_map_maximalIdeal_sup_span_pair"
p2m_open "ModularCurve.UVCrossingModel~U_mul_V ModularCurve~UVCrossingModel.U_mul_V"

variable {W : Type u} [CommRing W]

noncomputable def axisFun (π : W) (j : Fin 2) : Fin 2 → MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  fun i => if i = j then MvPowerSeries.X () else 0

theorem hasSubst_axisFun (π : W) (j : Fin 2) : MvPowerSeries.HasSubst (axisFun π j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    unfold axisFun
    split_ifs <;> simp)

noncomputable def axisHomAmbient (π : W) (j : Fin 2) :
    MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  MvPowerSeries.substAlgHom (hasSubst_axisFun π j)

theorem axisHomAmbient_X (π : W) (j i : Fin 2) :
    axisHomAmbient π j (MvPowerSeries.X i) = axisFun π j i := by
  rw [axisHomAmbient, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X (hasSubst_axisFun π j)]

theorem axisHomAmbient_C (π : W) (j : Fin 2) (w : W) :
    axisHomAmbient π j (MvPowerSeries.C w) = MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [show (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = algebraMap W _ w from rfl, AlgHom.commutes,
    MvPowerSeries.algebraMap_apply]
  rfl

theorem axisHomAmbient_rel (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) :
    axisHomAmbient π j (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C θ) = 0 := by
  rw [map_sub, map_mul, axisHomAmbient_X, axisHomAmbient_X, axisHomAmbient_C,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hdiv), map_zero, sub_zero]
  unfold axisFun
  fin_cases j <;> simp

noncomputable def axisHom (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) :
    UVCrossingModel W θ →+* MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  Ideal.Quotient.lift (uvCrossingIdeal W θ) (axisHomAmbient π j).toRingHom (fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, axisHomAmbient_rel θ π hdiv j, mul_zero])

theorem axisHom_mk (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) (F : MvPowerSeries (Fin 2) W) :
    axisHom θ π hdiv j (mk θ F) = axisHomAmbient π j F :=
  Ideal.Quotient.lift_mk _ _ _

theorem axisHom_U (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) : axisHom θ π hdiv j (U θ) = axisFun π j 0 := by
  rw [U, axisHom_mk, axisHomAmbient_X]

theorem axisHom_V (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) : axisHom θ π hdiv j (V θ) = axisFun π j 1 := by
  rw [V, axisHom_mk, axisHomAmbient_X]

theorem axisHom_const (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) (w : W) :
    axisHom θ π hdiv j (const θ w) = MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [const, axisHom_mk, axisHomAmbient_C]

theorem exists_isPrime_U_mem_const_mem_V_notMem (θ π : W) (hdiv : π ∣ θ) [IsDomain (W ⧸ Ideal.span {π})] :
    ∃ P : Ideal (UVCrossingModel W θ), P.IsPrime ∧ U θ ∈ P ∧ const θ π ∈ P ∧ V θ ∉ P := by
  refine ⟨RingHom.ker (axisHom θ π hdiv 1), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, axisHom_U]; simp [axisFun]
  · rw [RingHom.mem_ker, axisHom_const, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π), map_zero]
  · rw [RingHom.mem_ker, axisHom_V]
    simp only [axisFun, if_true]
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) h
    rw [MvPowerSeries.coeff_X, map_zero, if_pos rfl] at h1
    exact one_ne_zero h1

theorem exists_isPrime_V_mem_const_mem_U_notMem (θ π : W) (hdiv : π ∣ θ) [IsDomain (W ⧸ Ideal.span {π})] :
    ∃ P : Ideal (UVCrossingModel W θ), P.IsPrime ∧ V θ ∈ P ∧ const θ π ∈ P ∧ U θ ∉ P := by
  refine ⟨RingHom.ker (axisHom θ π hdiv 0), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, axisHom_V]; simp [axisFun]
  · rw [RingHom.mem_ker, axisHom_const, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π), map_zero]
  · rw [RingHom.mem_ker, axisHom_U]
    simp only [axisFun, if_true]
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) h
    rw [MvPowerSeries.coeff_X, map_zero, if_pos rfl] at h1
    exact one_ne_zero h1

end ModularCurve.UVCrossingModel

namespace IsLocalRing p2m_export "IsLocalRing" "maximalIdeal mem_maximalIdeal of_surjective'" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.not_map_le_of_forall_lt_eq_bot
    {B R : Type*} [CommRing B] [IsLocalRing B] [CommRing R] [IsLocalRing R]
    (φ : B →+* R) (hmR : (maximalIdeal B).map φ = maximalIdeal R)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮0 : 𝔮 ≠ ⊥)
    (P : Ideal R) [P.IsPrime] (hP : ¬ maximalIdeal R ≤ P)
    (b : B) (hbP : φ b ∈ P) (hb𝔮 : b ∉ 𝔮) :
    ¬ 𝔮.map φ ≤ P := by
  intro hle
  set 𝔭₁ : Ideal B := P.comap φ with h𝔭₁
  haveI : 𝔭₁.IsPrime := Ideal.IsPrime.comap φ
  have h1 : 𝔮 ≤ 𝔭₁ := by rw [h𝔭₁, ← Ideal.map_le_iff_le_comap]; exact hle
  have h2 : 𝔮 < 𝔭₁ := lt_of_le_of_ne h1 (fun h => hb𝔮 (h ▸ (show b ∈ 𝔭₁ from hbP)))
  have h3 : 𝔭₁ ≠ maximalIdeal B := by
    intro h
    apply hP
    rw [← hmR, Ideal.map_le_iff_le_comap, ← h]
  exact h𝔮0 (hht 𝔮 𝔭₁ inferInstance inferInstance h3 h2)

namespace RingEquiv p2m_export "RingEquiv" "mk toRingHom toRingHom_eq_coe finite ext" end RingEquiv
p2m_open_scoped "RingEquiv" in

theorem RingEquiv.map_maximalIdeal_eq {S T : Type*} [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]
    (e : S ≃+* T) : (maximalIdeal S).map e.toRingHom = maximalIdeal T := by
  ext t
  rw [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact (isUnit_map_iff e.symm t).not

p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.map_maximalIdeal_comp_adicCompletion_eq
    {B : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {R : Type*} [CommRing R] [IsLocalRing R]
    (ι : AdicCompletion (maximalIdeal B) B ≃+* R) :
    (maximalIdeal B).map (ι.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B))) = maximalIdeal R := by
  rw [← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map, RingEquiv.map_maximalIdeal_eq]

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap height map_map Quotient.eq_zero_iff_mem mem_span_singleton IsPrime.comap map_comap_of_equiv span eq_top_of_isUnit_mem span_singleton_prime Quotient.mk mul_mem_left map mk_ker Quotient.lift_mk ext mem_span_singleton' IsPrime Quotient.lift span_le mem_sup_right mem_comap comap Quotient.mk_eq_mk_iff_sub_mem Quotient.isDomain_iff_prime subset_span comap_minimalPrimes_eq_of_surjective Quotient.mk_surjective mem_span_singleton_self" end Ideal
p2m_open_scoped "Ideal" in
theorem Ideal.minimalPrimes_finite_of_moduleFinite_quotient {W : Type*} [CommRing W] [IsNoetherianRing W]
    {R : Type*} [CommRing R] [Algebra W R] (J : Ideal R) [Module.Finite W (R ⧸ J)] :
    J.minimalPrimes.Finite := by
  haveI : IsNoetherianRing (R ⧸ J) := isNoetherian_of_tower W (inferInstance : IsNoetherian W (R ⧸ J))
  have h := Ideal.comap_minimalPrimes_eq_of_surjective (Ideal.Quotient.mk_surjective (I := J)) (⊥ : Ideal (R ⧸ J))
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
  rw [h]
  exact (minimalPrimes.finite_of_isNoetherianRing (R ⧸ J)).image _

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel" namespace UVCrossingModel p2m_export "ModularCurve.UVCrossingModel" "mk U V const constHom_apply mk_surjective S moduleFinite_quotient_of_not_le_span_pair maximalIdeal_eq_map_maximalIdeal_sup_span_pair" end ModularCurve.UVCrossingModel
p2m_open_scoped "ModularCurve ModularCurve.UVCrossingModel" in

theorem ModularCurve.UVCrossingModel.U_mul_V {W : Type u} [CommRing W] (θ : W) :
    U θ * V θ = const θ θ := by
  rw [U, V, const, ← map_mul, mk]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.subset_span rfl)

p2m_open_scoped "ModularCurve ModularCurve.UVCrossingModel" in
theorem ModularCurve.UVCrossingModel.const_pow {W : Type u} [CommRing W] (θ w : W) (n : ℕ) :
    const θ (w ^ n) = const θ w ^ n := by
  rw [← constHom_apply, ← constHom_apply, map_pow]

p2m_open "ModularCurve.UVCrossingModel~U_mul_V" in open _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero.ModularCurve.UVCrossingModel Valued ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime]
    (h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮)
    (h𝔮0 : 𝔮 ≠ ⊥)
    (j : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
          𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    (βV : UVCrossingModel W (π ^ E)) (hβV : IsUnit βV) (hιy : ι (algebraMap ↥(R.nodeIntegersOver K w) _ c.y) = V (π ^ E) * βV)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V, V ∈ S ↔ (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0))
    (hcard : (S.card : ℕ∞) = ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
              (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
            const (π ^ E) π ∉ Q.asIdeal),
          (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞)) :
    ∃ (n : PrimeSpectrum (UVCrossingModel W (π ^ E)) → ℕ) (u : PrimeSpectrum (UVCrossingModel W (π ^ E)) → Wˣ),
      (∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
        Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
              (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes → const (π ^ E) π ∉ Q.asIdeal →
          Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (ι (algebraMap ↥(R.nodeIntegersOver K w) _ c.y))) = π ^ n Q * (u Q : W)) ∧
      ((∏ V ∈ S, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) : AlgebraicClosure ℚ) :
          (A.valuation).Completion) =
        ((j (τ.symm (π ^ (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
              (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
              (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), n Q) *
            ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
              (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
              (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), (u Q : W))) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
  classical

  haveI : Nontrivial (UVCrossingModel W (π ^ E)) := ι.injective.nontrivial
  haveI : IsLocalRing (UVCrossingModel W (π ^ E)) := IsLocalRing.of_surjective' ι.toRingHom ι.surjective
  haveI : IsDomain (W ⧸ Ideal.span {π}) :=
    (Ideal.Quotient.isDomain_iff_prime _).2
      ((Ideal.span_singleton_prime hπ.ne_zero).2 ((UniqueFactorizationMonoid.irreducible_iff_prime).1 hπ))
  have hE0 : E ≠ 0 := by omega
  have hdiv : π ∣ π ^ E := dvd_pow_self π hE0
  have hπE : ¬ IsUnit (π ^ E) := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hdiv h)
  have hmRsup := maximalIdeal_eq_map_maximalIdeal_sup_span_pair (W := W) hπE
  have hUm : U (π ^ E) ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [hmRsup]; exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
  have hVm : V (π ^ E) ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [hmRsup]; exact Ideal.mem_sup_right (Ideal.subset_span (by simp))

  set φ : ↥(R.nodeIntegersOver K w) →+* UVCrossingModel W (π ^ E) :=
    ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) with hφ
  set yR : UVCrossingModel W (π ^ E) := ι (algebraMap ↥(R.nodeIntegersOver K w) _ c.y) with hyR
  have hmR : (maximalIdeal ↥(R.nodeIntegersOver K w)).map φ = maximalIdeal (UVCrossingModel W (π ^ E)) :=
    IsLocalRing.map_maximalIdeal_comp_adicCompletion_eq ι
  have hφϖ : φ (R.nodeConst K w ϖ) = const (π ^ E) π := hιϖ
  have hϖ𝔮 : R.nodeConst K w ϖ ∉ 𝔮 := h𝔮 ϖ hϖ0

  have hJU : ¬ Ideal.map φ 𝔮 ≤ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    obtain ⟨P₁, hP₁, hUP, hcP, hVP⟩ := exists_isPrime_U_mem_const_mem_V_notMem (π ^ E) π hdiv
    haveI := hP₁
    intro hle
    have hle' : Ideal.map φ 𝔮 ≤ P₁ :=
      hle.trans (Ideal.span_le.2 (by rintro z (rfl | rfl); exacts [hcP, hUP]))
    exact IsLocalRing.not_map_le_of_forall_lt_eq_bot φ hmR hht 𝔮 h𝔮0 P₁
      (fun h => hVP (h hVm)) (R.nodeConst K w ϖ) (hφϖ ▸ hcP) hϖ𝔮 hle'
  have hJV : ¬ Ideal.map φ 𝔮 ≤ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    obtain ⟨P₂, hP₂, hVP, hcP, hUP⟩ := exists_isPrime_V_mem_const_mem_U_notMem (π ^ E) π hdiv
    haveI := hP₂
    intro hle
    have hle' : Ideal.map φ 𝔮 ≤ P₂ :=
      hle.trans (Ideal.span_le.2 (by rintro z (rfl | rfl); exacts [hcP, hVP]))
    exact IsLocalRing.not_map_le_of_forall_lt_eq_bot φ hmR hht 𝔮 h𝔮0 P₂
      (fun h => hUP (h hUm)) (R.nodeConst K w ϖ) (hφϖ ▸ hcP) hϖ𝔮 hle'
  haveI hJfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Ideal.map φ 𝔮) :=
    moduleFinite_quotient_of_not_le_span_pair π hπ E hE _ hJU hJV

  have hfin : {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) |
      Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal}.Finite := by
    have hmin : (Ideal.map φ 𝔮).minimalPrimes.Finite := Ideal.minimalPrimes_finite_of_moduleFinite_quotient (W := W) _
    have hpre : ((fun Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) => Q.asIdeal) ⁻¹'
        (Ideal.map φ 𝔮).minimalPrimes).Finite :=
      hmin.preimage (fun Q _ Q' _ h => PrimeSpectrum.ext h)
    exact hpre.subset (fun Q hQ => hQ.1)

  have hynot : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)), const (π ^ E) π ∉ Q.asIdeal → yR ∉ Q.asIdeal := by
    intro Q hπQ hyQ
    rw [hιy] at hyQ
    have hVQ : V (π ^ E) ∈ Q.asIdeal := by
      rcases Q.isPrime.mem_or_mem hyQ with h | h
      · exact h
      · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hβV) Q.isPrime.ne_top
    have hpow : const (π ^ E) π ^ E ∈ Q.asIdeal := by
      rw [← const_pow, ← U_mul_V]
      exact Ideal.mul_mem_left _ _ hVQ
    exact hπQ (Q.isPrime.mem_of_pow_mem E hpow)

  have hnorm : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)), const (π ^ E) π ∉ Q.asIdeal →
      Algebra.norm W (Ideal.Quotient.mk Q.asIdeal yR) ≠ 0 := by
    intro Q hπQ
    by_cases H : ∃ s : Finset (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal),
        Nonempty (Module.Basis s W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal))
    · obtain ⟨s, ⟨b⟩⟩ := H
      haveI : Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := Module.Free.of_basis b
      haveI : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := Module.Finite.of_basis b
      rw [Ne, Algebra.norm_eq_zero_iff]
      intro h0
      exact hynot Q hπQ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    · rw [Algebra.norm_eq_one_of_not_exists_basis W H]
      exact one_ne_zero
  have hex : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)), ∃ (n : ℕ) (u : Wˣ),
      (const (π ^ E) π ∉ Q.asIdeal → Algebra.norm W (Ideal.Quotient.mk Q.asIdeal yR) = π ^ n * (u : W)) := by
    intro Q
    by_cases hπQ : const (π ^ E) π ∈ Q.asIdeal
    · exact ⟨0, 1, fun h => absurd hπQ h⟩
    · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hnorm Q hπQ) hπ
      exact ⟨n, u, fun _ => by rw [h, mul_comm]⟩
  choose n u hnu using hex
  refine ⟨n, u, fun Q _ hπQ => hnu Q hπQ, ?_⟩

  rw [prod_evalAt_eq_prod_norm_quotient_of_forall_iff_evalAt_eq_zero R K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ
    αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 h𝔮0 j hj c.y S hS hcard]
  have hprod : (∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
      (_ : Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal),
        Algebra.norm W (Ideal.Quotient.mk Q.asIdeal yR)) =
      π ^ (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), n Q) *
        ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), (u Q : W) := by
    change (∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) |
        Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal},
        Algebra.norm W (Ideal.Quotient.mk Q.asIdeal yR)) =
      π ^ (∑ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) |
          Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal}, n Q) *
        ∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) |
          Q.asIdeal ∈ (Ideal.map φ 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal}, (u Q : W)
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [Set.Finite.mem_toFinset] at hQ
    exact hnu Q hQ.2
  rw [hprod]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero (solution)
