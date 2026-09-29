-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6f6a93b3-9431-59c5-848a-d7032006c7c6

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
import Theorems.Thm_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open scoped Valued

namespace PlaceDepthAux

open ModularCurve ModularCurve.UVCrossingModel

section Model
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

noncomputable def residueMap (π : W) (E : ℕ) (hE : 1 ≤ E) : UVCrossingModel W (π ^ E) →+* W ⧸ Ideal.span {π} :=
  Ideal.Quotient.lift (uvCrossingIdeal W (π ^ E))
    ((Ideal.Quotient.mk (Ideal.span {π})).comp MvPowerSeries.constantCoeff) (by
      intro F hF
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
      · rintro _ ⟨rfl⟩
        simp only [RingHom.comp_apply, map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C]
        rw [map_zero, zero_mul, zero_sub, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton π)) E hE
      · exact map_zero _
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])

theorem residueMap_mk (π : W) (E : ℕ) (hE : 1 ≤ E) (F : MvPowerSeries (Fin 2) W) :
    residueMap π E hE (mk (π ^ E) F) = Ideal.Quotient.mk (Ideal.span {π}) (MvPowerSeries.constantCoeff F) := rfl

theorem not_isUnit_of_residueMap_eq_zero (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (x : UVCrossingModel W (π ^ E)) (hx : residueMap π E hE x = 0) : ¬ IsUnit x := by
  intro hu
  have hmax : (Ideal.span {π} : Ideal W).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]; exact IsLocalRing.maximalIdeal.isMaximal W
  haveI : Nontrivial (W ⧸ Ideal.span {π}) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  exact not_isUnit_zero (hx ▸ hu.map (residueMap π E hE))

theorem V_not_isUnit (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) : ¬ IsUnit (V (π ^ E)) :=
  not_isUnit_of_residueMap_eq_zero π hπ E hE _ (by
    change residueMap π E hE (mk (π ^ E) (MvPowerSeries.X 1)) = 0
    rw [residueMap_mk, MvPowerSeries.constantCoeff_X, map_zero])

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem U_mul_V (π : W) (E : ℕ) : U (π ^ E) * V (π ^ E) = const (π ^ E) (π ^ E) := by
  change mk (π ^ E) (MvPowerSeries.X 0) * mk (π ^ E) (MvPowerSeries.X 1) = mk (π ^ E) (MvPowerSeries.C (π ^ E))
  rw [← map_mul]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem const_pow (π : W) (E : ℕ) (w : W) (n : ℕ) : const (π ^ E) (w ^ n) = const (π ^ E) w ^ n := by
  change mk (π ^ E) (MvPowerSeries.C (w ^ n)) = mk (π ^ E) (MvPowerSeries.C w) ^ n
  rw [map_pow, map_pow]

theorem eq_zero_of_const_eq_zero (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) (w : W)
    (hw : const (π ^ E) w = 0) : w = 0 := by
  classical
  have hmem : (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) ∈ uvCrossingIdeal W (π ^ E) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  set s : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hs
  have hXX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 = MvPowerSeries.monomial s 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, one_mul]
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) =
      (if s ≤ m then MvPowerSeries.coeff (m - s) g else 0) - π ^ E * MvPowerSeries.coeff m g := by
    intro m
    rw [← hg, mul_comm, sub_mul, hXX, map_sub, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_C_mul, one_mul]
  have hs0 : ¬ s ≤ 0 := by
    intro h
    have := h 0
    simp [hs] at this
  have hsn : ∀ n : ℕ, (n + 1) • s ≠ 0 := by
    intro n h
    have := Finsupp.ext_iff.mp h 0
    simp [hs] at this
  have h0 : w = -(π ^ E * MvPowerSeries.coeff 0 g) := by
    have := hcoeff 0
    rw [MvPowerSeries.coeff_C, if_pos rfl, if_neg hs0, zero_sub] at this
    exact this
  have hrec : ∀ n : ℕ, MvPowerSeries.coeff (n • s) g = π ^ E * MvPowerSeries.coeff ((n + 1) • s) g := by
    intro n
    have := hcoeff ((n + 1) • s)
    rw [MvPowerSeries.coeff_C, if_neg (hsn n), if_pos (by rw [succ_nsmul]; exact le_add_self),
      show (n + 1) • s - s = n • s by rw [succ_nsmul, add_tsub_cancel_right]] at this
    exact (sub_eq_zero.mp this.symm)
  have hdiv : ∀ n : ℕ, MvPowerSeries.coeff 0 g = (π ^ E) ^ n * MvPowerSeries.coeff (n • s) g := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul, zero_nsmul]
    | succ n ih => rw [ih, hrec n, pow_succ, mul_assoc]

  have hg0 : MvPowerSeries.coeff 0 g = 0 := by
    by_contra hne
    have htop : IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff 0 g) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    have hle : ((E * (m + 1) : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff 0 g) := by
      have hd : (π ^ E) ^ (m + 1) ∣ MvPowerSeries.coeff 0 g := ⟨_, hdiv (m + 1)⟩
      have := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hd
      rwa [← pow_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ,
        nsmul_eq_mul, mul_one] at this
    rw [← hm] at hle
    have : E * (m + 1) ≤ m := by exact_mod_cast hle
    nlinarith
  rw [h0, hg0, mul_zero, neg_zero]

end Model

end PlaceDepthAux

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
open ModularCurve.UVCrossingModel in

theorem PlaceDepthAux.exists_xDepth_pow_eq_frame
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧
        c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p := by

  classical
  intro Vp hVp
  haveI : IsAlgClosed (AlgebraicClosure ℚ) := inferInstance

  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply PlaceDepthAux.eq_zero_of_const_eq_zero π hπ E hE π
    rw [← hιϖ, h0, map_zero, map_zero, map_zero]

  have hvϖ1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 :=
    R.valuation_coe_lt_one_of_maximalIdeal_eq_span K w c ϖ hmax
  have hϖQ0 : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hvϖ0 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hϖQ0
  have hvϖpos : 0 < A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := zero_lt_iff.mpr hvϖ0

  obtain ⟨ψ, hψloc, hψ⟩ := R.exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt K w c ϖ hϖ0 hmax hVI Vp hVp

  set z := ι.symm (((hαU.unit⁻¹ : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) * V (π ^ E)) with hz
  have hιz : ι z = ((hαU.unit⁻¹ : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) * V (π ^ E) :=
    ι.apply_symm_apply _
  have hxz : algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) c.x * z =
      algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) (R.nodeConst K w ϖ) ^ E := by
    apply ι.injective
    rw [map_mul, hιx, hιz, map_pow, hιϖ, ← PlaceDepthAux.const_pow, ← PlaceDepthAux.U_mul_V,
      mul_assoc, ← mul_assoc αU, IsUnit.mul_val_inv, one_mul]
  have hzu : ¬ IsUnit z := by
    intro hu
    have h1 : IsUnit (ι z) := hu.map ι
    rw [hιz] at h1
    exact PlaceDepthAux.V_not_isUnit π hπ E hE (isUnit_of_mul_isUnit_right h1)
  have hψz : ¬ IsUnit (ψ z) := fun hu => hzu (IsLocalHom.map_nonunit z hu)
  have hvt : Valued.v ((ψ z : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hψz

  have hψϖ : ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ (R.nodeConst K w ϖ)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
      (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) : (A.valuation).Completion) := by
    rw [hψ, ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst, Vp.evalAt_algebraMap]
  have hprodC : ((Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion) *
      ((ψ z : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
      (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) : (A.valuation).Completion) ^ E := by
    have h0 := congrArg ψ hxz
    rw [map_mul, map_pow] at h0
    have h1 := congrArg (Subtype.val : 𝒪[(A.valuation).Completion] → (A.valuation).Completion) h0
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, hψ, hψϖ] at h1
    exact h1
  have hval : A.valuation (Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q)))) *
      Valued.v ((ψ z : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ E := by
    have h1 := congrArg Valued.v hprodC
    rw [map_mul, map_pow, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply] at h1
    exact h1

  have ha1 : c.xDepth Vp < 1 := by
    show A.valuation (Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q)))) < 1
    rw [R.valuation_evalAt_lt_one_iff_mem_maximalIdeal K w hVI Vp hVp c.x, hmax]
    exact Ideal.subset_span (by simp)
  have ha0 : c.xDepth Vp ≠ 0 := by
    intro h0
    have := hval
    rw [show A.valuation (Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q)))) = c.xDepth Vp from rfl, h0, zero_mul] at this
    exact pow_ne_zero E hvϖ0 this.symm
  have hapos : 0 < c.xDepth Vp := zero_lt_iff.mpr ha0
  have halow : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ E < c.xDepth Vp := by
    rw [← hval]
    calc _ < A.valuation (Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q)))) * 1 := mul_lt_mul_of_pos_left hvt hapos
      _ = c.xDepth Vp := mul_one _
  have hx0 : Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => ha0 (by
    show A.valuation (Vp.evalAt (c.x : ↥(modularFunctionFieldBar (N * q)))) = 0; rw [h, map_zero])

  obtain ⟨m, hm, kk, hk⟩ := A.exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic hvϖ0 hvϖ1 hx0
  change c.xDepth Vp ^ m = _ at hk
  have hk0 : 0 < kk := by
    rw [← zpow_lt_one_iff_right_of_lt_one₀ hvϖpos hvϖ1, ← hk]
    exact pow_lt_one₀ zero_le' ha1 hm.ne'
  have hkE : kk < (m * E : ℕ) := by
    rw [← zpow_lt_zpow_iff_right_of_lt_one₀ hvϖpos hvϖ1, ← hk, zpow_natCast, pow_mul']
    exact pow_lt_pow_left₀ halow zero_le' hm.ne'
  refine ⟨m, hm, kk.toNat, by omega, by omega, ?_⟩
  rw [hk, ← zpow_natCast, Int.toNat_of_nonneg hk0.le]

open ModularCurve.UVCrossingModel in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧
        c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p := by
  exact PlaceDepthAux.exists_xDepth_pow_eq_frame R K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq (solution)
