-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f155c3f9-3f3f-5d78-9db6-2e23185021bc

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_fixingSubgroup_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_componentMap_frobenius_smul_eq_zero_of_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_frobenius_smul_eq_glueMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_inertia_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_good
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

private theorem WidthCompSp.smul_mem_inertiaInvariants_of_mem_decompositionSubgroup
    {A : ValuationSubring (AlgebraicClosure ℚ)} {M : ℕ}
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.decompositionSubgroup ℚ)
    {z : JZero M} (hz : z ∈ inertiaInvariants A M) :
    σ • z ∈ inertiaInvariants A M := by
  haveI hnorm : (A.inertiaSubgroup ℚ).Normal :=
    inferInstanceAs (Subgroup.Normal (MonoidHom.ker
      (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ)
        (IsLocalRing.ResidueField A))))
  intro τ hτ
  obtain ⟨τ₀, hτ₀, hcoe⟩ := Subgroup.mem_map.mp hτ
  have hcoe' : (τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = τ := hcoe
  have hconj : (⟨σ, hσ⟩ : A.decompositionSubgroup ℚ)⁻¹ * τ₀ * ⟨σ, hσ⟩ ∈
      A.inertiaSubgroup ℚ := by
    simpa [mul_assoc] using hnorm.conj_mem τ₀ hτ₀ (⟨σ, hσ⟩ : A.decompositionSubgroup ℚ)⁻¹
  have hfix : (((⟨σ, hσ⟩ : A.decompositionSubgroup ℚ)⁻¹ * τ₀ * ⟨σ, hσ⟩ :
      A.decompositionSubgroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • z = z :=
    hz _ (Subgroup.mem_map_of_mem _ hconj)
  have hcoe2 : (((⟨σ, hσ⟩ : A.decompositionSubgroup ℚ)⁻¹ * τ₀ * ⟨σ, hσ⟩ :
      A.decompositionSubgroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      = σ⁻¹ * τ * σ := by
    push_cast
    rw [hcoe']
  have hstep : τ • σ • z = σ • ((σ⁻¹ * τ * σ) • z) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  rw [hstep, ← hcoe2, hfix]

private theorem WidthCompSp.smul_eq_pow_smul_smul_of_fix {M : ℕ} (a : JZero M)
    {σ φ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {n : ℕ}
    (hfix : ((φ ^ n * τ)⁻¹ * σ) • a = a) : σ • a = φ ^ n • τ • a := by
  have h := congrArg (fun y => (φ ^ n * τ) • y) hfix
  simp only [smul_smul, mul_inv_cancel_left] at h
  rw [h, mul_smul]

private theorem WidthCompSp.smul_eq_pow_smul_of_fix {A : ValuationSubring (AlgebraicClosure ℚ)}
    {M : ℕ} (x : JZero M) (hxH : x ∈ inertiaInvariants A M)
    {σ φ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {n : ℕ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (hfix : ((φ ^ n * τ)⁻¹ * σ) • x = x) : σ • x = φ ^ n • x := by
  rw [WidthCompSp.smul_eq_pow_smul_smul_of_fix x hfix, (ModularCurve.mem_inertiaInvariants.mp hxH) τ hτ]

private theorem WidthCompSp.frobPow_transport {A : ValuationSubring (AlgebraicClosure ℚ)} {M : ℕ}
    {C G : Type*} [AddCommGroup C] [AddCommGroup G]
    {comp : ↥(inertiaInvariants A M) →+ C} {sp : ↥(inertiaInvariants A M) →+ G} {g : G →+ G}
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : φ ∈ A.decompositionSubgroup ℚ)
    (h11 : ∀ (y : ↥(inertiaInvariants A M)) (hy : φ • (y : JZero M) ∈ inertiaInvariants A M),
      comp y = 0 → comp ⟨φ • (y : JZero M), hy⟩ = 0)
    (h15 : ∀ (y : ↥(inertiaInvariants A M)) (hy : φ • (y : JZero M) ∈ inertiaInvariants A M),
      comp y = 0 → sp ⟨φ • (y : JZero M), hy⟩ = g (sp y))
    (m : ℕ) (y : ↥(inertiaInvariants A M)) (hy0 : comp y = 0) :
    ∃ hm : φ ^ m • (y : JZero M) ∈ inertiaInvariants A M,
      comp ⟨φ ^ m • (y : JZero M), hm⟩ = 0 ∧ sp ⟨φ ^ m • (y : JZero M), hm⟩ = (⇑g)^[m] (sp y) := by
  induction m with
  | zero =>
    have hm : φ ^ 0 • (y : JZero M) ∈ inertiaInvariants A M := by
      rw [pow_zero, one_smul]; exact y.2
    have e : (⟨φ ^ 0 • (y : JZero M), hm⟩ : ↥(inertiaInvariants A M)) = y :=
      Subtype.ext (by
        show φ ^ 0 • (y : JZero M) = (y : JZero M)
        rw [pow_zero, one_smul])
    refine ⟨hm, ?_, ?_⟩
    · rw [e]; exact hy0
    · rw [e, Function.iterate_zero, id]
  | succ m ih =>
    obtain ⟨hm, hc, hs⟩ := ih
    have hmem : φ • (φ ^ m • (y : JZero M)) ∈ inertiaInvariants A M :=
      WidthCompSp.smul_mem_inertiaInvariants_of_mem_decompositionSubgroup hφ hm
    have hm' : φ ^ (m + 1) • (y : JZero M) ∈ inertiaInvariants A M := by
      rw [pow_succ', mul_smul]; exact hmem
    have e : (⟨φ ^ (m + 1) • (y : JZero M), hm'⟩ : ↥(inertiaInvariants A M))
        = ⟨φ • (φ ^ m • (y : JZero M)), hmem⟩ :=
      Subtype.ext (by
        show φ ^ (m + 1) • (y : JZero M) = φ • (φ ^ m • (y : JZero M))
        rw [pow_succ', mul_smul])
    refine ⟨hm', ?_, ?_⟩
    · rw [e]; exact h11 ⟨φ ^ m • (y : JZero M), hm⟩ hmem hc
    · rw [e, h15 ⟨φ ^ m • (y : JZero M), hm⟩ hmem hc, hs, Function.iterate_succ_apply']

private theorem WidthCompSp.frobPow_transport2 {A : ValuationSubring (AlgebraicClosure ℚ)} {M : ℕ}
    {C G : Type*} [Zero C]
    {compf : ↥(inertiaInvariants A M) → C} {spf : ↥(inertiaInvariants A M) → G} {gf : G → G}
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : φ ∈ A.decompositionSubgroup ℚ)
    (h11 : ∀ (y : ↥(inertiaInvariants A M)) (hy : φ • (y : JZero M) ∈ inertiaInvariants A M),
      compf y = 0 → compf ⟨φ • (y : JZero M), hy⟩ = 0)
    (h15 : ∀ (y : ↥(inertiaInvariants A M)) (hy : φ • (y : JZero M) ∈ inertiaInvariants A M),
      compf y = 0 → spf ⟨φ • (y : JZero M), hy⟩ = gf (spf y))
    (m : ℕ) (y : ↥(inertiaInvariants A M)) (hy0 : compf y = 0) :
    ∃ hm : φ ^ m • (y : JZero M) ∈ inertiaInvariants A M,
      compf ⟨φ ^ m • (y : JZero M), hm⟩ = 0 ∧ spf ⟨φ ^ m • (y : JZero M), hm⟩ = gf^[m] (spf y) := by
  induction m with
  | zero =>
    have hm : φ ^ 0 • (y : JZero M) ∈ inertiaInvariants A M := by
      rw [pow_zero, one_smul]; exact y.2
    have e : (⟨φ ^ 0 • (y : JZero M), hm⟩ : ↥(inertiaInvariants A M)) = y :=
      Subtype.ext (by
        show φ ^ 0 • (y : JZero M) = (y : JZero M)
        rw [pow_zero, one_smul])
    refine ⟨hm, ?_, ?_⟩
    · rw [e]; exact hy0
    · rw [e, Function.iterate_zero, id]
  | succ m ih =>
    obtain ⟨hm, hc, hs⟩ := ih
    have hmem : φ • (φ ^ m • (y : JZero M)) ∈ inertiaInvariants A M :=
      WidthCompSp.smul_mem_inertiaInvariants_of_mem_decompositionSubgroup hφ hm
    have hm' : φ ^ (m + 1) • (y : JZero M) ∈ inertiaInvariants A M := by
      rw [pow_succ', mul_smul]; exact hmem
    have e : (⟨φ ^ (m + 1) • (y : JZero M), hm'⟩ : ↥(inertiaInvariants A M))
        = ⟨φ • (φ ^ m • (y : JZero M)), hmem⟩ :=
      Subtype.ext (by
        show φ ^ (m + 1) • (y : JZero M) = φ • (φ ^ m • (y : JZero M))
        rw [pow_succ', mul_smul])
    refine ⟨hm', ?_, ?_⟩
    · rw [e]; exact h11 ⟨φ ^ m • (y : JZero M), hm⟩ hmem hc
    · rw [e, h15 ⟨φ ^ m • (y : JZero M), hm⟩ hmem hc, hs, Function.iterate_succ_apply']

private theorem WidthCompSp.toPic0Pair_glueMap_iterate {K F : Type*} [Field K] [Field F]
    [Algebra K F] {S : Finset (Place K F × Place K F)} {g : SemilinearAut K F}
    (hstab : SemilinearAut.IsNodeStable S g) (m : ℕ) (ξ : GluedPic0 K F S) :
    GluedPic0.toPic0Pair S ((⇑(GluedPic0.glueMap S g hstab))^[m] ξ)
      = ((fun c => g • c)^[m] (GluedPic0.toPic0Pair S ξ).1,
         (fun c => g • c)^[m] (GluedPic0.toPic0Pair S ξ).2) := by
  induction m with
  | zero => simp only [Function.iterate_zero, id]
  | succ m ih =>
    rw [Function.iterate_succ_apply', GluedPic0.toPic0Pair_glueMap, ih,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

private theorem WidthCompSp.smul_iterate_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (m : ℕ) : (fun c : Pic0 K F => g • c)^[m] 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    exact map_zero (DistribSMul.toAddMonoidHom (Pic0 K F) g)

private theorem WidthCompSp.pair_transport {A : ValuationSubring (AlgebraicClosure ℚ)} {M : ℕ}
    {C G Q : Type*} [Zero C]
    {compf : ↥(inertiaInvariants A M) → C} {spf : ↥(inertiaInvariants A M) → G} {gf : G → G}
    {ν : G → Q × Q} {f : Q → Q}
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : φ ∈ A.decompositionSubgroup ℚ)
    (h11 : ∀ (y : ↥(inertiaInvariants A M)) (hy : φ • (y : JZero M) ∈ inertiaInvariants A M),
      compf y = 0 → compf ⟨φ • (y : JZero M), hy⟩ = 0)
    (h15 : ∀ (y : ↥(inertiaInvariants A M)) (hy : φ • (y : JZero M) ∈ inertiaInvariants A M),
      compf y = 0 → spf ⟨φ • (y : JZero M), hy⟩ = gf (spf y))
    (hν : ∀ z : G, ν (gf z) = (f (ν z).1, f (ν z).2))
    (m : ℕ) (y : ↥(inertiaInvariants A M)) (hy0 : compf y = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hxσ : σ • (y : JZero M) ∈ inertiaInvariants A M)
    (hσy : σ • (y : JZero M) = φ ^ m • (y : JZero M)) :
    compf ⟨σ • (y : JZero M), hxσ⟩ = 0 ∧
      ν (spf ⟨σ • (y : JZero M), hxσ⟩) = (f^[m] (ν (spf y)).1, f^[m] (ν (spf y)).2) := by
  obtain ⟨hm, hc, hs⟩ := WidthCompSp.frobPow_transport2 hφ h11 h15 m y hy0
  have e : (⟨σ • (y : JZero M), hxσ⟩ : ↥(inertiaInvariants A M)) = ⟨φ ^ m • (y : JZero M), hm⟩ :=
    Subtype.ext hσy
  have hiter : ∀ (k : ℕ) (z : G), ν (gf^[k] z) = (f^[k] (ν z).1, f^[k] (ν z).2) := by
    intro k
    induction k with
    | zero => intro z; simp only [Function.iterate_zero, id]
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply', hν, ih, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
  refine ⟨?_, ?_⟩
  · rw [e]; exact hc
  · rw [e, hs]; exact hiter m (spf y)

private theorem WidthCompSp.smul_iterate_pair_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (m : ℕ) :
    ((fun c : Pic0 K F => g • c)^[m] (0 : Pic0 K F × Pic0 K F).1,
      (fun c : Pic0 K F => g • c)^[m] (0 : Pic0 K F × Pic0 K F).2) = 0 := by
  have h1 : (0 : Pic0 K F × Pic0 K F).1 = 0 := rfl
  have h2 : (0 : Pic0 K F × Pic0 K F).2 = 0 := rfl
  rw [h1, h2, WidthCompSp.smul_iterate_zero]
  rfl

private theorem WidthCompSp.arithFrobC_smul_pic0 (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K]
    [CharP K ℓ] [IsAlgClosed K] (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (c : Pic0 K (modularFunctionFieldC K N)) :
    arithFrobC ℓ K N • c = frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr c := by
  have hdiv : ∀ E : Divisor K (modularFunctionFieldC K N),
      arithFrobC ℓ K N • E = frobeniusPushforwardGeomLevel K N data hKr E := by
    intro E
    refine Finsupp.induction_linear E ?_ ?_ ?_
    · rw [smul_zero, map_zero]
    · intro f₁ f₂ h₁ h₂
      rw [smul_add, map_add, h₁, h₂]
    · intro w n
      rw [SemilinearAut.smul_single, frobeniusPushforwardGeomLevel_single,
        ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel ℓ K N data hKr w]
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [SemilinearAut.pic0_smul_mk, frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  change arithFrobC ℓ K N • (D : Divisor K (modularFunctionFieldC K N))
    = frobeniusPushforwardGeomLevel K N data hKr (D : Divisor K (modularFunctionFieldC K N))
  exact hdiv _

private theorem WidthCompSp.spPic0_frobPow_smul {A : ValuationSubring (AlgebraicClosure ℚ)}
    {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N] {data : ModularPolynomialData ℓ}
    {hKr : KroneckerCongruence ℓ data} {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] [IsCurveOver k (modularFunctionFieldC k N)]
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ ℓ) (m : ℕ)
    (z : JZero N) :
    S.spPic0 (φ ^ m • z) = (fun c => arithFrobC ℓ k N • c)^[m] (S.spPic0 z) := by
  induction m with
  | zero => rw [pow_zero, one_smul, Function.iterate_zero, id]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih, pow_succ', mul_smul,
      ModularCurve.PlaceSpecialization.spPic0_frobenius_smul_eq S φ hφ,
      WidthCompSp.arithFrobC_smul_pic0 ℓ k N data hKr]

theorem solution (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : σ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 → ∀ a b : JZero N,
              GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp x) = (P.spPic0 a, P.spPic0 b) →
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    (sp ⟨σ • (x : JZero (N * q)), hx⟩)
                  = (P.spPic0 (σ • a), P.spPic0 (σ • b))) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  intro W hW hstab data hKr hα hβ P e comp sp hsurj hker hsp σ hσ x hx hc a b hab
  have hfr := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA
  obtain ⟨φ, hφ⟩ := hfr
  have hL := ModularCurve.JZero.exists_finiteDimensional_fixingSubgroup_smul_eq (N * q) (x : JZero (N * q))
  obtain ⟨L₁, hL₁, hfix₁⟩ := hL
  have hLa := ModularCurve.JZero.exists_finiteDimensional_fixingSubgroup_smul_eq N a
  obtain ⟨L₂, hL₂, hfix₂⟩ := hLa
  have hLb := ModularCurve.JZero.exists_finiteDimensional_fixingSubgroup_smul_eq N b
  obtain ⟨L₃, hL₃, hfix₃⟩ := hLb
  haveI := hL₁
  haveI := hL₂
  haveI := hL₃
  have hGL : ∃ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ A.inertiaSubgroupIn ℚ ∧ (φ ^ n * τ)⁻¹ * σ ∈ (L₁ ⊔ L₂ ⊔ L₃).fixingSubgroup :=
    ModularCurve.exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup q hq A hA φ hφ σ hσ (L₁ ⊔ L₂ ⊔ L₃)
  obtain ⟨n, τ, hτ, hmem⟩ := hGL
  have hκ₁ := hfix₁ _ (IntermediateField.fixingSubgroup_le (le_sup_left.trans le_sup_left) hmem)
  have hκ₂ := hfix₂ _ (IntermediateField.fixingSubgroup_le (le_sup_right.trans le_sup_left) hmem)
  have hκ₃ := hfix₃ _ (IntermediateField.fixingSubgroup_le le_sup_right hmem)
  have hσx : σ • (x : JZero (N * q)) = φ ^ n • (x : JZero (N * q)) :=
    WidthCompSp.smul_eq_pow_smul_of_fix (x : JZero (N * q)) x.2 hτ hκ₁
  have hσa : σ • a = φ ^ n • τ • a := WidthCompSp.smul_eq_pow_smul_smul_of_fix a hκ₂
  have hσb : σ • b = φ ^ n • τ • b := WidthCompSp.smul_eq_pow_smul_smul_of_fix b hκ₃
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_good (ResidueField A) N q hqN
  have h11 := ModularCurve.PlaceSpecialization.componentMap_frobenius_smul_eq_zero_of_eq_zero N q hq hqN A hA W hW hstab data hKr hα hβ P e comp sp hsurj hker hsp φ hφ
  have h15 := ModularCurve.PlaceSpecialization.gluedSpecialization_frobenius_smul_eq_glueMap N q hq hqN A hA W hW hstab data hKr hα hβ P e comp sp hsurj hker hsp φ hφ
  have hT := WidthCompSp.pair_transport hφ.mem_decompositionSubgroup h11 h15
    (GluedPic0.toPic0Pair_glueMap _ _ hstab) n x hc σ hx hσx
  obtain ⟨-, hpair⟩ := hT
  rw [hab] at hpair
  have ha := WidthCompSp.spPic0_frobPow_smul P φ hφ n (τ • a)
  rw [ModularCurve.PlaceSpecialization.spPic0_inertia_smul P τ hτ a, ← hσa] at ha
  have hb := WidthCompSp.spPic0_frobPow_smul P φ hφ n (τ • b)
  rw [ModularCurve.PlaceSpecialization.spPic0_inertia_smul P τ hτ b, ← hσb] at hb
  exact hpair.trans (Prod.ext ha.symm hb.symm)

end

end S_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul (solution)
