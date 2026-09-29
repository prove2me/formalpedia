-- Prove2me | solution 1 for ModularCurve.neg_width_le_ord_of_order_eq_mul_ord_of_qExpansion_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c2314ac3-a44b-5672-9928-2ee3729dcb03

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_mul_width
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_neg_width_le_ord_of_order_eq_mul_ord_of_qExpansion_slash
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

noncomputable section

namespace WidthLE

p2m_open "UpperHalfPlane ModularForm Filter Function Complex Function.Complex Matrix.SpecialLinearGroup OnePoint"
open scoped Topology Pointwise Manifold

theorem coe_eq_mapGL (γ : SL(2, ℤ)) : (γ : GL (Fin 2) ℝ) = mapGL ℝ γ := rfl

theorem mapGL_T_zpow (n : ℕ) :
    mapGL ℝ (ModularGroup.T ^ (n : ℤ)) = Matrix.GeneralLinearGroup.upperRightHom (n : ℝ) := by
  have hmat : ((ModularGroup.T ^ (n : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (n : ℤ); 0, 1] := ModularGroup.coe_T_zpow (n : ℤ)
  rw [Units.ext_iff]
  have hval : (↑(mapGL ℝ (ModularGroup.T ^ (n : ℤ))) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1, (n : ℤ); 0, 1]).map (Int.cast : ℤ → ℝ) := by
    rw [← hmat]; rfl
  rw [hval]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom]

theorem natCast_mem_strictPeriods_of_conj_mem (Δ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ)) (n : ℕ)
    (hn : σ * ModularGroup.T ^ n * σ⁻¹ ∈ Δ) :
    (n : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ • ((Δ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul, ← mapGL_T_zpow n, coe_eq_mapGL, ← map_inv, ← map_mul, ← map_mul]
  refine Subgroup.mem_map_of_mem _ ?_
  rwa [zpow_natCast]

theorem one_mem_strictPeriods (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  have h1 : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) = mapGL ℝ ModularGroup.T := by
    rw [← Nat.cast_one, ← mapGL_T_zpow 1]; simp
  rw [h1]
  exact Subgroup.mem_map_of_mem _ hT

theorem conj_T_pow_index_mem (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (σ : SL(2, ℤ)) :
    σ * ModularGroup.T ^ Γ.normalCore.index * σ⁻¹ ∈ Γ := by
  have h1 : ModularGroup.T ^ Γ.normalCore.index ∈ Γ.normalCore :=
    Subgroup.pow_index_mem Γ.normalCore ModularGroup.T
  exact Subgroup.normalCore_le Γ ((Subgroup.normalCore_normal Γ).conj_mem _ h1 σ)

def stab (k : ℤ) (F : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | F ∣[k] γ = F}
  mul_mem' := by
    intro a b ha hb
    show F ∣[k] (a * b) = F
    rw [SlashAction.slash_mul, ha, hb]
  one_mem' := by
    show F ∣[k] (1 : SL(2, ℤ)) = F
    exact SlashAction.slash_one k F
  inv_mem' := by
    intro a ha
    show F ∣[k] a⁻¹ = F
    have h := congrArg (fun G : ℍ → ℂ => G ∣[k] a⁻¹) ha
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h.symm

theorem mem_stab_iff (k : ℤ) (F : ℍ → ℂ) (γ : SL(2, ℤ)) : γ ∈ stab k F ↔ F ∣[k] γ = F := Iff.rfl

variable {Γ : Subgroup SL(2, ℤ)}

theorem le_stab {k : ℤ} (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Γ ≤ stab k ⇑G := by
  intro γ hγ
  rw [mem_stab_iff, SL_slash]
  exact SlashInvariantForm.slash_action_eqn G _ (Subgroup.mem_map_of_mem _ hγ)

theorem neg_one_mem_stab {k : ℤ} (hk : Even k) (F : ℍ → ℂ) : (-1 : SL(2, ℤ)) ∈ stab k F := by
  rw [mem_stab_iff]
  funext τ
  rw [SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have hd : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      (-1 : SL(2, ℤ)))) (τ : ℂ) = -1 := by
    simp [denom]
  rw [hd, Even.neg_one_zpow (Even.neg hk), mul_one]

theorem sup_le_stab {k : ℤ} (hk : Even k) (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ stab k ⇑G :=
  sup_le (le_stab G) ((Subgroup.zpowers_le).mpr (neg_one_mem_stab hk ⇑G))

theorem slash_T_pow_eq {k : ℤ} (G : ℍ → ℂ) (σ : SL(2, ℤ)) (h : ℕ)
    (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ stab k G) :
    (G ∣[k] σ) ∣[k] (ModularGroup.T ^ h) = G ∣[k] σ := by
  rw [mem_stab_iff] at hmem
  have h1 : σ * ModularGroup.T ^ h = (σ * ModularGroup.T ^ h * σ⁻¹) * σ := by group
  rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul, hmem]

theorem periodic_of_slash_T_pow_eq {k : ℤ} (F : ℍ → ℂ) (h : ℕ)
    (hF : F ∣[k] (ModularGroup.T ^ h) = F) : Periodic (F ∘ ofComplex) (h : ℝ) := by

  let Δ : Subgroup SL(2, ℤ) := Subgroup.zpowers (ModularGroup.T ^ h)
  have hΔ : Δ ≤ stab k F := (Subgroup.zpowers_le).mpr hF
  let S : SlashInvariantForm ((Δ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    SlashInvariantForm.mk F (by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
      have := hΔ hδ
      rw [mem_stab_iff, SL_slash] at this
      exact this)
  have hper : (h : ℝ) ∈ ((Δ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    have := natCast_mem_strictPeriods_of_conj_mem Δ 1 h
      (by simpa only [one_mul, inv_one, mul_one] using Subgroup.mem_zpowers (ModularGroup.T ^ h))
    simpa using this
  exact SlashInvariantFormClass.periodic_comp_ofComplex S hper

variable [Γ.FiniteIndex]

theorem coe_translate_SL {k : ℤ} (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    ⇑(ModularForm.translate g (σ : GL (Fin 2) ℝ)) = ⇑g ∣[k] σ := by
  rw [SL_slash]
  exact ModularForm.coe_translate g _

theorem slash_periodic_index {k : ℤ} (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    Periodic ((⇑g ∣[k] σ) ∘ ofComplex) (Γ.normalCore.index : ℝ) := by
  rw [← coe_translate_SL g σ]
  exact SlashInvariantFormClass.periodic_comp_ofComplex
    (ModularForm.translate g (σ : GL (Fin 2) ℝ))
    (natCast_mem_strictPeriods_of_conj_mem Γ σ _ (conj_T_pow_index_mem Γ σ))

theorem slash_mdiff {k : ℤ} (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    MDiff (⇑g ∣[k] σ) := by
  rw [← coe_translate_SL g σ]
  exact ModularFormClass.holo _

theorem index_pos : (0 : ℝ) < (Γ.normalCore.index : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

theorem slash_bddAtImInfty {k : ℤ} (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    IsBoundedAtImInfty (⇑g ∣[k] σ) := by
  haveI hFact : Fact (IsCusp ∞ (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods index_pos
      (natCast_mem_strictPeriods_of_conj_mem Γ σ _ (conj_T_pow_index_mem Γ σ))⟩
  have h := ModularFormClass.bdd_at_infty (f := ModularForm.translate g (σ : GL (Fin 2) ℝ))
  rwa [coe_translate_SL] at h

theorem qExpansion_slash_ne_zero {k : ℤ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (σ : SL(2, ℤ)) (hh : h ≠ 0) :
    qExpansion (Γ.normalCore.index : ℝ) (⇑h ∣[k] σ) ≠ 0 := by
  rw [Ne, qExpansion_eq_zero_iff index_pos (slash_periodic_index h σ) (slash_mdiff h σ)
    (slash_bddAtImInfty h σ)]
  intro h0
  apply hh
  have h1 : ⇑h = (0 : ℍ → ℂ) := by
    have h2 := congrArg (· ∣[k] (σ⁻¹ : SL(2, ℤ))) h0
    simpa only [SL_slash, ← SlashAction.slash_mul, ← map_mul, mul_inv_cancel, map_one,
      SlashAction.slash_one, SlashAction.zero_slash] using h2
  ext τ
  rw [h1]
  rfl

theorem dvd_order_coe {p : PowerSeries ℂ} (hp : p ≠ 0) (m : ℕ)
    (hcoeff : ∀ i : ℕ, ¬ m ∣ i → PowerSeries.coeff i p = 0) :
    (m : ℤ) ∣ (p : LaurentSeries ℂ).order := by
  have hp' : (p : LaurentSeries ℂ) ≠ 0 := by
    intro h0
    apply hp
    have : ((0 : PowerSeries ℂ) : LaurentSeries ℂ) = (p : LaurentSeries ℂ) := by rw [h0]; simp
    exact (HahnSeries.ofPowerSeries_injective this).symm
  have hne := (HahnSeries.coeff_order_eq_zero.not.mpr) hp'
  rw [PowerSeries.coeff_coe] at hne
  split_ifs at hne with hneg
  · exact absurd rfl hne
  · have hdvd : m ∣ ((p : LaurentSeries ℂ).order).natAbs := by
      by_contra hnd
      exact hne (hcoeff _ hnd)
    have h0 : 0 ≤ (p : LaurentSeries ℂ).order := not_lt.mp hneg
    rw [← Int.natAbs_of_nonneg h0]
    exact Int.natCast_dvd_natCast.mpr hdvd

theorem dvd_order_qExpansion {F : ℍ → ℂ} {N : ℕ} (hN : 0 < N) (h : ℕ) (hh : 0 < h)
    (pN : Periodic (F ∘ ofComplex) (N : ℝ)) (ph : Periodic (F ∘ ofComplex) (h : ℝ))
    (dF : MDiff F) (bF : IsBoundedAtImInfty F) (hF0 : qExpansion (N : ℝ) F ≠ 0) :
    ((N / Nat.gcd h N : ℕ) : ℤ) ∣ ((qExpansion (N : ℝ) F : PowerSeries ℂ) : LaurentSeries ℂ).order := by
  set d := Nat.gcd h N with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left N hh
  have hdN : d ∣ N := Nat.gcd_dvd_right h N
  set m := N / d with hm
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hN hdN) hdpos
  have hmd : (m : ℝ) * (d : ℝ) = (N : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdN]

  have pd : Periodic (F ∘ ofComplex) (d : ℝ) := by
    have p1 := (ph.int_mul (Nat.gcdA h N)).add_period (pN.int_mul (Nat.gcdB h N))
    have hbez : ((d : ℤ) : ℂ) = ((h * Nat.gcdA h N + N * Nat.gcdB h N : ℤ) : ℂ) := by
      have := Nat.gcd_eq_gcd_ab h N
      rw [← hd] at this
      exact_mod_cast congrArg (Int.cast : ℤ → ℂ) this
    have heq : ((Nat.gcdA h N : ℤ) : ℂ) * ((h : ℝ) : ℂ) + ((Nat.gcdB h N : ℤ) : ℂ) * ((N : ℝ) : ℂ) =
        ((d : ℝ) : ℂ) := by
      push_cast at hbez ⊢
      linear_combination -hbez
    rw [heq] at p1
    exact p1
  apply dvd_order_coe hF0 m
  intro i hi
  have key := UpperHalfPlane.qExpansion_coeff_mul_width F (d : ℝ) (by exact_mod_cast hdpos) pd dF bF m hmpos i
  rw [hmd] at key
  rw [key, if_neg hi]

theorem dvd_order_qExpansion_slash {k : ℤ} (hk : Even k)
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ))
    (hG : qExpansion (Γ.normalCore.index : ℝ) (⇑G ∣[k] σ) ≠ 0)
    (h : ℕ) (hh : 0 < h) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    ((Γ.normalCore.index / Nat.gcd h Γ.normalCore.index : ℕ) : ℤ) ∣
      ((qExpansion (Γ.normalCore.index : ℝ) (⇑G ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ).order := by
  have ph : Periodic ((⇑G ∣[k] σ) ∘ ofComplex) (h : ℝ) :=
    periodic_of_slash_T_pow_eq _ h (slash_T_pow_eq ⇑G σ h (sup_le_stab hk G hmem))
  exact dvd_order_qExpansion (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) h hh
    (slash_periodic_index G σ) ph (slash_mdiff G σ) (slash_bddAtImInfty G σ) hG

end WidthLE

end

open WidthLE UpperHalfPlane in
set_option maxHeartbeats 3200000 in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (σ : SL(2, ℤ))
    (Φ : ModularCurve.laurentBaseChange ℂ F₀ →+* LaurentSeries ℂ)
    (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀)) (e : ℕ) (he : 0 < e)
    (hpres : ∀ (x : ModularCurve.laurentBaseChange ℂ F₀) (k : ℤ)
          (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 →
        (x : LaurentSeries ℂ) *
            ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) →
        Φ x * ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((h : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((g : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (hord : ∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ≠ 0 → (Φ x).order = e * P.ord x)
    (hyo : (Φ y).order = -(Γ.normalCore.index : ℤ))
    (h : ℕ) (hh : 0 < h) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    -(h : ℤ) ≤ P.ord y := by
  classical
  set N : ℕ := Γ.normalCore.index with hNdef
  have hNpos : 0 < N := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  set d : ℕ := Nat.gcd h N with hddef
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left N hh
  have hdN : d ∣ N := Nat.gcd_dvd_right h N
  have hdh : d ≤ h := Nat.le_of_dvd hh (Nat.gcd_dvd_left h N)
  set m : ℕ := N / d with hmdef
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hNpos hdN) hdpos
  have h1 : (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    one_mem_strictPeriods Γ hT

  have key : ∀ x : ↥(ModularCurve.laurentBaseChange ℂ F₀), x ≠ 0 → (m : ℤ) ∣ (Φ x).order := by
    intro x hx
    obtain ⟨k, g, h₁, hh₁, hxgh⟩ :=
      ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC Γ hT
        (x : LaurentSeries ℂ) (by rw [← hF]; exact x.2)

    have hH : h₁.mul h₁ ≠ 0 := by
      intro h0
      apply hh₁
      have hc : ⇑(h₁.mul h₁) = 0 := by rw [h0]; rfl
      rw [ModularForm.coe_mul] at hc
      apply DFunLike.ext
      intro τ
      have := congrFun hc τ
      simp only [Pi.mul_apply, Pi.zero_apply, mul_self_eq_zero] at this
      simpa using this
    have hxGH : (x : LaurentSeries ℂ) *
        ((qExpansion 1 (⇑(h₁.mul h₁)) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (⇑(g.mul h₁)) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rw [ModularForm.qExpansion_mul one_pos h1, ModularForm.qExpansion_mul one_pos h1, map_mul, map_mul,
        ← mul_assoc, hxgh]
    have e1 := hpres x (k + k) (g.mul h₁) (h₁.mul h₁) hH hxGH
    set A := ((qExpansion (N : ℝ) (⇑(g.mul h₁) ∣[k + k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) with hA
    set B := ((qExpansion (N : ℝ) (⇑(h₁.mul h₁) ∣[k + k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) with hB
    have hBq : qExpansion (N : ℝ) (⇑(h₁.mul h₁) ∣[k + k] σ) ≠ 0 := qExpansion_slash_ne_zero (h₁.mul h₁) σ hH
    have hB0 : B ≠ 0 := by
      intro h0
      exact hBq (HahnSeries.ofPowerSeries_injective
        (h0.trans (map_zero (HahnSeries.ofPowerSeries ℤ ℂ)).symm))
    have hΦx : Φ x ≠ 0 := (map_ne_zero Φ).mpr hx
    have hA0 : A ≠ 0 := by rw [← e1]; exact mul_ne_zero hΦx hB0
    have hAq : qExpansion (N : ℝ) (⇑(g.mul h₁) ∣[k + k] σ) ≠ 0 := by
      intro h0
      apply hA0
      rw [hA, h0, map_zero]
    have hk2 : Even (k + k) := ⟨k, rfl⟩
    have dA : (m : ℤ) ∣ A.order := dvd_order_qExpansion_slash hk2 (g.mul h₁) σ hAq h hh hmem
    have dB : (m : ℤ) ∣ B.order := dvd_order_qExpansion_slash hk2 (h₁.mul h₁) σ hBq h hh hmem
    have hord' : (Φ x).order = A.order - B.order := by
      have := HahnSeries.order_mul hΦx hB0
      rw [e1] at this
      linarith
    rw [hord']
    exact dvd_sub dA dB

  obtain ⟨g₀, hg₀, hg₀1⟩ := AlgebraicCurve.Place.exists_forall_ord_eq_finset ({P} : Finset _) (fun _ => (1 : ℤ))
  have hP1 : P.ord g₀ = 1 := hg₀1 P (Finset.mem_singleton_self P)
  have dme : (m : ℤ) ∣ (e : ℤ) := by
    have := key g₀ hg₀
    rwa [hord g₀ hg₀, hP1, mul_one] at this

  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, map_zero, HahnSeries.order_zero] at hyo
    have : (Γ.normalCore.index : ℤ) = 0 := by linarith
    exact Subgroup.FiniteIndex.index_ne_zero (by exact_mod_cast this)
  have ey : (e : ℤ) * P.ord y = -(N : ℤ) := by rw [← hord y hy0, hyo]
  obtain ⟨c, hc⟩ := dme
  have hmdN : (m : ℤ) * (d : ℤ) = (N : ℤ) := by exact_mod_cast Nat.div_mul_cancel hdN
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hcpos : 0 < c := by
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    rw [hc] at he'
    exact pos_of_mul_pos_right he' (by exact_mod_cast hmpos.le)
  have hcd : c * P.ord y = -(d : ℤ) := by
    have : (m : ℤ) * (c * P.ord y) = (m : ℤ) * (-(d : ℤ)) := by
      rw [← mul_assoc, ← hc, ey, ← hmdN]; ring
    exact mul_left_cancel₀ hm0 this
  have hdh' : (d : ℤ) ≤ (h : ℤ) := by exact_mod_cast hdh
  nlinarith [hcd, hcpos, hdh']

end S_ModularCurve_neg_width_le_ord_of_order_eq_mul_ord_of_qExpansion_slash
end P2MW
export P2MW.S_ModularCurve_neg_width_le_ord_of_order_eq_mul_ord_of_qExpansion_slash (solution)
