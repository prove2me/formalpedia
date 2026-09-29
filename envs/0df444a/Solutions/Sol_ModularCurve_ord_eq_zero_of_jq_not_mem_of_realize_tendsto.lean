-- Prove2me | solution 1 for ModularCurve.ord_eq_zero_of_jq_not_mem_of_realize_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7eb9ccff-d036-56b5-ae95-aca189cb52ae

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Theorems.Thm_ModularCurve_exists_modularForm_realize_eventuallyEq_div
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq
import Theorems.Thm_ModularCurve_exists_slot_of_isCusp
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"

set_option autoImplicit false

p2m_open "UpperHalfPlane ModularForm Filter Function Complex Function.Complex Matrix.SpecialLinearGroup OnePoint"
open scoped MatrixGroups Topology CongruenceSubgroup Pointwise Manifold

noncomputable section

namespace S3CuspLimit

variable {k : ℤ}

private theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (σ : SL(2, ℤ)) :
    σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have h1 : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have h2 : σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ h1 σ
  rw [CongruenceSubgroup.Gamma0_mem]
  obtain ⟨-, -, hc, -⟩ := CongruenceSubgroup.Gamma_mem.mp h2
  exact hc

private theorem coe_eq_mapGL (γ : SL(2, ℤ)) : (γ : GL (Fin 2) ℝ) = mapGL ℝ γ := rfl

private theorem mapGL_T_zpow (N : ℕ) :
    mapGL ℝ (ModularGroup.T ^ (N : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
  have hmat : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (N : ℤ); 0, 1] := ModularGroup.coe_T_zpow (N : ℤ)
  rw [Units.ext_iff]
  have hval : (↑(mapGL ℝ (ModularGroup.T ^ (N : ℤ))) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1, (N : ℤ); 0, 1]).map (Int.cast : ℤ → ℝ) := by
    rw [← hmat]; rfl
  rw [hval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom]

private theorem natCast_mem_strictPeriods_translate (N : ℕ) (σ : SL(2, ℤ)) :
    (N : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ •
        ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul, ← mapGL_T_zpow N, coe_eq_mapGL, ← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ (conj_T_zpow_mem_Gamma0 N σ)

private theorem coe_translate_SL {N : ℕ} (g : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (σ : SL(2, ℤ)) :
    ⇑(ModularForm.translate g (σ : GL (Fin 2) ℝ)) = ⇑g ∣[k] σ := by
  rw [SL_slash]
  exact ModularForm.coe_translate g _

private theorem slash_periodic {N : ℕ} (g : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (σ : SL(2, ℤ)) : Periodic ((⇑g ∣[k] σ) ∘ ofComplex) (N : ℝ) := by
  rw [← coe_translate_SL g σ]
  exact SlashInvariantFormClass.periodic_comp_ofComplex
    (ModularForm.translate g (σ : GL (Fin 2) ℝ))
    (natCast_mem_strictPeriods_translate N σ)

private theorem slash_mdiff {N : ℕ} (g : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (σ : SL(2, ℤ)) : MDiff (⇑g ∣[k] σ) := by
  rw [← coe_translate_SL g σ]
  exact ModularFormClass.holo _

private theorem slash_bddAtImInfty {N : ℕ} [NeZero N]
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    IsBoundedAtImInfty (⇑g ∣[k] σ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  haveI hFact : Fact (IsCusp ∞ (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ •
      ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods hN (natCast_mem_strictPeriods_translate N σ)⟩
  have h := ModularFormClass.bdd_at_infty
    (f := ModularForm.translate g (σ : GL (Fin 2) ℝ))
  rwa [coe_translate_SL] at h

private theorem slash_analyticAt_cusp {N : ℕ} [NeZero N]
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction N (⇑g ∣[k] σ)) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    (slash_periodic g σ) (slash_mdiff g σ) (slash_bddAtImInfty g σ)

private theorem slash_eq_self_of_Gamma0_one
    (g : ModularForm (CongruenceSubgroup.Gamma0 1) k) (σ : SL(2, ℤ)) :
    ⇑g ∣[k] σ = ⇑g := by
  have hσ : mapGL ℝ σ ∈
      ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _))
  have h := SlashInvariantForm.slash_action_eqn g _ hσ
  rw [SL_slash, coe_eq_mapGL]
  exact h

private def restrictGamma0 (N : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 1) k) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toSlashInvariantForm :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ => SlashInvariantForm.slash_action_eqn f γ <| by
        refine Subgroup.map_mono (fun x _ => ?_) hγ
        exact CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _) }
  holo' := ModularFormClass.holo f
  bdd_at_cusps' {c} hc := ModularFormClass.bdd_at_cusps (f := f) <| hc.mono <|
    Subgroup.map_mono fun x _ => CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _)

private theorem coe_restrictGamma0 (N : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 1) k) :
    ⇑(restrictGamma0 N f) = ⇑f := rfl

private theorem qExpansion_injOn_triple {h : ℝ} (hh : 0 < h) {f₁ f₂ : ℍ → ℂ}
    (p₁ : Periodic (f₁ ∘ ofComplex) h) (d₁ : MDiff f₁) (b₁ : IsBoundedAtImInfty f₁)
    (p₂ : Periodic (f₂ ∘ ofComplex) h) (d₂ : MDiff f₂) (b₂ : IsBoundedAtImInfty f₂)
    (hq : qExpansion h f₁ = qExpansion h f₂) : f₁ = f₂ := by
  have hA1 := analyticAt_cuspFunction_zero hh p₁ d₁ b₁
  have hA2 := analyticAt_cuspFunction_zero hh p₂ d₂ b₂
  have hsub : qExpansion h (f₁ - f₂) = 0 := by
    rw [qExpansion_sub hA1 hA2, hq, sub_self]
  have psub : Periodic ((f₁ - f₂) ∘ ofComplex) h := p₁.sub p₂
  have dsub : MDiff (f₁ - f₂) := d₁.sub d₂
  have bsub : IsBoundedAtImInfty (f₁ - f₂) := b₁.sub b₂
  have h0 : f₁ - f₂ = 0 := by
    rw [← qExpansion_eq_zero_iff hh psub dsub bsub]
    exact hsub
  exact sub_eq_zero.mp h0

private theorem exists_chart {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (pF : Periodic (F ∘ ofComplex) N) (dF : MDiff F) (bF : IsBoundedAtImInfty F)
    (hF0 : qExpansion N F ≠ 0) :
    ∃ u : ℂ → ℂ, ContinuousAt u 0 ∧
      u 0 = (qExpansion N F).coeff ((qExpansion N F).order.toNat) ∧ u 0 ≠ 0 ∧
      ∀ τ : ℍ, F τ = Periodic.qParam N τ ^ ((qExpansion N F).order.toNat) *
        u (Periodic.qParam N τ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set P := qExpansion N F with hP

  have hsummN : Summable fun n : ℕ => ‖P.coeff n‖ * (1 / 2 : ℝ) ^ n := by
    letI : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
    have h1 : HasSum (fun n : ℕ => P.coeff n • ((1 / 2 : ℝ) : ℂ) ^ n)
        (cuspFunction N F ((1 / 2 : ℝ) : ℂ)) :=
      hasSum_qExpansion_of_norm_lt hN pF dF bF (by
        rw [Complex.norm_real]
        norm_num)
    refine (summable_norm_iff.mpr h1.summable).congr fun n => ?_
    rw [norm_smul, norm_pow, Complex.norm_real]
    norm_num
  have hsummShift : Summable fun j : ℕ => ‖P.coeff ((P.order.toNat) + j)‖ * (1 / 2 : ℝ) ^ j := by
    have h1 : Summable fun j : ℕ =>
        ‖P.coeff (j + P.order.toNat)‖ * (1 / 2 : ℝ) ^ (j + P.order.toNat) :=
      (summable_nat_add_iff (f := fun n : ℕ => ‖P.coeff n‖ * (1 / 2 : ℝ) ^ n)
        (P.order.toNat)).mpr hsummN
    have h2 := h1.mul_right ((2 : ℝ) ^ P.order.toNat)
    refine h2.congr fun j => ?_
    have hpow : ((1 : ℝ) / 2) ^ P.order.toNat * (2 : ℝ) ^ P.order.toNat = 1 := by
      rw [← mul_pow]
      norm_num
    rw [pow_add, add_comm j P.order.toNat]
    linear_combination ‖P.coeff (P.order.toNat + j)‖ * ((1 : ℝ) / 2) ^ j * hpow

  set u : ℂ → ℂ := fun z => ∑' j : ℕ, P.coeff (P.order.toNat + j) * z ^ j with hu
  have hucont : ContinuousOn u (Metric.ball (0 : ℂ) (1 / 2)) := by
    refine continuousOn_tsum (fun j => ?_) hsummShift fun j z hz => ?_
    · exact (continuous_const.mul (continuous_pow j)).continuousOn
    · rw [norm_mul, norm_pow]
      gcongr
      exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  have huCA : ContinuousAt u 0 :=
    hucont.continuousAt (Metric.ball_mem_nhds _ (by norm_num))
  have hu0 : u 0 = P.coeff (P.order.toNat) := by
    have hval : u 0 = ∑' j : ℕ, P.coeff (P.order.toNat + j) * (0 : ℂ) ^ j := rfl
    rw [hval, tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
    simp
  have hum : P.coeff (P.order.toNat) ≠ 0 := PowerSeries.coeff_order hF0
  refine ⟨u, huCA, hu0, by rw [hu0]; exact hum, fun τ => ?_⟩
  set z := Periodic.qParam (N : ℝ) (τ : ℂ) with hz
  have hz1 : ‖z‖ < 1 := UpperHalfPlane.norm_qParam_lt_one N τ
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hsum : HasSum (fun n : ℕ => P.coeff n • z ^ n) (F τ) :=
    hasSum_qExpansion hN pF dF bF τ
  have hshift : HasSum (fun j : ℕ => P.coeff (j + P.order.toNat) • z ^ (j + P.order.toNat))
      (F τ) := by
    have hvan : ∑ i ∈ Finset.range (P.order.toNat), P.coeff i • z ^ i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [PowerSeries.coeff_of_lt_order_toNat i (Finset.mem_range.mp hi), zero_smul]
    have h4 := (hasSum_nat_add_iff' (P.order.toNat)).mpr hsum
    rwa [hvan, sub_zero] at h4
  have husum : HasSum (fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j)
      (F τ / z ^ P.order.toNat) := by
    have h2 : HasSum (fun j : ℕ => (P.coeff (P.order.toNat + j) * z ^ j) * z ^ P.order.toNat)
        (F τ) := by
      have heq : (fun j : ℕ => (P.coeff (P.order.toNat + j) * z ^ j) * z ^ P.order.toNat) =
          fun j : ℕ => P.coeff (j + P.order.toNat) • z ^ (j + P.order.toNat) := by
        funext j
        rw [smul_eq_mul, pow_add, add_comm j (P.order.toNat)]
        ring
      rw [heq]
      exact hshift
    have h3 := h2.div_const (z ^ P.order.toNat)
    have heq2 : (fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j * z ^ P.order.toNat /
        z ^ P.order.toNat) = fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j := by
      funext j
      rw [mul_div_assoc, div_self (pow_ne_zero _ hz0), mul_one]
    rwa [heq2] at h3
  have huz : u z = F τ / z ^ P.order.toNat := husum.tsum_eq
  rw [huz, mul_div_cancel₀ _ (pow_ne_zero _ hz0)]

private theorem eventually_ne_zero_atImInfty {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (pF : Periodic (F ∘ ofComplex) N) (dF : MDiff F) (bF : IsBoundedAtImInfty F)
    (hF0 : qExpansion N F ≠ 0) : ∀ᶠ τ : ℍ in atImInfty, F τ ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨u, hu, -, hu0, hid⟩ := exists_chart pF dF bF hF0
  have h1 : Tendsto (fun τ : ℍ => u (Periodic.qParam N τ)) atImInfty (𝓝 (u 0)) :=
    hu.tendsto.comp (qParam_tendsto_atImInfty hN)
  filter_upwards [h1.eventually_ne hu0] with τ hτ
  rw [hid τ]
  exact mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) hτ

private theorem tendsto_div_atImInfty_of_triple {N : ℕ} [NeZero N] {G H : ℍ → ℂ}
    (pG : Periodic (G ∘ ofComplex) N) (dG : MDiff G) (bG : IsBoundedAtImInfty G)
    (pH : Periodic (H ∘ ofComplex) N) (dH : MDiff H) (bH : IsBoundedAtImInfty H)
    (hG0 : qExpansion N G ≠ 0) (hH0 : qExpansion N H ≠ 0)
    (hord : (qExpansion N G).order = (qExpansion N H).order) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : ℍ => G τ / H τ) atImInfty (𝓝 L) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨uG, cG, -, nG, idG⟩ := exists_chart pG dG bG hG0
  obtain ⟨uH, cH, -, nH, idH⟩ := exists_chart pH dH bH hH0
  have hm : (qExpansion (N : ℝ) G).order.toNat = (qExpansion (N : ℝ) H).order.toNat := by
    rw [hord]
  refine ⟨uG 0 / uH 0, div_ne_zero nG nH, ?_⟩
  have hTG : Tendsto (fun τ : ℍ => uG (Periodic.qParam N τ)) atImInfty (𝓝 (uG 0)) :=
    cG.tendsto.comp (qParam_tendsto_atImInfty hN)
  have hTH : Tendsto (fun τ : ℍ => uH (Periodic.qParam N τ)) atImInfty (𝓝 (uH 0)) :=
    cH.tendsto.comp (qParam_tendsto_atImInfty hN)
  refine (hTG.div hTH nH).congr fun τ => ?_
  have hqne : Periodic.qParam (N : ℝ) (τ : ℂ) ^ (qExpansion (N : ℝ) H).order.toNat ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  rw [Pi.div_apply, idG τ, idH τ, hm, mul_div_mul_left _ _ hqne]

private theorem div_comp_smul_eq_div_slash (k : ℤ) (g h : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    g (σ • τ) / h (σ • τ) = (g ∣[k] σ) τ / (h ∣[k] σ) τ := by
  rw [SL_slash_apply, SL_slash_apply,
    mul_div_mul_right _ _ (zpow_ne_zero _ (denom_ne_zero _ τ))]

private theorem qExpansion_slash_ne_zero {N : ℕ} [NeZero N]
    (h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) (hh : h ≠ 0) :
    qExpansion N (⇑h ∣[k] σ) ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [Ne, qExpansion_eq_zero_iff hN (slash_periodic h σ) (slash_mdiff h σ)
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

private theorem exists_tendsto_div_comp_smul (N : ℕ) [NeZero N]
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ))
    (hg : qExpansion N (⇑g ∣[k] σ) ≠ 0) (hh : qExpansion N (⇑h ∣[k] σ) ≠ 0)
    (hord : (qExpansion N (⇑g ∣[k] σ)).order = (qExpansion N (⇑h ∣[k] σ)).order) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => g (σ • τ) / h (σ • τ)) atImInfty (𝓝 L) := by
  obtain ⟨L, hL, hT⟩ := tendsto_div_atImInfty_of_triple
    (slash_periodic g σ) (slash_mdiff g σ) (slash_bddAtImInfty g σ)
    (slash_periodic h σ) (slash_mdiff h σ) (slash_bddAtImInfty h σ) hg hh hord
  refine ⟨L, hL, hT.congr fun τ => ?_⟩
  exact (div_comp_smul_eq_div_slash k (⇑g) (⇑h) σ τ).symm

private theorem qParam_one_eq_pow (N : ℕ) [NeZero N] (z : ℂ) :
    Periodic.qParam 1 z = Periodic.qParam N z ^ (N : ℕ) := by
  unfold Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_natCast_coeff {F : ℍ → ℂ} (N : ℕ) [NeZero N]
    (p1 : Periodic (F ∘ ofComplex) 1) (dF : MDiff F) (bF : IsBoundedAtImInfty F)
    (n : ℕ) :
    (qExpansion N F).coeff n =
      if N ∣ n then (qExpansion 1 F).coeff (n / N) else 0 := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have pN : Periodic (F ∘ ofComplex) (N : ℝ) := by
    simpa using p1.nat_mul N
  set c : ℕ → ℂ := fun j => if N ∣ j then (qExpansion 1 F).coeff (j / N) else 0 with hc
  have key : ∀ τ : ℍ, HasSum (fun j : ℕ => c j • Periodic.qParam N τ ^ j) (F τ) := by
    intro τ
    have h1 : HasSum (fun j : ℕ => (qExpansion 1 F).coeff j • Periodic.qParam 1 τ ^ j)
        (F τ) := hasSum_qExpansion one_pos p1 dF bF τ
    have h2 : ∀ j : ℕ, (qExpansion 1 F).coeff j • Periodic.qParam 1 (τ : ℂ) ^ j =
        c (N * j) • Periodic.qParam N (τ : ℂ) ^ (N * j) := by
      intro j
      rw [qParam_one_eq_pow N, ← pow_mul, hc]
      simp [Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero (NeZero.ne N))]
    have hinj : Function.Injective (fun j : ℕ => N * j) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) hab
    have hoff : ∀ j : ℕ, j ∉ Set.range (fun i : ℕ => N * i) →
        c j • Periodic.qParam N (τ : ℂ) ^ j = 0 := by
      intro j hj
      have hdvd : ¬ N ∣ j := by
        rintro ⟨i, rfl⟩
        exact hj ⟨i, rfl⟩
      rw [hc]
      simp [hdvd]
    simp only [h2] at h1
    exact (hinj.hasSum_iff hoff).mp h1
  have hA : AnalyticAt ℂ (cuspFunction (N : ℝ) F) 0 :=
    analyticAt_cuspFunction_zero hN pN dF bF
  letI : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, fun _ _ hfg => hfg⟩
  exact (qExpansion_coeff_unique F hN hA key n).symm

end S3CuspLimit

namespace S3c

private def _root_.S3c.Lq (n : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion n f)

p2m_export "S3c" "Lq"
private theorem Lq_def (n : ℝ) (f : ℍ → ℂ) :
    Lq n f = ((qExpansion n f : PowerSeries ℂ) : LaurentSeries ℂ) := rfl

private theorem Lq_eq_zero_iff (n : ℝ) (f : ℍ → ℂ) : Lq n f = 0 ↔ qExpansion n f = 0 := by
  rw [Lq]
  constructor
  · intro h
    exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

private theorem Lq_zero_fun (n : ℝ) : Lq n (0 : ℍ → ℂ) = 0 := by
  rw [Lq_eq_zero_iff]
  exact qExpansion_zero n

section Generic

variable {Γ : Subgroup (GL (Fin 2) ℝ)} (σ : SL(2, ℤ)) (N : ℕ) [NeZero N]

private def cuspRatio {k : ℤ} (g h : ModularForm Γ k) : LaurentSeries ℂ :=
  Lq N (⇑g ∣[k] σ) / Lq N (⇑h ∣[k] σ)

private theorem coe_translate_SL {k : ℤ} (g : ModularForm Γ k) :
    ⇑(ModularForm.translate g (σ : GL (Fin 2) ℝ)) = ⇑g ∣[k] σ := by
  rw [ModularForm.coe_translate, SL_slash]

private theorem slash_ne_zero {k : ℤ} {h : ModularForm Γ k} (hh : h ≠ 0) : ⇑h ∣[k] σ ≠ 0 := by
  intro H
  apply hh
  have key : ⇑h = (⇑h ∣[k] σ) ∣[k] σ⁻¹ := by
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  rw [H, SlashAction.zero_slash] at key
  exact DFunLike.coe_injective (key.trans ModularForm.coe_zero.symm)

variable (hN : (N : ℝ) ∈ (ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹ • Γ).strictPeriods)

include hN in
private theorem translate_ne_zero_iff {k : ℤ} (h : ModularForm Γ k) :
    Lq N (⇑h ∣[k] σ) ≠ 0 ↔ h ≠ 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [ne_eq, Lq_eq_zero_iff, ← coe_translate_SL,
    ModularForm.qExpansion_eq_zero_iff hN0 hN (ModularForm.translate h (σ : GL (Fin 2) ℝ))]
  constructor
  · intro H rfl
    apply H
    have key : ⇑(ModularForm.translate (0 : ModularForm Γ k) (σ : GL (Fin 2) ℝ)) = 0 := by
      rw [coe_translate_SL, ModularForm.coe_zero, SlashAction.zero_slash]
    exact DFunLike.coe_injective (key.trans ModularForm.coe_zero.symm)
  · intro H H'
    exact slash_ne_zero σ H (by rw [← coe_translate_SL, H', ModularForm.coe_zero])

include hN in
private theorem Lq_slash_ne_zero {k : ℤ} {h : ModularForm Γ k} (hh : h ≠ 0) : Lq N (⇑h ∣[k] σ) ≠ 0 :=
  (translate_ne_zero_iff σ N hN h).2 hh

include hN in

private theorem Lq_slash_mul [Γ.HasDetOne] {k k' : ℤ} (g : ModularForm Γ k) (g' : ModularForm Γ k') :
    Lq N (⇑(g.mul g') ∣[k + k'] σ) = Lq N (⇑g ∣[k] σ) * Lq N (⇑g' ∣[k'] σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [ModularForm.coe_mul, mul_slash_SL2, Lq, Lq, Lq, ← map_mul, ← coe_translate_SL,
    ← coe_translate_SL,
    ← ModularForm.qExpansion_mul_coe hN0 hN (ModularForm.translate g (σ : GL (Fin 2) ℝ))
      (ModularForm.translate g' (σ : GL (Fin 2) ℝ))]

include hN in

private theorem Lq_slash_add {k : ℤ} (A B : ModularForm Γ k) :
    Lq N (⇑(A + B) ∣[k] σ) = Lq N (⇑A ∣[k] σ) + Lq N (⇑B ∣[k] σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [ModularForm.coe_add, SlashAction.add_slash, Lq, Lq, Lq, ← map_add, ← coe_translate_SL,
    ← coe_translate_SL,
    ← ModularForm.qExpansion_add hN0 hN (ModularForm.translate A (σ : GL (Fin 2) ℝ))
      (ModularForm.translate B (σ : GL (Fin 2) ℝ))]

include hN in

private theorem Lq_slash_smul [Γ.HasDetOne] {k : ℤ} (c : ℂ) (A : ModularForm Γ k) :
    Lq N (⇑(c • A) ∣[k] σ) = HahnSeries.C c * Lq N (⇑A ∣[k] σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [ModularForm.IsGLPos.coe_smul, SL_smul_slash, Lq, Lq, ← coe_translate_SL,
    ModularForm.qExpansion_smul hN0 hN c (ModularForm.translate A (σ : GL (Fin 2) ℝ)),
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

variable (h1 : (1 : ℝ) ∈ Γ.strictPeriods)

include h1 in
private theorem Lq_one_mul [Γ.HasDetOne] {k k' : ℤ} (A : ModularForm Γ k) (B : ModularForm Γ k') :
    Lq 1 ⇑(A.mul B) = Lq 1 ⇑A * Lq 1 ⇑B := by
  rw [Lq, Lq, Lq, ← map_mul, ModularForm.qExpansion_mul one_pos h1]

include h1 in
private theorem Lq_one_add {k : ℤ} (A B : ModularForm Γ k) :
    Lq 1 ⇑(A + B) = Lq 1 ⇑A + Lq 1 ⇑B := by
  rw [Lq, Lq, Lq, ← map_add, ModularForm.coe_add, ← ModularForm.qExpansion_add one_pos h1 A B]

include h1 in
private theorem Lq_one_smul [Γ.HasDetOne] {k : ℤ} (c : ℂ) (A : ModularForm Γ k) :
    Lq 1 ⇑(c • A) = HahnSeries.C c * Lq 1 ⇑A := by
  rw [Lq, Lq, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1 c A,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

private theorem Lq_one_zero {k : ℤ} : Lq 1 ⇑(0 : ModularForm Γ k) = 0 := by
  rw [ModularForm.coe_zero]
  exact Lq_zero_fun 1

include h1 in

private theorem eq_of_Lq_one_eq {k : ℤ} {A B : ModularForm Γ k} (H : Lq 1 ⇑A = Lq 1 ⇑B) : A = B := by
  have hsub : qExpansion 1 ⇑(A - B) = 0 := by
    have := ModularForm.qExpansion_sub one_pos h1 A B
    rw [ModularForm.coe_sub]
    rw [this, sub_eq_zero]
    exact HahnSeries.ofPowerSeries_injective H
  have := (ModularForm.qExpansion_eq_zero_iff one_pos h1 (A - B)).1 hsub
  exact sub_eq_zero.1 this

include h1 in
private theorem Lq_one_ne_zero {k : ℤ} {A : ModularForm Γ k} (hA : A ≠ 0) : Lq 1 ⇑A ≠ 0 := by
  rw [ne_eq, Lq_eq_zero_iff, ModularForm.qExpansion_eq_zero_iff one_pos h1]
  exact hA

include h1 in

private theorem mul_ne_zero_MF [Γ.HasDetOne] {k k' : ℤ} {A : ModularForm Γ k} {B : ModularForm Γ k'}
    (hA : A ≠ 0) (hB : B ≠ 0) : A.mul B ≠ 0 := by
  intro H
  have h := congrArg (fun C : ModularForm Γ (k + k') => Lq 1 ⇑C) H
  rw [Lq_one_mul h1, Lq_one_zero] at h
  exact mul_ne_zero (Lq_one_ne_zero h1 hA) (Lq_one_ne_zero h1 hB) h

include hN h1 in

private theorem cuspRatio_eq_of_cross [Γ.HasDetOne] {k k' : ℤ} {g h : ModularForm Γ k} {g' h' : ModularForm Γ k'}
    (hh : h ≠ 0) (hh' : h' ≠ 0) (H : Lq 1 ⇑g * Lq 1 ⇑h' = Lq 1 ⇑g' * Lq 1 ⇑h) :
    cuspRatio σ N g h = cuspRatio σ N g' h' := by

  have hforms : g.mul h' = h.mul g' := by
    apply eq_of_Lq_one_eq h1
    rw [Lq_one_mul h1, Lq_one_mul h1, H, mul_comm]
  have hL : Lq N (⇑g ∣[k] σ) * Lq N (⇑h' ∣[k'] σ) = Lq N (⇑h ∣[k] σ) * Lq N (⇑g' ∣[k'] σ) := by
    rw [← Lq_slash_mul σ N hN, ← Lq_slash_mul σ N hN, hforms]
  rw [cuspRatio, cuspRatio, div_eq_div_iff (Lq_slash_ne_zero σ N hN hh)
    (Lq_slash_ne_zero σ N hN hh'), hL, mul_comm]

include hN in
private theorem cuspRatio_mul [Γ.HasDetOne] {k k' : ℤ} (g h : ModularForm Γ k) (g' h' : ModularForm Γ k') :
    cuspRatio σ N (g.mul g') (h.mul h') = cuspRatio σ N g h * cuspRatio σ N g' h' := by
  rw [cuspRatio, cuspRatio, cuspRatio, Lq_slash_mul σ N hN, Lq_slash_mul σ N hN,
    mul_div_mul_comm]

include hN in
private theorem cuspRatio_add [Γ.HasDetOne] {k k' : ℤ} {g h : ModularForm Γ k} {g' h' : ModularForm Γ k'}
    (hh : h ≠ 0) (hh' : h' ≠ 0) :
    cuspRatio σ N (g.mul h' + h.mul g') (h.mul h') = cuspRatio σ N g h + cuspRatio σ N g' h' := by
  rw [cuspRatio, cuspRatio, cuspRatio, Lq_slash_add σ N hN, Lq_slash_mul σ N hN,
    Lq_slash_mul σ N hN, Lq_slash_mul σ N hN,
    div_add_div _ _ (Lq_slash_ne_zero σ N hN hh) (Lq_slash_ne_zero σ N hN hh')]

omit [NeZero N] in
private theorem cuspRatio_zero_left {k : ℤ} (h : ModularForm Γ k) :
    cuspRatio σ N (0 : ModularForm Γ k) h = 0 := by
  rw [cuspRatio, ModularForm.coe_zero, SlashAction.zero_slash, Lq_zero_fun, zero_div]

include hN in
private theorem cuspRatio_self {k : ℤ} {h : ModularForm Γ k} (hh : h ≠ 0) : cuspRatio σ N h h = 1 :=
  div_self (Lq_slash_ne_zero σ N hN hh)

include hN in
private theorem cuspRatio_smul [Γ.HasDetOne] {k : ℤ} (c : ℂ) {h : ModularForm Γ k} (hh : h ≠ 0) :
    cuspRatio σ N (c • h) h = HahnSeries.C c := by
  rw [cuspRatio, Lq_slash_smul σ N hN, mul_div_assoc, div_self (Lq_slash_ne_zero σ N hN hh),
    mul_one]

end Generic

section Orders

private theorem order_eq_of_coeff {R : Type*} [CommRing R] {x : LaurentSeries R} {m : ℤ}
    (hm : x.coeff m ≠ 0) (hlt : ∀ k < m, x.coeff k = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => hm (by simp [h])
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hm)
  by_contra hlt'
  exact (fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)) (hlt _ (not_le.mp hlt'))

private theorem order_qExpand (N : ℕ) [NeZero N] {R : Type*} [CommRing R] {y : LaurentSeries R}
    (hy : y ≠ 0) :
    (ModularCurve.qExpand R N y).order = N * y.order := by
  apply order_eq_of_coeff
  · rw [ModularCurve.qExpand_coeff_mul]
    exact fun h => hy (HahnSeries.coeff_order_eq_zero.mp h)
  · intro k hk
    by_cases hdvd : (N : ℤ) ∣ k
    · obtain ⟨k', rfl⟩ := hdvd
      rw [ModularCurve.qExpand_coeff_mul]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    · exact ModularCurve.qExpand_coeff_of_not_dvd N y hdvd

private theorem order_coeffEmb_jq : (ModularCurve.coeffEmb ℂ ModularCurve.jq).order = -1 := by
  apply order_eq_of_coeff
  · rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_jq_neg_one, map_one]
    exact one_ne_zero
  · intro k hk
    rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_jq_of_lt hk, map_zero]

private theorem coeffEmb_jq_ne_zero : ModularCurve.coeffEmb ℂ ModularCurve.jq ≠ 0 := by
  intro h
  have := order_coeffEmb_jq
  rw [h, HahnSeries.order_zero] at this
  omega

private theorem Lq_natCast_eq_qExpand (N : ℕ) [NeZero N] {F : ℍ → ℂ}
    (hcoeff : ∀ n : ℕ, (qExpansion N F).coeff n =
      if N ∣ n then (qExpansion 1 F).coeff (n / N) else 0) :
    Lq N F = ModularCurve.qExpand ℂ N (Lq 1 F) := by
  ext m
  rw [Lq, Lq]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [ModularCurve.qExpand_coeff_mul]
    rcases lt_or_ge k 0 with hk | hk
    · have hNk : (N : ℤ) * k < 0 := by
        have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        nlinarith
      rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hNk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [show ((N : ℤ) * (n : ℤ)) = ((N * n : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, hcoeff,
        if_pos (dvd_mul_right N n), Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero (NeZero.ne N))]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd N _ hdvd]
    rcases lt_or_ge m 0 with hm | hm
    · exact ModularCurve.ofPowerSeries_coeff_of_neg _ hm
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcoeff, if_neg]
      exact fun h => hdvd (by exact_mod_cast h)

private theorem order_ofPowerSeries {R : Type*} [CommRing R] {p : PowerSeries R} (hp : p ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ R p).order = p.order.toNat := by
  apply order_eq_of_coeff
  · rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact PowerSeries.coeff_order hp
  · intro k hk
    rcases lt_or_ge k 0 with hk0 | hk0
    · exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk0
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact PowerSeries.coeff_of_lt_order_toNat n (by exact_mod_cast hk)

private theorem order_inv_lq {R : Type*} [Field R] {x : LaurentSeries R} (hx : x ≠ 0) :
    (x⁻¹).order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

private theorem PowerSeries_order_eq_of_div_order_eq_zero {R : Type*} [Field R] {p q : PowerSeries R}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h0 : (HahnSeries.ofPowerSeries ℤ R p / HahnSeries.ofPowerSeries ℤ R q).order = 0) :
    p.order = q.order := by
  have hpL : HahnSeries.ofPowerSeries ℤ R p ≠ 0 := fun h =>
    hp (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  have hqL : HahnSeries.ofPowerSeries ℤ R q ≠ 0 := fun h =>
    hq (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  rw [div_eq_mul_inv, HahnSeries.order_mul hpL (inv_ne_zero hqL), order_inv_lq hqL,
    order_ofPowerSeries hp, order_ofPowerSeries hq] at h0
  rw [← PowerSeries.coe_toNat_order hp, ← PowerSeries.coe_toNat_order hq]
  norm_cast
  omega

end Orders

section Concrete

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

private abbrev _root_.S3c.Γ0 : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ))

p2m_export "S3c" "Γ0"

private abbrev CF : IntermediateField ℂ (LaurentSeries ℂ) :=
  ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)

omit [NeZero N] in
private theorem one_mem_strictPeriods_Gamma0 : (1 : ℝ) ∈ (Γ0 N).strictPeriods := by
  show (1 : ℝ) ∈ Subgroup.strictPeriods
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

private def Pres : Prop :=
  ∀ x : LaurentSeries ℂ,
    x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) →
      ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
        x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

variable (pres : Pres N)
variable (hN : (N : ℝ) ∈ (ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹ • Γ0 N).strictPeriods)

private def presWt (x : CF N) : ℤ := (pres x x.2).choose

private def presNum (x : CF N) : ModularForm (Γ0 N) (presWt N pres x) := (pres x x.2).choose_spec.choose

private def presDen (x : CF N) : ModularForm (Γ0 N) (presWt N pres x) :=
  (pres x x.2).choose_spec.choose_spec.choose

omit [NeZero N] in
private theorem presDen_ne_zero (x : CF N) : presDen N pres x ≠ 0 :=
  (pres x x.2).choose_spec.choose_spec.choose_spec.1

omit [NeZero N] in
private theorem pres_eq (x : CF N) :
    (x : LaurentSeries ℂ) * Lq 1 ⇑(presDen N pres x) = Lq 1 ⇑(presNum N pres x) :=
  (pres x x.2).choose_spec.choose_spec.choose_spec.2

private def Φσfun (x : CF N) : LaurentSeries ℂ :=
  cuspRatio σ N (presNum N pres x) (presDen N pres x)

include hN in

private theorem Φσfun_eq {x : CF N} {k : ℤ} {g h : ModularForm (Γ0 N) k} (hh : h ≠ 0)
    (hx : (x : LaurentSeries ℂ) * Lq 1 ⇑h = Lq 1 ⇑g) :
    Φσfun N σ pres x = cuspRatio σ N g h := by
  apply cuspRatio_eq_of_cross σ N hN (one_mem_strictPeriods_Gamma0 N) (presDen_ne_zero N pres x) hh
  rw [← pres_eq N pres x, ← hx]
  ring

include hN in

private def Φσ : CF N →+* LaurentSeries ℂ where
  toFun := Φσfun N σ pres
  map_one' := by
    have h := Φσfun_eq N σ pres hN (x := 1) (presDen_ne_zero N pres 1)
      (g := presDen N pres 1) (by simp)
    rw [h, cuspRatio_self σ N hN (presDen_ne_zero N pres 1)]
  map_mul' x y := by
    have hx := pres_eq N pres x
    have hy := pres_eq N pres y
    have h := Φσfun_eq N σ pres hN (x := x * y)
      (g := (presNum N pres x).mul (presNum N pres y))
      (h := (presDen N pres x).mul (presDen N pres y))
      (mul_ne_zero_MF (one_mem_strictPeriods_Gamma0 N) (presDen_ne_zero N pres x)
        (presDen_ne_zero N pres y)) (by
        rw [Lq_one_mul (one_mem_strictPeriods_Gamma0 N), Lq_one_mul (one_mem_strictPeriods_Gamma0 N),
          ← hx, ← hy]
        push_cast
        ring)
    rw [h, cuspRatio_mul σ N hN, Φσfun, Φσfun]
  map_zero' := by
    have h := Φσfun_eq N σ pres hN (x := 0) (presDen_ne_zero N pres 1)
      (g := (0 : ModularForm (Γ0 N) (presWt N pres 1))) (by
        rw [Lq_one_zero]; simp)
    rw [h, cuspRatio_zero_left]
  map_add' x y := by
    have hx := pres_eq N pres x
    have hy := pres_eq N pres y
    have h := Φσfun_eq N σ pres hN (x := x + y)
      (g := (presNum N pres x).mul (presDen N pres y) + (presDen N pres x).mul (presNum N pres y))
      (h := (presDen N pres x).mul (presDen N pres y))
      (mul_ne_zero_MF (one_mem_strictPeriods_Gamma0 N) (presDen_ne_zero N pres x)
        (presDen_ne_zero N pres y)) (by
        rw [Lq_one_add (one_mem_strictPeriods_Gamma0 N),
          Lq_one_mul (one_mem_strictPeriods_Gamma0 N), Lq_one_mul (one_mem_strictPeriods_Gamma0 N),
          Lq_one_mul (one_mem_strictPeriods_Gamma0 N), ← hx, ← hy]
        push_cast
        ring)
    rw [h, cuspRatio_add σ N hN (presDen_ne_zero N pres x) (presDen_ne_zero N pres y), Φσfun,
      Φσfun]

include hN in
private theorem Φσ_apply (x : CF N) : Φσ N σ pres hN x = Φσfun N σ pres x := rfl

include hN in

private theorem Φσ_eq {x : CF N} {k : ℤ} {g h : ModularForm (Γ0 N) k} (hh : h ≠ 0)
    (hx : (x : LaurentSeries ℂ) * Lq 1 ⇑h = Lq 1 ⇑g) :
    Φσ N σ pres hN x = Lq N (⇑g ∣[k] σ) / Lq N (⇑h ∣[k] σ) :=
  Φσfun_eq N σ pres hN hh hx

include hN in

private theorem Φσ_algebraMap (c : ℂ) : Φσ N σ pres hN (algebraMap ℂ (CF N) c) = HahnSeries.C c := by
  have h := Φσfun_eq N σ pres hN (x := algebraMap ℂ (CF N) c) (presDen_ne_zero N pres 1)
    (g := c • presDen N pres 1) (by
      rw [Lq_one_smul (one_mem_strictPeriods_Gamma0 N)]
      simp [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply])
  rw [Φσ_apply, h, cuspRatio_smul σ N hN c (presDen_ne_zero N pres 1)]

omit [NeZero N] in
private theorem Gamma0_le_Gamma0_one : Γ0 N ≤ Γ0 1 :=
  Subgroup.map_mono fun _ _ => CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _)

private def restrictOne {k : ℤ} (f : ModularForm (Γ0 1) k) : ModularForm (Γ0 N) k where
  toSlashInvariantForm :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ =>
        SlashInvariantForm.slash_action_eqn f γ (Gamma0_le_Gamma0_one N hγ) }
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono (Gamma0_le_Gamma0_one N))

omit [NeZero N] in
@[scoped simp]
private theorem coe_restrictOne {k : ℤ} (f : ModularForm (Γ0 1) k) : ⇑(restrictOne N f) = ⇑f := rfl

omit [NeZero N] in

private theorem slash_eq_self_of_level_one {k : ℤ} (f : ModularForm (Γ0 1) k) : ⇑f ∣[k] σ = ⇑f := by
  have hσ : (σ : GL (Fin 2) ℝ) ∈ Γ0 1 :=
    Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _))
  rw [SL_slash]
  exact SlashInvariantForm.slash_action_eqn f _ hσ

private def PresJ : Prop :=
  ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 1) k), h ≠ 0 ∧
    ModularCurve.coeffEmb ℂ (ModularCurve.qExpand ℚ 1 ModularCurve.jq) *
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

private def Reindex : Prop :=
  ∀ (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 1) k) (n : ℕ),
    (qExpansion N ⇑f).coeff n = if N ∣ n then (qExpansion 1 ⇑f).coeff (n / N) else 0

include hN in

private theorem Φσ_jq (presJ : PresJ) (reindex : Reindex N)
    (hj : ModularCurve.coeffEmb ℂ ModularCurve.jq ∈ CF N) :
    Φσ N σ pres hN ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, hj⟩ =
      ModularCurve.qExpand ℂ N (ModularCurve.coeffEmb ℂ ModularCurve.jq) := by
  obtain ⟨k, g₁, h₁, hh₁, HJ⟩ := presJ
  rw [ModularCurve.qExpand_one_apply] at HJ
  have hh : restrictOne N h₁ ≠ 0 := fun H =>
    hh₁ (DFunLike.coe_injective (by simpa using congrArg DFunLike.coe H))
  have hpres : ((⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, hj⟩ : CF N) : LaurentSeries ℂ) *
      Lq 1 ⇑(restrictOne N h₁) = Lq 1 ⇑(restrictOne N g₁) := HJ
  rw [Φσ_eq N σ pres hN hh hpres, coe_restrictOne, coe_restrictOne,
    slash_eq_self_of_level_one σ g₁, slash_eq_self_of_level_one σ h₁,
    Lq_natCast_eq_qExpand N (reindex k g₁), Lq_natCast_eq_qExpand N (reindex k h₁), ← map_div₀]
  congr 1
  have hh₁L : Lq 1 ⇑h₁ ≠ 0 := Lq_one_ne_zero (one_mem_strictPeriods_Gamma0 1) hh₁
  exact (eq_div_of_mul_eq hh₁L HJ).symm

include hN in

private theorem order_Φσ_jq (presJ : PresJ) (reindex : Reindex N)
    (hj : ModularCurve.coeffEmb ℂ ModularCurve.jq ∈ CF N) :
    (Φσ N σ pres hN ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, hj⟩).order = -N := by
  rw [Φσ_jq N σ pres hN presJ reindex hj, order_qExpand N coeffEmb_jq_ne_zero, order_coeffEmb_jq,
    mul_neg_one]

end Concrete

end S3c
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

namespace S3bR2

private theorem exists_chart {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (pF : Periodic (F ∘ ofComplex) N) (dF : MDiff F) (bF : IsBoundedAtImInfty F)
    (hF0 : qExpansion N F ≠ 0) :
    ∃ u : ℂ → ℂ, ContinuousAt u 0 ∧
      u 0 = (qExpansion N F).coeff ((qExpansion N F).order.toNat) ∧ u 0 ≠ 0 ∧
      ∀ τ : ℍ, F τ = Periodic.qParam N τ ^ ((qExpansion N F).order.toNat) *
        u (Periodic.qParam N τ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set P := qExpansion N F with hP

  have hsummN : Summable fun n : ℕ => ‖P.coeff n‖ * (1 / 2 : ℝ) ^ n := by
    letI : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
    have h1 : HasSum (fun n : ℕ => P.coeff n • ((1 / 2 : ℝ) : ℂ) ^ n)
        (cuspFunction N F ((1 / 2 : ℝ) : ℂ)) :=
      hasSum_qExpansion_of_norm_lt hN pF dF bF (by
        rw [Complex.norm_real]
        norm_num)
    refine (summable_norm_iff.mpr h1.summable).congr fun n => ?_
    rw [norm_smul, norm_pow, Complex.norm_real]
    norm_num
  have hsummShift : Summable fun j : ℕ => ‖P.coeff ((P.order.toNat) + j)‖ * (1 / 2 : ℝ) ^ j := by
    have h1 : Summable fun j : ℕ =>
        ‖P.coeff (j + P.order.toNat)‖ * (1 / 2 : ℝ) ^ (j + P.order.toNat) :=
      (summable_nat_add_iff (f := fun n : ℕ => ‖P.coeff n‖ * (1 / 2 : ℝ) ^ n)
        (P.order.toNat)).mpr hsummN
    have h2 := h1.mul_right ((2 : ℝ) ^ P.order.toNat)
    refine h2.congr fun j => ?_
    have hpow : ((1 : ℝ) / 2) ^ P.order.toNat * (2 : ℝ) ^ P.order.toNat = 1 := by
      rw [← mul_pow]
      norm_num
    rw [pow_add, add_comm j P.order.toNat]
    linear_combination ‖P.coeff (P.order.toNat + j)‖ * ((1 : ℝ) / 2) ^ j * hpow

  set u : ℂ → ℂ := fun z => ∑' j : ℕ, P.coeff (P.order.toNat + j) * z ^ j with hu
  have hucont : ContinuousOn u (Metric.ball (0 : ℂ) (1 / 2)) := by
    refine continuousOn_tsum (fun j => ?_) hsummShift fun j z hz => ?_
    · exact (continuous_const.mul (continuous_pow j)).continuousOn
    · rw [norm_mul, norm_pow]
      gcongr
      exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  have huCA : ContinuousAt u 0 :=
    hucont.continuousAt (Metric.ball_mem_nhds _ (by norm_num))
  have hu0 : u 0 = P.coeff (P.order.toNat) := by
    have hval : u 0 = ∑' j : ℕ, P.coeff (P.order.toNat + j) * (0 : ℂ) ^ j := rfl
    rw [hval, tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
    simp
  have hum : P.coeff (P.order.toNat) ≠ 0 := PowerSeries.coeff_order hF0
  refine ⟨u, huCA, hu0, by rw [hu0]; exact hum, fun τ => ?_⟩
  set z := Periodic.qParam (N : ℝ) (τ : ℂ) with hz
  have hz1 : ‖z‖ < 1 := UpperHalfPlane.norm_qParam_lt_one N τ
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hsum : HasSum (fun n : ℕ => P.coeff n • z ^ n) (F τ) :=
    hasSum_qExpansion hN pF dF bF τ
  have hshift : HasSum (fun j : ℕ => P.coeff (j + P.order.toNat) • z ^ (j + P.order.toNat))
      (F τ) := by
    have hvan : ∑ i ∈ Finset.range (P.order.toNat), P.coeff i • z ^ i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [PowerSeries.coeff_of_lt_order_toNat i (Finset.mem_range.mp hi), zero_smul]
    have h4 := (hasSum_nat_add_iff' (P.order.toNat)).mpr hsum
    rwa [hvan, sub_zero] at h4
  have husum : HasSum (fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j)
      (F τ / z ^ P.order.toNat) := by
    have h2 : HasSum (fun j : ℕ => (P.coeff (P.order.toNat + j) * z ^ j) * z ^ P.order.toNat)
        (F τ) := by
      have heq : (fun j : ℕ => (P.coeff (P.order.toNat + j) * z ^ j) * z ^ P.order.toNat) =
          fun j : ℕ => P.coeff (j + P.order.toNat) • z ^ (j + P.order.toNat) := by
        funext j
        rw [smul_eq_mul, pow_add, add_comm j (P.order.toNat)]
        ring
      rw [heq]
      exact hshift
    have h3 := h2.div_const (z ^ P.order.toNat)
    have heq2 : (fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j * z ^ P.order.toNat /
        z ^ P.order.toNat) = fun j : ℕ => P.coeff (P.order.toNat + j) * z ^ j := by
      funext j
      rw [mul_div_assoc, div_self (pow_ne_zero _ hz0), mul_one]
    rwa [heq2] at h3
  have huz : u z = F τ / z ^ P.order.toNat := husum.tsum_eq
  rw [huz, mul_div_cancel₀ _ (pow_ne_zero _ hz0)]

private theorem eventually_ne_zero_atImInfty {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (pF : Periodic (F ∘ ofComplex) N) (dF : MDiff F) (bF : IsBoundedAtImInfty F)
    (hF0 : qExpansion N F ≠ 0) : ∀ᶠ τ : ℍ in atImInfty, F τ ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨u, hu, -, hu0, hid⟩ := exists_chart pF dF bF hF0
  have h1 : Tendsto (fun τ : ℍ => u (Periodic.qParam N τ)) atImInfty (𝓝 (u 0)) :=
    hu.tendsto.comp (qParam_tendsto_atImInfty hN)
  filter_upwards [h1.eventually_ne hu0] with τ hτ
  rw [hid τ]
  exact mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) hτ

private theorem tendsto_div_atImInfty_zero_of_order_lt {N : ℕ} [NeZero N] {G H : ℍ → ℂ}
    (pG : Periodic (G ∘ ofComplex) N) (dG : MDiff G) (bG : IsBoundedAtImInfty G)
    (pH : Periodic (H ∘ ofComplex) N) (dH : MDiff H) (bH : IsBoundedAtImInfty H)
    (hG0 : qExpansion N G ≠ 0) (hH0 : qExpansion N H ≠ 0)
    (hlt : (qExpansion N H).order.toNat < (qExpansion N G).order.toNat) :
    Tendsto (fun τ : ℍ => G τ / H τ) atImInfty (𝓝 0) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨uG, cG, -, nG, idG⟩ := exists_chart pG dG bG hG0
  obtain ⟨uH, cH, -, nH, idH⟩ := exists_chart pH dH bH hH0
  set mG := (qExpansion (N : ℝ) G).order.toNat with hmG
  set mH := (qExpansion (N : ℝ) H).order.toNat with hmH
  set d := mG - mH with hd
  have hd0 : d ≠ 0 := Nat.sub_ne_zero_of_lt hlt
  have hmGd : mG = mH + d := (Nat.add_sub_cancel' hlt.le).symm
  have hq : Tendsto (fun τ : ℍ => Periodic.qParam (N : ℝ) (τ : ℂ) ^ d) atImInfty (𝓝 0) := by
    have h1 := (qParam_tendsto_atImInfty hN).pow d
    rwa [zero_pow hd0] at h1
  have hu : Tendsto (fun τ : ℍ => uG (Periodic.qParam N τ) / uH (Periodic.qParam N τ))
      atImInfty (𝓝 (uG 0 / uH 0)) :=
    (cG.tendsto.comp (qParam_tendsto_atImInfty hN)).div
      (cH.tendsto.comp (qParam_tendsto_atImInfty hN)) nH
  have hmain := hq.mul hu
  rw [zero_mul] at hmain
  refine hmain.congr fun τ => ?_
  have hqne : Periodic.qParam (N : ℝ) (τ : ℂ) ^ mH ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  rw [idG τ, idH τ, hmGd, pow_add, mul_assoc,
    mul_div_mul_left _ _ hqne, mul_div_assoc]

private theorem tendsto_norm_div_atTop_of_order_gt {N : ℕ} [NeZero N] {G H : ℍ → ℂ}
    (pG : Periodic (G ∘ ofComplex) N) (dG : MDiff G) (bG : IsBoundedAtImInfty G)
    (pH : Periodic (H ∘ ofComplex) N) (dH : MDiff H) (bH : IsBoundedAtImInfty H)
    (hG0 : qExpansion N G ≠ 0) (hH0 : qExpansion N H ≠ 0)
    (hlt : (qExpansion N G).order.toNat < (qExpansion N H).order.toNat) :
    Tendsto (fun τ : ℍ => ‖G τ / H τ‖) atImInfty atTop := by
  have h0 : Tendsto (fun τ : ℍ => H τ / G τ) atImInfty (𝓝 0) :=
    tendsto_div_atImInfty_zero_of_order_lt pH dH bH pG dG bG hH0 hG0 hlt
  have hGne := eventually_ne_zero_atImInfty pG dG bG hG0
  have hHne := eventually_ne_zero_atImInfty pH dH bH hH0
  have hpos : ∀ᶠ τ : ℍ in atImInfty, ‖H τ / G τ‖ ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [hGne, hHne] with τ hG hH
    exact norm_pos_iff.mpr (div_ne_zero hH hG)
  have h1 : Tendsto (fun τ : ℍ => ‖H τ / G τ‖) atImInfty (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hpos
    simpa using h0.norm
  have h2 : Tendsto (fun τ : ℍ => ‖H τ / G τ‖⁻¹) atImInfty atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  refine h2.congr fun τ => ?_
  rw [← norm_inv, inv_div]

private theorem neBot_inf_principal_of_frequently {E : Set ℍ}
    (h : ∀ A : ℝ, ∃ τ : ℍ, A < UpperHalfPlane.im τ ∧ τ ∈ E) :
    (atImInfty ⊓ 𝓟 E).NeBot := by
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  rw [UpperHalfPlane.atImInfty_mem] at hU
  obtain ⟨A, hA⟩ := hU
  obtain ⟨τ, hτA, hτE⟩ := h A
  exact ⟨τ, hA τ hτA.le, hτE⟩

private theorem order_eq_of_tendsto_div_ne_zero {N : ℕ} [NeZero N] {G H Φ : ℍ → ℂ} {L : ℂ}
    (pG : Periodic (G ∘ ofComplex) N) (dG : MDiff G) (bG : IsBoundedAtImInfty G)
    (pH : Periodic (H ∘ ofComplex) N) (dH : MDiff H) (bH : IsBoundedAtImInfty H)
    (hG0 : qExpansion N G ≠ 0) (hH0 : qExpansion N H ≠ 0)
    {E : Set ℍ} (hE : (atImInfty ⊓ 𝓟 E).NeBot)
    (hagree : ∀ τ ∈ E, Φ τ = G τ / H τ)
    (hlim : Tendsto Φ atImInfty (𝓝 L)) (hL : L ≠ 0) :
    (qExpansion N G).order = (qExpansion N H).order := by
  haveI := hE
  have hΦF : Tendsto Φ (atImInfty ⊓ 𝓟 E) (𝓝 L) := hlim.mono_left inf_le_left
  have hagreeF : ∀ᶠ τ : ℍ in atImInfty ⊓ 𝓟 E, Φ τ = G τ / H τ :=
    eventually_inf_principal.mpr (Eventually.of_forall hagree)
  have hdiv : Tendsto (fun τ : ℍ => G τ / H τ) (atImInfty ⊓ 𝓟 E) (𝓝 L) :=
    hΦF.congr' (by filter_upwards [hagreeF] with τ hτ using hτ)
  rcases lt_trichotomy ((qExpansion (N : ℝ) G).order.toNat)
      ((qExpansion (N : ℝ) H).order.toNat) with hlt | heq | hgt
  ·
    have h1 : Tendsto (fun τ : ℍ => ‖G τ / H τ‖) (atImInfty ⊓ 𝓟 E) atTop :=
      (tendsto_norm_div_atTop_of_order_gt pG dG bG pH dH bH hG0 hH0 hlt).mono_left
        inf_le_left
    exact absurd h1 (not_tendsto_atTop_of_tendsto_nhds hdiv.norm)
  ·
    have hGfin : (qExpansion (N : ℝ) G).order ≠ ⊤ :=
      (PowerSeries.order_finite_iff_ne_zero.mpr hG0).ne
    have hHfin : (qExpansion (N : ℝ) H).order ≠ ⊤ :=
      (PowerSeries.order_finite_iff_ne_zero.mpr hH0).ne
    rw [← ENat.coe_toNat hGfin, ← ENat.coe_toNat hHfin, heq]
  ·
    have h1 : Tendsto (fun τ : ℍ => G τ / H τ) (atImInfty ⊓ 𝓟 E) (𝓝 0) :=
      (tendsto_div_atImInfty_zero_of_order_lt pG dG bG pH dH bH hG0 hH0 hgt).mono_left
        inf_le_left
    exact absurd (tendsto_nhds_unique hdiv h1) hL

end S3bR2
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

namespace S3bR2T

private theorem order_eq_of_coeff {R : Type*} [CommRing R] {x : LaurentSeries R} {m : ℤ}
    (hm : x.coeff m ≠ 0) (hlt : ∀ k < m, x.coeff k = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => hm (by simp [h])
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hm)
  by_contra hlt'
  exact (fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)) (hlt _ (not_le.mp hlt'))

private theorem order_ofPowerSeries {R : Type*} [CommRing R] {p : PowerSeries R} (hp : p ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ R p).order = p.order.toNat := by
  apply order_eq_of_coeff
  · rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact PowerSeries.coeff_order hp
  · intro k hk
    rcases lt_or_ge k 0 with hk0 | hk0
    · exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk0
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact PowerSeries.coeff_of_lt_order_toNat n (by exact_mod_cast hk)

private theorem order_inv_lq {R : Type*} [Field R] {x : LaurentSeries R} (hx : x ≠ 0) :
    (x⁻¹).order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

private theorem order_div_eq_zero_of_order_eq {R : Type*} [Field R] {p q : PowerSeries R}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : p.order = q.order) :
    (HahnSeries.ofPowerSeries ℤ R p / HahnSeries.ofPowerSeries ℤ R q).order = 0 := by
  have hpL : HahnSeries.ofPowerSeries ℤ R p ≠ 0 := fun h' =>
    hp (HahnSeries.ofPowerSeries_injective (by rw [h', map_zero]))
  have hqL : HahnSeries.ofPowerSeries ℤ R q ≠ 0 := fun h' =>
    hq (HahnSeries.ofPowerSeries_injective (by rw [h', map_zero]))
  rw [div_eq_mul_inv, HahnSeries.order_mul hpL (inv_ne_zero hqL), order_inv_lq hqL,
    order_ofPowerSeries hp, order_ofPowerSeries hq, h]
  omega

private theorem qParam_one_upperTriangular {T : GL (Fin 2) ℝ} {a b D' : ℕ}
    [NeZero a] [NeZero D']
    (hTa : (T : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = a)
    (hTb : (T : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b)
    (hTc : (T : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0)
    (hTd : (T : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = D')
    (hdet : 0 < T.det.val) (τ : ℍ) :
    Periodic.qParam 1 ((T • τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * b / D') *
        Periodic.qParam ((a : ℝ) * D') (τ : ℂ) ^ (a ^ 2 : ℕ) := by
  have ha : ((a : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hD : ((D' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D')
  have hcoe : ((T • τ : ℍ) : ℂ) = ((a : ℂ) * (τ : ℂ) + b) / D' := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hTa, hTb, hTc, hTd]
    push_cast
    rw [zero_mul, zero_add]
  rw [hcoe]
  unfold Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem qExpansion_comp_coeff {f : ℍ → ℂ}
    (p1 : Periodic (f ∘ ofComplex) 1) (df : MDiff f) (bf : IsBoundedAtImInfty f)
    {φ : ℍ → ℍ} {h : ℝ} (hh : 0 < h) {α : ℕ} (hα : α ≠ 0) {ζ : ℂ}
    (hq : ∀ τ : ℍ, Periodic.qParam 1 ((φ τ : ℍ) : ℂ) = ζ * Periodic.qParam h (τ : ℂ) ^ α)
    (pφ : Periodic ((f ∘ φ) ∘ ofComplex) h) (dφ : MDiff (f ∘ φ))
    (bφ : IsBoundedAtImInfty (f ∘ φ)) (m : ℕ) :
    (qExpansion h (f ∘ φ)).coeff m =
      if α ∣ m then ζ ^ (m / α) * (qExpansion 1 f).coeff (m / α) else 0 := by
  classical
  set c : ℕ → ℂ := fun n =>
    if α ∣ n then ζ ^ (n / α) * (qExpansion 1 f).coeff (n / α) else 0 with hc
  have key : ∀ τ : ℍ, HasSum (fun n : ℕ => c n • Periodic.qParam h τ ^ n) ((f ∘ φ) τ) := by
    intro τ
    have h1 : HasSum
        (fun j : ℕ => (qExpansion 1 f).coeff j • Periodic.qParam 1 ((φ τ : ℍ) : ℂ) ^ j)
        (f (φ τ)) := hasSum_qExpansion one_pos p1 df bf (φ τ)
    have h2 : ∀ j : ℕ,
        (qExpansion 1 f).coeff j • Periodic.qParam 1 ((φ τ : ℍ) : ℂ) ^ j =
          c (α * j) • Periodic.qParam h (τ : ℂ) ^ (α * j) := by
      intro j
      rw [hq τ, mul_pow, ← pow_mul, hc]
      simp only [dvd_mul_right, if_pos,
        Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero hα)]
      rw [smul_eq_mul, smul_eq_mul]
      ring
    have hinj : Function.Injective (fun j : ℕ => α * j) := fun x y hxy =>
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hα) hxy
    have hoff : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ => α * j) →
        c n • Periodic.qParam h (τ : ℂ) ^ n = 0 := by
      intro n hn
      have hdvd : ¬ α ∣ n := by
        rintro ⟨j, rfl⟩
        exact hn ⟨j, rfl⟩
      rw [hc]
      simp [hdvd]
    simp only [h2] at h1
    exact (hinj.hasSum_iff hoff).mp h1
  have hA : AnalyticAt ℂ (cuspFunction h (f ∘ φ)) 0 :=
    analyticAt_cuspFunction_zero hh pφ dφ bφ
  letI : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, fun _ _ hfg => hfg⟩
  exact (qExpansion_coeff_unique (f ∘ φ) hh hA key m).symm

end S3bR2T
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

namespace S3bR2D

variable {k : ℤ}

private def _root_.S3bR2D.Dm (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(N : ℝ), 0; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    first | exact Nat.cast_ne_zero.mpr (NeZero.ne N) | simpa using (Nat.cast_ne_zero (R := ℝ)).mpr (NeZero.ne N) | simp [NeZero.ne N])

p2m_export "S3bR2D" "Dm"
private theorem Dm_val (N : ℕ) [NeZero N] :
    ((Dm N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(N : ℝ), 0; 0, 1] := rfl

private theorem int_dvd_of_mem_Gamma0 {N : ℕ} {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    (N : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem] at hA
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by exact_mod_cast hA)

private def conjWitness {N : ℕ} (A : SL(2, ℤ))
    (hdvd : (N : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0) : SL(2, ℤ) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, N * (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    have hdet : ((A : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of]
    have hc : (N : ℤ) * ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N) =
        (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := Int.mul_ediv_cancel' hdvd
    linear_combination hdet - (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc⟩

private theorem Dm_mul_mapGL {N : ℕ} [NeZero N] (A : SL(2, ℤ))
    (hdvd : (N : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    Dm N * mapGL ℝ A = mapGL ℝ (conjWitness A hdvd) * Dm N := by
  have hc : (N : ℤ) * ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N) =
      (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := Int.mul_ediv_cancel' hdvd
  have hcR : (N : ℝ) * (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N : ℤ) : ℝ) =
      (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hc
  rw [Units.ext_iff]
  have hL : (↑(Dm N * mapGL ℝ A) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(N : ℝ), 0; 0, 1] * ((A : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) := rfl
  have hR : (↑(mapGL ℝ (conjWitness A hdvd) * Dm N) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((conjWitness A hdvd : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) *
        !![(N : ℝ), 0; 0, 1] := rfl
  rw [hL, hR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjWitness, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, mul_comm, hcR]

private theorem Gamma0_le_conj_Dm (N : ℕ) [NeZero N] :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (Dm N)⁻¹ •
        ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  intro A hA
  obtain ⟨A₀, hA₀, rfl⟩ := Subgroup.mem_map.mp hA
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hdvd := int_dvd_of_mem_Gamma0 hA₀
  have hconj : Dm N * mapGL ℝ A₀ * (Dm N)⁻¹ = mapGL ℝ (conjWitness A₀ hdvd) := by
    rw [Dm_mul_mapGL A₀ hdvd, mul_inv_cancel_right]
  rw [hconj]
  exact Subgroup.mem_map_of_mem _
    (CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _))

private def restrictLE {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ModularForm Γ' k where
  toSlashInvariantForm :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ => SlashInvariantForm.slash_action_eqn f γ (hle hγ) }
  holo' := ModularFormClass.holo f
  bdd_at_cusps' {_c} hc := ModularFormClass.bdd_at_cusps (f := f) (hc.mono hle)

private theorem coe_restrictLE {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ⇑(restrictLE hle f) = ⇑f := rfl

private def translateD (N : ℕ) [NeZero N]
    (f : ModularForm (CongruenceSubgroup.Gamma0 1) k) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k :=
  restrictLE (Gamma0_le_conj_Dm N) (ModularForm.translate f (Dm N))

private theorem coe_translateD (N : ℕ) [NeZero N]
    (f : ModularForm (CongruenceSubgroup.Gamma0 1) k) :
    ⇑(translateD N f) = ⇑f ∣[k] Dm N := by
  show ⇑(ModularForm.translate f (Dm N)) = ⇑f ∣[k] Dm N
  exact ModularForm.coe_translate f (Dm N)

end S3bR2D
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

section BridgeSplice

open Topology

namespace S3bBridge

private def hShift (τ : ℍ) (t : ℝ) : ℍ :=
  ⟨(τ : ℂ) + (t : ℂ), by
    have : ((τ : ℂ) + (t : ℂ)).im = (τ : ℂ).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
    rw [this]; exact τ.im_pos⟩

private theorem coe_hShift (τ : ℍ) (t : ℝ) : ((hShift τ t : ℍ) : ℂ) = (τ : ℂ) + t := rfl

private theorem im_hShift (τ : ℍ) (t : ℝ) : UpperHalfPlane.im (hShift τ t) = UpperHalfPlane.im τ := by
  have : ((hShift τ t : ℍ) : ℂ).im = ((τ : ℍ) : ℂ).im := by
    rw [coe_hShift, Complex.add_im, Complex.ofReal_im, add_zero]
  exact this

private theorem hShift_zero (τ : ℍ) : hShift τ 0 = τ :=
  UpperHalfPlane.ext (show ((hShift τ 0 : ℍ) : ℂ) = (τ : ℂ) by
    rw [coe_hShift, Complex.ofReal_zero, add_zero])

private theorem hShift_ne_of_ne_zero (τ : ℍ) {t : ℝ} (ht : t ≠ 0) : hShift τ t ≠ τ := by
  intro h
  have : ((hShift τ t : ℍ) : ℂ) = (τ : ℂ) := congrArg _ h
  rw [coe_hShift, add_eq_left] at this
  exact ht (Complex.ofReal_eq_zero.mp this)

private theorem continuous_coe_comp_hShift (τ : ℍ) :
    Continuous fun t : ℝ => ((hShift τ t : ℍ) : ℂ) := by
  simp only [coe_hShift]
  exact continuous_const.add Complex.continuous_ofReal

private theorem continuous_slSmul_coe (σ : SL(2, ℤ)) :
    Continuous fun w : ℍ => ((σ • w : ℍ) : ℂ) := by
  have h1 : Continuous fun w : ℍ => (((σ : GL (Fin 2) ℝ) • w : ℍ) : ℂ) :=
    UpperHalfPlane.continuous_coe.comp (continuous_const_smul _)
  convert h1 using 2 <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _

private theorem exists_im_lt_and_agree {F G : ℍ → ℂ}
    (hF : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => G (ofComplex z))
    (σ : SL(2, ℤ)) (A : ℝ) :
    ∃ τ : ℍ, A < UpperHalfPlane.im τ ∧ F (σ • τ) = G (σ • τ) := by

  set y : ℝ := max A 0 + 1 with hy_def
  have hy_pos : 0 < y := by positivity
  set τ₀ : ℍ := ⟨((y : ℂ) * Complex.I), by
    rw [Complex.mul_I_im, Complex.ofReal_re]; exact hy_pos⟩
  have hτ₀_im : UpperHalfPlane.im τ₀ = y := by
    show (((y : ℝ) : ℂ) * Complex.I).im = y
    rw [Complex.mul_I_im, Complex.ofReal_re]
  have hAτ₀ : A < UpperHalfPlane.im τ₀ := by
    rw [hτ₀_im, hy_def]; exact lt_of_le_of_lt (le_max_left A 0) (lt_add_one _)
  set w₀ : ℍ := σ • τ₀
  have hagree := hF w₀

  have hpath_cont : Continuous fun t : ℝ => ((σ • hShift τ₀ t : ℍ) : ℂ) := by
    have h1 : Continuous fun t : ℝ => (hShift τ₀ t : ℍ) :=
      UpperHalfPlane.isOpenEmbedding_coe.continuous_iff.mpr (continuous_coe_comp_hShift τ₀)
    exact (continuous_slSmul_coe σ).comp h1
  have hpath_zero : ((σ • hShift τ₀ 0 : ℍ) : ℂ) = (w₀ : ℂ) := by rw [hShift_zero]
  have hpath_tendsto :
      Tendsto (fun t : ℝ => ((σ • hShift τ₀ t : ℍ) : ℂ)) (𝓝[≠] 0) (𝓝[≠] (w₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h2 : Tendsto (fun t : ℝ => ((σ • hShift τ₀ t : ℍ) : ℂ)) (𝓝 0) (𝓝 (w₀ : ℂ)) := by
        have := hpath_cont.tendsto 0
        rwa [show ((σ • hShift τ₀ 0 : ℍ) : ℂ) = (w₀ : ℂ) from hpath_zero] at this
      exact h2.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun t ht => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      have hw_eq : σ • hShift τ₀ t = w₀ :=
        UpperHalfPlane.ext heq
      have hτ_eq : hShift τ₀ t = τ₀ := by
        have h3 : σ • hShift τ₀ t = σ • τ₀ := hw_eq
        exact smul_left_cancel (α := SL(2, ℤ)) σ h3
      exact (hShift_ne_of_ne_zero τ₀ ht) hτ_eq

  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      F (ofComplex ((σ • hShift τ₀ t : ℍ) : ℂ)) =
        G (ofComplex ((σ • hShift τ₀ t : ℍ) : ℂ)) :=
    hpath_tendsto.eventually hagree
  obtain ⟨t, ht_agree⟩ := hev.exists
  refine ⟨hShift τ₀ t, ?_, ?_⟩
  · rw [im_hShift]; exact hAτ₀
  · rwa [ofComplex_apply] at ht_agree

private theorem frequently_agree_atImInfty {F G : ℍ → ℂ}
    (hF : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => G (ofComplex z))
    (σ : SL(2, ℤ)) :
    ∃ᶠ τ in atImInfty, F (σ • τ) = G (σ • τ) := by
  rw [UpperHalfPlane.atImInfty, Filter.frequently_comap, Filter.frequently_atTop]
  intro A
  obtain ⟨τ, hA, heq⟩ := exists_im_lt_and_agree hF σ A
  exact ⟨UpperHalfPlane.im τ, le_of_lt hA, τ, rfl, heq⟩

end S3bBridge
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

end BridgeSplice
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

namespace S3c2

private def _root_.S3c2.Lq (n : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion n f)

p2m_export "S3c2" "Lq"
private theorem _root_.S3c2.Lq_def (n : ℝ) (f : ℍ → ℂ) :
    Lq n f = ((qExpansion n f : PowerSeries ℂ) : LaurentSeries ℂ) := rfl

p2m_export "S3c2" "Lq_def"

private abbrev _root_.S3c2.Γ0 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

p2m_export "S3c2" "Γ0"

private abbrev CF (N : ℕ) : IntermediateField ℂ (LaurentSeries ℂ) :=
  ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)

private def jC (N : ℕ) [NeZero N] : CF N :=
  ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
    ModularCurve.coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.jq_mem_full N)⟩

private def jNC (N : ℕ) [NeZero N] : CF N :=
  ⟨ModularCurve.coeffEmb ℂ (ModularCurve.jqN N),
    ModularCurve.coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.jqd_mem_full N (dvd_refl N))⟩

private theorem coe_jC (N : ℕ) [NeZero N] :
    (jC N : LaurentSeries ℂ) = ModularCurve.coeffEmb ℂ ModularCurve.jq := rfl

private theorem coe_jNC (N : ℕ) [NeZero N] :
    (jNC N : LaurentSeries ℂ) = ModularCurve.coeffEmb ℂ (ModularCurve.jqN N) := rfl

private theorem isCusp_of_not_mem {K E : Type*} [Field K] [Field E] [Algebra K E] {j : E}
    {v : AlgebraicCurve.Place K E} (h : j ∉ v.toValuationSubring) : ModularCurve.IsCusp j v :=
  h

private theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    ModularCurve.coeffEmb ℂ (ModularCurve.qExpand ℚ n x) =
      ModularCurve.qExpand ℂ n (ModularCurve.coeffEmb ℂ x) := by
  ext m
  rw [ModularCurve.coeffEmb_coeff]
  by_cases hdvd : (n : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul,
      ModularCurve.coeffEmb_coeff]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd n _ hdvd,
      ModularCurve.qExpand_coeff_of_not_dvd n _ hdvd, map_zero]

private theorem coeffEmb_jq_eq_jqModC :
    ModularCurve.coeffEmb ℂ ModularCurve.jq = ModularCurve.jqModC ℂ :=

  ModularCurve.map_jqModC (K := ℚ) (algebraMap ℚ ℂ)

private theorem coe_jNC_eq_jqNModC (N : ℕ) [NeZero N] :
    (jNC N : LaurentSeries ℂ) = ModularCurve.jqNModC ℂ N := by
  rw [coe_jNC, ModularCurve.jqN, coeffEmb_qExpand, coeffEmb_jq_eq_jqModC]
  rfl

section Ext

variable (N : ℕ) [NeZero N]

private def GenFull : Prop :=
  ModularCurve.modularFunctionField N = ModularCurve.modularFunctionFieldFull N

private def GenC : Prop :=
  ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionField N) =
    ModularCurve.modularFunctionFieldC ℂ N

variable {N}

private theorem CF_eq_adjoin (hfull : GenFull N) (hC : GenC N) :
    CF N = IntermediateField.adjoin ℂ {ModularCurve.jqModC ℂ, ModularCurve.jqNModC ℂ N} := by
  rw [CF, ← hfull]
  exact hC

private theorem ringHom_ext_of_jq_jqN (hfull : GenFull N) (hC : GenC N) {R : Type*} [Field R]
    (Φ Ψ : CF N →+* R)
    (hc : ∀ c : ℂ, Φ (algebraMap ℂ (CF N) c) = Ψ (algebraMap ℂ (CF N) c))
    (h1 : Φ (jC N) = Ψ (jC N)) (h2 : Φ (jNC N) = Ψ (jNC N)) : Φ = Ψ := by
  have hCF := CF_eq_adjoin hfull hC
  set S : Set (LaurentSeries ℂ) := Set.range (algebraMap ℂ (LaurentSeries ℂ)) ∪
    {ModularCurve.jqModC ℂ, ModularCurve.jqNModC ℂ N} with hS

  have memCF : ∀ {y : LaurentSeries ℂ}, y ∈ Subfield.closure S → y ∈ CF N := fun {y} hy =>
    (SetLike.ext_iff.mp hCF y).mpr hy
  suffices key : ∀ (y : LaurentSeries ℂ) (hy : y ∈ Subfield.closure S),
      Φ ⟨y, memCF hy⟩ = Ψ ⟨y, memCF hy⟩ by
    apply RingHom.ext
    rintro ⟨z, hz⟩
    exact key z ((SetLike.ext_iff.mp hCF z).mp hz)
  intro y hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | hy
      · have e : (⟨algebraMap ℂ (LaurentSeries ℂ) c, memCF (Subfield.subset_closure
            (Set.mem_union_left _ ⟨c, rfl⟩))⟩ : CF N) = algebraMap ℂ (CF N) c :=
          Subtype.ext rfl
        rw [e]
        exact hc c
      · rcases hy with rfl | rfl
        · have e : (⟨ModularCurve.jqModC ℂ, memCF (Subfield.subset_closure
              (Set.mem_union_right _ (Set.mem_insert _ _)))⟩ : CF N) = jC N :=
            Subtype.ext coeffEmb_jq_eq_jqModC.symm
          rw [e]
          exact h1
        · have e : (⟨ModularCurve.jqNModC ℂ N, memCF (Subfield.subset_closure
              (Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)))⟩ : CF N) = jNC N :=
            Subtype.ext (coe_jNC_eq_jqNModC N).symm
          rw [e]
          exact h2
  | one =>
      have e : (⟨1, memCF (one_mem _)⟩ : CF N) = 1 := rfl
      rw [e, map_one, map_one]
  | add x y hx hy ihx ihy =>
      have e : (⟨x + y, memCF (add_mem hx hy)⟩ : CF N) = ⟨x, memCF hx⟩ + ⟨y, memCF hy⟩ := rfl
      rw [e, Φ.map_add, Ψ.map_add, ihx, ihy]
  | neg x hx ih =>
      have e : (⟨-x, memCF (neg_mem hx)⟩ : CF N) = -⟨x, memCF hx⟩ := rfl
      rw [e, Φ.map_neg, Ψ.map_neg, ih]
  | inv x hx ih =>
      have e : (⟨x⁻¹, memCF (inv_mem hx)⟩ : CF N) = (⟨x, memCF hx⟩ : CF N)⁻¹ := rfl
      rw [e, map_inv₀ Φ, map_inv₀ Ψ, ih]
  | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, memCF (mul_mem hx hy)⟩ : CF N) = ⟨x, memCF hx⟩ * ⟨y, memCF hy⟩ := rfl
      rw [e, Φ.map_mul, Ψ.map_mul, ihx, ihy]

end Ext
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

private theorem exists_slot_matrices (N a b : ℕ) (hN : N ≠ 0) (ha : a ∣ N)
    (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) :
    ∃ σ γ : SL(2, ℤ),
      !![(N : ℤ), 0; 0, 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, ((N / a : ℕ) : ℤ)] := by
  set D : ℕ := N / a with hD
  have haD : a * D = N := Nat.mul_div_cancel' ha
  have hD0 : D ≠ 0 := fun h => hN (by rw [← haD, h, mul_zero])
  have ha0 : a ≠ 0 := fun h => hN (by rw [← haD, h, zero_mul])

  set m : ℕ := ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ b), p with hm
  set q : ℤ := (a : ℤ) * m - b with hq
  have hcopN : Nat.Coprime D q.natAbs := by
    apply Nat.coprime_of_dvd
    intro p hp hpD hpq
    have hpq' : (p : ℤ) ∣ q := Int.ofNat_dvd_left.mpr hpq
    by_cases hpb : p ∣ b
    ·
      have hpa : ¬ p ∣ a := by
        intro hpa
        have h1 : p ∣ Nat.gcd (Nat.gcd a b) D := Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) hpD
        rw [hg] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      have hpm : ¬ p ∣ m := by
        intro hpm'
        obtain ⟨p', hp'mem, hpp'⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun p : ℕ => p)).mp hpm'
        rw [Finset.mem_filter, Nat.mem_primeFactors] at hp'mem
        obtain ⟨⟨hp'prime, -, -⟩, hp'b⟩ := hp'mem
        rw [Nat.prime_dvd_prime_iff_eq hp hp'prime] at hpp'
        exact hp'b (hpp' ▸ hpb)
      have hpam : ¬ p ∣ a * m := fun h => (hp.dvd_mul.mp h).elim hpa hpm
      apply hpam
      have h2 : (p : ℤ) ∣ ((a * m : ℕ) : ℤ) := by
        have e : ((a * m : ℕ) : ℤ) = q + b := by rw [hq]; push_cast; ring
        rw [e]
        exact dvd_add hpq' (by exact_mod_cast hpb)
      exact_mod_cast h2
    ·
      have hpm : p ∣ m :=
        Finset.dvd_prod_of_mem (fun p : ℕ => p)
          (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpD, hD0⟩, hpb⟩)
      apply hpb
      have h2 : (p : ℤ) ∣ (b : ℤ) := by
        have e : (b : ℤ) = (a : ℤ) * m - q := by rw [hq]; ring
        rw [e]
        exact dvd_sub (dvd_mul_of_dvd_right (by exact_mod_cast hpm) _) hpq'
      exact_mod_cast h2
  have hcop : IsCoprime q (D : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact hcopN.symm
  obtain ⟨u, v, huv⟩ := hcop

  refine ⟨⟨!![1, (m : ℤ); -u * a, -u * b + v * D], ?_⟩, ⟨!![(D : ℤ), q; -u, v], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination huv
  · rw [Matrix.det_fin_two_of]
    linear_combination huv
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast [← haD] <;> ring

private theorem Lq_eq_qExpand_qTwist {h : ℝ} {F f : ℍ → ℂ} (α : ℕ) [NeZero α] (ζ : ℂˣ)
    (hcoeff : ∀ m : ℕ, (qExpansion h F).coeff m =
      if α ∣ m then (ζ : ℂ) ^ (m / α) * (qExpansion 1 f).coeff (m / α) else 0) :
    Lq h F = ModularCurve.qExpand ℂ α (ModularCurve.qTwist ζ (Lq 1 f)) := by
  ext m
  rw [Lq, Lq]
  by_cases hdvd : (α : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.qTwist_coeff]
    rcases lt_or_ge k 0 with hk | hk
    · have hαk : (α : ℤ) * k < 0 := by
        have hα0 : (0 : ℤ) < α := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne α)
        nlinarith
      rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hαk,
        ModularCurve.ofPowerSeries_coeff_of_neg _ hk, mul_zero]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [show ((α : ℤ) * (n : ℤ)) = ((α * n : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, hcoeff,
        if_pos (dvd_mul_right α n), Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero (NeZero.ne α)),
        zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd α _ hdvd]
    rcases lt_or_ge m 0 with hm | hm
    · exact ModularCurve.ofPowerSeries_coeff_of_neg _ hm
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcoeff, if_neg]
      exact fun H => hdvd (by exact_mod_cast H)

section CuspJN

variable (N : ℕ) [NeZero N]

private def _root_.S3c2.Dm : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(N : ℝ), 0; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    first | exact Nat.cast_ne_zero.mpr (NeZero.ne N) | simpa using (Nat.cast_ne_zero (R := ℝ)).mpr (NeZero.ne N) | simp [NeZero.ne N])

p2m_export "S3c2" "Dm"
private theorem Dm_val : ((Dm N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(N : ℝ), 0; 0, 1] := rfl

private theorem det_Dm : (Dm N).det.val = N := by
  show Matrix.det ((Dm N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = N
  rw [Dm_val, Matrix.det_fin_two_of]
  ring

variable (a D' : ℕ) [NeZero a] [NeZero D'] (b : ℕ)

private def Tm : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℝ), b; 0, D'] (by
    rw [Matrix.det_fin_two_of]
    have h : (a : ℝ) * D' ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne a))
      (Nat.cast_ne_zero.mpr (NeZero.ne D'))
    simpa using h)

private theorem Tm_val : ((Tm a D' b : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; 0, D'] :=
  rfl

private theorem det_Tm : (Tm a D' b).det.val = a * D' := by
  show Matrix.det ((Tm a D' b : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = a * D'
  rw [Tm_val, Matrix.det_fin_two_of]
  ring

variable {N a D' b}

private theorem Dm_mul_eq_of_int {σ γ : SL(2, ℤ)}
    (h : !![(N : ℤ), 0; 0, 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, (D' : ℤ)]) :
    Dm N * (σ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * Tm a D' b := by
  rw [Units.ext_iff]
  have hL : (↑(Dm N * (σ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(N : ℝ), 0; 0, 1] * ((σ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) := rfl
  have hR : (↑((γ : GL (Fin 2) ℝ) * Tm a D' b) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) * !![(a : ℝ), b; 0, D'] := rfl
  rw [hL, hR]
  have hij : ∀ i j, ((!![(N : ℤ), 0; 0, 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ) =
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, (D' : ℤ)]) i j : ℝ) := fun i j => by
    rw [h]
  ext i j
  have hij' := hij i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at hij' ⊢ <;>
    exact hij'

variable {k : ℤ}

private theorem slash_apply_of_det_pos (f : ℍ → ℂ) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (τ : ℍ) :
    (f ∣[k] g) τ = f (g • τ) * ((g.det.val : ℝ) : ℂ) ^ (k - 1) * denom g τ ^ (-k) := by
  rw [ModularForm.slash_apply]
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have h1 : UpperHalfPlane.σ g (f (g • τ)) = f (g • τ) := by
    simp [UpperHalfPlane.σ, hg']
  rw [h1, abs_of_pos hg]

private theorem denom_Tm (τ : ℍ) : denom (Tm a D' b) τ = D' := by
  simp [denom, Tm_val]

private theorem slash_Tm_apply (haD : a * D' = N) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] Tm a D' b) τ = ((N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k)) * f (Tm a D' b • τ) := by
  have hdet : (0 : ℝ) < (Tm a D' b).det.val := by
    rw [det_Tm]
    exact_mod_cast Nat.pos_of_ne_zero (by rw [haD]; exact NeZero.ne N)
  rw [slash_apply_of_det_pos f hdet, det_Tm, denom_Tm]
  have : ((a : ℝ) * D' : ℝ) = (N : ℝ) := by exact_mod_cast haD
  rw [this]
  push_cast
  ring

private theorem slash_Dm_slash_eq {σ γ : SL(2, ℤ)}
    (hslot : Dm N * (σ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * Tm a D' b)
    (f : ModularForm (Γ0 1) k) :
    (⇑f ∣[k] Dm N) ∣[k] σ = ⇑f ∣[k] Tm a D' b := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ Γ0 1 :=
    Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _))
  rw [SL_slash, ← SlashAction.slash_mul, hslot, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn f _ hγ]

private def ζT (D' b : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * b / D')) (Complex.exp_ne_zero _)

private theorem coe_ζT (D' b : ℕ) :
    (ζT D' b : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / D') := rfl

private def TwistFormula (F f : ℍ → ℂ) (h : ℝ) (α : ℕ) (ζ : ℂ) : Prop :=
  ∀ m : ℕ, (qExpansion h F).coeff m =
    if α ∣ m then ζ ^ (m / α) * (qExpansion 1 f).coeff (m / α) else 0

private theorem Lq_of_TwistFormula {F f : ℍ → ℂ} {h : ℝ} {α : ℕ} [NeZero α] (ζ : ℂˣ)
    (hT : TwistFormula F f h α ζ) :
    Lq h F = ModularCurve.qExpand ℂ α (ModularCurve.qTwist ζ (Lq 1 f)) :=
  Lq_eq_qExpand_qTwist α ζ hT

private theorem Lq_eq_zero_iff (n : ℝ) (f : ℍ → ℂ) : Lq n f = 0 ↔ qExpansion n f = 0 := by
  rw [Lq]
  constructor
  · intro h
    exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

private theorem _root_.S3c2.one_mem_strictPeriods_Gamma0 (M : ℕ) : (1 : ℝ) ∈ (Γ0 M).strictPeriods := by
  show (1 : ℝ) ∈ Subgroup.strictPeriods
    ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

p2m_export "S3c2" "one_mem_strictPeriods_Gamma0"
private theorem Lq_one_smul {M : ℕ} (c : ℂ) (A : ModularForm (Γ0 M) k) :
    Lq 1 ⇑(c • A) = HahnSeries.C c * Lq 1 ⇑A := by
  rw [Lq, Lq, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma0 M) c A,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

private theorem _root_.S3c2.Lq_one_ne_zero {M : ℕ} {A : ModularForm (Γ0 M) k} (hA : A ≠ 0) : Lq 1 ⇑A ≠ 0 := by
  rw [ne_eq, Lq_eq_zero_iff,
    ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_Gamma0 M)]
  exact hA

p2m_export "S3c2" "Lq_one_ne_zero"
private theorem qTwist_one {R : Type*} [CommRing R] (x : LaurentSeries R) :
    ModularCurve.qTwist 1 x = x := by
  ext m
  rw [ModularCurve.qTwist_coeff, one_zpow, Units.val_one, one_mul]

private theorem ne_zero_of_coe_eq_slash {M : ℕ} {G : ModularForm (Γ0 M) k} {f : ModularForm (Γ0 1) k}
    (g : GL (Fin 2) ℝ) (hG : ⇑G = ⇑f ∣[k] g) (hf : f ≠ 0) : G ≠ 0 := by
  intro h0
  apply hf
  have h1 : ⇑f ∣[k] g = 0 := by rw [← hG, h0, ModularForm.coe_zero]
  have h2 : ⇑f = 0 := (SlashAction.slash_eq_zero_iff k g ⇑f).mp h1
  exact DFunLike.coe_injective (h2.trans ModularForm.coe_zero.symm)

p2m_open "ModularCurve~coeffEmb_qExpand~order_qExpand" in

private theorem Φ_jNC {σ γ : SL(2, ℤ)}
    (hslot : Dm N * (σ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * Tm a D' b)
    (g₁ h₁ : ModularForm (Γ0 1) k) (hh₁ : h₁ ≠ 0)
    (HJ : coeffEmb ℂ jq * Lq 1 ⇑h₁ = Lq 1 ⇑g₁)
    (G H : ModularForm (Γ0 N) k) (hG : ⇑G = ⇑g₁ ∣[k] Dm N) (hH : ⇑H = ⇑h₁ ∣[k] Dm N)
    (Φ : CF N →+* LaurentSeries ℂ)
    (hΦ : ∀ (x : CF N) {k : ℤ} {g h : ModularForm (Γ0 N) k}, h ≠ 0 →
      (x : LaurentSeries ℂ) * Lq 1 ⇑h = Lq 1 ⇑g → Φ x = Lq N (⇑g ∣[k] σ) / Lq N (⇑h ∣[k] σ))
    (twT : ∀ f : ModularForm (Γ0 1) k,
      TwistFormula (⇑f ∣[k] Tm a D' b)
        ⇑((((N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k))) • f) N (a * a) (ζT D' b))
    (twD : ∀ f : ModularForm (Γ0 1) k,
      TwistFormula (⇑f ∣[k] Dm N) ⇑(((N : ℂ) ^ (k - 1)) • f) 1 N 1) :
    Φ (jNC N) = qExpand ℂ (a * a) (qTwist (ζT D' b) (coeffEmb ℂ jq)) := by
  haveI : NeZero (a * a) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  set cD : ℂ := (N : ℂ) ^ (k - 1) with hcD
  set cT : ℂ := (N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k) with hcT
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcD0 : cD ≠ 0 := zpow_ne_zero _ hN0
  have hcT0 : cT ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hN0) (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne D')))

  have hLG : Lq 1 ⇑G = HahnSeries.C cD * qExpand ℂ N (Lq 1 ⇑g₁) := by
    rw [hG, Lq_of_TwistFormula (1 : ℂˣ) (twD g₁), qTwist_one, Lq_one_smul,
      map_mul, ModularCurve.qExpand_C]
  have hLH : Lq 1 ⇑H = HahnSeries.C cD * qExpand ℂ N (Lq 1 ⇑h₁) := by
    rw [hH, Lq_of_TwistFormula (1 : ℂˣ) (twD h₁), qTwist_one, Lq_one_smul,
      map_mul, ModularCurve.qExpand_C]

  have hh₁L : Lq 1 ⇑h₁ ≠ 0 := Lq_one_ne_zero hh₁
  have hjq : coeffEmb ℂ jq = Lq 1 ⇑g₁ / Lq 1 ⇑h₁ := (eq_div_of_mul_eq hh₁L HJ)

  have hpres : (jNC N : LaurentSeries ℂ) * Lq 1 ⇑H = Lq 1 ⇑G := by
    rw [coe_jNC, ModularCurve.jqN, coeffEmb_qExpand, hjq, hLG, hLH, map_div₀]
    have hq : qExpand ℂ N (Lq 1 ⇑h₁) ≠ 0 :=
      (map_ne_zero_iff _ (ModularCurve.qExpand_injective (R := ℂ) N)).mpr hh₁L
    field_simp
  have hH0 : H ≠ 0 := ne_zero_of_coe_eq_slash (Dm N) hH hh₁

  rw [hΦ (jNC N) hH0 hpres, hG, hH, slash_Dm_slash_eq hslot g₁, slash_Dm_slash_eq hslot h₁,
    Lq_of_TwistFormula (ζT D' b) (twT g₁), Lq_of_TwistFormula (ζT D' b) (twT h₁), ← map_div₀,
    ← map_div₀, Lq_one_smul, Lq_one_smul,
    mul_div_mul_left _ _ ((map_ne_zero HahnSeries.C).mpr hcT0), hjq]

private def ζN (M : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / M)) (Complex.exp_ne_zero _)

private theorem coe_ζN (M : ℕ) : (ζN M : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) := rfl

private theorem isPrimitiveRoot_ζN (M : ℕ) [NeZero M] : IsPrimitiveRoot (ζN M : ℂ) M :=
  Complex.isPrimitiveRoot_exp M (NeZero.ne M)

omit [NeZero N] in

private theorem ζN_pow_eq_ζT (haD : a * D' = N) : ζN N ^ (b * a) = ζT D' b := by
  ext
  rw [Units.val_pow_eq_pow_val, coe_ζN, coe_ζT, ← Complex.exp_nat_mul]
  congr 1
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hD : (D' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D')
  have hN : (N : ℂ) = a * D' := by exact_mod_cast haD.symm
  rw [hN]
  field_simp
  push_cast
  ring

private theorem smul_comp_Tm_eq_slash (haD : a * D' = N) (f : ModularForm (Γ0 1) k) :
    ⇑((((N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k))) • f) ∘ (fun τ : ℍ => Tm a D' b • τ) =
      ⇑f ∣[k] Tm a D' b := by
  funext τ
  rw [Function.comp_apply, ModularForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul,
    slash_Tm_apply haD]

private theorem denom_Dm (τ : ℍ) : denom (Dm N) τ = 1 := by
  simp [denom, Dm_val]

private theorem det_Dm_pos : (0 : ℝ) < (Dm N).det.val := by
  rw [det_Dm]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private theorem slash_Dm_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] Dm N) τ = (N : ℂ) ^ (k - 1) * f (Dm N • τ) := by
  rw [slash_apply_of_det_pos f (det_Dm_pos (N := N)), det_Dm, denom_Dm]
  simp [mul_comm]

private theorem smul_comp_Dm_eq_slash (f : ModularForm (Γ0 1) k) :
    ⇑(((N : ℂ) ^ (k - 1)) • f) ∘ (fun τ : ℍ => Dm N • τ) = ⇑f ∣[k] Dm N := by
  funext τ
  rw [Function.comp_apply, ModularForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul,
    slash_Dm_apply]

private theorem coe_Dm_smul (τ : ℍ) : ((Dm N • τ : ℍ) : ℂ) = (N : ℂ) * τ := by
  rw [coe_smul_of_det_pos (det_Dm_pos (N := N))]
  simp [num, denom, Dm_val]

private theorem qParam_one_Dm_smul (τ : ℍ) :
    Function.Periodic.qParam 1 ((Dm N • τ : ℍ) : ℂ) =
      1 * Function.Periodic.qParam 1 (τ : ℂ) ^ (N : ℕ) := by
  rw [coe_Dm_smul, one_mul, Function.Periodic.qParam, Function.Periodic.qParam,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

omit [NeZero N] in
private theorem algHom_algebraMap (ι : CF N →ₐ[ℂ] LaurentSeries ℂ) (c : ℂ) :
    (ι : CF N →+* LaurentSeries ℂ) (algebraMap ℂ (CF N) c) = HahnSeries.C c := by
  rw [AlgHom.coe_toRingHom, AlgHom.commutes, ModularCurve.algebraMap_laurentSeries_eq_single,
    HahnSeries.C_apply]

omit [NeZero N] in

private theorem ord_eq_zero_of_slot {γ' : ℤ} (hγ' : 0 < γ') (w : AlgebraicCurve.Place ℂ (CF N))
    (ι Φ : CF N →+* LaurentSeries ℂ) (hιΦ : ι = Φ)
    (hw : ∀ x, w.ord x * γ' = (ι x).order) {x : CF N} (hx : (Φ x).order = 0) :
    w.ord x = 0 := by
  have h := hw x
  rw [hιΦ, hx] at h
  exact (mul_eq_zero.mp h).resolve_right hγ'.ne'

end CuspJN
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

section LegII

variable {N : ℕ} [NeZero N] {k : ℤ}

p2m_open "ModularCurve~coeffEmb_qExpand~order_qExpand" in

private theorem leg_ii (hfull : GenFull N) (hC : GenC N)
    {a b : ℕ} (ha : a ∣ N) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a]
    (ι : CF N →ₐ[ℂ] LaurentSeries ℂ)
    (hι₁ : ι (jC N) = qExpand ℂ N (coeffEmb ℂ jq))
    (hι₂ : ι (jNC N) = qExpand ℂ (a * a) (qTwist (ζN N ^ (b * a)) (coeffEmb ℂ jq)))
    (w : AlgebraicCurve.Place ℂ (CF N)) {γ' : ℤ} (hγ' : 0 < γ')
    (hw : ∀ x, w.ord x * γ' = (ι x).order)
    (Φ : SL(2, ℤ) → (CF N →+* LaurentSeries ℂ))
    (hΦc : ∀ σ (c : ℂ), Φ σ (algebraMap ℂ (CF N) c) = HahnSeries.C c)
    (hΦpres : ∀ σ (x : CF N) {k : ℤ} {g h : ModularForm (Γ0 N) k}, h ≠ 0 →
      (x : LaurentSeries ℂ) * Lq 1 ⇑h = Lq 1 ⇑g → Φ σ x = Lq N (⇑g ∣[k] σ) / Lq N (⇑h ∣[k] σ))
    (hΦj : ∀ σ, Φ σ (jC N) = qExpand ℂ N (coeffEmb ℂ jq))
    (g₁ h₁ : ModularForm (Γ0 1) k) (hh₁ : h₁ ≠ 0)
    (HJ : coeffEmb ℂ jq * Lq 1 ⇑h₁ = Lq 1 ⇑g₁)
    (G H : ModularForm (Γ0 N) k) (hG : ⇑G = ⇑g₁ ∣[k] Dm N) (hH : ⇑H = ⇑h₁ ∣[k] Dm N)
    (twT : ∀ (D' : ℕ) [NeZero D'], a * D' = N → ∀ σ γ : SL(2, ℤ),
      Dm N * (σ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * Tm a D' b →
      ∀ f : ModularForm (Γ0 1) k,
        TwistFormula (⇑f ∣[k] Tm a D' b)
          ⇑((((N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k))) • f) N (a * a) (ζT D' b))
    (twD : ∀ f : ModularForm (Γ0 1) k,
      TwistFormula (⇑f ∣[k] Dm N) ⇑(((N : ℂ) ^ (k - 1)) • f) 1 N 1)
    (x : CF N) (hx : ∀ σ, (Φ σ x).order = 0) :
    w.ord x = 0 := by

  haveI : NeZero (N / a) := ⟨fun h => NeZero.ne N (by
    rw [← Nat.mul_div_cancel' ha, h, mul_zero])⟩
  have haD : a * (N / a) = N := Nat.mul_div_cancel' ha
  obtain ⟨σ, γ, hint⟩ := exists_slot_matrices N a b (NeZero.ne N) ha hg
  have hslot : Dm N * (σ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * Tm a (N / a) b :=
    Dm_mul_eq_of_int hint

  have hιΦ : (ι : CF N →+* LaurentSeries ℂ) = Φ σ := by
    apply ringHom_ext_of_jq_jqN hfull hC
    · intro c
      rw [algHom_algebraMap, hΦc]
    · rw [AlgHom.coe_toRingHom, hι₁, hΦj]
    · rw [AlgHom.coe_toRingHom, hι₂, ζN_pow_eq_ζT haD,
        Φ_jNC hslot g₁ h₁ hh₁ HJ G H hG hH (Φ σ) (hΦpres σ) (twT (N / a) haD σ γ hslot) twD]
  exact ord_eq_zero_of_slot hγ' w ι (Φ σ) hιΦ hw (hx σ)

end LegII
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

end S3c2
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

namespace S3glue2

p2m_open "ModularCurve~coeffEmb_qExpand~order_qExpand"

variable (N : ℕ) [NeZero N]

private theorem presN : S3c.Pres N := fun x hx => by
  obtain ⟨k, g, h, hh, hxgh, -⟩ := exists_modularForm_realize_eventuallyEq_div N ⟨x, hx⟩
  exact ⟨k, g, h, hh, hxgh⟩

private theorem presJ1 : S3c.PresJ :=
  exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq 1 1 (dvd_refl 1)

private theorem reindexN : S3c.Reindex N := fun k f n => by
  haveI : Fact (IsCusp OnePoint.infty (S3c.Γ0 1)) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (S3c.one_mem_strictPeriods_Gamma0 1)⟩
  exact S3CuspLimit.qExpansion_natCast_coeff N
    (SlashInvariantFormClass.periodic_comp_ofComplex f (S3c.one_mem_strictPeriods_Gamma0 1))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

omit [NeZero N] in
private theorem hNσ (σ : SL(2, ℤ)) :
    (N : ℝ) ∈ (ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹ • S3c.Γ0 N).strictPeriods :=
  S3CuspLimit.natCast_mem_strictPeriods_translate N σ

private theorem order_Φσ_eq_zero
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (hx : x ≠ 0)
    (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (σ : SL(2, ℤ)) :
    (S3c.Φσ N σ (presN N) (hNσ N σ) x).order = 0 := by
  obtain ⟨k, g, h, hh, hxgh, hev⟩ := exists_modularForm_realize_eventuallyEq_div N x

  have hg : g ≠ 0 := by
    intro hc
    apply hx
    apply Subtype.ext
    have h1 : (x : LaurentSeries ℂ) *
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [hxgh, hc, ModularForm.coe_zero, qExpansion_zero, map_zero]
    have hhL : ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 :=
      S3c.Lq_one_ne_zero (S3c.one_mem_strictPeriods_Gamma0 N) hh
    exact (mul_eq_zero.mp h1).resolve_right hhL

  have hFgh : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (fun w : ℍ => (g : ℍ → ℂ) w / (h : ℍ → ℂ) w) (ofComplex z) :=
    fun τ => (hF τ).trans (hev τ)

  have hfreq := S3bBridge.frequently_agree_atImInfty (F := F)
    (G := fun w : ℍ => (g : ℍ → ℂ) w / (h : ℍ → ℂ) w) hFgh σ
  have hE : (atImInfty ⊓ 𝓟 {τ : ℍ | F (σ • τ) =
      (fun w : ℍ => (g : ℍ → ℂ) w / (h : ℍ → ℂ) w) (σ • τ)}).NeBot :=
    Filter.frequently_iff_neBot.mp hfreq
  obtain ⟨L, hL, hlim⟩ := hcusp σ
  have hgqne : qExpansion (N : ℝ) (⇑g ∣[k] σ) ≠ 0 :=
    S3CuspLimit.qExpansion_slash_ne_zero g σ hg
  have hhqne : qExpansion (N : ℝ) (⇑h ∣[k] σ) ≠ 0 :=
    S3CuspLimit.qExpansion_slash_ne_zero h σ hh
  have horder : (qExpansion (N : ℝ) (⇑g ∣[k] σ)).order =
      (qExpansion (N : ℝ) (⇑h ∣[k] σ)).order :=
    S3bR2.order_eq_of_tendsto_div_ne_zero
      (S3CuspLimit.slash_periodic g σ) (S3CuspLimit.slash_mdiff g σ)
      (S3CuspLimit.slash_bddAtImInfty g σ)
      (S3CuspLimit.slash_periodic h σ) (S3CuspLimit.slash_mdiff h σ)
      (S3CuspLimit.slash_bddAtImInfty h σ)
      hgqne hhqne hE
      (fun τ hτ => by
        have hτ' : F (σ • τ) = (g : ℍ → ℂ) (σ • τ) / (h : ℍ → ℂ) (σ • τ) := hτ
        rw [hτ']
        exact S3CuspLimit.div_comp_smul_eq_div_slash k (⇑g) (⇑h) σ τ)
      hlim hL
  have hxL : (x : LaurentSeries ℂ) * S3c.Lq 1 ⇑h = S3c.Lq 1 ⇑g := hxgh
  rw [S3c.Φσ_eq N σ (presN N) (hNσ N σ) hh hxL, S3c.Lq_def, S3c.Lq_def]
  exact S3bR2T.order_div_eq_zero_of_order_eq hgqne hhqne horder

private theorem Dm_eq : S3c2.Dm N = S3bR2D.Dm N := rfl

private theorem factCusp_one : Fact (IsCusp OnePoint.infty (S3c.Γ0 1)) :=
  ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (S3c.one_mem_strictPeriods_Gamma0 1)⟩

omit [NeZero N] in
private theorem factCusp_N : Fact (IsCusp OnePoint.infty (S3c.Γ0 N)) :=
  ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (S3c.one_mem_strictPeriods_Gamma0 N)⟩

private theorem twD {k : ℤ} (f : ModularForm (S3c2.Γ0 1) k) :
    S3c2.TwistFormula (⇑f ∣[k] S3c2.Dm N) ⇑(((N : ℂ) ^ (k - 1)) • f) 1 N 1 := by
  haveI := factCusp_one
  set F₁ : ModularForm (S3c2.Γ0 1) k := ((N : ℂ) ^ (k - 1)) • f
  have hcomp : ⇑F₁ ∘ (fun τ : ℍ => S3c2.Dm N • τ) = ⇑f ∣[k] S3c2.Dm N :=
    S3c2.smul_comp_Dm_eq_slash f
  have hfun : ⇑F₁ ∘ (fun τ : ℍ => S3c2.Dm N • τ) = ⇑(S3bR2D.translateD N f) := by
    rw [hcomp, S3bR2D.coe_translateD, Dm_eq]
  have pφ : Periodic ((⇑F₁ ∘ (fun τ : ℍ => S3c2.Dm N • τ)) ∘ ofComplex) (1 : ℝ) := by
    rw [hfun]
    exact SlashInvariantFormClass.periodic_comp_ofComplex (S3bR2D.translateD N f)
      (S3c.one_mem_strictPeriods_Gamma0 N)
  have dφ : MDiff (⇑F₁ ∘ (fun τ : ℍ => S3c2.Dm N • τ)) := by
    rw [hfun]
    exact ModularFormClass.holo (S3bR2D.translateD N f)
  have bφ : IsBoundedAtImInfty (⇑F₁ ∘ (fun τ : ℍ => S3c2.Dm N • τ)) := by
    rw [hfun]
    haveI := factCusp_N N
    exact ModularFormClass.bdd_at_infty (S3bR2D.translateD N f)
  intro m
  rw [← hcomp]
  exact S3bR2T.qExpansion_comp_coeff
    (SlashInvariantFormClass.periodic_comp_ofComplex F₁ (S3c.one_mem_strictPeriods_Gamma0 1))
    (ModularFormClass.holo F₁) (ModularFormClass.bdd_at_infty F₁)
    one_pos (NeZero.ne N) (fun τ => S3c2.qParam_one_Dm_smul (N := N) τ) pφ dφ bφ m

private theorem twT {k : ℤ} {a b : ℕ} [NeZero a] (D' : ℕ) [NeZero D'] (haD : a * D' = N)
    (σ γ : SL(2, ℤ))
    (hslot : S3c2.Dm N * (σ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * S3c2.Tm a D' b)
    (f : ModularForm (S3c2.Γ0 1) k) :
    S3c2.TwistFormula (⇑f ∣[k] S3c2.Tm a D' b)
      ⇑((((N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k))) • f) N (a * a) (S3c2.ζT D' b) := by
  haveI := factCusp_one
  set F₁ : ModularForm (S3c2.Γ0 1) k := (((N : ℂ) ^ (k - 1) * (D' : ℂ) ^ (-k))) • f
  have hcomp : ⇑F₁ ∘ (fun τ : ℍ => S3c2.Tm a D' b • τ) = ⇑f ∣[k] S3c2.Tm a D' b :=
    S3c2.smul_comp_Tm_eq_slash haD f
  have hfun : ⇑F₁ ∘ (fun τ : ℍ => S3c2.Tm a D' b • τ) = ⇑(S3bR2D.translateD N f) ∣[k] σ := by
    rw [hcomp, ← S3c2.slash_Dm_slash_eq hslot f, S3bR2D.coe_translateD, Dm_eq]
  have pφ : Periodic ((⇑F₁ ∘ (fun τ : ℍ => S3c2.Tm a D' b • τ)) ∘ ofComplex) (N : ℝ) := by
    rw [hfun]
    exact S3CuspLimit.slash_periodic (S3bR2D.translateD N f) σ
  have dφ : MDiff (⇑F₁ ∘ (fun τ : ℍ => S3c2.Tm a D' b • τ)) := by
    rw [hfun]
    exact S3CuspLimit.slash_mdiff (S3bR2D.translateD N f) σ
  have bφ : IsBoundedAtImInfty (⇑F₁ ∘ (fun τ : ℍ => S3c2.Tm a D' b • τ)) := by
    rw [hfun]
    exact S3CuspLimit.slash_bddAtImInfty (S3bR2D.translateD N f) σ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have haa : a * a ≠ 0 := mul_ne_zero (NeZero.ne a) (NeZero.ne a)
  have hND : ((a : ℝ) * D') = (N : ℝ) := by rw [← haD, Nat.cast_mul]
  have hdet : 0 < (S3c2.Tm a D' b).det.val := by
    rw [S3c2.det_Tm]
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne a)))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D')))
  have hq : ∀ τ : ℍ, Periodic.qParam 1 ((S3c2.Tm a D' b • τ : ℍ) : ℂ) =
      (S3c2.ζT D' b : ℂ) * Periodic.qParam (N : ℝ) (τ : ℂ) ^ (a * a) := by
    intro τ
    have h := S3bR2T.qParam_one_upperTriangular (T := S3c2.Tm a D' b) (a := a) (b := b) (D' := D')
      (by simp [S3c2.Tm_val]) (by simp [S3c2.Tm_val]) (by simp [S3c2.Tm_val])
      (by simp [S3c2.Tm_val]) hdet τ
    rw [S3c2.coe_ζT, ← hND, ← sq]
    exact h
  intro m
  rw [← hcomp]
  exact S3bR2T.qExpansion_comp_coeff
    (SlashInvariantFormClass.periodic_comp_ofComplex F₁ (S3c.one_mem_strictPeriods_Gamma0 1))
    (ModularFormClass.holo F₁) (ModularFormClass.bdd_at_infty F₁)
    hNpos haa hq pφ dφ bφ m

private theorem ord_eq_zero_of_forall_order_eq_zero
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (v : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
    (hv : (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
        ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
          (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
        ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∉
      v.toValuationSubring)
    (hleg1 : ∀ σ : SL(2, ℤ), (S3c.Φσ N σ (presN N) (hNσ N σ) x).order = 0) :
    v.ord x = 0 := by

  obtain ⟨a, b, ha, -, hg, hNZa, ι, hι₁, hι₂, hw⟩ :=
    exists_slot_of_isCusp ℂ N (S3c2.ζN N) (S3c2.isPrimitiveRoot_ζN N) v hv
  haveI : NeZero a := hNZa
  have hγ' : (0 : ℤ) < ((a * Nat.gcd a (N / a) : ℕ) : ℤ) := by
    have h1 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact_mod_cast Nat.mul_pos h1 (Nat.gcd_pos_of_pos_left _ h1)

  obtain ⟨k₁, g₁, h₁, hh₁, HJ⟩ := presJ1
  rw [ModularCurve.qExpand_one_apply] at HJ
  have HJ' : ModularCurve.coeffEmb ℂ ModularCurve.jq * S3c2.Lq 1 ⇑h₁ = S3c2.Lq 1 ⇑g₁ := HJ
  refine S3c2.leg_ii (N := N) (modularFunctionField_eq_full N)
    (laurentBaseChange_modularFunctionField ℂ N) ha hg ι hι₁ hι₂ v hγ' hw
    (fun σ => S3c.Φσ N σ (presN N) (hNσ N σ))
    (fun σ c => S3c.Φσ_algebraMap N σ (presN N) (hNσ N σ) c)
    ?_
    (fun σ => S3c.Φσ_jq N σ (presN N) (hNσ N σ) presJ1 (reindexN N)
      (ModularCurve.coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.jq_mem_full N)))
    g₁ h₁ hh₁ HJ' (S3bR2D.translateD N g₁) (S3bR2D.translateD N h₁)
    (by rw [S3bR2D.coe_translateD, Dm_eq]) (by rw [S3bR2D.coe_translateD, Dm_eq])
    ?_ (fun f => twD N f) x hleg1
  · intro σ y k g h hh hy
    exact S3c.Φσ_eq N σ (presN N) (hNσ N σ) hh hy
  · intro D' hD' haD σ γ hslot f
    exact twT N D' haD σ γ hslot f

end S3glue2
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

p2m_open "ModularCurve~coeffEmb_qExpand~order_qExpand"

theorem solution (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (v : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
    (hv : (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
        ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
          (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
        ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∉
      v.toValuationSubring) :
    v.ord x = 0 := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact AlgebraicCurve.Place.ord_zero v
  · exact S3glue2.ord_eq_zero_of_forall_order_eq_zero N x v hv
      (fun σ => S3glue2.order_Φσ_eq_zero N x hx0 F hF hcusp σ)

end
p2m_reactivate "P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto.S3c"

end S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto
end P2MW
export P2MW.S_ModularCurve_ord_eq_zero_of_jq_not_mem_of_realize_tendsto (solution)
