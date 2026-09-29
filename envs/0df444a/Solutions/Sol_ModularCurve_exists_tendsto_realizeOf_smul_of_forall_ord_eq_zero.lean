-- Prove2me | solution 1 for ModularCurve.exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b7819fba-0c81-573a-8fbc-1ffef4b238e6

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "UpperHalfPlane ModularForm Filter Function Complex Function.Complex Matrix.SpecialLinearGroup OnePoint"
open scoped MatrixGroups Topology CongruenceSubgroup Pointwise Manifold

noncomputable section

namespace Ws49
namespace CUSPLIM

namespace S3CuspLimit

variable {k : ℤ}

def wd (Γ : Subgroup SL(2, ℤ)) : ℕ := Γ.normalCore.index

scoped instance wd_neZero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : NeZero (wd Γ) :=
  ⟨Subgroup.FiniteIndex.index_ne_zero⟩

theorem wd_pos (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (0 : ℝ) < wd Γ := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (wd Γ))

private theorem conj_T_zpow_mem (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (σ : SL(2, ℤ)) :
    σ * ModularGroup.T ^ (wd Γ : ℤ) * σ⁻¹ ∈ Γ := by
  have h1 : ModularGroup.T ^ (wd Γ : ℤ) ∈ Γ.normalCore := by
    rw [zpow_natCast]
    exact Subgroup.pow_index_mem Γ.normalCore ModularGroup.T
  have h2 : σ * ModularGroup.T ^ (wd Γ : ℤ) * σ⁻¹ ∈ Γ.normalCore :=
    (Subgroup.normalCore_normal Γ).conj_mem _ h1 σ
  exact Subgroup.normalCore_le Γ h2

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

theorem natCast_mem_strictPeriods_translate (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (σ : SL(2, ℤ)) :
    (wd Γ : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ • ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul, ← mapGL_T_zpow (wd Γ), coe_eq_mapGL, ← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ (conj_T_zpow_mem Γ σ)

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem coe_translate_SL (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    ⇑(ModularForm.translate g (σ : GL (Fin 2) ℝ)) = ⇑g ∣[k] σ := by
  rw [SL_slash]
  exact ModularForm.coe_translate g _

theorem slash_periodic (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    Periodic ((⇑g ∣[k] σ) ∘ ofComplex) (wd Γ : ℝ) := by
  rw [← coe_translate_SL g σ]
  exact SlashInvariantFormClass.periodic_comp_ofComplex
    (ModularForm.translate g (σ : GL (Fin 2) ℝ))
    (natCast_mem_strictPeriods_translate Γ σ)

theorem slash_mdiff (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    MDiff (⇑g ∣[k] σ) := by
  rw [← coe_translate_SL g σ]
  exact ModularFormClass.holo _

theorem slash_bddAtImInfty (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) :
    IsBoundedAtImInfty (⇑g ∣[k] σ) := by
  haveI hFact : Fact (IsCusp ∞ (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods (wd_pos Γ) (natCast_mem_strictPeriods_translate Γ σ)⟩
  have h := ModularFormClass.bdd_at_infty
    (f := ModularForm.translate g (σ : GL (Fin 2) ℝ))
  rwa [coe_translate_SL] at h

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

theorem qExpansion_slash_ne_zero
    (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (σ : SL(2, ℤ)) (hh : h ≠ 0) :
    qExpansion (wd Γ) (⇑h ∣[k] σ) ≠ 0 := by
  rw [Ne, qExpansion_eq_zero_iff (wd_pos Γ) (slash_periodic h σ) (slash_mdiff h σ)
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
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit"

namespace S3c

set_option linter.unusedSectionVars false

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem order_inv_laurent {x : LaurentSeries K} (hx : x ≠ 0) : (x⁻¹).order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

private theorem order_zpow_laurent {x : LaurentSeries K} (hx : x ≠ 0) (n : ℤ) :
    (x ^ n).order = n * x.order := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, HahnSeries.order_pow, nsmul_eq_mul]
  · rw [zpow_neg, zpow_natCast, order_inv_laurent (pow_ne_zero _ hx), HahnSeries.order_pow,
      nsmul_eq_mul, neg_mul]

variable (Φ : F →+* LaurentSeries K)

omit [Algebra K F] in
private theorem map_ne_zero_iff' {x : F} : Φ x ≠ 0 ↔ x ≠ 0 :=
  _root_.map_ne_zero_iff Φ Φ.injective

private def orderValuationSubring : ValuationSubring F where
  carrier := {x | 0 ≤ (Φ x).order}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff' Φ).2 hx0) ((map_ne_zero_iff' Φ).2 hy0)]
    omega
  one_mem' := by simp [HahnSeries.order_one]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rcases eq_or_ne (Φ x + Φ y) 0 with h0 | h0
    · simp [h0]
    · rw [map_add]
      exact (le_min hx hy).trans (HahnSeries.min_order_le_order_add h0)
  zero_mem' := by simp
  neg_mem' {x} hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rwa [map_neg, HahnSeries.order_neg]
  mem_or_inv_mem' x := by
    simp only [Set.mem_setOf_eq]
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    rw [map_inv₀, order_inv_laurent ((map_ne_zero_iff' Φ).2 hx0)]
    omega

private theorem mem_orderValuationSubring_iff {x : F} :
    x ∈ orderValuationSubring Φ ↔ 0 ≤ (Φ x).order :=
  Iff.rfl

private theorem coe_ne_zero_of_ne_zero {x : orderValuationSubring Φ} (hx : x ≠ 0) : (x : F) ≠ 0 :=
  fun h => hx (Subtype.ext h)

private theorem order_eq_zero_of_isUnit {x : orderValuationSubring Φ} (hu : IsUnit x) :
    (Φ (x : F)).order = 0 := by
  obtain ⟨u, rfl⟩ := hu
  have h1 : 0 ≤ (Φ ((u : orderValuationSubring Φ) : F)).order := u.val.2
  have h2 : 0 ≤ (Φ (((u⁻¹ : (orderValuationSubring Φ)ˣ) : orderValuationSubring Φ) : F)).order :=
    (u⁻¹).val.2
  have hprod : ((u : orderValuationSubring Φ) : F) *
      (((u⁻¹ : (orderValuationSubring Φ)ˣ) : orderValuationSubring Φ) : F) = 1 :=
    congrArg Subtype.val u.mul_inv
  have hx0 : ((u : orderValuationSubring Φ) : F) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  have hy0 : (((u⁻¹ : (orderValuationSubring Φ)ˣ) : orderValuationSubring Φ) : F) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact zero_ne_one hprod
  have := congrArg (fun z => (Φ z).order) hprod
  simp only [map_mul, map_one, HahnSeries.order_one] at this
  rw [HahnSeries.order_mul ((map_ne_zero_iff' Φ).2 hx0) ((map_ne_zero_iff' Φ).2 hy0)] at this
  omega

private theorem isUnit_of_order_eq_zero {x : orderValuationSubring Φ} (hx : (x : F) ≠ 0)
    (h0 : (Φ (x : F)).order = 0) : IsUnit x := by
  have hinv : (x : F)⁻¹ ∈ orderValuationSubring Φ := by
    rw [mem_orderValuationSubring_iff, map_inv₀, order_inv_laurent ((map_ne_zero_iff' Φ).2 hx),
      h0, neg_zero]
  exact ⟨⟨x, ⟨(x : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx),
    Subtype.ext (inv_mul_cancel₀ hx)⟩, rfl⟩

private theorem isPrincipalIdealRing_orderValuationSubring :
    IsPrincipalIdealRing (orderValuationSubring Φ) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · refine ⟨⟨0, ?_⟩⟩
    rw [hI]
    exact (Ideal.span_singleton_eq_bot.mpr rfl).symm
  obtain ⟨x₁, hx₁I, hx₁0⟩ := (Submodule.ne_bot_iff I).mp hI

  let P : ℕ → Prop := fun n =>
    ∃ x : orderValuationSubring Φ, x ∈ I ∧ x ≠ 0 ∧ (Φ (x : F)).order = n
  have hP : ∃ n, P n :=
    ⟨((Φ (x₁ : F)).order).toNat, x₁, hx₁I, hx₁0, (Int.toNat_of_nonneg x₁.2).symm⟩
  obtain ⟨x₀, hx₀I, hx₀0, hx₀n⟩ := Nat.find_spec hP
  have hmin : ∀ y : orderValuationSubring Φ, y ∈ I → y ≠ 0 →
      (Φ (x₀ : F)).order ≤ (Φ (y : F)).order := by
    intro y hyI hy0
    have h1 : Nat.find hP ≤ ((Φ (y : F)).order).toNat :=
      Nat.find_min' hP ⟨y, hyI, hy0, (Int.toNat_of_nonneg y.2).symm⟩
    have h2 : ((Nat.find hP : ℕ) : ℤ) ≤ ((((Φ (y : F)).order).toNat : ℕ) : ℤ) := by
      exact_mod_cast h1
    rw [Int.toNat_of_nonneg y.2] at h2
    rw [hx₀n]
    exact h2
  have hx₀F : (x₀ : F) ≠ 0 := coe_ne_zero_of_ne_zero Φ hx₀0
  have key : I = Ideal.span {x₀} := by
    apply le_antisymm
    · intro y hyI
      rcases eq_or_ne y 0 with rfl | hy0
      · exact Ideal.zero_mem _
      have hyF : (y : F) ≠ 0 := coe_ne_zero_of_ne_zero Φ hy0
      have hc : (y : F) * (x₀ : F)⁻¹ ∈ orderValuationSubring Φ := by
        rw [mem_orderValuationSubring_iff, map_mul, map_inv₀,
          HahnSeries.order_mul ((map_ne_zero_iff' Φ).2 hyF)
            (inv_ne_zero ((map_ne_zero_iff' Φ).2 hx₀F)),
          order_inv_laurent ((map_ne_zero_iff' Φ).2 hx₀F)]
        have := hmin y hyI hy0
        omega
      refine Ideal.mem_span_singleton'.mpr ⟨⟨(y : F) * (x₀ : F)⁻¹, hc⟩, ?_⟩
      apply Subtype.ext
      change (y : F) * (x₀ : F)⁻¹ * (x₀ : F) = (y : F)
      exact inv_mul_cancel_right₀ hx₀F _
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hx₀I
  exact ⟨⟨x₀, key⟩⟩

variable (hΦ : ∀ c : K, Φ (algebraMap K F c) = HahnSeries.C c) {t : F} (ht : (Φ t).order < 0)

private def orderPlace : AlgebraicCurve.Place K F where
  toValuationSubring := orderValuationSubring Φ
  algebraMap_mem' c := by
    show 0 ≤ (Φ (algebraMap K F c)).order
    rw [hΦ, HahnSeries.order_C]
  ne_top' h := by
    have : t ∈ orderValuationSubring Φ := h ▸ ValuationSubring.mem_top t
    exact not_le.mpr ht this
  isPrincipalIdealRing' := isPrincipalIdealRing_orderValuationSubring Φ

private theorem orderPlace_toValuationSubring :
    (orderPlace Φ hΦ ht).toValuationSubring = orderValuationSubring Φ := rfl

private theorem mem_orderPlace_iff {x : F} :
    x ∈ (orderPlace Φ hΦ ht).toValuationSubring ↔ 0 ≤ (Φ x).order :=
  Iff.rfl

private theorem not_mem_orderPlace : t ∉ (orderPlace Φ hΦ ht).toValuationSubring :=
  not_le.mpr ht

private theorem exists_order_eq_mul_ord :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, x ≠ 0 → (Φ x).order = e * (orderPlace Φ hΦ ht).ord x := by
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (orderPlace Φ hΦ ht).toValuationSubring
  have hϖ0 : (ϖ : F) ≠ 0 := coe_ne_zero_of_ne_zero Φ hϖ.ne_zero
  have hϖnn : 0 ≤ (Φ (ϖ : F)).order := ϖ.2
  have hϖpos : 0 < (Φ (ϖ : F)).order := by
    rcases hϖnn.lt_or_eq with h | h
    · exact h
    · exact absurd (isUnit_of_order_eq_zero Φ hϖ0 h.symm) hϖ.not_isUnit
  refine ⟨((Φ (ϖ : F)).order).toNat, by omega, fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := (orderPlace Φ hΦ ht).exists_unit_mul_zpow hx hϖ
  have hu0 : (((u : ((orderPlace Φ hΦ ht).toValuationSubring)ˣ) :
      (orderPlace Φ hΦ ht).toValuationSubring) : F) ≠ 0 :=
    coe_ne_zero_of_ne_zero Φ u.ne_zero
  have huord : (Φ (((u : ((orderPlace Φ hΦ ht).toValuationSubring)ˣ) :
      (orderPlace Φ hΦ ht).toValuationSubring) : F)).order = 0 :=
    order_eq_zero_of_isUnit Φ u.isUnit
  rw [Int.toNat_of_nonneg hϖnn]
  conv_lhs => rw [hu]
  rw [map_mul, map_zpow₀, HahnSeries.order_mul ((map_ne_zero_iff' Φ).2 hu0)
      (zpow_ne_zero _ ((map_ne_zero_iff' Φ).2 hϖ0)), huord, zero_add,
    order_zpow_laurent ((map_ne_zero_iff' Φ).2 hϖ0), mul_comm]

private theorem ord_eq_zero_iff {x : F} (hx : x ≠ 0) :
    (orderPlace Φ hΦ ht).ord x = 0 ↔ (Φ x).order = 0 := by
  obtain ⟨e, he, h⟩ := exists_order_eq_mul_ord Φ hΦ ht
  rw [h x hx]
  constructor
  · intro h0
    rw [h0, mul_zero]
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (by exact_mod_cast he.ne')
    · exact h1

end S3c
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit"

namespace S3c

private def Lq (n : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion n f)

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
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit"

section Concrete

variable (Γ : Subgroup SL(2, ℤ)) (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

private abbrev Γ0 : Subgroup (GL (Fin 2) ℝ) := (Γ : Subgroup (GL (Fin 2) ℝ))

private abbrev Γ1top : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ))

private abbrev CF : IntermediateField ℂ (LaurentSeries ℂ) :=
  ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)

private theorem one_mem_strictPeriods_levelOne : (1 : ℝ) ∈ Γ1top.strictPeriods := by
  show (1 : ℝ) ∈ Subgroup.strictPeriods
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

variable [hTΓ : Fact (ModularGroup.T ∈ Γ)]

private theorem one_mem_strictPeriods_Gamma0 : (1 : ℝ) ∈ (Γ0 Γ).strictPeriods := by
  show (1 : ℝ) ∈ Subgroup.strictPeriods ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hTΓ.out]
  exact AddSubgroup.mem_zmultiples _

private def Pres : Prop :=
  ∀ x : LaurentSeries ℂ,
    x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) →
      ∃ (k : ℤ) (g h : ModularForm (Γ0 Γ) k), h ≠ 0 ∧
        x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

variable (pres : Pres Γ)
variable (hN : (N : ℝ) ∈ (ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹ • Γ0 Γ).strictPeriods)

private def presWt (x : CF Γ) : ℤ := (pres x x.2).choose

private def presNum (x : CF Γ) : ModularForm (Γ0 Γ) (presWt Γ pres x) := (pres x x.2).choose_spec.choose

private def presDen (x : CF Γ) : ModularForm (Γ0 Γ) (presWt Γ pres x) :=
  (pres x x.2).choose_spec.choose_spec.choose

private theorem presDen_ne_zero (x : CF Γ) : presDen Γ pres x ≠ 0 :=
  (pres x x.2).choose_spec.choose_spec.choose_spec.1

private theorem pres_eq (x : CF Γ) :
    (x : LaurentSeries ℂ) * Lq 1 ⇑(presDen Γ pres x) = Lq 1 ⇑(presNum Γ pres x) :=
  (pres x x.2).choose_spec.choose_spec.choose_spec.2

private def Φσfun (x : CF Γ) : LaurentSeries ℂ :=
  cuspRatio σ N (presNum Γ pres x) (presDen Γ pres x)

include hN in

private theorem Φσfun_eq {x : CF Γ} {k : ℤ} {g h : ModularForm (Γ0 Γ) k} (hh : h ≠ 0)
    (hx : (x : LaurentSeries ℂ) * Lq 1 ⇑h = Lq 1 ⇑g) :
    Φσfun Γ N σ pres x = cuspRatio σ N g h := by
  apply cuspRatio_eq_of_cross σ N hN (one_mem_strictPeriods_Gamma0 Γ) (presDen_ne_zero Γ pres x) hh
  rw [← pres_eq Γ pres x, ← hx]
  ring

include hN in

private def Φσ : CF Γ →+* LaurentSeries ℂ where
  toFun := Φσfun Γ N σ pres
  map_one' := by
    have h := Φσfun_eq Γ N σ pres hN (x := 1) (presDen_ne_zero Γ pres 1)
      (g := presDen Γ pres 1) (by simp)
    rw [h, cuspRatio_self σ N hN (presDen_ne_zero Γ pres 1)]
  map_mul' x y := by
    have hx := pres_eq Γ pres x
    have hy := pres_eq Γ pres y
    have h := Φσfun_eq Γ N σ pres hN (x := x * y)
      (g := (presNum Γ pres x).mul (presNum Γ pres y))
      (h := (presDen Γ pres x).mul (presDen Γ pres y))
      (mul_ne_zero_MF (one_mem_strictPeriods_Gamma0 Γ) (presDen_ne_zero Γ pres x)
        (presDen_ne_zero Γ pres y)) (by
        rw [Lq_one_mul (one_mem_strictPeriods_Gamma0 Γ), Lq_one_mul (one_mem_strictPeriods_Gamma0 Γ),
          ← hx, ← hy]
        push_cast
        ring)
    rw [h, cuspRatio_mul σ N hN, Φσfun, Φσfun]
  map_zero' := by
    have h := Φσfun_eq Γ N σ pres hN (x := 0) (presDen_ne_zero Γ pres 1)
      (g := (0 : ModularForm (Γ0 Γ) (presWt Γ pres 1))) (by
        rw [Lq_one_zero]; simp)
    rw [h, cuspRatio_zero_left]
  map_add' x y := by
    have hx := pres_eq Γ pres x
    have hy := pres_eq Γ pres y
    have h := Φσfun_eq Γ N σ pres hN (x := x + y)
      (g := (presNum Γ pres x).mul (presDen Γ pres y) + (presDen Γ pres x).mul (presNum Γ pres y))
      (h := (presDen Γ pres x).mul (presDen Γ pres y))
      (mul_ne_zero_MF (one_mem_strictPeriods_Gamma0 Γ) (presDen_ne_zero Γ pres x)
        (presDen_ne_zero Γ pres y)) (by
        rw [Lq_one_add (one_mem_strictPeriods_Gamma0 Γ),
          Lq_one_mul (one_mem_strictPeriods_Gamma0 Γ), Lq_one_mul (one_mem_strictPeriods_Gamma0 Γ),
          Lq_one_mul (one_mem_strictPeriods_Gamma0 Γ), ← hx, ← hy]
        push_cast
        ring)
    rw [h, cuspRatio_add σ N hN (presDen_ne_zero Γ pres x) (presDen_ne_zero Γ pres y), Φσfun,
      Φσfun]

include hN in
private theorem Φσ_apply (x : CF Γ) : Φσ Γ N σ pres hN x = Φσfun Γ N σ pres x := rfl

include hN in

private theorem Φσ_eq {x : CF Γ} {k : ℤ} {g h : ModularForm (Γ0 Γ) k} (hh : h ≠ 0)
    (hx : (x : LaurentSeries ℂ) * Lq 1 ⇑h = Lq 1 ⇑g) :
    Φσ Γ N σ pres hN x = Lq N (⇑g ∣[k] σ) / Lq N (⇑h ∣[k] σ) :=
  Φσfun_eq Γ N σ pres hN hh hx

include hN in

private theorem Φσ_algebraMap (c : ℂ) : Φσ Γ N σ pres hN (algebraMap ℂ (CF Γ) c) = HahnSeries.C c := by
  have h := Φσfun_eq Γ N σ pres hN (x := algebraMap ℂ (CF Γ) c) (presDen_ne_zero Γ pres 1)
    (g := c • presDen Γ pres 1) (by
      rw [Lq_one_smul (one_mem_strictPeriods_Gamma0 Γ)]
      simp [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.C_apply])
  rw [Φσ_apply, h, cuspRatio_smul σ N hN c (presDen_ne_zero Γ pres 1)]

private theorem Gamma0_le_Gamma0_one : Γ0 Γ ≤ Γ1top :=
  Subgroup.map_mono fun _ _ => CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _)

private def restrictOne {k : ℤ} (f : ModularForm (Γ1top) k) : ModularForm (Γ0 Γ) k where
  toSlashInvariantForm :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ =>
        SlashInvariantForm.slash_action_eqn f γ (Gamma0_le_Gamma0_one Γ hγ) }
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono (Gamma0_le_Gamma0_one Γ))

@[scoped simp]
private theorem coe_restrictOne {k : ℤ} (f : ModularForm (Γ1top) k) : ⇑(restrictOne Γ f) = ⇑f := rfl

private theorem slash_eq_self_of_level_one {k : ℤ} (f : ModularForm (Γ1top) k) : ⇑f ∣[k] σ = ⇑f := by
  have hσ : (σ : GL (Fin 2) ℝ) ∈ Γ1top :=
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
    (hj : ModularCurve.coeffEmb ℂ ModularCurve.jq ∈ CF Γ) :
    Φσ Γ N σ pres hN ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, hj⟩ =
      ModularCurve.qExpand ℂ N (ModularCurve.coeffEmb ℂ ModularCurve.jq) := by
  obtain ⟨k, g₁, h₁, hh₁, HJ⟩ := presJ
  rw [ModularCurve.qExpand_one_apply] at HJ
  have hh : restrictOne Γ h₁ ≠ 0 := fun H =>
    hh₁ (DFunLike.coe_injective (by simpa using congrArg DFunLike.coe H))
  have hpres : ((⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, hj⟩ : CF Γ) : LaurentSeries ℂ) *
      Lq 1 ⇑(restrictOne Γ h₁) = Lq 1 ⇑(restrictOne Γ g₁) := HJ
  rw [Φσ_eq Γ N σ pres hN hh hpres, coe_restrictOne, coe_restrictOne,
    slash_eq_self_of_level_one σ g₁, slash_eq_self_of_level_one σ h₁,
    Lq_natCast_eq_qExpand N (reindex k g₁), Lq_natCast_eq_qExpand N (reindex k h₁), ← map_div₀]
  congr 1
  have hh₁L : Lq 1 ⇑h₁ ≠ 0 := Lq_one_ne_zero (one_mem_strictPeriods_levelOne) hh₁
  exact (eq_div_of_mul_eq hh₁L HJ).symm

include hN in

private theorem order_Φσ_jq (presJ : PresJ) (reindex : Reindex N)
    (hj : ModularCurve.coeffEmb ℂ ModularCurve.jq ∈ CF Γ) :
    (Φσ Γ N σ pres hN ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, hj⟩).order = -N := by
  rw [Φσ_jq Γ N σ pres hN presJ reindex hj, order_qExpand N coeffEmb_jq_ne_zero, order_coeffEmb_jq,
    mul_neg_one]

end Concrete
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit"

end S3c
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3c"

namespace S3glue

open ModularCurve

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [hTΓ : Fact (ModularGroup.T ∈ Γ)]

private theorem presN : S3c.Pres Γ := fun x hx =>
  exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC Γ hTΓ.out x hx

private theorem presJ1 : S3c.PresJ :=
  exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq 1 1 (dvd_refl 1)

private theorem reindexN (N : ℕ) [NeZero N] : S3c.Reindex N := fun k f n => by
  haveI : Fact (IsCusp OnePoint.infty S3c.Γ1top) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos S3c.one_mem_strictPeriods_levelOne⟩
  exact S3CuspLimit.qExpansion_natCast_coeff N
    (SlashInvariantFormClass.periodic_comp_ofComplex f S3c.one_mem_strictPeriods_levelOne)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

variable (σ : SL(2, ℤ))

private theorem hNσ :
    ((S3CuspLimit.wd Γ : ℕ) : ℝ) ∈ (ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹ • S3c.Γ0 Γ).strictPeriods :=
  S3CuspLimit.natCast_mem_strictPeriods_translate Γ σ

private theorem realizeOf_smul_eventuallyEq_div {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (x : LaurentSeries ℂ)
    (hxgh : x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (hne : ∀ᶠ τ in atImInfty, (h : ℍ → ℂ) (σ • τ) ≠ 0) :
    (fun τ : ℍ => realizeOf Γ x (σ • τ)) =ᶠ[atImInfty]
      fun τ : ℍ => (g : ℍ → ℂ) (σ • τ) / (h : ℍ → ℂ) (σ • τ) := by
  filter_upwards [hne] with τ hτ
  exact realizeOf_eq_div Γ hTΓ.out g h x hxgh (σ • τ) hτ

private theorem eventually_apply_smul_ne_zero {k : ℤ}
    (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) :
    ∀ᶠ τ in atImInfty, (h : ℍ → ℂ) (σ • τ) ≠ 0 := by
  have key := S3CuspLimit.eventually_ne_zero_atImInfty (S3CuspLimit.slash_periodic h σ)
    (S3CuspLimit.slash_mdiff h σ) (S3CuspLimit.slash_bddAtImInfty h σ)
    (S3CuspLimit.qExpansion_slash_ne_zero h σ hh)
  filter_upwards [key] with τ hτ hc
  apply hτ
  rw [SL_slash_apply, hc, zero_mul]

theorem jqModC_complex_eq_coeffEmb : ModularCurve.jqModC ℂ = ModularCurve.coeffEmb ℂ ModularCurve.jq := by
  rw [← ModularCurve.map_jqModC (algebraMap ℚ ℂ), ModularCurve.jqModC_rat]
  ext n
  rw [HahnSeries.map_coeff, ModularCurve.coeffEmb_coeff]

end S3glue
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3c"

end Ws49.CUSPLIM
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3c P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49 P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM"
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3c P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49"

open ModularCurve Ws49.CUSPLIM in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (x : ModularCurve.laurentBaseChange ℂ F₀) (hx : x ≠ 0)
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hord : ∀ v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀),
      y ∉ v.toValuationSubring → v.ord x = 0)
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ))
        atImInfty (𝓝 L) := by
  subst hF
  haveI hTΓ : Fact (ModularGroup.T ∈ Γ) := ⟨hT⟩

  obtain ⟨k, g, h, hh, hxgh⟩ :=
    exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC Γ hT
      (x : LaurentSeries ℂ) x.2

  have hne := S3glue.eventually_apply_smul_ne_zero Γ σ h hh
  have heq := S3glue.realizeOf_smul_eventuallyEq_div Γ σ g h (x : LaurentSeries ℂ) hxgh hne

  have hg : g ≠ 0 := by
    intro hc
    apply hx
    apply Subtype.ext
    have h1 : (x : LaurentSeries ℂ) *
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [hxgh, hc, ModularForm.coe_zero, qExpansion_zero, map_zero]
    have hhL : ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 :=
      S3c.Lq_one_ne_zero (S3c.one_mem_strictPeriods_Gamma0 Γ) hh
    exact (mul_eq_zero.mp h1).resolve_right hhL

  have hNσ := S3glue.hNσ Γ σ
  set Φ := S3c.Φσ Γ (S3CuspLimit.wd Γ) σ (S3glue.presN Γ) hNσ with hΦdef
  have hyeq : (y : LaurentSeries ℂ) = coeffEmb ℂ jq := hy.trans (S3glue.jqModC_complex_eq_coeffEmb)
  have hjmem : coeffEmb ℂ jq ∈ S3c.CF Γ := hyeq ▸ y.2
  have hyel : y = ⟨coeffEmb ℂ jq, hjmem⟩ := Subtype.ext hyeq
  have hordj : (Φ ⟨coeffEmb ℂ jq, hjmem⟩).order = -(S3CuspLimit.wd Γ : ℤ) :=
    S3c.order_Φσ_jq Γ (S3CuspLimit.wd Γ) σ (S3glue.presN Γ) hNσ S3glue.presJ1
      (S3glue.reindexN (S3CuspLimit.wd Γ)) hjmem
  have htj : (Φ ⟨coeffEmb ℂ jq, hjmem⟩).order < 0 := by
    rw [hordj]; simp [Nat.pos_of_ne_zero (NeZero.ne (S3CuspLimit.wd Γ))]
  set vσ := S3c.orderPlace Φ (S3c.Φσ_algebraMap Γ (S3CuspLimit.wd Γ) σ (S3glue.presN Γ) hNσ) htj
  have hjnmem : (⟨coeffEmb ℂ jq, hjmem⟩ : S3c.CF Γ) ∉ vσ.toValuationSubring :=
    S3c.not_mem_orderPlace Φ (S3c.Φσ_algebraMap Γ (S3CuspLimit.wd Γ) σ (S3glue.presN Γ) hNσ) htj
  have hordx : vσ.ord x = 0 := hord vσ (hyel ▸ hjnmem)
  have hΦx : (Φ x).order = 0 :=
    (S3c.ord_eq_zero_iff Φ (S3c.Φσ_algebraMap Γ (S3CuspLimit.wd Γ) σ (S3glue.presN Γ) hNσ) htj hx).mp
      hordx

  have hxL : (x : LaurentSeries ℂ) * S3c.Lq 1 ⇑h = S3c.Lq 1 ⇑g := hxgh
  have hΦval : Φ x = S3c.Lq (S3CuspLimit.wd Γ) (⇑g ∣[k] σ) / S3c.Lq (S3CuspLimit.wd Γ) (⇑h ∣[k] σ) :=
    S3c.Φσ_eq Γ (S3CuspLimit.wd Γ) σ (S3glue.presN Γ) hNσ hh hxL
  have hgqne : qExpansion (S3CuspLimit.wd Γ : ℝ) (⇑g ∣[k] σ) ≠ 0 :=
    S3CuspLimit.qExpansion_slash_ne_zero g σ hg
  have hhqne : qExpansion (S3CuspLimit.wd Γ : ℝ) (⇑h ∣[k] σ) ≠ 0 :=
    S3CuspLimit.qExpansion_slash_ne_zero h σ hh
  have horder : (qExpansion (S3CuspLimit.wd Γ : ℝ) (⇑g ∣[k] σ)).order =
      (qExpansion (S3CuspLimit.wd Γ : ℝ) (⇑h ∣[k] σ)).order := by
    apply S3c.PowerSeries_order_eq_of_div_order_eq_zero hgqne hhqne
    rw [← S3c.Lq_def, ← S3c.Lq_def, ← hΦval]
    exact hΦx

  obtain ⟨L, hL, htend⟩ :=
    S3CuspLimit.tendsto_div_atImInfty_of_triple
      (S3CuspLimit.slash_periodic g σ) (S3CuspLimit.slash_mdiff g σ)
      (S3CuspLimit.slash_bddAtImInfty g σ)
      (S3CuspLimit.slash_periodic h σ) (S3CuspLimit.slash_mdiff h σ)
      (S3CuspLimit.slash_bddAtImInfty h σ)
      hgqne hhqne horder

  refine ⟨L, hL, ?_⟩
  refine Tendsto.congr' heq.symm ?_
  refine htend.congr fun τ => ?_
  exact (S3CuspLimit.div_comp_smul_eq_div_slash k (⇑g) (⇑h) σ τ).symm

end
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM.S3c P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49 P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.Ws49.CUSPLIM"

end S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
end P2MW
export P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero (solution)
