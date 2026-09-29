-- Prove2me | solution 1 for ModularCurve.exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9df7f04e-bfd6-5262-9ad6-4bc63c106f8e

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "UpperHalfPlane ModularForm Filter Function Complex Function.Complex Matrix.SpecialLinearGroup OnePoint"
open scoped MatrixGroups Topology CongruenceSubgroup Pointwise Manifold

noncomputable section

namespace Ws49
namespace LIMTR

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
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR.S3CuspLimit"

namespace Glue

open ModularCurve

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (σ : SL(2, ℤ))

theorem eventually_apply_smul_ne_zero {k : ℤ}
    (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) :
    ∀ᶠ τ in atImInfty, (h : ℍ → ℂ) (σ • τ) ≠ 0 := by
  have key := S3CuspLimit.eventually_ne_zero_atImInfty (S3CuspLimit.slash_periodic h σ)
    (S3CuspLimit.slash_mdiff h σ) (S3CuspLimit.slash_bddAtImInfty h σ)
    (S3CuspLimit.qExpansion_slash_ne_zero h σ hh)
  filter_upwards [key] with τ hτ hc
  apply hτ
  rw [SL_slash_apply, hc, zero_mul]

theorem continuous_sl_smul : Continuous fun τ : ℍ => σ • τ := by
  show Continuous fun τ : ℍ => ((σ : GL (Fin 2) ℝ) • τ)
  exact continuous_const_smul _

theorem punctured_nhds_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  rw [← not_not (a := (𝓝[≠] τ).NeBot), Filter.not_neBot, ← isOpen_singleton_iff_punctured_nhds]
  intro hopen
  have h1 : IsOpen ({(τ : ℂ)} : Set ℂ) := by
    have := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hopen
    simpa using this
  rw [isOpen_singleton_iff_punctured_nhds] at h1
  exact (inferInstance : (𝓝[≠] (τ : ℂ)).NeBot).ne h1

theorem tendsto_coe_smul_punctured (τ : ℍ) :
    Tendsto (fun w : ℍ => ((σ • w : ℍ) : ℂ)) (𝓝[≠] τ) (𝓝[≠] ((σ • τ : ℍ) : ℂ)) := by
  have hc : Continuous fun w : ℍ => ((σ • w : ℍ) : ℂ) :=
    UpperHalfPlane.continuous_coe.comp (continuous_sl_smul σ)
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  intro hw'
  apply hw
  have h1 : σ • w = σ • τ := UpperHalfPlane.ext (Set.mem_singleton_iff.mp hw')
  simpa using congrArg (fun z => σ⁻¹ • z) h1

end Glue
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR.S3CuspLimit"

end Ws49.LIMTR
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49 P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR"
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR.S3CuspLimit P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49 P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.Ws49.LIMTR"

open Ws49.LIMTR in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (F : UpperHalfPlane → ℂ)
    (hFx : ∀ τ : UpperHalfPlane, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ x (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) atImInfty (𝓝 L))
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => (g : UpperHalfPlane → ℂ) (σ • τ) / (h : UpperHalfPlane → ℂ) (σ • τ))
        atImInfty (𝓝 L) := by
  obtain ⟨L, hL, hF⟩ := hcusp σ
  refine ⟨L, hL, ?_⟩
  set G : UpperHalfPlane → ℂ := fun τ => (g : ℍ → ℂ) (σ • τ) / (h : ℍ → ℂ) (σ • τ) with hGdef

  have hne : ∀ᶠ τ in atImInfty, (h : ℍ → ℂ) (σ • τ) ≠ 0 := Glue.eventually_apply_smul_ne_zero Γ σ h hh

  have hloc : ∀ τ : ℍ, ∀ᶠ w in 𝓝[≠] τ, F (σ • w) = ModularCurve.realizeOf Γ x (σ • w) := by
    intro τ
    have h1 := (Glue.tendsto_coe_smul_punctured σ τ).eventually (hFx (σ • τ))
    filter_upwards [h1] with w hw
    simpa only [ofComplex_apply] using hw

  rw [Metric.tendsto_nhds]
  intro ε hε
  have hFε : ∀ᶠ τ in atImInfty, dist (F (σ • τ)) L < ε / 2 := Metric.tendsto_nhds.mp hF (ε / 2) (half_pos hε)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (hFε.and hne)
  have hmem : {τ : ℍ | dist (G τ) L < ε} ∈ atImInfty := by
    rw [atImInfty_mem]
    refine ⟨A + 1, fun τ hτ => ?_⟩
    have hτA : A < τ.im := by linarith

    have hU : {w : ℍ | A < w.im} ∈ 𝓝 τ :=
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hτA
    have hhτ : (h : ℍ → ℂ) (σ • τ) ≠ 0 := (hA τ hτA.le).2

    have hcg : Continuous fun w : ℍ => (g : ℍ → ℂ) (σ • w) :=
      (ModularFormClass.holo g).continuous.comp (Glue.continuous_sl_smul σ)
    have hch : Continuous fun w : ℍ => (h : ℍ → ℂ) (σ • w) :=
      (ModularFormClass.holo h).continuous.comp (Glue.continuous_sl_smul σ)
    have hGcont : ContinuousAt G τ := (hcg.continuousAt).div (hch.continuousAt) hhτ

    have hFG : ∀ᶠ w in 𝓝[≠] τ, F (σ • w) = G w := by
      filter_upwards [hloc τ, mem_nhdsWithin_of_mem_nhds hU] with w h1 h2
      rw [h1, hGdef]
      exact ModularCurve.realizeOf_eq_div Γ hT g h x hx (σ • w) (hA w (le_of_lt h2)).2
    have ht : Tendsto (fun w : ℍ => F (σ • w)) (𝓝[≠] τ) (𝓝 (G τ)) :=
      (hGcont.tendsto.mono_left nhdsWithin_le_nhds).congr' (hFG.mono fun w hw => hw.symm)
    have hev : ∀ᶠ w in 𝓝[≠] τ, dist (F (σ • w)) L ≤ ε / 2 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with w hw
      exact (hA w (le_of_lt hw)).1.le
    haveI := Glue.punctured_nhds_neBot τ
    have hle : dist (G τ) L ≤ ε / 2 := le_of_tendsto (ht.dist tendsto_const_nhds) hev
    show dist (G τ) L < ε
    linarith
  exact hmem

end S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
end P2MW
export P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto (solution)
