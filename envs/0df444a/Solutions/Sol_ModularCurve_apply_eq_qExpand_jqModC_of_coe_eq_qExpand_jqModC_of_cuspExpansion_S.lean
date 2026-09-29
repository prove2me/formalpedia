-- Prove2me | solution 1 for ModularCurve.apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3dc866ba-e659-58af-8bed-45b2eb6734ec

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Definitions.Def_ModularCurve_XH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open ConjAct Pointwise

namespace NC2
namespace Forms

open ModularCurve UpperHalfPlane

noncomputable def spread (d : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if d ∣ n then PowerSeries.coeff (n / d) p else 0

@[scoped simp] theorem coeff_spread (d : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (spread d p) = if d ∣ n then PowerSeries.coeff (n / d) p else 0 := by
  rw [spread, PowerSeries.coeff_mk]

theorem intSeriesC_spread (K : Type*) [Field K] (d : ℕ) [NeZero d] (p : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (NC2.Forms.spread d p) = ModularCurve.qExpand K d (ModularCurve.intSeriesC K p) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  ext n
  simp only [intSeriesC]
  by_cases hdn : (d : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hneg : (d : ℤ) * m < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hd) hm
      rw [ofPowerSeries_coeff_of_neg _ hneg, ofPowerSeries_coeff_of_neg _ hm]
    · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [show (d : ℤ) * (m' : ℤ) = ((d * m' : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_map, coeff_spread, if_pos (dvd_mul_right d m'), Nat.mul_div_cancel_left _ hd]
  · rw [qExpand_coeff_of_not_dvd d _ hdn]
    rcases lt_or_ge n 0 with hn | hn
    · rw [ofPowerSeries_coeff_of_neg _ hn]
    · obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, coeff_spread, if_neg, map_zero]
      exact fun h => hdn (Int.natCast_dvd_natCast.mpr h)

section J

variable (K : Type*) [Field K]

theorem intSeriesC_X_mul_dedekindEtaUnit_ne_zero :
    ModularCurve.intSeriesC K (PowerSeries.X * ModularCurve.dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem jqModC_mul_X_mul_dedekindEtaUnit :
    ModularCurve.jqModC K * ModularCurve.intSeriesC K (PowerSeries.X * ModularCurve.dedekindEtaUnit) =
      ModularCurve.intSeriesC K (ModularCurve.eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_div :
    ModularCurve.jqModC K = ModularCurve.intSeriesC K (ModularCurve.eisenstein4 ^ 3)
      / ModularCurve.intSeriesC K (PowerSeries.X * ModularCurve.dedekindEtaUnit) := by
  rw [eq_div_iff (intSeriesC_X_mul_dedekindEtaUnit_ne_zero K), jqModC_mul_X_mul_dedekindEtaUnit]

theorem intSeriesC_spread_X_mul_dedekindEtaUnit_ne_zero (d : ℕ) [NeZero d] :
    ModularCurve.intSeriesC K (NC2.Forms.spread d (PowerSeries.X * ModularCurve.dedekindEtaUnit)) ≠ 0 := by
  rw [intSeriesC_spread]
  exact (map_ne_zero_iff _ (qExpand_injective d)).mpr (intSeriesC_X_mul_dedekindEtaUnit_ne_zero K)

end J

theorem gammaH_le_conj_heckeDiagMatrix (M d : ℕ) [NeZero d] (hdM : d ∣ M) (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (ModularForm.heckeDiagMatrix d)⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  intro x hx
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, toConjAct_smul]
  have hδ0 : δ ∈ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hδ
  have hκ : ((M : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hδ0)
  obtain ⟨c', hc'⟩ := (Int.natCast_dvd_natCast.mpr hdM).trans hκ
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := δ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  let δ'' : SL(2, ℤ) := ⟨!![δ 0 0, d * δ 0 1; c', δ 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hc'] at hdet; linear_combination hdet⟩
  have hconj : ModularForm.heckeDiagMatrix d * (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ)
      = (δ'' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix d := by
    have hcR : ((δ 1 0 : ℤ) : ℝ) = d * c' := by exact_mod_cast hc'
    apply Units.ext
    ext i j
    simp only [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [δ'', Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hd0,
        Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, hcR] <;> ring
  rw [show ModularForm.heckeDiagMatrix d * (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) *
      (ModularForm.heckeDiagMatrix d)⁻¹ = (δ'' : GL (Fin 2) ℝ) from by rw [mul_inv_eq_iff_eq_mul]; exact hconj]
  exact ⟨δ'', rfl⟩

section Dilate

variable (M d : ℕ) [NeZero M] [NeZero d] (hdM : d ∣ M)

noncomputable def dilate {k : ℤ} (F : ModularForm 𝒮ℒ k) : ModularForm (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) k :=
  ((d : ℂ) ^ (k - 1))⁻¹ • ModularCurve.restrictForm (gammaH_le_conj_heckeDiagMatrix M d hdM ⊥)
    (ModularForm.translate F (ModularForm.heckeDiagMatrix d))

theorem coe_dilate {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    (⇑(dilate M d hdM F) : ℍ → ℂ) = fun τ : ℍ => F (ModularForm.heckeDiagMatrix d • τ) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  ext τ
  simp only [dilate, ModularForm.IsGLPos.coe_smul, ModularCurve.coe_restrictForm, ModularForm.coe_translate, Pi.smul_apply,
    smul_eq_mul, ModularForm.slash_heckeDiagMatrix_apply _ hd0]
  rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hdC), one_mul]

theorem isIntegralQExp_dilate {k : ℤ} (F : ModularForm 𝒮ℒ k) {P : PowerSeries ℤ}
    (hP : ModularCurve.IsIntegralQExp F P) :
    ModularCurve.IsIntegralQExp (dilate M d hdM F) (spread d P) := by
  show (spread d P).map (Int.castRingHom ℂ) = qExpansion 1 (⇑(dilate M d hdM F) : ℍ → ℂ)
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  change intSeriesC ℂ (spread d P) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(dilate M d hdM F) : ℍ → ℂ))
  rw [intSeriesC_spread, coe_dilate, ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne d F, intSeriesC, hP]

end Dilate

open ModularForm EisensteinSeries in
theorem isIntegralQExp_E4 : ModularCurve.IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

noncomputable def e4cube : ModularForm 𝒮ℒ 12 := (ModularForm.E₄.pow 3).mcast (by norm_num)

theorem coe_e4cube : (⇑e4cube : ℍ → ℂ) = fun τ => (ModularForm.E₄ τ) ^ 3 := by
  have h : (⇑e4cube : ℍ → ℂ) = ⇑(ModularForm.E₄.pow 3) := rfl
  rw [h, ModularForm.coe_pow]
  rfl

open ModularForm in
theorem isIntegralQExp_e4cube : ModularCurve.IsIntegralQExp (⇑e4cube : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, e4cube, map_pow, isIntegralQExp_E4, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

noncomputable def delta : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem coe_delta : (⇑delta : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_delta :
    ModularCurve.IsIntegralQExp (⇑delta : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_delta]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem exists_forms (M d : ℕ) [NeZero M] [NeZero d] (hdM : d ∣ M) :
    ∃ (f h : ModularForm (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) 12),
      ((⇑f : UpperHalfPlane → ℂ) = fun τ => (ModularForm.E₄ (ModularForm.heckeDiagMatrix d • τ)) ^ 3) ∧
      ((⇑h : UpperHalfPlane → ℂ) = fun τ => ModularForm.discriminant (ModularForm.heckeDiagMatrix d • τ)) ∧
      ModularCurve.IsIntegralQExp f (NC2.Forms.spread d (ModularCurve.eisenstein4 ^ 3)) ∧
      ModularCurve.IsIntegralQExp h (NC2.Forms.spread d (PowerSeries.X * ModularCurve.dedekindEtaUnit)) := by
  refine ⟨dilate M d hdM e4cube, dilate M d hdM delta, ?_, ?_,
    isIntegralQExp_dilate M d hdM e4cube isIntegralQExp_e4cube,
    isIntegralQExp_dilate M d hdM delta isIntegralQExp_delta⟩
  · rw [coe_dilate, coe_e4cube]
  · rw [coe_dilate, coe_delta]

end NC2.Forms
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2"

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm Function
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace NC2
namespace S

theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

section WidthMul
variable (N : ℕ) [NeZero N]

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem qParam_eq_pow_mul (h : ℕ) [NeZero h] (τ : ℍ) :
    Periodic.qParam h τ = Periodic.qParam ((N * h : ℕ) : ℝ) τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hh : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
  push_cast
  field_simp

theorem qExpansion_coeff_width_mul (h : ℕ) [NeZero h] {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) h) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion ((N * h : ℕ) : ℝ) g).coeff n = if (N : ℕ) ∣ n then (qExpansion h g).coeff (n / N) else 0 := by
  classical
  haveI : NeZero (N * h) := NeZero.mul
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (NeZero.pos h)
  have hperN : Periodic (g ∘ ofComplex) ((N * h : ℕ) : ℝ) := by
    have := hper.nat_mul N
    push_cast at this ⊢
    exact this
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion h g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam ((N * h : ℕ) : ℝ) τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion hhpos (by simpa using hper) hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam ((N * h : ℕ) : ℝ) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_eq_pow_mul N h τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos (N * h)) (analyticAt_cuspFunction_zero (natCast_pos (N * h))
    (by simpa using hperN) hg hbd) hsum n]

end WidthMul
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"

theorem heckeDiagMatrix_mul_S (d : ℕ) (hd : d ≠ 0) :
    heckeDiagMatrix d * ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeMatrix d 0 := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, val_heckeDiagMatrix hd, val_heckeMatrix hd, ModularGroup.S,
      Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map]

theorem slash_S_comp_heckeDiagMatrix (k : ℤ) (F : ℍ → ℂ) (hS : F ∣[k] ModularGroup.S = F)
    (d : ℕ) (hd : d ≠ 0) :
    ((fun τ : ℍ => F (heckeDiagMatrix d • τ)) ∣[k] ModularGroup.S) =
      fun τ : ℍ => ((d : ℂ) ^ k)⁻¹ * F (heckeMatrix d 0 • τ) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hpk : (d : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hdC
  set cst : ℂ := ((d : ℂ) ^ (k - 1))⁻¹ with hcst
  have dil : (fun τ : ℍ => F (heckeDiagMatrix d • τ)) = cst • (F ∣[k] heckeDiagMatrix d) := by
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, slash_heckeDiagMatrix_apply k hd, hcst, ← mul_assoc, inv_mul_cancel₀ hpk, one_mul]
  rw [dil, ModularForm.SL_smul_slash, ModularForm.SL_slash, ← SlashAction.slash_mul, heckeDiagMatrix_mul_S d hd,
    SlashAction.slash_mul, ← ModularForm.SL_slash, hS]
  funext τ
  rw [Pi.smul_apply, smul_eq_mul, slash_heckeMatrix_apply k hd 0 F τ, hcst, ← mul_assoc]
  congr 1
  rw [← mul_inv, ← zpow_add_one₀ hdC, sub_add_cancel]

section GFacts

variable (F : ℍ → ℂ) (d : ℕ) [NeZero d]

theorem mdifferentiable_comp_heckeMatrix (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (heckeMatrix d 0 • τ)) := by
  have hd : d ≠ 0 := NeZero.ne d
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have heq : (fun τ : ℍ => F (heckeMatrix d 0 • τ)) = (d : ℂ) • (F ∣[(0 : ℤ)] heckeMatrix d 0) := by
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, slash_heckeMatrix_apply (0 : ℤ) hd 0 F τ, ← mul_assoc, mul_inv_cancel₀ hdC, one_mul]
  rw [heq]
  exact (hhol.slash (0 : ℤ) _).const_smul _

theorem coe_heckeMatrix_zero_smul (τ : ℍ) : ((heckeMatrix d 0 • τ : ℍ) : ℂ) = (τ : ℂ) / d := by
  rw [coe_heckeMatrix_smul (NeZero.ne d) 0 τ, Nat.cast_zero, add_zero]

theorem im_heckeMatrix_zero_smul (τ : ℍ) : (heckeMatrix d 0 • τ : ℍ).im = τ.im / d := by
  have h := congrArg Complex.im (coe_heckeMatrix_zero_smul d τ)
  rw [UpperHalfPlane.coe_im] at h
  rw [h, Complex.div_natCast_im, UpperHalfPlane.coe_im]

theorem isBoundedAtImInfty_comp_heckeMatrix (hbdd : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (fun τ : ℍ => F (heckeMatrix d 0 • τ)) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨C, A, hA⟩ := hbdd
  refine ⟨C, A * d, fun τ hτ => hA _ ?_⟩
  rw [im_heckeMatrix_zero_smul]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  rwa [le_div_iff₀ hdpos]

theorem periodic_comp_heckeMatrix (hper : Periodic (F ∘ ofComplex) 1) :
    Periodic ((fun τ : ℍ => F (heckeMatrix d 0 • τ)) ∘ ofComplex) (d : ℂ) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  intro w
  by_cases hw : 0 < im w
  · have hw' : 0 < im (w + d) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]

    have hz : 0 < im ((w : ℂ) / d) := by rw [Complex.div_natCast_im]; exact div_pos hw hdpos
    have e1 : (heckeMatrix d 0 • (⟨w + d, hw'⟩ : ℍ) : ℍ) = ofComplex ((w : ℂ) / d + 1) := by
      have hz1 : 0 < im ((w : ℂ) / d + 1) := by simpa using hz
      rw [ofComplex_apply_of_im_pos hz1]
      apply UpperHalfPlane.ext
      rw [coe_heckeMatrix_zero_smul]
      show ((w + d : ℂ)) / d = (w : ℂ) / d + 1
      field_simp
    have e2 : (heckeMatrix d 0 • (⟨w, hw⟩ : ℍ) : ℍ) = ofComplex ((w : ℂ) / d) := by
      rw [ofComplex_apply_of_im_pos hz]
      apply UpperHalfPlane.ext
      rw [coe_heckeMatrix_zero_smul]
    rw [e1, e2]
    exact hper _
  · push Not at hw
    have hw' : im (w + d) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

end GFacts
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"

theorem qExpansion_coeff_slash_S_comp_heckeDiagMatrix
    (k : ℤ) (F : UpperHalfPlane → ℂ)
    (hS : F ∣[k] ModularGroup.S = F)
    (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F)
    (d N : ℕ) [NeZero d] [NeZero N] (m : ℕ) :
    (UpperHalfPlane.qExpansion ((N * d : ℕ) : ℝ)
        ((fun τ : UpperHalfPlane => F (ModularForm.heckeDiagMatrix d • τ)) ∣[k] ModularGroup.S)).coeff m =
      if N ∣ m then ((d : ℂ) ^ k)⁻¹ * (UpperHalfPlane.qExpansion 1 F).coeff (m / N) else 0 := by
  classical
  have hd : d ≠ 0 := NeZero.ne d
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)

  set G : ℍ → ℂ := fun τ => F (heckeMatrix d 0 • τ) with hG
  set g : ℍ → ℂ := fun τ => ((d : ℂ) ^ k)⁻¹ * G τ with hg
  have key : ((fun τ : ℍ => F (heckeDiagMatrix d • τ)) ∣[k] ModularGroup.S) = g :=
    slash_S_comp_heckeDiagMatrix k F hS d hd
  rw [key]

  have hGhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := mdifferentiable_comp_heckeMatrix F d hhol
  have hGbdd : IsBoundedAtImInfty G := isBoundedAtImInfty_comp_heckeMatrix F d hbdd
  have hGper : Periodic (G ∘ ofComplex) (d : ℂ) := periodic_comp_heckeMatrix F d hper
  have hgeq : g = ((d : ℂ) ^ k)⁻¹ • G := by funext τ; rfl
  have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by rw [hgeq]; exact hGhol.const_smul _
  have hgbdd : IsBoundedAtImInfty g := by rw [hgeq]; exact hGbdd.const_smul_left _
  have hgper : Periodic (g ∘ ofComplex) (d : ℂ) := by
    intro w; have := hGper w; simp only [comp_apply] at this ⊢; simp only [hg, this]

  have hcoeff : ∀ n : ℕ, (qExpansion (d : ℝ) g).coeff n = ((d : ℂ) ^ k)⁻¹ * (qExpansion 1 F).coeff n := by
    intro n
    have hsum : ∀ τ : ℍ, HasSum (fun m => (((d : ℂ) ^ k)⁻¹ * (qExpansion 1 F).coeff m) • Periodic.qParam (d : ℝ) τ ^ m) (g τ) := by
      intro τ
      have h1 := hasSum_qExpansion one_pos hper hhol hbdd (heckeMatrix d 0 • τ)
      have hq : Periodic.qParam 1 ((heckeMatrix d 0 • τ : ℍ) : ℂ) = Periodic.qParam (d : ℝ) τ := by
        rw [coe_heckeMatrix_zero_smul]
        simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
        ring_nf
      rw [hq] at h1
      have h2 := h1.mul_left (((d : ℂ) ^ k)⁻¹)
      simp only [hg]
      convert h2 using 1
      all_goals try rfl
      funext m
      simp only [smul_eq_mul]
      ring
    exact (qExpansion_coeff_unique' hdpos (analyticAt_cuspFunction_zero hdpos (by simpa using hgper) hghol hgbdd) hsum n).symm

  rw [qExpansion_coeff_width_mul N d hghol (by simpa using hgper) hgbdd m]
  split_ifs with h
  · rw [hcoeff]
  · rfl

end NC2.S
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"

namespace NC2
namespace Inst

open ModularCurve EisensteinSeries

theorem S_mem_SL : ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨ModularGroup.S, rfl⟩

theorem one_mem_strictPeriods_SL' : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

def e4cube : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

theorem coe_e4cube : (⇑e4cube : ℍ → ℂ) = fun τ : ℍ => E₄ τ ^ 3 := by
  show ⇑((E₄.pow 3).mcast _) = _
  rw [ModularForm.coe_mcast, ModularForm.coe_pow]
  funext τ
  simp [Pi.pow_apply]

theorem qExpansion_e4cube : (eisenstein4 ^ 3).map (Int.castRingHom ℂ) = qExpansion 1 (fun τ : ℍ => E₄ τ ^ 3) := by
  rw [← coe_e4cube, e4cube, map_pow, isIntegralQExp_E4, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL']

theorem qExpansion_disc : (PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℂ) = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem facts_of_levelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S = ⇑f) ∧ Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) 1 ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f : ℍ → ℂ) ∧ IsBoundedAtImInfty (⇑f : ℍ → ℂ) := by
  refine ⟨?_, ?_, f.holo', ?_⟩
  · rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ S_mem_SL
  · exact SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL'
  · simpa using ModularFormClass.bdd_at_infty_slash f (1 : SL(2, ℤ))

theorem smul_qExpansion_eq_of_S_lemma (N d : ℕ) [NeZero N] [NeZero d] (F : ℍ → ℂ) (p : PowerSeries ℤ)
    (hS : F ∣[(12 : ℤ)] ModularGroup.S = F) (hper : Periodic (F ∘ ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : IsBoundedAtImInfty F)
    (hq : p.map (Int.castRingHom ℂ) = qExpansion 1 F) :
    ((N * d : ℕ) : ℂ) ^ (12 : ℕ) • qExpansion ((N * d : ℕ) : ℝ) ((fun τ : ℍ => F (heckeDiagMatrix d • τ)) ∣[(12 : ℤ)] ModularGroup.S)
      = (PowerSeries.C ((N : ℤ) ^ 12) * NC2.Forms.spread N p).map (Int.castRingHom ℂ) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext m
  rw [map_smul, NC2.S.qExpansion_coeff_slash_S_comp_heckeDiagMatrix (12 : ℤ) F hS hper hhol hbdd d N m, ← hq,
    PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_C_mul, NC2.Forms.spread, PowerSeries.coeff_mk]
  split_ifs with h
  · simp only [smul_eq_mul, map_mul, map_pow, eq_intCast, Int.cast_natCast, zpow_ofNat]
    push_cast
    field_simp
  · simp

theorem smul_qExpansion_slash_S_E4cube (N d : ℕ) [NeZero N] [NeZero d] :
    ((N * d : ℕ) : ℂ) ^ (12 : ℕ) • UpperHalfPlane.qExpansion ((N * d : ℕ) : ℝ)
        ((fun τ : UpperHalfPlane => (ModularForm.E₄ (ModularForm.heckeDiagMatrix d • τ)) ^ 3) ∣[(12 : ℤ)] ModularGroup.S)
      = (PowerSeries.C ((N : ℤ) ^ 12) * NC2.Forms.spread N (ModularCurve.eisenstein4 ^ 3)).map (Int.castRingHom ℂ) := by
  obtain ⟨hS, hper, hhol, hbdd⟩ := facts_of_levelOne e4cube
  rw [coe_e4cube] at hS hper hhol hbdd
  exact smul_qExpansion_eq_of_S_lemma N d (fun τ : ℍ => E₄ τ ^ 3) (eisenstein4 ^ 3) hS hper hhol hbdd qExpansion_e4cube

theorem smul_qExpansion_slash_S_discriminant (N d : ℕ) [NeZero N] [NeZero d] :
    ((N * d : ℕ) : ℂ) ^ (12 : ℕ) • UpperHalfPlane.qExpansion ((N * d : ℕ) : ℝ)
        ((fun τ : UpperHalfPlane => ModularForm.discriminant (ModularForm.heckeDiagMatrix d • τ)) ∣[(12 : ℤ)] ModularGroup.S)
      = (PowerSeries.C ((N : ℤ) ^ 12) * NC2.Forms.spread N (PowerSeries.X * ModularCurve.dedekindEtaUnit)).map (Int.castRingHom ℂ) := by
  obtain ⟨hS, hper, hhol, hbdd⟩ := facts_of_levelOne (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hcoe : (⇑(CuspForm.discriminant : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl
  rw [hcoe] at hS hper hhol hbdd
  exact smul_qExpansion_eq_of_S_lemma N d ModularForm.discriminant _ hS hper hhol hbdd qExpansion_disc

theorem exists_lift (p : PowerSeries ℤ) :
    ∃ F : PowerSeries (integralClosure ℤ ℂ),
      F.map (algebraMap (integralClosure ℤ ℂ) ℂ) = p.map (Int.castRingHom ℂ) ∧
      ∀ (K : Type*) [Field K] (φ : integralClosure ℤ ℂ →+* K), F.map φ = p.map (Int.castRingHom K) := by
  refine ⟨p.map (Int.castRingHom (integralClosure ℤ ℂ)), ?_, ?_⟩
  · have : (PowerSeries.map (algebraMap (integralClosure ℤ ℂ) ℂ)) ((PowerSeries.map (Int.castRingHom (integralClosure ℤ ℂ))) p) =
        PowerSeries.map ((algebraMap (integralClosure ℤ ℂ) ℂ).comp (Int.castRingHom (integralClosure ℤ ℂ))) p := by
      rw [PowerSeries.map_comp]; rfl
    rw [this, RingHom.ext_int ((algebraMap (integralClosure ℤ ℂ) ℂ).comp (Int.castRingHom _)) (Int.castRingHom ℂ)]
  · intro K _ φ
    have : (PowerSeries.map φ) ((PowerSeries.map (Int.castRingHom (integralClosure ℤ ℂ))) p) =
        PowerSeries.map (φ.comp (Int.castRingHom (integralClosure ℤ ℂ))) p := by
      rw [PowerSeries.map_comp]; rfl
    rw [this, RingHom.ext_int (φ.comp (Int.castRingHom _)) (Int.castRingHom K)]

end NC2.Inst
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"

end
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"

namespace NC2

theorem ofPowerSeries_reduce (K : Type*) [Field K] (N : ℕ) [NeZero N] (p : PowerSeries ℤ) :
    HahnSeries.ofPowerSeries ℤ K ((PowerSeries.C ((N : ℤ) ^ 12) * Forms.spread N p).map (Int.castRingHom K))
      = HahnSeries.C ((N : K) ^ 12) * ModularCurve.qExpand K N (ModularCurve.intSeriesC K p) := by
  rw [map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C, ← Forms.intSeriesC_spread]
  congr 1
  simp

end NC2
p2m_reactivate "P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2 P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.NC2.Forms"

theorem solution
    (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (φ : integralClosure ℤ ℂ →+* K)
    (N d : ℕ) [NeZero N] [NeZero d] (hM : N * d = M)
    (Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] LaurentSeries K)
    (hΘ :
      ∀ (k : ℤ) (f h : ModularForm (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) k)
        (pf ph : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf →
        ModularCurve.IsIntegralQExp h ph → ModularCurve.intSeriesC K ph ≠ 0 →
        ∀ (a : ℕ) (F G : PowerSeries (integralClosure ℤ ℂ)),
          F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑h : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K ph →
            HahnSeries.ofPowerSeries ℤ K (G.map φ) ≠ 0 ∧
              (Θ x : LaurentSeries K) =
                HahnSeries.ofPowerSeries ℤ K (F.map φ) / HahnSeries.ofPowerSeries ℤ K (G.map φ)) :
    ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (x : LaurentSeries K) = ModularCurve.qExpand K d (ModularCurve.jqModC K) →
        (Θ x : LaurentSeries K) = ModularCurve.qExpand K N (ModularCurve.jqModC K) := by
  classical
  intro x hx
  subst hM
  have hℓ : Fact ℓ.Prime := inferInstance

  have hNK : ((N : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K ℓ] at h0
    exact hℓM (dvd_mul_of_dvd_left h0 d)
  have hCN : (HahnSeries.C ((N : K) ^ 12) : LaurentSeries K) ≠ 0 := HahnSeries.C_ne_zero (pow_ne_zero _ hNK)

  obtain ⟨f, h, hfcoe, hhcoe, hfint, hhint⟩ := NC2.Forms.exists_forms (N * d) d (dvd_mul_left d N)
  have hx' : (x : LaurentSeries K) = ModularCurve.intSeriesC K (NC2.Forms.spread d (ModularCurve.eisenstein4 ^ 3))
      / ModularCurve.intSeriesC K (NC2.Forms.spread d (PowerSeries.X * ModularCurve.dedekindEtaUnit)) := by
    rw [hx, NC2.Forms.intSeriesC_spread, NC2.Forms.intSeriesC_spread, NC2.Forms.jqModC_eq_div, map_div₀]
  have hph0 := NC2.Forms.intSeriesC_spread_X_mul_dedekindEtaUnit_ne_zero K d

  obtain ⟨F, hF, hFφ⟩ := NC2.Inst.exists_lift (PowerSeries.C ((N : ℤ) ^ 12) * NC2.Forms.spread N (ModularCurve.eisenstein4 ^ 3))
  obtain ⟨G, hG, hGφ⟩ := NC2.Inst.exists_lift (PowerSeries.C ((N : ℤ) ^ 12) * NC2.Forms.spread N (PowerSeries.X * ModularCurve.dedekindEtaUnit))
  have hF' : F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
      ((N * d : ℕ) : ℂ) ^ (12 : ℕ) • UpperHalfPlane.qExpansion ((N * d : ℕ) : ℝ) ((⇑f : UpperHalfPlane → ℂ) ∣[(12 : ℤ)] ModularGroup.S) := by
    rw [hF, hfcoe, NC2.Inst.smul_qExpansion_slash_S_E4cube]
  have hG' : G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
      ((N * d : ℕ) : ℂ) ^ (12 : ℕ) • UpperHalfPlane.qExpansion ((N * d : ℕ) : ℝ) ((⇑h : UpperHalfPlane → ℂ) ∣[(12 : ℤ)] ModularGroup.S) := by
    rw [hG, hhcoe, NC2.Inst.smul_qExpansion_slash_S_discriminant]
  obtain ⟨-, hΘx⟩ := hΘ 12 f h _ _ hfint hhint hph0 12 F G (by exact_mod_cast hF') (by exact_mod_cast hG') x hx'
  rw [hΘx, hFφ K φ, hGφ K φ, NC2.ofPowerSeries_reduce, NC2.ofPowerSeries_reduce, mul_div_mul_left _ _ hCN,
    ← map_div₀, ← NC2.Forms.jqModC_eq_div]

end S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
end P2MW
export P2MW.S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S (solution)
