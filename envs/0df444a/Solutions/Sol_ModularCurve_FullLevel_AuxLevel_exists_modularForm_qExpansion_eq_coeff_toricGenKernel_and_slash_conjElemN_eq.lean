-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/04826609-8135-5896-b5a8-e6d5cbe08d19

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped ModularForm MatrixGroups Real

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C Gamma1_le_GammaH FullLevel.dvd_sq_mul FullLevel.levelH FullLevel.mem_levelH_iff FullLevel.conjElemN toricPoint toricPoint_fst gamma0PowDeg toricPoint_level_mul"
namespace ToricDivisionForms
p2m_open "ModularCurve"

theorem mapGL_injective :
    Function.Injective (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) → GL (Fin 2) ℝ) := by
  intro a b h
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

theorem mem_coe_iff {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ γ ∈ Γ := by
  constructor
  · rintro ⟨g, hg, hgg⟩
    rwa [← mapGL_injective hgg]
  · exact fun h => Subgroup.mem_map_of_mem _ h

theorem coe_mono {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ ≤ Γ') :
    (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ' : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono h

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

theorem T_mem_Gamma1 (n : ℕ) : ModularGroup.T ∈ Gamma1 n := by
  rw [Gamma1_mem, ModularGroup.coe_T]
  simp

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (h : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem h]
  exact AddSubgroup.mem_zmultiples _

theorem Gamma1_le_GammaH (n : ℕ) (H : Subgroup (ZMod n)ˣ) : Gamma1 n ≤ CohCarrier.GammaH n H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ Gamma0 n := Gamma1_in_Gamma0 n hA
  refine ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units n ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    change (((A : SL(2, ℤ)) 1 1 : ℤ) : ZMod n) = ((1 : (ZMod n)ˣ) : ZMod n)
    rw [Units.val_one]
    exact ((Gamma1_mem n A).mp hA).2.1
  rw [h1]
  exact one_mem H

scoped instance instFiniteIndexGammaH (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ) :
    (CohCarrier.GammaH n H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH n H)

theorem T_mem_GammaH (n : ℕ) (H : Subgroup (ZMod n)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH n H :=
  Gamma1_le_GammaH n H (T_mem_Gamma1 n)

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn f γ (hle hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono hle)

@[scoped simp]
theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) : ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

def transport {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k)
    (hcusp : ∀ c : OnePoint ℝ, IsCusp c Γ' → IsCusp c Γ)
    (hinv : ∀ γ ∈ Γ', (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' := hinv
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hcusp _ hc)

@[scoped simp]
theorem coe_transport {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k)
    (hcusp : ∀ c : OnePoint ℝ, IsCusp c Γ' → IsCusp c Γ)
    (hinv : ∀ γ ∈ Γ', (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f) : (⇑(transport f hcusp hinv) : ℍ → ℂ) = f := rfl

theorem isCusp_of_isArithmetic {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic]
    (c : OnePoint ℝ) (hc : IsCusp c Γ') : IsCusp c Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact hc

section Stretch

variable (N : ℕ)

def conjUp (γ : SL(2, ℤ)) (e : ℤ) (he : γ 1 0 = N * e) : SL(2, ℤ) :=
  ⟨!![γ 0 0, N * γ 0 1; e, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination det_eq γ + (γ 0 1) * he⟩

@[scoped simp] theorem conjUp_apply_zero_zero (γ : SL(2, ℤ)) (e : ℤ) (he : γ 1 0 = N * e) :
    conjUp N γ e he 0 0 = γ 0 0 := rfl
@[scoped simp] theorem conjUp_apply_zero_one (γ : SL(2, ℤ)) (e : ℤ) (he : γ 1 0 = N * e) :
    conjUp N γ e he 0 1 = N * γ 0 1 := rfl
@[scoped simp] theorem conjUp_apply_one_zero (γ : SL(2, ℤ)) (e : ℤ) (he : γ 1 0 = N * e) :
    conjUp N γ e he 1 0 = e := rfl
@[scoped simp] theorem conjUp_apply_one_one (γ : SL(2, ℤ)) (e : ℤ) (he : γ 1 0 = N * e) :
    conjUp N γ e he 1 1 = γ 1 1 := rfl

theorem heckeDiagMatrix_mul_mapGL (hN : N ≠ 0) (γ : SL(2, ℤ)) (e : ℤ) (he : γ 1 0 = N * e) :
    ModularForm.heckeDiagMatrix N * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjUp N γ e he) * ModularForm.heckeDiagMatrix N := by
  have he' : ((γ 1 0 : ℤ) : ℝ) = (N : ℝ) * (e : ℝ) := by exact_mod_cast he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hN, Matrix.mul_apply, Fin.sum_univ_two, conjUp, he'] <;> ring

def diagQ (hN : N ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(N : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [hN])

theorem map_diagQ (hN : N ≠ 0) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (diagQ N hN) = ModularForm.heckeDiagMatrix N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagQ, hN]

open scoped Pointwise in
theorem isArithmetic_conj_heckeDiagMatrix (hN : N ≠ 0) (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsArithmetic] :
    (ConjAct.toConjAct (ModularForm.heckeDiagMatrix N)⁻¹ • 𝒢).IsArithmetic := by
  have := Subgroup.IsArithmetic.conj 𝒢 (diagQ N hN)⁻¹
  rwa [map_inv, map_diagQ N hN] at this

variable (M : ℕ)

abbrev GammaMid : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 M

theorem T_mem_GammaMid : ModularGroup.T ∈ GammaMid N M :=
  ⟨T_mem_Gamma1 N, Gamma1_in_Gamma0 M (T_mem_Gamma1 M)⟩

theorem exists_conjUp_mem [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CohCarrier.GammaH (N ^ 2 * M) (ModularCurve.FullLevel.levelH N M)) :
    ∃ (e : ℤ) (he : γ 1 0 = N * e), conjUp N γ e he ∈ GammaMid N M := by
  obtain ⟨hγ0, hγH⟩ := CohCarrier.mem_GammaH_iff.mp hγ

  have hc : ((N ^ 2 * M : ℕ) : ℤ) ∣ γ 1 0 := by
    rw [Gamma0_mem] at hγ0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ0
  obtain ⟨e', he'⟩ := hc
  refine ⟨N * M * e', by rw [he']; push_cast; ring, ?_⟩

  have hd : ((γ 1 1 : ℤ) : ZMod N) = 1 := by
    rw [ModularCurve.FullLevel.mem_levelH_iff] at hγH
    have h := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hγH
    simp only [ZMod.unitsMap_val, CohCarrier.val_gamma0Units, Units.val_one] at h
    rw [← h]
    change ((γ 1 1 : ℤ) : ZMod N) = ZMod.cast ((((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N ^ 2 * M)))
    rw [ZMod.cast_intCast (ModularCurve.FullLevel.dvd_sq_mul N M)]

  have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod N)) (det_eq γ)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hd, mul_one, he'] at h
    have h0 : (((N ^ 2 * M : ℕ) : ℤ) : ZMod N) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast ModularCurve.FullLevel.dvd_sq_mul N M
    rw [h0, zero_mul, mul_zero, sub_zero] at h
    exact h
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨by simpa using ha, by simpa using hd, ?_⟩
    rw [conjUp_apply_one_zero]
    push_cast
    rw [mul_comm (N : ZMod N) (M : ZMod N), ZMod.natCast_self, mul_zero, zero_mul]
  · rw [Gamma0_mem, conjUp_apply_one_zero]
    push_cast
    rw [ZMod.natCast_self, mul_zero, zero_mul]

def stretch [NeZero N] [NeZero M] {k : ℤ} (R : ModularForm (GammaMid N M : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (CohCarrier.GammaH (N ^ 2 * M) (ModularCurve.FullLevel.levelH N M) :
      Subgroup (GL (Fin 2) ℝ)) k where
  toFun := (⇑R : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix N
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    obtain ⟨e, he, hmem⟩ := exists_conjUp_mem N M γ hγ
    rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_mapGL N (NeZero.ne N) γ e he,
      SlashAction.slash_mul,
      SlashInvariantForm.slash_action_eqn R _ ((mem_coe_iff _).mpr hmem)]
  holo' := (R.holo').slash k _
  bdd_at_cusps' := by
    intro c hc
    haveI := isArithmetic_conj_heckeDiagMatrix N (NeZero.ne N)
      (GammaMid N M : Subgroup (GL (Fin 2) ℝ))
    exact (ModularForm.translate R (ModularForm.heckeDiagMatrix N)).bdd_at_cusps'
      (isCusp_of_isArithmetic c hc)

@[scoped simp]
theorem coe_stretch [NeZero N] [NeZero M] {k : ℤ} (R : ModularForm (GammaMid N M : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(stretch N M R) : ℍ → ℂ) = (⇑R : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix N := rfl

theorem stretch_apply [NeZero N] [NeZero M] {k : ℤ} (R : ModularForm (GammaMid N M : Subgroup (GL (Fin 2) ℝ)) k)
    (τ : ℍ) :
    stretch N M R τ = (N : ℂ) ^ (k - 1) * R (ModularForm.heckeDiagMatrix N • τ) := by
  rw [coe_stretch, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne N)]

end Stretch

section QExp

local notation "𝕢" => Function.Periodic.qParam

theorem hasSum_qExpansion_of_mf {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 f).coeff m • 𝕢 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

theorem apply_eq_of_qExpansion_eq {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k k' : ℤ} (f : ModularForm Γ k)
    (g : ModularForm Γ' k') (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (hΓ' : (1 : ℝ) ∈ Γ'.strictPeriods)
    (h : qExpansion 1 f = qExpansion 1 g) (τ : ℍ) : f τ = g τ := by
  have hf := hasSum_qExpansion_of_mf f hΓ τ
  rw [h] at hf
  exact hf.unique (hasSum_qExpansion_of_mf g hΓ' τ)

theorem qExpansion_coe_prod {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {k : ℤ} (F : ℕ → ModularForm Γ k) (s : Finset ℕ) :
    qExpansion 1 (∏ i ∈ s, (⇑(F i) : ℍ → ℂ)) = ∏ i ∈ s, qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
    have hs : (∏ i ∈ s, (⇑(F i) : ℍ → ℂ)) =
        ⇑(ModularForm.prod (s := s) (k := fun _ => k) (s.card * k) (by simp) F) := by
      rw [ModularForm.coe_prod]
    have han : AnalyticAt ℂ (cuspFunction 1 (∏ i ∈ s, (⇑(F i) : ℍ → ℂ))) 0 := by
      rw [hs]; exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos hΓ
    exact qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero (F a) one_pos hΓ) han

theorem qParam_heckeDiagMatrix_smul (N : ℕ) (hN : N ≠ 0) (τ : ℍ) :
    𝕢 1 ((ModularForm.heckeDiagMatrix N • τ : ℍ) : ℂ) = 𝕢 1 (τ : ℂ) ^ N := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ModularForm.coe_heckeDiagMatrix_smul hN,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_expand {a : ℕ → ℂ} {q x : ℂ} (N : ℕ) (hN : N ≠ 0)
    (h : HasSum (fun m : ℕ => a m • (q ^ N) ^ m) x) :
    HasSum (fun n : ℕ => (if N ∣ n then a (n / N) else 0) • q ^ n) x := by
  have hinj : Function.Injective (fun m : ℕ => N * m) := mul_right_injective₀ hN
  rw [← hinj.hasSum_iff]
  · convert h using 1
    ext m
    simp [Function.comp, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN), pow_mul]
  · intro n hn
    have : ¬ N ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
    simp [this]

variable (N M : ℕ) [NeZero N] [NeZero M]

theorem coe_qExpansion_stretch {k : ℤ} (R : ModularForm (GammaMid N M : Subgroup (GL (Fin 2) ℝ)) k) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (stretch N M R)) =
      HahnSeries.C ((N : ℂ) ^ (k - 1)) *
        qExpand ℂ N (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 R)) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hsum : ∀ τ : ℍ, HasSum (fun n : ℕ =>
      ((N : ℂ) ^ (k - 1) * (if N ∣ n then (qExpansion 1 R).coeff (n / N) else 0)) • 𝕢 1 τ ^ n)
      (stretch N M R τ) := by
    intro τ
    have h1 := hasSum_qExpansion_of_mf R (one_mem_strictPeriods_of_T_mem (T_mem_GammaMid N M))
      (ModularForm.heckeDiagMatrix N • τ)
    rw [qParam_heckeDiagMatrix_smul N hN] at h1
    have h2 := hasSum_expand N hN h1
    have h3 := h2.mul_left ((N : ℂ) ^ (k - 1))
    rw [stretch_apply]
    convert h3 using 1 <;> try rfl
    ext n
    simp only [smul_eq_mul, mul_assoc]
  have hcoeff : ∀ n : ℕ, (qExpansion 1 (stretch N M R)).coeff n =
      (N : ℂ) ^ (k - 1) * (if N ∣ n then (qExpansion 1 R).coeff (n / N) else 0) :=
    fun n => (ModularFormClass.qExpansion_coeff_unique one_pos
      (one_mem_strictPeriods_of_T_mem (T_mem_GammaH _ _)) hsum n).symm
  ext i
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases hi : (N : ℤ) ∣ i
  · obtain ⟨j, rfl⟩ := hi
    rw [qExpand_coeff_mul]
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · rw [show ((N : ℤ) * (m : ℕ) : ℤ) = ((N * m : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, hcoeff,
        if_pos (dvd_mul_right N m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN)]
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [Nat.cast_zero, neg_zero, mul_zero]
        rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by simp, HahnSeries.ofPowerSeries_apply_coeff,
          HahnSeries.ofPowerSeries_apply_coeff, hcoeff, if_pos (dvd_zero N), Nat.zero_div]
      · have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
        have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
        rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe, if_pos (by nlinarith), if_pos (by omega),
          mul_zero]
  · rw [qExpand_coeff_of_not_dvd (hk := hi), mul_zero, PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · rw [hcoeff, if_neg, mul_zero]
      intro hdvd
      apply hi
      rw [show i = (i.natAbs : ℤ) from (Int.natAbs_of_nonneg (not_lt.mp hneg)).symm]
      exact_mod_cast hdvd

end QExp

section Toric

def X₁ (u : ℂ) : PowerSeries ℂ := PowerSeries.mk fun m =>
  if m = 0 then u / (1 - u) ^ 2
  else (∑ d ∈ m.divisors, (d : ℂ) * (u ^ d + u⁻¹ ^ d)) - 2 * ∑ d ∈ m.divisors, (d : ℂ)

theorem coeff_X₁ (u : ℂ) (m : ℕ) : (X₁ u).coeff m =
    if m = 0 then u / (1 - u) ^ 2
    else (∑ d ∈ m.divisors, (d : ℂ) * (u ^ d + u⁻¹ ^ d)) - 2 * ∑ d ∈ m.divisors, (d : ℂ) := by
  rw [X₁, PowerSeries.coeff_mk]

theorem X₁_inv (u : ℂ) : X₁ u⁻¹ = X₁ u := by
  ext m
  rw [coeff_X₁, coeff_X₁]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
    by_cases hc : u = 0
    · simp [hc]
    · field_simp
      ring
  · rw [if_neg hm, if_neg hm, inv_inv]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [add_comm]

theorem toricPoint_one_fst (u : ℂ) :
    (toricPoint ℂ 1 u).1 = HahnSeries.ofPowerSeries ℤ ℂ (X₁ u) := by
  rw [toricPoint_fst]
  congr 1
  ext m
  rw [PowerSeries.coeff_mk, coeff_X₁]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm]
    simp only [one_dvd, if_true, Nat.div_one]
    congr 1
    exact Nat.sum_div_divisors m (fun e => (e : ℂ) * (u ^ e + u⁻¹ ^ e))

theorem toricPoint_fst_eq_qExpand (N : ℕ) [NeZero N] (u : ℂ) :
    (toricPoint ℂ N u).1 = qExpand ℂ N (HahnSeries.ofPowerSeries ℤ ℂ (X₁ u)) := by
  have h := ModularCurve.toricPoint_level_mul ℂ 1 N u
  rw [Nat.mul_one] at h
  rw [h, toricPoint_one_fst]

variable {n : ℕ} (ζ : ℂ) (hζ : ζ ^ n = 1)

include hζ in
theorem pow_mod_eq (r : ℕ) : ζ ^ r = ζ ^ (r % n) := by
  conv_lhs => rw [← Nat.div_add_mod r n, pow_add, pow_mul, hζ, one_pow, one_mul]

include hζ in
theorem pow_sub_eq_inv {s : ℕ} (hs : s ≤ n) : ζ ^ (n - s) = (ζ ^ s)⁻¹ := by
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · have hn : n = 0 := by
      by_contra h
      rw [zero_pow h] at hζ
      exact zero_ne_one hζ
    subst hn
    have : s = 0 := by omega
    subst this
    simp
  · exact eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.sub_add_cancel hs, hζ])

include hζ in

theorem X₁_pow_neg_val [NeZero n] (t : ZMod n) : X₁ (ζ ^ (-t).val) = X₁ (ζ ^ t.val) := by
  rw [ZMod.neg_val]
  split_ifs with ht
  · rw [ht, ZMod.val_zero]
  · rw [pow_sub_eq_inv ζ hζ (ZMod.val_lt t).le, X₁_inv]

end Toric

section Fold

def fold (M r : ℕ) : ℕ := if r % M ≤ (M - 1) / 2 then r % M else M - r % M

variable {M : ℕ}

theorem fold_cast (hM : 0 < M) (r : ℕ) :
    ((fold M r : ℕ) : ZMod M) = (r : ZMod M) ∨ ((fold M r : ℕ) : ZMod M) = -(r : ZMod M) := by
  unfold fold
  split_ifs with h
  · left
    exact ZMod.natCast_mod r M
  · right
    rw [Nat.cast_sub (Nat.mod_lt r hM).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

variable (hMeq : M = 2 * ((M - 1) / 2) + 1)
include hMeq

theorem fold_mem {s : ℕ} (hs : Nat.Coprime M s) {k : ℕ} (hk : k ∈ Finset.Icc 1 ((M - 1) / 2)) :
    fold M (s * k) ∈ Finset.Icc 1 ((M - 1) / 2) := by
  rw [Finset.mem_Icc] at hk ⊢
  have hM : 0 < M := by omega
  have hlt : (s * k) % M < M := Nat.mod_lt _ hM
  have hne : (s * k) % M ≠ 0 := by
    intro h
    have hdvd : M ∣ s * k := Nat.dvd_of_mod_eq_zero h
    have : M ∣ k := hs.dvd_of_dvd_mul_left hdvd
    have := Nat.le_of_dvd (by omega) this
    omega
  unfold fold
  split_ifs with h
  · exact ⟨Nat.pos_of_ne_zero hne, h⟩
  · constructor <;> omega

theorem fold_inj {s : ℕ} (hs : Nat.Coprime M s) {k₁ k₂ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 ((M - 1) / 2))
    (hk₂ : k₂ ∈ Finset.Icc 1 ((M - 1) / 2)) (h : fold M (s * k₁) = fold M (s * k₂)) : k₁ = k₂ := by
  rw [Finset.mem_Icc] at hk₁ hk₂
  have hM : 0 < M := by omega
  have hlt₁ : (s * k₁) % M < M := Nat.mod_lt _ hM
  have hlt₂ : (s * k₂) % M < M := Nat.mod_lt _ hM
  have hcases : (s * k₁) % M = (s * k₂) % M ∨ (s * k₁) % M + (s * k₂) % M = M := by
    unfold fold at h
    split_ifs at h with h₁ h₂ h₂ <;> omega
  rcases hcases with heq | hsum
  · have hmod : k₁ ≡ k₂ [MOD M] := Nat.ModEq.cancel_left_of_coprime hs heq
    exact Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)
  · exfalso
    have hdvd : M ∣ s * (k₁ + k₂) := by
      rw [mul_add, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hsum, Nat.mod_self]
    have : M ∣ k₁ + k₂ := hs.dvd_of_dvd_mul_left hdvd
    have := Nat.le_of_dvd (by omega) this
    omega

theorem prod_fold_eq {α : Type*} [CommMonoid α] (g : ℕ → α) {s : ℕ} (hs : Nat.Coprime M s) :
    ∏ k ∈ Finset.Icc 1 ((M - 1) / 2), g (fold M (s * k)) = ∏ k ∈ Finset.Icc 1 ((M - 1) / 2), g k := by
  refine Finset.prod_nbij (fun k => fold M (s * k)) (fun k hk => fold_mem hMeq hs hk)
    (fun k₁ hk₁ k₂ hk₂ h => fold_inj hMeq hs hk₁ hk₂ h) ?_ (fun _ _ => rfl)
  intro b hb
  obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.Icc 1 ((M - 1) / 2))
    (t := Finset.Icc 1 ((M - 1) / 2)) (fun k _ => fold M (s * k)) (fun k hk => fold_mem hMeq hs hk)
    (fun k₁ k₂ hk₁ hk₂ h => fold_inj hMeq hs hk₁ hk₂ h) le_rfl b hb
  exact ⟨a, ha, hab.symm⟩

end Fold

section WForms

def rootOfUnity (n : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / n)

theorem rootOfUnity_pow_self (n : ℕ) [NeZero n] : rootOfUnity n ^ n = 1 := by
  rw [rootOfUnity, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast NeZero.ne n),
    Complex.exp_two_pi_mul_I]

theorem inv_pow_mul (u : ℂ) (a b : ℕ) : (u ^ a)⁻¹ ^ b = u⁻¹ ^ (a * b) := by
  rw [← inv_pow, ← pow_mul]

variable {n : ℕ} [NeZero n] (W : ZMod n → ModularForm (Gamma1 n : Subgroup (GL (Fin 2) ℝ)) 2)
  (hq : ∀ t : ZMod n, t ≠ 0 → ∀ m : ℕ,
    (qExpansion 1 (W t)).coeff m =
      if m = 0 then
        1 + 12 * Complex.exp (2 * π * Complex.I / n) ^ t.val /
          (1 - Complex.exp (2 * π * Complex.I / n) ^ t.val) ^ 2
      else
        12 * ((∑ d ∈ m.divisors, (d : ℂ) *
            (Complex.exp (2 * π * Complex.I / n) ^ (t.val * d) +
              (Complex.exp (2 * π * Complex.I / n))⁻¹ ^ (t.val * d))) -
          2 * ∑ d ∈ m.divisors, (d : ℂ)))

omit [NeZero n] in
include hq in

theorem qExpansion_W (t : ZMod n) (ht : t ≠ 0) :
    qExpansion 1 (W t) = PowerSeries.C 1 + PowerSeries.C 12 * X₁ (rootOfUnity n ^ t.val) := by
  ext m
  rw [hq t ht m, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, coeff_X₁]
  by_cases hm : m = 0
  · simp only [hm, if_true, rootOfUnity]
    ring
  · simp only [hm, if_false, zero_add, rootOfUnity]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [inv_pow_mul, ← pow_mul]

include hq in

theorem W_neg_apply (t : ZMod n) (τ : ℍ) : W (-t) τ = W t τ := by
  by_cases ht : t = 0
  · rw [ht, neg_zero]
  · have hΓ := one_mem_strictPeriods_of_T_mem (T_mem_Gamma1 n)
    apply apply_eq_of_qExpansion_eq (W (-t)) (W t) hΓ hΓ
    rw [qExpansion_W W hq (-t) (neg_ne_zero.mpr ht), qExpansion_W W hq t ht,
      X₁_pow_neg_val _ (rootOfUnity_pow_self n)]

include hq in

theorem coe_W_neg_natCast (r : ℕ) : (⇑(W (-(r : ZMod n))) : ℍ → ℂ) = ⇑(W (r : ZMod n)) := by
  ext τ
  exact W_neg_apply W hq _ τ

include hq in

theorem qExpansion_W_natCast (r : ℕ) (hr : ¬ n ∣ r) :
    qExpansion 1 (W (r : ZMod n)) = PowerSeries.C 1 + PowerSeries.C 12 * X₁ (rootOfUnity n ^ r) := by
  have hr0 : (r : ZMod n) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [qExpansion_W W hq _ hr0, ZMod.val_natCast, ← pow_mod_eq _ (rootOfUnity_pow_self n)]

end WForms

end ModularCurve.ToricDivisionForms
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve"

namespace TFormsSym

open Finset

def A (p k : ℕ) : Finset ℕ := (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)

theorem mem_A {p k a : ℕ} : a ∈ A p k ↔ (1 ≤ a ∧ a ≤ p ^ k / 2) ∧ ¬ p ∣ a := by
  simp [A, Finset.mem_filter, Finset.mem_Icc]

theorem card_filter_not_dvd_Icc (p h : ℕ) (hp : 0 < p) :
    ((Finset.Icc 1 h).filter (fun a => ¬ p ∣ a)).card = h - h / p := by
  have h1 : Finset.Icc 1 h = Finset.Ioc 0 h := by
    ext a; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1]
  have hdvd : ((Finset.Ioc 0 h).filter (fun a => p ∣ a)).card = h / p := Nat.Ioc_filter_dvd_card_eq_div h p
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 h) (fun a => p ∣ a)
  rw [hdvd, Nat.card_Ioc] at htot
  omega

theorem card_A (p k : ℕ) (hp : p.Prime) : (A p k).card = ModularCurve.gamma0PowDeg p k := by
  unfold ModularCurve.gamma0PowDeg
  split_ifs with h2
  ·
    have : A p k = {1} := by
      have hp2 : p = 2 := by
        have hk : k ≠ 0 := by rintro rfl; simp at h2
        have : p ∣ 2 := h2 ▸ dvd_pow_self p hk
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      ext a
      rw [mem_A, h2, hp2, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; omega
      · rintro rfl; exact ⟨⟨le_rfl, by norm_num⟩, by norm_num⟩
    rw [this, Finset.card_singleton]
  · rw [A, card_filter_not_dvd_Icc p _ hp.pos]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow hp hk]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rcases hp.eq_two_or_odd' with rfl | hodd
      ·
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact absurd rfl h2
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 : 2 ^ (i + 1 + 1) / 2 = 2 * 2 ^ i := by
          rw [pow_succ, Nat.mul_div_cancel _ two_pos, pow_succ, mul_comm]
        rw [e1, Nat.mul_div_cancel_left _ two_pos, pow_succ, mul_comm (2 ^ i) 2, show (2 - 1) = 1 from rfl, mul_one,
          Nat.mul_div_cancel_left _ two_pos]
        omega
      ·
        obtain ⟨s, hs⟩ : Odd (p ^ j) := hodd.pow
        obtain ⟨r, hr⟩ := hodd
        have hps : p ^ (j + 1) = 2 * (2 * r * s + r + s) + 1 := by
          rw [pow_succ, hs, hr]; ring
        have e1 : p ^ (j + 1) / 2 = 2 * r * s + r + s := by rw [hps]; omega
        have e2 : (2 * r * s + r + s) / p = s := by
          rw [show 2 * r * s + r + s = r + s * (2 * r + 1) by ring, hr, Nat.add_mul_div_right _ _ (by omega),
            Nat.div_eq_of_lt (by omega), zero_add]
        have e3 : p ^ j * (p - 1) / 2 = r * (2 * s + 1) := by
          rw [hs, hr, show 2 * r + 1 - 1 = 2 * r by omega, show (2 * s + 1) * (2 * r) = 2 * (r * (2 * s + 1)) by ring,
            Nat.mul_div_cancel_left _ two_pos]
        rw [e1, e2, e3]
        ring_nf
        omega

def foldVal {n : ℕ} (t : ZMod n) : ℕ := min t.val (n - t.val)

theorem foldVal_cast_eq {n : ℕ} [NeZero n] (t : ZMod n) :
    ((foldVal t : ℕ) : ZMod n) = t ∨ ((foldVal t : ℕ) : ZMod n) = -t := by
  unfold foldVal
  rcases le_total t.val (n - t.val) with h | h
  · left; rw [min_eq_left h, ZMod.natCast_zmod_val]
  · right; rw [min_eq_right h]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [show n - t.val = (-t).val by rw [ZMod.neg_val, if_neg ht], ZMod.natCast_zmod_val]

theorem map_A_mul_unit_eq {α : Type*} (p k : ℕ) (hp : p.Prime) [NeZero (p ^ k)]
    (s : ZMod (p ^ k)) (hs : IsUnit s) (G : ZMod (p ^ k) → α) (hG : ∀ t, G (-t) = G t) :
    Multiset.map (fun a : ℕ => G ((a : ZMod (p ^ k)) * s)) (A p k).val =
      Multiset.map (fun a : ℕ => G (a : ZMod (p ^ k))) (A p k).val := by
  classical

  set σ : ℕ → ℕ := fun a => foldVal ((a : ZMod (p ^ k)) * s) with hσ
  have hGσ : ∀ a, G ((σ a : ℕ) : ZMod (p ^ k)) = G ((a : ZMod (p ^ k)) * s) := by
    intro a
    rcases foldVal_cast_eq ((a : ZMod (p ^ k)) * s) with h | h
    · rw [hσ]; simp only []; rw [h]
    · rw [hσ]; simp only []; rw [h, hG]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : A p 0 = ∅ := by
      ext a
      constructor
      · intro ha
        obtain ⟨⟨h1, h2⟩, -⟩ := mem_A.mp ha
        rw [pow_zero] at h2
        omega
      · simp
    simp [this]
  have hn1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  haveI : Fact (1 < p ^ k) := ⟨hn1⟩
  have hunit_iff : ∀ a : ℕ, IsUnit (a : ZMod (p ^ k)) ↔ ¬ p ∣ a := by
    intro a
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hk, Nat.coprime_comm, hp.coprime_iff_not_dvd]
  have hs0 : s ≠ 0 := hs.ne_zero

  have hval_lt : ∀ t : ZMod (p ^ k), t.val < p ^ k := fun t => ZMod.val_lt t
  have hfold_mem : ∀ t : ZMod (p ^ k), IsUnit t → foldVal t ∈ A p k := by
    intro t ht
    have ht0 : t ≠ 0 := ht.ne_zero
    have hv0 : t.val ≠ 0 := (ZMod.val_ne_zero t).mpr ht0
    have hvlt := hval_lt t
    rw [mem_A]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold foldVal; exact le_min (Nat.one_le_iff_ne_zero.mpr hv0) (by omega)
    · unfold foldVal
      rcases le_total t.val (p ^ k - t.val) with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; omega
    · rw [← hunit_iff]
      rcases foldVal_cast_eq t with h | h
      · rw [h]; exact ht
      · rw [h]; exact ht.neg
  have hmemA : ∀ a ∈ A p k, σ a ∈ A p k := by
    intro a ha
    apply hfold_mem
    exact ((hunit_iff a).mpr (mem_A.mp ha).2).mul hs

  have hcast_inj : ∀ a b : ℕ, a ∈ A p k → b ∈ A p k →
      ((a : ZMod (p ^ k)) = b ∨ (a : ZMod (p ^ k)) = -b) → a = b := by
    intro a b ha hb h
    obtain ⟨⟨ha1, ha2⟩, -⟩ := mem_A.mp ha
    obtain ⟨⟨hb1, hb2⟩, -⟩ := mem_A.mp hb
    have halt : a < p ^ k := by omega
    have hblt : b < p ^ k := by omega
    rcases h with h | h
    · have := (ZMod.natCast_eq_natCast_iff' a b (p ^ k)).mp h
      rwa [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] at this
    · have hab : ((a + b : ℕ) : ZMod (p ^ k)) = 0 := by push_cast; rw [h, neg_add_cancel]
      rw [ZMod.natCast_eq_zero_iff] at hab
      obtain ⟨c, hc⟩ := hab
      rcases Nat.eq_zero_or_pos c with rfl | hc0
      · omega
      · have : a + b ≥ p ^ k := by nlinarith
        omega
  have hinj : Set.InjOn σ (A p k) := by
    intro a ha b hb hab
    apply hcast_inj a b ha hb
    have hσa := foldVal_cast_eq ((a : ZMod (p ^ k)) * s)
    have hσb := foldVal_cast_eq ((b : ZMod (p ^ k)) * s)
    have e : ((σ a : ℕ) : ZMod (p ^ k)) = ((σ b : ℕ) : ZMod (p ^ k)) := by rw [hab]
    simp only [hσ] at e hσa hσb
    have key : (a : ZMod (p ^ k)) * s = b * s ∨ (a : ZMod (p ^ k)) * s = -(b * s) := by
      rcases hσa with ha' | ha' <;> rcases hσb with hb' | hb'
      · left; rw [← ha', ← hb', e]
      · right; rw [← ha', ← hb', e]
      · right; rw [← neg_neg ((a : ZMod (p ^ k)) * s), ← ha', e, hb']
      · left; rw [← neg_neg ((a : ZMod (p ^ k)) * s), ← ha', e, hb', neg_neg]
    rcases key with h | h
    · left; exact hs.mul_right_cancel h
    · right; rw [← neg_mul] at h; exact hs.mul_right_cancel h
  have himage : (A p k).image σ = A p k :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmemA)
      (by rw [Finset.card_image_of_injOn hinj])
  calc Multiset.map (fun a : ℕ => G ((a : ZMod (p ^ k)) * s)) (A p k).val
      = Multiset.map (fun a : ℕ => G ((σ a : ℕ) : ZMod (p ^ k))) (A p k).val :=
        Multiset.map_congr rfl (fun a _ => (hGσ a).symm)
    _ = Multiset.map (fun b : ℕ => G (b : ZMod (p ^ k))) (Multiset.map σ (A p k).val) := by
        rw [Multiset.map_map]; rfl
    _ = Multiset.map (fun b : ℕ => G (b : ZMod (p ^ k))) ((A p k).image σ).val := by
        rw [Finset.image_val_of_injOn hinj]
    _ = Multiset.map (fun a : ℕ => G (a : ZMod (p ^ k))) (A p k).val := by rw [himage]

end TFormsSym
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"

namespace TFormsSym

open UpperHalfPlane
open scoped ModularForm MatrixGroups

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

theorem coe_finset_sum {ι : Type*} {k : ℤ} (s : Finset ι) (F : ι → ModularForm Γ k) :
    (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

theorem finset_sum_slash {ι : Type*} (k : ℤ) (g : GL (Fin 2) ℝ) (s : Finset ι) (F : ι → ℍ → ℂ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, (F i ∣[k] g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

def prodForm2 [Γ.HasDetPlusMinusOne] (f : ℕ → ModularForm Γ 2) (T : Finset ℕ) : ModularForm Γ (2 * (T.card : ℤ)) :=
  ModularForm.prod (s := T) (k := fun _ => (2 : ℤ)) (2 * (T.card : ℤ)) (by simp [mul_comm]) f

theorem coe_prodForm2 [Γ.HasDetPlusMinusOne] (f : ℕ → ModularForm Γ 2) (T : Finset ℕ) :
    (⇑(prodForm2 f T) : ℍ → ℂ) = ∏ a ∈ T, (⇑(f a) : ℍ → ℂ) :=
  ModularForm.coe_prod _ _ _

def esymmForm [Γ.HasDetPlusMinusOne] (A : Finset ℕ) (f : ℕ → ModularForm Γ 2) (m : ℕ) : ModularForm Γ (2 * (m : ℤ)) := by
  classical
  exact ∑ T ∈ A.powersetCard m,
    if h : T.card = m then ModularForm.mcast (by rw [h]) (prodForm2 f T) else 0

theorem coe_esymmForm [Γ.HasDetPlusMinusOne] (A : Finset ℕ) (f : ℕ → ModularForm Γ 2) (m : ℕ) :
    (⇑(esymmForm A f m) : ℍ → ℂ) = (A.val.map fun a => (⇑(f a) : ℍ → ℂ)).esymm m := by
  classical
  rw [Finset.esymm_map_val, esymmForm, coe_finset_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hc : T.card = m := (Finset.mem_powersetCard.mp hT).2
  rw [dif_pos hc, ModularForm.coe_mcast, coe_prodForm2]

theorem coe_esymmForm_slash [Γ.HasDetPlusMinusOne] (A : Finset ℕ) (f : ℕ → ModularForm Γ 2) (m : ℕ) (g : SL(2, ℤ)) :
    (⇑(esymmForm A f m) : ℍ → ℂ) ∣[(2 * (m : ℤ))] (g : GL (Fin 2) ℝ) =
      (A.val.map fun a => ((⇑(f a) : ℍ → ℂ) ∣[(2 : ℤ)] (g : GL (Fin 2) ℝ))).esymm m := by
  classical
  rw [Finset.esymm_map_val, coe_esymmForm, Finset.esymm_map_val, finset_sum_slash]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hc : T.card = m := (Finset.mem_powersetCard.mp hT).2
  show (∏ a ∈ T, (⇑(f a) : ℍ → ℂ)) ∣[(2 * (m : ℤ))] (g : GL (Fin 2) ℝ) = ∏ a ∈ T, ((⇑(f a) : ℍ → ℂ) ∣[(2 : ℤ)] (g : GL (Fin 2) ℝ))
  rw [show (2 * (m : ℤ)) = 2 * (T.card : ℕ) by rw [hc], ModularForm.prod_slash]
  simp only [Matrix.SpecialLinearGroup.coeToGL_det, Units.val_one, abs_one, one_zpow, one_smul]

theorem qExpansion_coe_prod [Γ.HasDetPlusMinusOne] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {k : ℤ} (F : ℕ → ModularForm Γ k) (s : Finset ℕ) :
    qExpansion 1 (∏ i ∈ s, (⇑(F i) : ℍ → ℂ)) = ∏ i ∈ s, qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
    have hs : (∏ i ∈ s, (⇑(F i) : ℍ → ℂ)) =
        ⇑(ModularForm.prod (s := s) (k := fun _ => k) (s.card * k) (by simp) F) := by
      rw [ModularForm.coe_prod]
    have han : AnalyticAt ℂ (cuspFunction 1 (∏ i ∈ s, (⇑(F i) : ℍ → ℂ))) 0 := by
      rw [hs]; exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos hΓ
    exact qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero (F a) one_pos hΓ) han

theorem qExpansion_coe_sum (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {ι : Type*} {k : ℤ} (F : ι → ModularForm Γ k) (s : Finset ι) :
    qExpansion 1 (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, ModularForm.coe_add]
    exact qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero (F a) one_pos hΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos hΓ)

theorem ofPowerSeries_qExpansion_esymmForm [Γ.HasDetPlusMinusOne] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (A : Finset ℕ) (f : ℕ → ModularForm Γ 2) (m : ℕ) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(esymmForm A f m) : ℍ → ℂ)) =
      (A.val.map fun a => HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(f a) : ℍ → ℂ))).esymm m := by
  classical
  rw [Finset.esymm_map_val, esymmForm, qExpansion_coe_sum hΓ, map_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hc : T.card = m := (Finset.mem_powersetCard.mp hT).2
  rw [dif_pos hc, ModularForm.coe_mcast, coe_prodForm2, qExpansion_coe_prod hΓ, map_prod]

end TFormsSym
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C Gamma1_le_GammaH FullLevel.dvd_sq_mul FullLevel.levelH FullLevel.mem_levelH_iff FullLevel.conjElemN toricPoint toricPoint_fst gamma0PowDeg toricPoint_level_mul"
namespace ToricDivisionForms
p2m_open "ModularCurve"

section TForms

theorem map_esymm {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (s : Multiset R) (m : ℕ) :
    φ (s.esymm m) = (s.map φ).esymm m := by
  simp only [Multiset.esymm, map_multiset_sum, Multiset.map_map, Multiset.powersetCard_map]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  simp [Function.comp, map_multiset_prod]

variable (N M' : ℕ) [NeZero N] [NeZero M'] (p k : ℕ) [hp : Fact p.Prime] [NeZero (p ^ k)]
  (W : ZMod (p ^ k) → ModularForm (Gamma1 (p ^ k) : Subgroup (GL (Fin 2) ℝ)) 2)

def fW (a : ℕ) : ModularForm (Gamma1 (p ^ k) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  (12 : ℂ)⁻¹ • W (a : ZMod (p ^ k))

def formE (m : ℕ) : ModularForm (Gamma1 (p ^ k) : Subgroup (GL (Fin 2) ℝ)) (2 * (m : ℤ)) :=
  TFormsSym.esymmForm (TFormsSym.A p k) (fW p k W) m

omit [NeZero N] [NeZero M'] hp [NeZero (p ^ k)] in
theorem coe_fW (a : ℕ) : (⇑(fW p k W a) : ℍ → ℂ) = (12 : ℂ)⁻¹ • ⇑(W (a : ZMod (p ^ k))) := by
  rw [fW, ModularForm.IsGLPos.coe_smul]

variable
  (hslash : ∀ (s : ZMod (p ^ k)) (γ : SL(2, ℤ)), γ ∈ Gamma0 (p ^ k) →
    (⇑(W s) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (s * ((γ 1 1 : ℤ) : ZMod (p ^ k)))))
  (hq : ∀ s : ZMod (p ^ k), s ≠ 0 → ∀ m : ℕ,
    (qExpansion 1 (W s)).coeff m =
      if m = 0 then
        1 + 12 * Complex.exp (2 * π * Complex.I / (p ^ k : ℕ)) ^ s.val /
          (1 - Complex.exp (2 * π * Complex.I / (p ^ k : ℕ)) ^ s.val) ^ 2
      else
        12 * ((∑ d ∈ m.divisors, (d : ℂ) *
            (Complex.exp (2 * π * Complex.I / (p ^ k : ℕ)) ^ (s.val * d) +
              (Complex.exp (2 * π * Complex.I / (p ^ k : ℕ)))⁻¹ ^ (s.val * d))) -
          2 * ∑ d ∈ m.divisors, (d : ℂ)))

omit [NeZero N] [NeZero M'] in
include hslash hq in

theorem coe_formE_slash_eq (m : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (p ^ k)) :
    (⇑(formE p k W m) : ℍ → ℂ) ∣[(2 * (m : ℤ))] γ = ⇑(formE p k W m) := by
  rw [ModularForm.SL_slash, formE, TFormsSym.coe_esymmForm_slash, TFormsSym.coe_esymmForm]
  set u : (ZMod (p ^ k))ˣ := CohCarrier.gamma0Units (p ^ k) ⟨γ, hγ⟩ with hu
  have huval : (u : ZMod (p ^ k)) = ((γ 1 1 : ℤ) : ZMod (p ^ k)) := rfl
  let G : ZMod (p ^ k) → ℍ → ℂ := fun t => (12 : ℂ)⁻¹ • ⇑(W t)
  have hG : ∀ t, G (-t) = G t := fun t => by
    simp only [G]; congr 1; ext τ; exact W_neg_apply W hq t τ
  have key : ((TFormsSym.A p k).val.map fun a => (⇑(fW p k W a) : ℍ → ℂ) ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ)) =
      (TFormsSym.A p k).val.map fun a : ℕ => G ((a : ZMod (p ^ k)) * (u : ZMod (p ^ k))) := by
    refine Multiset.map_congr rfl fun a _ => ?_
    rw [coe_fW, ← ModularForm.SL_slash, ModularForm.SL_smul_slash, hslash _ γ hγ, huval]
  rw [key, TFormsSym.map_A_mul_unit_eq p k hp.out (u : ZMod (p ^ k)) u.isUnit G hG]
  refine congrArg (fun s : Multiset (ℍ → ℂ) => s.esymm m) (Multiset.map_congr rfl fun a _ => ?_)
  rw [coe_fW]

variable (hpk : p ^ k ∣ M')

omit [NeZero N] [NeZero M'] hp [NeZero (p ^ k)] in
include hpk in
theorem mem_Gamma0_pow_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') : γ ∈ Gamma0 (p ^ k) := by
  rw [Gamma0_mem] at hγ ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact dvd_trans (by exact_mod_cast hpk) hγ

def formEMid (m : ℕ) : ModularForm (GammaMid N M' : Subgroup (GL (Fin 2) ℝ)) (2 * (m : ℤ)) :=
  transport (formE p k W m) (fun x hx => isCusp_of_isArithmetic x hx)
    (fun g hg => by
      obtain ⟨γ, hγ, rfl⟩ := hg
      exact coe_formE_slash_eq p k W hslash hq m γ (mem_Gamma0_pow_of_mem M' p k hpk hγ.2))

def formS (m : ℕ) : ModularForm (CohCarrier.GammaH (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M') :
    Subgroup (GL (Fin 2) ℝ)) (2 * (m : ℤ)) :=
  ((-1 : ℂ) ^ m * (N : ℂ) ^ ((1 : ℤ) - 2 * (m : ℤ))) • stretch N M' (formEMid N M' p k W hslash hq hpk m)

theorem heckeDiagMatrix_mul_conjElemN (ρ : SL(2, ℤ)) :
    ModularForm.heckeDiagMatrix N * ModularCurve.FullLevel.conjElemN N ρ =
      (ρ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularForm.val_heckeDiagMatrix (NeZero.ne N), ModularCurve.FullLevel.conjElemN, Matrix.mul_apply,
      Fin.sum_univ_two, hN] <;> field_simp

theorem det_conjElemN_val (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) :
    (((ModularCurve.FullLevel.conjElemN m γ).det : ℝˣ) : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (!![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]) = 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [Matrix.det_fin_two_of]
  field_simp
  linear_combination hdet

theorem σ_conjElemN_apply (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) (z : ℂ) :
    UpperHalfPlane.σ (ModularCurve.FullLevel.conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

include hslash hq in

theorem formS_slash_conjElemN (m : ℕ) (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 M') :
    (⇑(formS N M' p k W hslash hq hpk m) : ℍ → ℂ) ∣[(2 * (m : ℤ))] ModularCurve.FullLevel.conjElemN N ρ =
      ⇑(formS N M' p k W hslash hq hpk m) := by
  rw [formS, ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, σ_conjElemN_apply, coe_stretch,
    ← SlashAction.slash_mul, heckeDiagMatrix_mul_conjElemN, SlashAction.slash_mul, formEMid, coe_transport,
    ← ModularForm.SL_slash, coe_formE_slash_eq p k W hslash hq m ρ (mem_Gamma0_pow_of_mem M' p k hpk hρ)]

include hq in
omit [NeZero N] [NeZero M'] in

theorem qExpansion_fW (a : ℕ) (ha : a ∈ TFormsSym.A p k) :
    qExpansion 1 (⇑(fW p k W a)) = PowerSeries.C (12 : ℂ)⁻¹ + X₁ (rootOfUnity (p ^ k) ^ a) := by
  have hΓ := one_mem_strictPeriods_of_T_mem (T_mem_Gamma1 (p ^ k))
  have ha' := (TFormsSym.mem_A.mp ha).1
  have hna : ¬ p ^ k ∣ a := fun h => by
    have := Nat.le_of_dvd (by omega) h
    have : p ^ k / 2 < p ^ k := Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne _)) one_lt_two
    omega
  rw [fW, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hΓ _ (W _), qExpansion_W_natCast W hq a hna,
    PowerSeries.smul_eq_C_mul, map_one]
  have h12 : (PowerSeries.C (12 : ℂ)⁻¹ : PowerSeries ℂ) * PowerSeries.C 12 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  linear_combination (X₁ (rootOfUnity (p ^ k) ^ a)) * h12

include hslash hq in

theorem coe_qExpansion_formS (m : ℕ) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(formS N M' p k W hslash hq hpk m))) =
      HahnSeries.C ((-1 : ℂ) ^ m) *
        ((TFormsSym.A p k).val.map fun a : ℕ =>
          (toricPoint ℂ N (rootOfUnity (p ^ k) ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹)).esymm m := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hΓH := one_mem_strictPeriods_of_T_mem (T_mem_GammaH (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M'))
  have hΓ1 := one_mem_strictPeriods_of_T_mem (T_mem_Gamma1 (p ^ k))
  rw [formS, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hΓH _ (stretch N M' _),
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, coe_qExpansion_stretch]

  have hE : HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(formEMid N M' p k W hslash hq hpk m))) =
      ((TFormsSym.A p k).val.map fun a : ℕ =>
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(fW p k W a)))).esymm m := by
    rw [formEMid, coe_transport, formE]
    exact TFormsSym.ofPowerSeries_qExpansion_esymmForm hΓ1 _ _ _
  rw [hE, map_esymm, Multiset.map_map]
  have hX : ∀ u : ℂ, qExpand ℂ N (HahnSeries.ofPowerSeries ℤ ℂ (X₁ u)) = (toricPoint ℂ N u).1 :=
    fun u => (toricPoint_fst_eq_qExpand N u).symm
  have hmap : ((TFormsSym.A p k).val.map
      ((qExpand ℂ N) ∘ fun a : ℕ => HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(fW p k W a))))) =
      (TFormsSym.A p k).val.map fun a : ℕ => (toricPoint ℂ N (rootOfUnity (p ^ k) ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹) := by
    refine Multiset.map_congr rfl fun a ha => ?_
    simp only [Function.comp, qExpansion_fW p k W hq a ha, map_add, HahnSeries.ofPowerSeries_C, qExpand_C, hX, add_comm]
  rw [hmap, ← mul_assoc, ← map_mul]
  congr 1
  congr 1
  rw [mul_assoc, ← zpow_add₀ hN, show (1 : ℤ) - 2 * (m : ℤ) + (2 * (m : ℤ) - 1) = 0 by ring, zpow_zero, mul_one]

end TForms
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"

end ModularCurve.ToricDivisionForms
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve.ToricDivisionForms"

open scoped MatrixGroups ModularForm in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.ModularCurve ModularCurve.ToricDivisionForms UpperHalfPlane in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M') (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∀ j : ℕ, j ≤ ModularCurve.gamma0PowDeg p k →
      ∃ S : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) (2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑S)) =
          (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (Polynomial.X - Polynomial.C ((ModularCurve.toricPoint ℂ (q * ℓ) (ζ ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹)))).coeff j ∧
        ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
          (⇑S ∣[(2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ))] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑S := by
  intro j hj
  set N : ℕ := q * ℓ with hN
  haveI : NeZero N := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set d : ℕ := ModularCurve.gamma0PowDeg p k with hd
  set m : ℕ := d - j with hm
  obtain ⟨W, -, hslash, hq⟩ :=
    PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff (p ^ k)
  refine ⟨formS N M' p k W hslash hq hpk m, ?_, fun ρ hρ => formS_slash_conjElemN N M' p k W hslash hq hpk m ρ hρ⟩
  rw [coe_qExpansion_formS]

  set ε : ℂ := rootOfUnity (p ^ k) with hε
  have hεprim : IsPrimitiveRoot ε (p ^ k) := by
    rw [hε, rootOfUnity]; exact Complex.isPrimitiveRoot_exp _ (NeZero.ne _)
  obtain ⟨s, -, hs⟩ := hεprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hscop : s.Coprime (p ^ k) := (hεprim.pow_iff_coprime (NeZero.pos _) s).mp (hs ▸ hζ)

  let T : ℂ → LaurentSeries ℂ := fun u => (toricPoint ℂ N u).1 + HahnSeries.C ((12 : ℂ)⁻¹)
  let G : ZMod (p ^ k) → LaurentSeries ℂ := fun t => T (ε ^ t.val)
  have hG : ∀ t, G (-t) = G t := fun t => by
    simp only [G, T, toricPoint_fst_eq_qExpand, X₁_pow_neg_val ε (rootOfUnity_pow_self (p ^ k))]
  have hGε : ∀ a : ℕ, G (a : ZMod (p ^ k)) = T (ε ^ a) := fun a => by
    simp only [G, ZMod.val_natCast, ← pow_mod_eq ε (rootOfUnity_pow_self (p ^ k))]
  have hGζ : ∀ a : ℕ, G ((a : ZMod (p ^ k)) * (s : ZMod (p ^ k))) = T (ζ ^ a) := fun a => by
    rw [← Nat.cast_mul, hGε, ← hs, ← pow_mul, mul_comm]
  have hunit : IsUnit ((s : ℕ) : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime s (p ^ k)).mpr hscop
  have hmult : ((TFormsSym.A p k).val.map fun a : ℕ => T (ζ ^ a)) =
      (TFormsSym.A p k).val.map fun a : ℕ => T (ε ^ a) := by
    rw [show ((TFormsSym.A p k).val.map fun a : ℕ => T (ζ ^ a)) =
        (TFormsSym.A p k).val.map fun a : ℕ => G ((a : ZMod (p ^ k)) * (s : ZMod (p ^ k))) from
        Multiset.map_congr rfl fun a _ => (hGζ a).symm,
      TFormsSym.map_A_mul_unit_eq p k hp _ hunit G hG]
    exact Multiset.map_congr rfl fun a _ => hGε a

  have hcard : ((TFormsSym.A p k).val.map fun a : ℕ => T (ζ ^ a)).card = d := by
    rw [Multiset.card_map, Finset.card_val, TFormsSym.card_A p k hp]
  have hprod : (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
      (Polynomial.X - Polynomial.C ((ModularCurve.toricPoint ℂ (q * ℓ) (ζ ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹)))) =
      (((TFormsSym.A p k).val.map fun a : ℕ => T (ζ ^ a)).map fun z => Polynomial.X - Polynomial.C z).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [hprod, Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact hj), hcard, hmult, map_pow, map_neg, map_one]

end S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq (solution)
