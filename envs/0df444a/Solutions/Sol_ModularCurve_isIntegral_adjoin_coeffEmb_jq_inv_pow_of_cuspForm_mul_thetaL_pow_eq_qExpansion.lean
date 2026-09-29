-- Prove2me | solution 1 for ModularCurve.isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fc616ea9-2fe0-5680-85fa-ca6d545c2d8d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne
import Theorems.Thm_omegaRow_T2
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion

noncomputable section

section Helpers

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Topology Pointwise

local notation "Δ" => ModularForm.discriminant

namespace IsIntegralAdjoinCoeffEmbJqInvSol

section Engine

open SlashInvariantForm

def qL (F : ℍ → ℂ) : LaurentSeries ℂ := ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ)

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

def restrictSL {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := F
  slash_action_eq' A hA := by
    obtain ⟨γ, -, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_eqn F _ ⟨γ, rfl⟩
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (hc.mono (Subgroup.map_le_range _ _))

omit [Γ.FiniteIndex] in
@[scoped simp] theorem coe_restrictSL {k : ℤ} (F : ModularForm 𝒮ℒ k) : ⇑(restrictSL Γ F) = ⇑F := rfl

abbrev Q := 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ

scoped instance : Fintype (Q Γ) := Fintype.ofFinite _

variable {Γ}
variable {n : ℕ} (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) ((n : ℤ) * 4))

def Mform (c : ℂ) : ModularForm 𝒮ℒ ((n : ℤ) * 4 * Nat.card (Q Γ)) :=
  ModularForm.norm 𝒮ℒ (G - c • restrictSL Γ (E₄.pow n))

def aq (q : Q Γ) (τ : ℍ) : ℂ := quotientFunc G q τ

omit [Γ.FiniteIndex] in
theorem aq_one : aq G ⟦1⟧ = ⇑G := by
  ext τ
  simp [aq]

omit [Γ.FiniteIndex] in
theorem quotientFunc_sub_smul (c : ℂ) (q : Q Γ) (τ : ℍ) :
    quotientFunc (G - c • restrictSL Γ (E₄.pow n)) q τ = aq G q τ - c * E₄ τ ^ n := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨γ, hγ⟩ := r.2
    have hinv : (r.val)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ := by
      rw [map_inv, hγ]
    simp only [aq, quotientFunc_mk, hinv]
    change ((⇑(G - c • restrictSL Γ (E₄.pow n))) ∣[((n : ℤ) * 4)] (γ⁻¹)) τ =
      ((⇑G) ∣[((n : ℤ) * 4)] (γ⁻¹)) τ - _
    rw [ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.SL_smul_slash]
    have hE : (⇑(restrictSL Γ (E₄.pow n))) ∣[((n : ℤ) * 4)] (γ⁻¹) = ⇑(E₄.pow n) := by
      have := SlashInvariantForm.slash_action_eqn (E₄.pow n)
        (Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹) ⟨γ⁻¹, rfl⟩
      exact this
    rw [hE]
    simp [sub_eq_add_neg]

def Pτ (τ : ℍ) : Polynomial ℂ :=
  ∏ q : Q Γ, (Polynomial.C (aq G q τ) - Polynomial.X * Polynomial.C (E₄ τ ^ n))

theorem Mform_apply (c : ℂ) (τ : ℍ) : Mform G c τ = (Pτ G τ).eval c := by
  rw [Mform, Pτ, Polynomial.eval_prod]
  change (ModularForm.norm 𝒮ℒ (G - c • restrictSL Γ (E₄.pow n)) : ℍ → ℂ) τ = _
  rw [ModularForm.coe_norm, Finset.prod_apply]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  rw [quotientFunc_sub_smul]
  simp

omit [Γ.FiniteIndex] in
theorem natDegree_factor_le (q : Q Γ) (τ : ℍ) :
    (Polynomial.C (aq G q τ) - Polynomial.X * Polynomial.C (E₄ τ ^ n)).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  rw [Polynomial.natDegree_C, Nat.zero_max]
  refine (Polynomial.natDegree_mul_le).trans ?_
  simp

theorem natDegree_Pτ_le (τ : ℍ) : (Pτ G τ).natDegree ≤ Fintype.card (Q Γ) := by
  unfold Pτ
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ ↦ natDegree_factor_le G q τ).trans ?_
  simp

theorem coeff_Pτ_card (τ : ℍ) :
    (Pτ G τ).coeff (Fintype.card (Q Γ)) = (-(E₄ τ ^ n)) ^ Fintype.card (Q Γ) := by
  unfold Pτ
  have := Polynomial.coeff_prod_of_natDegree_le
    (fun q : Q Γ ↦ Polynomial.C (aq G q τ) - Polynomial.X * Polynomial.C (E₄ τ ^ n)) 1
    (s := Finset.univ) (fun q _ ↦ natDegree_factor_le G q τ)
  rw [mul_one, Finset.card_univ] at this
  rw [this]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_zero, zero_sub, Finset.prod_const, Finset.card_univ]

def Lc (d i m : ℕ) : ℂ :=
  (Lagrange.basis (Finset.range (d + 1)) (fun j : ℕ ↦ (j : ℂ)) i).coeff m

theorem coeff_Pτ_eq_sum (τ : ℍ) (m : ℕ) :
    (Pτ G τ).coeff m = ∑ i ∈ Finset.range (Fintype.card (Q Γ) + 1),
      Lc (Fintype.card (Q Γ)) i m * Mform G (i : ℂ) τ := by
  set d := Fintype.card (Q Γ)
  have hinj : Set.InjOn (fun j : ℕ ↦ (j : ℂ)) (Finset.range (d + 1) : Set ℕ) :=
    Nat.cast_injective.injOn
  have hdeg : (Pτ G τ).degree < (Finset.range (d + 1)).card := by
    rw [Finset.card_range]
    refine lt_of_le_of_lt (Polynomial.degree_le_natDegree) ?_
    exact_mod_cast Nat.lt_succ_of_le (natDegree_Pτ_le G τ)
  have hL := Lagrange.eq_interpolate hinj hdeg
  conv_lhs => rw [hL]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.coeff_C_mul, Mform_apply, Lc, mul_comm]

theorem sum_coeff_mul_pow_eq_zero (τ : ℍ) :
    ∑ m ∈ Finset.range (Fintype.card (Q Γ) + 1),
      (Pτ G τ).coeff m * G τ ^ m * (E₄ τ ^ n) ^ (Fintype.card (Q Γ) - m) = 0 := by
  set d := Fintype.card (Q Γ)
  by_cases he : E₄ τ ^ n = 0
  · refine Finset.sum_eq_zero fun m hm ↦ ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · have hd : 0 < d := Fintype.card_pos
      rw [he, Nat.sub_zero, zero_pow hd.ne', mul_zero]
    · have hP : Pτ G τ = Polynomial.C (∏ q : Q Γ, aq G q τ) := by
        unfold Pτ
        rw [map_prod]
        refine Finset.prod_congr rfl fun q _ ↦ ?_
        rw [he, map_zero, mul_zero, sub_zero]
      rw [hP, Polynomial.coeff_C, if_neg hm0.ne', zero_mul, zero_mul]
  ·
    have heval : (Pτ G τ).eval (G τ / E₄ τ ^ n) = 0 := by
      unfold Pτ
      rw [Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ (α := Q Γ) ⟦1⟧) ?_
      rw [aq_one]
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      field_simp
      ring
    have hexp : (Pτ G τ).eval (G τ / E₄ τ ^ n) =
        ∑ m ∈ Finset.range (d + 1), (Pτ G τ).coeff m * (G τ / E₄ τ ^ n) ^ m := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_Pτ_le G τ))]
    have key : ∑ m ∈ Finset.range (d + 1),
        (Pτ G τ).coeff m * G τ ^ m * (E₄ τ ^ n) ^ (d - m) =
        (E₄ τ ^ n) ^ d * ∑ m ∈ Finset.range (d + 1), (Pτ G τ).coeff m * (G τ / E₄ τ ^ n) ^ m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmd : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      rw [div_pow, ← Nat.sub_add_cancel hmd, pow_add, Nat.add_sub_cancel]
      field_simp
    rw [key, ← hexp, heval, mul_zero]

def An (F : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 F) 0

theorem An.of_mf {𝒢' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F 𝒢' k] (f : F) (h1 : (1 : ℝ) ∈ 𝒢'.strictPeriods) : An ⇑f :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos h1

theorem An.one : An (1 : ℍ → ℂ) := by
  have := An.of_mf (1 : ModularForm 𝒮ℒ 0) one_mem_strictPeriods_SL
  simpa using this

theorem An.zero : An (0 : ℍ → ℂ) := by
  have := An.of_mf (0 : ModularForm 𝒮ℒ 0) one_mem_strictPeriods_SL
  simpa using this

theorem An.mul {F₁ F₂ : ℍ → ℂ} (h₁ : An F₁) (h₂ : An F₂) : An (F₁ * F₂) := by
  unfold An at *
  rw [cuspFunction_mul h₁.continuousAt h₂.continuousAt]
  exact h₁.mul h₂

theorem An.add {F₁ F₂ : ℍ → ℂ} (h₁ : An F₁) (h₂ : An F₂) : An (F₁ + F₂) := by
  unfold An at *
  rw [cuspFunction_add h₁.continuousAt h₂.continuousAt]
  exact h₁.add h₂

theorem An.smul {F₁ : ℍ → ℂ} (c : ℂ) (h₁ : An F₁) : An (c • F₁) := by
  unfold An at *
  rw [cuspFunction_smul h₁.continuousAt]
  exact h₁.const_smul

theorem An.neg {F₁ : ℍ → ℂ} (h₁ : An F₁) : An (-F₁) := by
  unfold An at *
  rw [cuspFunction_neg h₁.continuousAt]
  exact h₁.neg

theorem An.pow {F₁ : ℍ → ℂ} (h₁ : An F₁) : ∀ m : ℕ, An (F₁ ^ m)
  | 0 => by simpa using An.one
  | m + 1 => by
    rw [pow_succ]
    exact (An.pow h₁ m).mul h₁

theorem An.sum {ι : Type*} {s : Finset ι} {F₁ : ι → ℍ → ℂ} (h : ∀ i ∈ s, An (F₁ i)) :
    An (∑ i ∈ s, F₁ i) :=
  Finset.sum_induction _ _ (fun _ _ ↦ An.add) An.zero h

theorem qExpansion_pow' {F₁ : ℍ → ℂ} (h₁ : An F₁) :
    ∀ m : ℕ, qExpansion 1 (F₁ ^ m) = qExpansion 1 F₁ ^ m
  | 0 => by rw [pow_zero, pow_zero, qExpansion_one]
  | m + 1 => by
    rw [pow_succ, pow_succ, qExpansion_mul (h₁.pow m) h₁, qExpansion_pow' h₁ m]

theorem qExpansion_sum' {ι : Type*} {s : Finset ι} {F₁ : ι → ℍ → ℂ} (h : ∀ i ∈ s, An (F₁ i)) :
    qExpansion 1 (∑ i ∈ s, F₁ i) = ∑ i ∈ s, qExpansion 1 (F₁ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, An (F₁ i) := fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExpansion_add (h a (Finset.mem_insert_self a s)) (An.sum hs), ih hs]

def bfun (m : ℕ) : ℍ → ℂ := fun τ ↦ (Pτ G τ).coeff m

theorem bfun_eq_sum (m : ℕ) :
    bfun G m = ∑ i ∈ Finset.range (Fintype.card (Q Γ) + 1),
      Lc (Fintype.card (Q Γ)) i m • ⇑(Mform G (i : ℂ)) := by
  ext τ
  simp only [bfun, coeff_Pτ_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem bfun_card : bfun G (Fintype.card (Q Γ)) = (-((⇑E₄) ^ n)) ^ Fintype.card (Q Γ) := by
  ext τ
  simp only [bfun, coeff_Pτ_card, Pi.pow_apply, Pi.neg_apply]

theorem sum_bfun_eq_zero :
    ∑ m ∈ Finset.range (Fintype.card (Q Γ) + 1),
      bfun G m * (⇑G) ^ m * ((⇑E₄) ^ n) ^ (Fintype.card (Q Γ) - m) = 0 := by
  ext τ
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, bfun]
  exact sum_coeff_mul_pow_eq_zero G τ

theorem An_bfun (m : ℕ) : An (bfun G m) := by
  rw [bfun_eq_sum]
  exact An.sum fun i _ ↦ An.smul _ (An.of_mf _ one_mem_strictPeriods_SL)

theorem qL_bfun (m : ℕ) :
    qL (bfun G m) = ∑ i ∈ Finset.range (Fintype.card (Q Γ) + 1),
      HahnSeries.C (Lc (Fintype.card (Q Γ)) i m) * qL ⇑(Mform G (i : ℂ)) := by
  unfold qL
  rw [bfun_eq_sum, qExpansion_sum' (fun i _ ↦ An.smul _ (An.of_mf _ one_mem_strictPeriods_SL)),
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [qExpansion_smul (An.of_mf _ one_mem_strictPeriods_SL), PowerSeries.coe_smul,
    HahnSeries.C_mul_eq_smul]

theorem qL_E4_pow : qL ((⇑E₄) ^ n) = qL ⇑E₄ ^ n := by
  unfold qL
  rw [qExpansion_pow' (An.of_mf _ one_mem_strictPeriods_SL), PowerSeries.coe_pow]

theorem qL_bfun_card :
    qL (bfun G (Fintype.card (Q Γ))) = (-(qL ⇑E₄ ^ n)) ^ Fintype.card (Q Γ) := by
  have hA : An ((⇑E₄) ^ n) := (An.of_mf _ one_mem_strictPeriods_SL).pow n
  rw [bfun_card, ← qL_E4_pow]
  unfold qL
  rw [qExpansion_pow' hA.neg, qExpansion_neg hA, PowerSeries.coe_pow, PowerSeries.coe_neg]

theorem qL_relation (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) :
    ∑ m ∈ Finset.range (Fintype.card (Q Γ) + 1),
      qL (bfun G m) * qL ⇑G ^ m * (qL ⇑E₄ ^ n) ^ (Fintype.card (Q Γ) - m) = 0 := by
  have hE : An ((⇑E₄) ^ n) := (An.of_mf _ one_mem_strictPeriods_SL).pow n
  have hG : An ⇑G := An.of_mf G h1
  have hs : ∀ m ∈ Finset.range (Fintype.card (Q Γ) + 1),
      An (bfun G m * (⇑G) ^ m * ((⇑E₄) ^ n) ^ (Fintype.card (Q Γ) - m)) :=
    fun m _ ↦ ((An_bfun G m).mul (hG.pow m)).mul (hE.pow _)
  have h := congrArg (qExpansion 1) (sum_bfun_eq_zero G)
  rw [qExpansion_zero, qExpansion_sum' hs] at h
  have h' := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) h
  rw [map_sum, map_zero] at h'
  rw [← h']
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [qExpansion_mul ((An_bfun G m).mul (hG.pow m)) (hE.pow _),
    qExpansion_mul (An_bfun G m) (hG.pow m), qExpansion_pow' hG, qExpansion_pow' hE,
    ← qL_E4_pow]
  simp only [map_mul, map_pow]
  rfl

theorem qL_ne_zero_of_coeff {F₁ : ℍ → ℂ} {i : ℕ} (h : (qExpansion 1 F₁).coeff i ≠ 0) :
    qL F₁ ≠ 0 := by
  intro h0
  apply h
  have : qExpansion 1 F₁ = 0 :=
    (map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h0
  rw [this, map_zero]

theorem qL_E4_ne_zero : qL ⇑E₄ ≠ 0 :=
  qL_ne_zero_of_coeff (i := 1) (by rw [ModularForm.E₄_qExpansion_coeff_one]; norm_num)

theorem qL_E6_ne_zero : qL ⇑E₆ ≠ 0 :=
  qL_ne_zero_of_coeff (i := 1) (by rw [ModularForm.E₆_qExpansion_coeff_one]; norm_num)

theorem qL_Δ_ne_zero : qL Δ ≠ 0 :=
  qL_ne_zero_of_coeff (i := 1) (by rw [ModularForm.discriminant_qExpansion_coeff_one]; norm_num)

def xL : LaurentSeries ℂ := qL Δ / qL ⇑E₄ ^ 3

abbrev Rx : Subalgebra ℂ (LaurentSeries ℂ) := Algebra.adjoin ℂ {xL}

theorem isIntegral_of_mem_Rx {y : LaurentSeries ℂ} (hy : y ∈ Rx) : IsIntegral Rx y :=
  isIntegral_algebraMap (R := Rx) (A := LaurentSeries ℂ) (x := ⟨y, hy⟩)

theorem hahnC_eq_algebraMap (c : ℂ) :
    (HahnSeries.C c : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [HahnSeries.algebraMap_apply', ← HahnSeries.ofPowerSeries_C, PowerSeries.C_eq_algebraMap]

theorem isIntegral_hahnC (c : ℂ) : IsIntegral Rx (HahnSeries.C c : LaurentSeries ℂ) := by
  refine isIntegral_of_mem_Rx ?_
  rw [hahnC_eq_algebraMap]
  exact Subalgebra.algebraMap_mem _ _

theorem levelOne_isIntegral (m : ℕ) {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (hk : ((3 : ℕ) : ℤ) * k = 12 * (m : ℤ)) :
    IsIntegral Rx (qL ⇑F / qL ⇑E₄ ^ m) := by
  refine IsIntegral.of_pow (by norm_num : 0 < 3) ?_
  obtain ⟨P, hP, hq⟩ :=
    ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne m ((F.pow 3).mcast hk)
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    PowerSeries.coe_pow] at hq
  have hq' : qL ⇑F ^ 3 = Polynomial.aeval (qL ⇑E₄ ^ 3 / qL Δ) P * qL Δ ^ m := hq
  have hE : qL ⇑E₄ ≠ 0 := qL_E4_ne_zero
  have hΔ : qL Δ ≠ 0 := qL_Δ_ne_zero
  have hx : (qL ⇑F / qL ⇑E₄ ^ m) ^ 3 =
      ∑ i ∈ Finset.range (m + 1), algebraMap ℂ (LaurentSeries ℂ) (P.coeff i) * xL ^ (m - i) := by
    rw [div_pow, ← pow_mul, pow_mul', hq', Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP),
      Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [Nat.add_sub_cancel_left, xL, Algebra.smul_def, mul_assoc, mul_div_assoc]
    congr 1
    have ha : qL ⇑E₄ ^ 3 ≠ 0 := pow_ne_zero _ hE
    generalize qL ⇑E₄ ^ 3 = a at ha ⊢
    rw [div_pow, div_pow, pow_add, pow_add, div_mul_eq_mul_div, mul_left_comm (a ^ i) (qL Δ ^ i),
      mul_div_cancel_left₀ _ (pow_ne_zero _ hΔ), mul_div_mul_left _ _ (pow_ne_zero _ ha)]
  rw [hx]
  refine isIntegral_of_mem_Rx ?_
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℂ xL) _)

theorem isIntegral_div_of_relation {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (d : ℕ) (β : ℕ → L) (g e : L) (he : e ≠ 0)
    (hsum : ∑ m ∈ Finset.range (d + 1), β m * g ^ m * e ^ (d - m) = 0)
    (hlead : β d = (-e) ^ d)
    (hint : ∀ m ∈ Finset.range d, IsIntegral R (β m / e ^ d)) :
    IsIntegral R (g / e) := by
  have hed : (-e) ^ d ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr he)
  have hsign : ∀ b : L, b / (-e) ^ d = (-1) ^ d * (b / e ^ d) := fun b ↦ by
    rw [neg_pow, div_mul_eq_div_div_swap, div_eq_mul_inv (b / e ^ d), ← inv_pow, inv_neg_one,
      mul_comm]
  have hint' : ∀ m ∈ Finset.range d, β m / (-e) ^ d ∈ integralClosure R L := fun m hm ↦ by
    rw [mem_integralClosure_iff, hsign]
    exact ((isIntegral_one.neg).pow d).mul (hint m hm)
  classical
  let c : ℕ → integralClosure R L := fun m ↦
    if hm : m ∈ Finset.range d then ⟨β m / (-e) ^ d, hint' m hm⟩ else 0
  let p : Polynomial (integralClosure R L) :=
    ∑ m ∈ Finset.range d, Polynomial.C (c m) * Polynomial.X ^ m
  have hp : p.degree < d := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun m hm ↦ ?_
    refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hm)
  have hc : ∀ m ∈ Finset.range d,
      (algebraMap (integralClosure R L) L (c m) : L) = β m / (-e) ^ d := by
    intro m hm
    simp only [c, dif_pos hm]
    rfl
  have key : ∀ m ∈ Finset.range (d + 1),
      β m / (-e) ^ d * (g / e) ^ m = (β m * g ^ m * e ^ (d - m)) / ((-e) ^ d * e ^ d) := by
    intro m hm
    have hmd : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hmd
    rw [hj, Nat.add_sub_cancel_left, div_pow, div_mul_div_comm, pow_add e m j,
      ← mul_assoc ((-e) ^ (m + j)), mul_div_mul_right _ _ (pow_ne_zero j he)]
  have hA : IsIntegral (integralClosure R L) (g / e) := by
    refine ⟨Polynomial.X ^ d + p, Polynomial.monic_X_pow_add hp, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
    rw [Finset.sum_congr rfl fun m hm ↦ by rw [hc m hm]]
    calc (g / e) ^ d + ∑ m ∈ Finset.range d, β m / (-e) ^ d * (g / e) ^ m
        = ∑ m ∈ Finset.range (d + 1), β m / (-e) ^ d * (g / e) ^ m := by
          rw [Finset.sum_range_succ, hlead, div_self hed, one_mul, add_comm]
      _ = ∑ m ∈ Finset.range (d + 1), (β m * g ^ m * e ^ (d - m)) / ((-e) ^ d * e ^ d) :=
          Finset.sum_congr rfl key
      _ = 0 := by rw [← Finset.sum_div, hsum, zero_div]
  exact isIntegral_trans (g / e) hA

theorem engine (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) :
    IsIntegral Rx (qL ⇑G / qL ⇑E₄ ^ n) := by
  set d := Fintype.card (Q Γ) with hd
  have hE : qL ⇑E₄ ^ n ≠ 0 := pow_ne_zero _ qL_E4_ne_zero
  refine isIntegral_div_of_relation d (fun m ↦ qL (bfun G m)) (qL ⇑G) (qL ⇑E₄ ^ n) hE
    (qL_relation G h1) (qL_bfun_card G) ?_
  intro m _
  change IsIntegral Rx (qL (bfun G m) / _)
  rw [qL_bfun G m, Finset.sum_div]
  refine IsIntegral.sum _ fun i _ ↦ ?_
  rw [mul_div_assoc]
  refine (isIntegral_hahnC _).mul ?_
  have hk : ((3 : ℕ) : ℤ) * ((n : ℤ) * 4 * (Nat.card (Q Γ) : ℤ)) = 12 * ((n * d : ℕ) : ℤ) := by
    rw [Nat.card_eq_fintype_card, ← hd]
    push_cast
    ring
  rw [← pow_mul]
  exact levelOne_isIntegral (n * d) (Mform G (i : ℂ)) hk

end Engine

section GformPart

open Matrix.SpecialLinearGroup CongruenceSubgroup

variable (N : ℕ)

theorem conj_T_pow_mem_Gamma0 (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ Gamma0 N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have hconj : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ Gamma N :=
    (Gamma_normal N).conj_mem _ hT γ
  rw [Gamma_mem] at hconj
  rw [Gamma0_mem]
  exact hconj.2.2.1

theorem mapGL_T_zpow (m : ℤ) :
    (mapGL ℝ (ModularGroup.T ^ m) : GL (Fin 2) ℝ) = Matrix.GeneralLinearGroup.upperRightHom (m : ℝ) := by
  rw [Units.ext_iff, mapGL_coe_matrix, map_apply_coe, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem natCast_mem_strictPeriods_conj (γ : SL(2, ℤ)) :
    (N : ℝ) ∈ (ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹ •
      (Gamma0 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  refine ⟨γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹, conj_T_pow_mem_Gamma0 N γ, ?_⟩
  rw [map_mul, map_mul, map_inv, mapGL_T_zpow, Int.cast_natCast]
  rfl

example [NeZero N] : ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).IsArithmetic :=
  inferInstance

theorem one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem pow_slash (k : ℤ) (γ : SL(2, ℤ)) (F : ℍ → ℂ) :
    ∀ m : ℕ, (F ^ m) ∣[(m : ℤ) * k] γ = (F ∣[k] γ) ^ m
  | 0 => by simpa using ModularForm.is_invariant_one γ
  | m + 1 => by
    have h : ((m + 1 : ℕ) : ℤ) * k = (m : ℤ) * k + k := by push_cast; ring
    rw [h, pow_succ, ModularForm.mul_slash_SL2, pow_slash k γ F m, pow_succ]

variable [NeZero N]

omit [NeZero N] in

theorem num_slash (m : ℕ) (f : CuspForm (Gamma0 N) (2 * (m : ℤ))) (γ : SL(2, ℤ)) :
    (fun τ ↦ f τ ^ (2 * N) * E₄ τ ^ 3) ∣[((2 * N : ℕ) : ℤ) * (2 * (m : ℤ)) + ((3 : ℕ) : ℤ) * 4] γ =
      fun τ ↦ ((f : ℍ → ℂ) ∣[(2 * (m : ℤ))] γ) τ ^ (2 * N) * E₄ τ ^ 3 := by
  have h1 : (fun τ ↦ f τ ^ (2 * N) * E₄ τ ^ 3) = (⇑f) ^ (2 * N) * (⇑E₄) ^ 3 := rfl
  rw [h1, ModularForm.mul_slash_SL2, pow_slash, pow_slash]
  have hE : (⇑E₄) ∣[(4 : ℤ)] γ = ⇑E₄ := by
    have := SlashInvariantForm.slash_action_eqn E₄ (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
    simpa [ModularForm.SL_slash] using this
  rw [hE]
  rfl

def Gform (m : ℕ) (f : CuspForm (Gamma0 N) (2 * (m : ℤ))) :
    ModularForm (Gamma0 N) (((2 * N : ℕ) : ℤ) * (2 * (m : ℤ)) + ((3 : ℕ) : ℤ) * 4 - 12) where
  toFun τ := f τ ^ (2 * N) * E₄ τ ^ 3 / Δ τ
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    change ((fun τ ↦ f τ ^ (2 * N) * E₄ τ ^ 3) / Δ) ∣[_] (γ : GL (Fin 2) ℝ) = _
    rw [← ModularForm.SL_slash, ModularForm.div_slash_SL2, num_slash N m]
    have hΔ : (Δ : ℍ → ℂ) ∣[(12 : ℤ)] γ = Δ := by
      have := SlashInvariantForm.slash_action_eqn CuspForm.discriminant (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
      simpa [ModularForm.SL_slash] using this
    have hf : (⇑f) ∣[(2 * (m : ℤ))] γ = ⇑f := by
      have := SlashInvariantForm.slash_action_eqn f (γ : GL (Fin 2) ℝ) ⟨γ, hγ, rfl⟩
      simpa [ModularForm.SL_slash] using this
    rw [hΔ, hf]
    rfl
  holo' := by
    have h1 : MDiff (fun τ : ℍ ↦ f τ ^ (2 * N) * E₄ τ ^ 3) :=
      (f.holo'.pow _).mul (E₄.holo'.pow _)
    exact h1.div CuspForm.discriminant.holo' discriminant_ne_zero
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    change IsBoundedAtImInfty (((fun τ ↦ f τ ^ (2 * N) * E₄ τ ^ 3) / Δ) ∣[_] γ)
    rw [ModularForm.div_slash_SL2, num_slash N m]
    have hΔ : (Δ : ℍ → ℂ) ∣[(12 : ℤ)] γ = Δ := by
      have := SlashInvariantForm.slash_action_eqn CuspForm.discriminant (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
      simpa [ModularForm.SL_slash] using this
    rw [hΔ, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    refine (Asymptotics.div_isBoundedUnder_of_isBigO ?_).isBigO_one ℝ

    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hF := CuspFormClass.exp_decay_atImInfty (CuspForm.translate f (γ : GL (Fin 2) ℝ)) hN
      (natCast_mem_strictPeriods_conj N γ)
    have hF' : (fun τ ↦ ((f : ℍ → ℂ) ∣[(2 * (m : ℤ))] γ) τ ^ (2 * N)) =O[atImInfty]
        fun τ ↦ Real.exp (-2 * Real.pi * τ.im / N) ^ (2 * N) := by
      have := hF.pow (2 * N)
      (first | exact this | simpa [CuspForm.coe_translate, ModularForm.SL_slash] using this | (have h__ := this; simp [CuspForm.coe_translate, ModularForm.SL_slash] at h__; exact h__))
    have hE0 : (⇑E₄) =O[atImInfty] (1 : ℍ → ℝ) := ModularFormClass.bdd_at_infty E₄
    have hE : (fun τ ↦ E₄ τ ^ 3) =O[atImInfty] fun _ : ℍ ↦ (1 : ℝ) := by
      have := hE0.pow 3
      simp only [Pi.one_apply, one_pow] at this
      exact this
    have h3 := hF'.mul hE
    refine h3.trans ?_
    refine Asymptotics.IsBigO.trans ?_ exp_isBigO_discriminant
    simp only [mul_one]
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with τ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hτ : 0 ≤ τ.im := τ.im_pos.le
    have : ((2 * N : ℕ) : ℝ) * (-2 * Real.pi * τ.im / N) = - 2 * (2 * Real.pi * τ.im) := by
      have hN' : (N : ℝ) ≠ 0 := hN.ne'
      field_simp
      push_cast
      ring
    rw [this]
    nlinarith [Real.pi_pos]

end GformPart

section Glue

open CongruenceSubgroup

variable (N : ℕ) [NeZero N]

theorem An_Δ : An Δ := An.of_mf CuspForm.discriminant one_mem_strictPeriods_SL

theorem qL_E4_cube_sub_E6_sq : qL ⇑E₄ ^ 3 - qL ⇑E₆ ^ 2 = 1728 * qL Δ := by
  have hfun : (⇑E₄) ^ 3 - (⇑E₆) ^ 2 = (1728 : ℂ) • (Δ : ℍ → ℂ) := by
    ext z
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have hA4 : An ⇑E₄ := An.of_mf E₄ one_mem_strictPeriods_SL
  have hA6 : An ⇑E₆ := An.of_mf E₆ one_mem_strictPeriods_SL
  have h := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) (congrArg (qExpansion 1) hfun)
  rw [qExpansion_sub (hA4.pow 3) (hA6.pow 2), qExpansion_pow' hA4, qExpansion_pow' hA6,
    qExpansion_smul An_Δ, map_sub, map_pow, map_pow, PowerSeries.coe_smul,
    ← HahnSeries.C_mul_eq_smul, map_ofNat] at h
  exact h

theorem qL_Gform_mul (m : ℕ) (f : CuspForm (Gamma0 N) (2 * (m : ℤ))) :
    qL ⇑(Gform N m f) * qL Δ = qL ⇑f ^ (2 * N) * qL ⇑E₄ ^ 3 := by
  have hfun : (⇑(Gform N m f)) * (Δ : ℍ → ℂ) = (⇑f) ^ (2 * N) * (⇑E₄) ^ 3 := by
    ext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    show f τ ^ (2 * N) * E₄ τ ^ 3 / Δ τ * Δ τ = _
    exact div_mul_cancel₀ _ (discriminant_ne_zero τ)
  have hG : An ⇑(Gform N m f) := An.of_mf (Gform N m f) (one_mem_strictPeriods_Gamma0 N)
  have hf : An ⇑f := An.of_mf f (one_mem_strictPeriods_Gamma0 N)
  have hE : An ⇑E₄ := An.of_mf E₄ one_mem_strictPeriods_SL
  have h := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) (congrArg (qExpansion 1) hfun)
  rw [qExpansion_mul hG An_Δ, qExpansion_mul (hf.pow _) (hE.pow _), qExpansion_pow' hf,
    qExpansion_pow' hE, map_mul, map_mul, map_pow, map_pow] at h
  exact h

p2m_open "ModularCurve~coeffEmb_jq"

theorem thetaL_coeff' {L : Type*} [Field L] (x : LaurentSeries L) (m : ℤ) :
    (thetaL L x).coeff m = (m : L) * x.coeff m := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem coeffMap_thetaL {L₁ L₂ : Type*} [Field L₁] [Field L₂] (σ : L₁ →+* L₂)
    (x : LaurentSeries L₁) :
    coeffMap σ (thetaL L₁ x) = thetaL L₂ (coeffMap σ x) := by
  ext m
  simp only [coeffMap_coeff, thetaL_coeff', map_mul, map_intCast]

theorem coeffEmb_jq : coeffEmb ℂ jq = qL ⇑E₄ ^ 3 / qL Δ := by
  have h := ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant
  rw [← map_jqModC (algebraMap ℚ ℂ), jqModC_rat] at h
  exact h

theorem thetaL_coeffEmb_jq_mul :
    thetaL ℂ (coeffEmb ℂ jq) * qL Δ = -(qL ⇑E₄ ^ 2 * qL ⇑E₆) := by
  have h := omegaRow_T2
  rw [coeffMap_thetaL] at h
  exact h

theorem field_identity_m {K : Type*} [Field K] (N m : ℕ) (F E S D θ Y j G : K) (hE : E ≠ 0)
    (hS : S ≠ 0) (hD : D ≠ 0) (hθ : θ * D = -(E ^ 2 * S)) (hY : Y * θ ^ m = F)
    (hj : j = E ^ 3 / D) (hES : E ^ 3 - S ^ 2 = 1728 * D) (hG : G * D = F ^ (2 * N) * E ^ 3) :
    Y ^ (2 * N) * j ^ (m * N + 1) * (j - 1728) ^ (m * N) = G / E ^ (m * N) := by
  have hθ' : θ = -(E ^ 2 * S) / D := by rw [eq_div_iff hD, hθ]
  have hθne : θ ≠ 0 := by
    rw [hθ']
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hE) hS)) hD
  have hY' : Y = F / θ ^ m := by rw [eq_div_iff (pow_ne_zero _ hθne), hY]
  have hj' : j - 1728 = S ^ 2 / D := by
    rw [hj, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    linear_combination hES
  have hθ2 : θ ^ 2 = E ^ 4 * S ^ 2 / D ^ 2 := by rw [hθ']; field_simp
  have h2 : Y ^ 2 * j ^ m * (j - 1728) ^ m = F ^ 2 / E ^ m := by
    have : Y ^ 2 = F ^ 2 / (θ ^ 2) ^ m := by rw [hY', div_pow, ← pow_mul, ← pow_mul, mul_comm m 2]
    rw [this, hj', hj, hθ2]
    field_simp
    ring
  have hG' : G = F ^ (2 * N) * E ^ 3 / D := by rw [eq_div_iff hD, hG]
  calc Y ^ (2 * N) * j ^ (m * N + 1) * (j - 1728) ^ (m * N)
      = (Y ^ 2 * j ^ m * (j - 1728) ^ m) ^ N * j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, pow_succ]; ring
    _ = (F ^ 2 / E ^ m) ^ N * (E ^ 3 / D) := by rw [h2, hj]
    _ = G / E ^ (m * N) := by
        rw [hG', div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, div_div, mul_comm D (E ^ (m * N)),
          mul_comm 2 N]

omit [NeZero N] in
theorem weight_eq_m (m : ℕ) : ((2 * N : ℕ) : ℤ) * (2 * (m : ℤ)) + ((3 : ℕ) : ℤ) * 4 - 12 = ((m * N : ℕ) : ℤ) * 4 := by
  push_cast
  ring

theorem target_m (m : ℕ) (f : CuspForm (Gamma0 N) (2 * (m : ℤ))) (Y : LaurentSeries ℂ)
    (hY : Y * thetaL ℂ (coeffEmb ℂ jq) ^ m =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({(coeffEmb ℂ jq)⁻¹} : Set (LaurentSeries ℂ)))
      (Y ^ (2 * N) * coeffEmb ℂ jq ^ (m * N + 1) * (coeffEmb ℂ jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * N)) := by
  rw [map_ofNat]
  have hprod : Y ^ (2 * N) * coeffEmb ℂ jq ^ (m * N + 1) * (coeffEmb ℂ jq - 1728) ^ (m * N) =
      qL ⇑((Gform N m f).mcast (weight_eq_m N m)) / qL ⇑E₄ ^ (m * N) :=
    field_identity_m N m (qL ⇑f) (qL ⇑E₄) (qL ⇑E₆) (qL Δ) (thetaL ℂ (coeffEmb ℂ jq)) Y
      (coeffEmb ℂ jq) _ qL_E4_ne_zero qL_E6_ne_zero qL_Δ_ne_zero (thetaL_coeffEmb_jq_mul) hY
      coeffEmb_jq qL_E4_cube_sub_E6_sq (qL_Gform_mul N m f)
  have hinv : (coeffEmb ℂ jq)⁻¹ = xL := by
    rw [coeffEmb_jq, inv_div]
    rfl
  rw [hprod, hinv]
  exact engine ((Gform N m f).mcast (weight_eq_m N m)) (one_mem_strictPeriods_Gamma0 N)

end Glue

end IsIntegralAdjoinCoeffEmbJqInvSol
p2m_reactivate "P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion.IsIntegralAdjoinCoeffEmbJqInvSol"

end Helpers
p2m_reactivate "P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion.IsIntegralAdjoinCoeffEmbJqInvSol"

p2m_open "UpperHalfPlane ModularCurve~coeffEmb_jq"

theorem solution (N : ℕ) [NeZero N] (m : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ))) (Y : LaurentSeries ℂ)
    (hY : Y * thetaL ℂ (coeffEmb ℂ jq) ^ m =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({(coeffEmb ℂ jq)⁻¹} : Set (LaurentSeries ℂ)))
      (Y ^ (2 * N) * coeffEmb ℂ jq ^ (m * N + 1) * (coeffEmb ℂ jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * N)) :=
  IsIntegralAdjoinCoeffEmbJqInvSol.target_m N m f Y hY

end
end S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion (solution)
