-- Prove2me | solution 1 for ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/43998ce8-8fb5-5857-a80d-aa9cced04059

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
import Theorems.Thm_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
import Theorems.Thm_ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ChartMemNorm

open ModularForm UpperHalfPlane SlashInvariantForm Polynomial

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

abbrev Cos (Γ : Subgroup SL(2, ℤ)) : Type := ↥𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ

noncomputable scoped instance : Fintype (Cos Γ) := Fintype.ofFinite _

theorem card_cos_eq_index : Nat.card (Cos Γ) = Γ.index := by
  rw [← Subgroup.index, ← Subgroup.relIndex, MonoidHom.range_eq_map,
    show ((Γ : Subgroup (GL (Fin 2) ℝ))) = Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ) from rfl,
    Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]

section Linear

variable (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)

theorem quotientFunc_smul_sub (c : ℂ) (q : (Cos Γ)) :
    quotientFunc (c • g - f) q = c • quotientFunc g q - quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    simp only [quotientFunc_mk]
    obtain ⟨γ, hγ⟩ := r.2
    have hr : (r.val)⁻¹ = ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by rw [← hγ, ← map_inv]; rfl
    rw [hr, ← ModularForm.SL_slash, ← ModularForm.SL_slash, ← ModularForm.SL_slash,
      ModularForm.coe_sub, IsGLPos.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.SL_smul_slash, sub_eq_add_neg]

theorem norm_smul_sub_apply (c : ℂ) (τ : ℍ) :
    (ModularForm.norm 𝒮ℒ (c • g - f)) τ = ∏ q : (Cos Γ), (c * quotientFunc g q τ - quotientFunc f q τ) := by
  have h := ModularForm.coe_norm 𝒮ℒ (c • g - f)
  rw [h]
  rw [Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  rw [quotientFunc_smul_sub]
  simp

noncomputable def charPolyAt (τ : ℍ) : ℂ[X] :=
  ∏ q : (Cos Γ), (C (quotientFunc g q τ) * X - C (quotientFunc f q τ))

theorem eval_charPolyAt (c : ℂ) (τ : ℍ) :
    (charPolyAt f g τ).eval c = (ModularForm.norm 𝒮ℒ (c • g - f)) τ := by
  rw [norm_smul_sub_apply, charPolyAt, eval_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

theorem natDegree_linear_le (a b : ℂ) : (C a * X - C b).natDegree ≤ 1 := by
  refine (natDegree_sub_le _ _).trans ?_
  rw [max_le_iff]
  exact ⟨(natDegree_C_mul_le _ _).trans natDegree_X_le, (natDegree_C b).le.trans zero_le_one⟩

theorem card_cos : (Finset.univ : Finset (Cos Γ)).card = Nat.card (Cos Γ) := by
  rw [Nat.card_eq_fintype_card, Finset.card_univ]

theorem natDegree_charPolyAt_le (τ : ℍ) : (charPolyAt f g τ).natDegree ≤ Nat.card (Cos Γ) := by
  rw [charPolyAt]
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ => natDegree_linear_le
    (quotientFunc g q τ) (quotientFunc f q τ)).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one, card_cos]

def node (n : ℕ) (j : Fin (n + 1)) : ℂ := (j : ℕ)

theorem node_injOn (n : ℕ) : Set.InjOn (node n) (Finset.univ : Finset (Fin (n + 1))) := by
  intro i _ j _ h
  simp only [node, Nat.cast_inj] at h
  exact Fin.ext h

noncomputable def lag (n : ℕ) (j : Fin (n + 1)) : ℂ[X] :=
  Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) (node n) j

theorem charPolyAt_eq_sum (τ : ℍ) :
    charPolyAt f g τ = ∑ j : Fin (Nat.card (Cos Γ) + 1),
      C ((ModularForm.norm 𝒮ℒ ((node _ j) • g - f)) τ) * lag (Nat.card (Cos Γ)) j := by
  classical
  have hdeg : (charPolyAt f g τ).degree < (Finset.univ : Finset (Fin (Nat.card (Cos Γ) + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    exact_mod_cast Nat.lt_succ_of_le (natDegree_charPolyAt_le f g τ)
  have h := Lagrange.eq_interpolate (f := charPolyAt f g τ) (node_injOn (Nat.card (Cos Γ))) hdeg
  rw [h, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_charPolyAt]
  rfl

noncomputable def coeffForm (i : ℕ) : ModularForm 𝒮ℒ (k * Nat.card (Cos Γ)) :=
  ∑ j : Fin (Nat.card (Cos Γ) + 1), ((lag (Nat.card (Cos Γ)) j).coeff i) • ModularForm.norm 𝒮ℒ ((node _ j) • g - f)

omit [Γ.FiniteIndex] in
theorem coe_finset_sum {ι : Type*} {k' : ℤ} (s : Finset ι) (F : ι → ModularForm 𝒮ℒ k') :
    ((∑ i ∈ s, F i : ModularForm 𝒮ℒ k') : ℍ → ℂ) = ∑ i ∈ s, (F i : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm 𝒮ℒ k') UpperHalfPlane ℂ) F s

theorem coeffForm_apply (i : ℕ) (τ : ℍ) : coeffForm f g i τ = (charPolyAt f g τ).coeff i := by
  rw [coeffForm, coe_finset_sum, Finset.sum_apply, charPolyAt_eq_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [IsGLPos.smul_apply, coeff_C_mul, smul_eq_mul, mul_comm]

end Linear

end ChartMemNorm
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial

section Nice

variable (N : ℕ) [NeZero N]

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

theorem natCast_mem_strictPeriods_SL : ((N : ℕ) : ℝ) ∈ (𝒮ℒ).strictPeriods := by
  simpa using nsmul_mem one_mem_strictPeriods_SL N

def Nice (F : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction (N : ℝ) F) 0

variable {N}

theorem Nice.mul {F G : ℍ → ℂ} (hF : Nice N F) (hG : Nice N G) : Nice N (F * G) := by
  unfold Nice at *
  rw [cuspFunction_mul hF.continuousAt hG.continuousAt]
  exact hF.mul hG

theorem Nice.add {F G : ℍ → ℂ} (hF : Nice N F) (hG : Nice N G) : Nice N (F + G) := by
  unfold Nice at *
  rw [cuspFunction_add hF.continuousAt hG.continuousAt]
  exact hF.add hG

theorem Nice.neg {F : ℍ → ℂ} (hF : Nice N F) : Nice N (-F) := by
  unfold Nice at *
  rw [cuspFunction_neg hF.continuousAt]
  exact hF.neg

variable (N) in
theorem nice_one : Nice N (1 : ℍ → ℂ) := by
  have : (1 : ℍ → ℂ) = ⇑(1 : ModularForm 𝒮ℒ 0) := rfl
  unfold Nice; rw [this]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ (natCast_pos N) (natCast_mem_strictPeriods_SL N)

variable (N) in
theorem nice_zero : Nice N (0 : ℍ → ℂ) := by
  have : (0 : ℍ → ℂ) = ⇑(0 : ModularForm 𝒮ℒ 0) := rfl
  unfold Nice; rw [this]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ (natCast_pos N) (natCast_mem_strictPeriods_SL N)

variable (N)

def niceSubring : Subring (ℍ → ℂ) where
  carrier := {F | Nice N F}
  mul_mem' := Nice.mul
  one_mem' := nice_one N
  add_mem' := Nice.add
  zero_mem' := nice_zero N
  neg_mem' := Nice.neg

def qExpHom : ↥(niceSubring N) →+* LaurentSeries ℂ where
  toFun F := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (N : ℝ) (F : ℍ → ℂ))
  map_one' := by
    show HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (N : ℝ) (1 : ℍ → ℂ)) = 1
    rw [qExpansion_one, map_one]
  map_mul' F G := by
    show HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (N : ℝ) ((F : ℍ → ℂ) * (G : ℍ → ℂ))) = _
    rw [qExpansion_mul F.2 G.2, map_mul]
  map_zero' := by
    show HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (N : ℝ) (0 : ℍ → ℂ)) = 0
    rw [qExpansion_zero, map_zero]
  map_add' F G := by
    show HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (N : ℝ) ((F : ℍ → ℂ) + (G : ℍ → ℂ))) = _
    rw [qExpansion_add F.2 G.2, map_add]

theorem qExpHom_apply (F : ↥(niceSubring N)) :
    qExpHom N F = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (N : ℝ) (F : ℍ → ℂ)) := rfl

end Nice
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

section Conj

open ConjAct Pointwise CongruenceSubgroup

variable (M : ℕ) [NeZero M]

theorem mapGL_T :
    (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ModularGroup.T =
      Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem mapGL_T_zpow :
    (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (ModularGroup.T ^ (M : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (M : ℝ) := by
  rw [zpow_natCast, map_pow, mapGL_T, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one]

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods_Gamma1 :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, ← mapGL_T]
  exact Subgroup.mem_map_of_mem _ (T_mem_Gamma1 M)

theorem natCast_mem_strictPeriods_Gamma1 :
    (M : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simpa using nsmul_mem (one_mem_strictPeriods_Gamma1 M) M

theorem T_zpow_mem_Gamma1 : ModularGroup.T ^ (M : ℤ) ∈ Gamma1 M := by
  have h := ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
  rw [Int.natAbs_natCast] at h
  rw [Gamma_mem] at h
  rw [Gamma1_mem]
  exact ⟨h.1, h.2.2.2, h.2.2.1⟩

theorem conj_T_zpow_mem_Gamma1 (r : SL(2, ℤ)) : r⁻¹ * ModularGroup.T ^ (M : ℤ) * r ∈ Gamma1 M := by
  have hT : ModularGroup.T ^ (M : ℤ) ∈ Gamma M := by
    have h := ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
    rwa [Int.natAbs_natCast] at h
  have hconj : r⁻¹ * ModularGroup.T ^ (M : ℤ) * r ∈ Gamma M := by
    have := (Gamma_normal M).conj_mem _ hT r⁻¹
    rwa [inv_inv] at this
  rw [Gamma_mem] at hconj
  rw [Gamma1_mem]
  exact ⟨hconj.1, hconj.2.2.2, hconj.2.2.1⟩

theorem natCast_mem_strictPeriods_conj (r : ↥𝒮ℒ) :
    (M : ℝ) ∈ (toConjAct (r : GL (Fin 2) ℝ) • ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  obtain ⟨r', hr'⟩ := r.2
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv,
    toConjAct_smul, inv_inv, ← hr', ← mapGL_T_zpow M, ← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ (conj_T_zpow_mem_Gamma1 M r')

variable {M}
variable {k : ℤ} (g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)

theorem nice_slash (r : ↥𝒮ℒ) : Nice M ((g : ℍ → ℂ) ∣[k] (r : GL (Fin 2) ℝ)⁻¹) := by
  have h := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate g (r : GL (Fin 2) ℝ)⁻¹)
    (natCast_pos M) (by rw [inv_inv]; exact natCast_mem_strictPeriods_conj M r)
  unfold Nice
  rw [show ((g : ℍ → ℂ) ∣[k] (r : GL (Fin 2) ℝ)⁻¹) =
    ⇑(ModularForm.translate g (r : GL (Fin 2) ℝ)⁻¹) from (SlashInvariantForm.coe_translate g _).symm]
  exact h

theorem nice_quotientFunc (q : ChartMemNorm.Cos (Gamma1 M)) : Nice M (SlashInvariantForm.quotientFunc g q) := by
  induction q using Quotient.inductionOn with
  | h r => rw [SlashInvariantForm.quotientFunc_mk]; exact nice_slash g r

theorem nice_self : Nice M (g : ℍ → ℂ) :=
  ModularFormClass.analyticAt_cuspFunction_zero g (natCast_pos M) (natCast_mem_strictPeriods_Gamma1 M)

end Conj
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

end ChartMemAsm
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial CongruenceSubgroup SlashInvariantForm ChartMemNorm

section Setup

variable (M : ℕ) [NeZero M] (k : ℕ)

theorem gamma1_le_SL : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

noncomputable def deltaPow : ModularForm 𝒮ℒ (12 * (k : ℤ)) :=
  ((ModularFormClass.modularForm (CuspForm.discriminant)).pow k).mcast (by ring)

noncomputable def g₀ : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (12 * (k : ℤ)) :=
  restrictForm (gamma1_le_SL M) (deltaPow k)

variable {M k}
variable (g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))

noncomputable def f₀ : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (12 * (k : ℤ)) :=
  (g.pow 12).mcast (by push_cast; ring)

theorem coe_f₀ : (f₀ g : ℍ → ℂ) = (g : ℍ → ℂ) ^ 12 := by
  rw [f₀, coe_mcast, ModularForm.coe_pow]

theorem coe_g₀ : (g₀ M k : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) ^ k := by
  rw [g₀, coe_restrictForm, deltaPow, coe_mcast, ModularForm.coe_pow]; rfl

theorem pow_slash (F : ℍ → ℂ) (k' : ℤ) (A : SL(2, ℤ)) :
    ∀ n : ℕ, (F ^ n) ∣[(n : ℤ) * k'] A = (F ∣[k'] A) ^ n
  | 0 => by
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact ModularForm.is_invariant_one A
  | n + 1 => by
      rw [pow_succ, pow_succ, show ((n + 1 : ℕ) : ℤ) * k' = (n : ℤ) * k' + k' by push_cast; ring,
        ModularForm.mul_slash_SL2, pow_slash F k' A n]

theorem quotientFunc_g₀ (q : Cos (Gamma1 M)) : quotientFunc (g₀ M k) q = (g₀ M k : ℍ → ℂ) := by
  induction q using Quotient.inductionOn with
  | h r =>
    rw [quotientFunc_mk, g₀, coe_restrictForm]
    exact SlashInvariantFormClass.slash_action_eq (deltaPow k) _ (inv_mem r.2)

theorem quotientFunc_f₀ (q : Cos (Gamma1 M)) : quotientFunc (f₀ g) q = quotientFunc g q ^ 12 := by
  induction q using Quotient.inductionOn with
  | h r =>
    rw [quotientFunc_mk, quotientFunc_mk, coe_f₀]
    obtain ⟨γ, hγ⟩ := r.2
    have hr : (r.val)⁻¹ = ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by rw [← hγ, ← map_inv]; rfl
    rw [hr, ← ModularForm.SL_slash, ← ModularForm.SL_slash,
      show (12 * (k : ℤ)) = ((12 : ℕ) : ℤ) * (k : ℤ) by push_cast; ring]
    exact pow_slash _ _ _ 12

theorem quotientFunc_one {k' : ℤ} (F : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k') :
    quotientFunc F (QuotientGroup.mk (1 : ↥𝒮ℒ) : Cos (Gamma1 M)) = (F : ℍ → ℂ) := by
  rw [show (QuotientGroup.mk (1 : ↥𝒮ℒ) : Cos (Gamma1 M)) = ⟦(1 : ↥𝒮ℒ)⟧ from rfl, quotientFunc_mk]
  simp only [OneMemClass.coe_one, inv_one, SlashAction.slash_one]

noncomputable def dN : ↥(niceSubring M) := ⟨(g₀ M k : ℍ → ℂ), nice_self (g₀ M k)⟩

noncomputable def FN (q : Cos (Gamma1 M)) : ↥(niceSubring M) := ⟨quotientFunc (f₀ g) q, nice_quotientFunc (f₀ g) q⟩

noncomputable def GN (q : Cos (Gamma1 M)) : ↥(niceSubring M) := ⟨quotientFunc g q, nice_quotientFunc g q⟩

theorem FN_eq_GN_pow (q : Cos (Gamma1 M)) : FN g q = GN g q ^ 12 :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact quotientFunc_f₀ g q)

noncomputable def Q : Polynomial ↥(niceSubring M) := ∏ q : Cos (Gamma1 M), (C (dN (M := M) (k := k)) * X - C (FN g q))

noncomputable def Qt : Polynomial ↥(niceSubring M) := ∏ q : Cos (Gamma1 M), (X - C (FN g q))

theorem Qt_monic : (Qt g).Monic := monic_prod_of_monic _ _ fun q _ => monic_X_sub_C _

theorem Qt_natDegree : (Qt g).natDegree = Nat.card (Cos (Gamma1 M)) := by
  rw [Qt, natDegree_prod_of_monic _ _ fun q _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, card_cos]

theorem Q_eq_Qt_comp : Q g = (Qt g).comp (C (dN (M := M) (k := k)) * X) := by
  rw [Q, Qt, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [sub_comp, X_comp, C_comp]

theorem coeff_comp_C_mul_X {R : Type*} [CommRing R] (p : Polynomial R) (a : R) (i : ℕ) :
    (p.comp (C a * X)).coeff i = a ^ i * p.coeff i := by
  rw [comp_eq_sum_left, sum_def, finsetSum_coeff]
  simp_rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · ring
  · rw [notMem_support_iff.mp h, mul_zero]

theorem Q_coeff (i : ℕ) : (Q g).coeff i = dN (M := M) (k := k) ^ i * (Qt g).coeff i := by
  rw [Q_eq_Qt_comp, coeff_comp_C_mul_X]

theorem Qt_eval_FN_one : (Qt g).eval (FN g (QuotientGroup.mk (1 : ↥𝒮ℒ))) = 0 := by
  rw [Qt, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk (1 : ↥𝒮ℒ))) (by simp)

theorem coe_FN_one : ((FN g (QuotientGroup.mk (1 : ↥𝒮ℒ)) : ↥(niceSubring M)) : ℍ → ℂ) = (f₀ g : ℍ → ℂ) :=
  quotientFunc_one (f₀ g)

noncomputable def evN (τ : ℍ) : ↥(niceSubring M) →+* ℂ := (Pi.evalRingHom (fun _ : ℍ => ℂ) τ).comp (niceSubring M).subtype

theorem evN_apply (τ : ℍ) (F : ↥(niceSubring M)) : evN (M := M) τ F = (F : ℍ → ℂ) τ := rfl

theorem Q_map_evN (τ : ℍ) : (Q g).map (evN τ) = charPolyAt (f₀ g) (g₀ M k) τ := by
  rw [Q, Polynomial.map_prod, charPolyAt]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, map_C, evN_apply, evN_apply, quotientFunc_g₀]
  rfl

theorem coe_Q_coeff (i : ℕ) : (((Q g).coeff i : ↥(niceSubring M)) : ℍ → ℂ) = ⇑(coeffForm (f₀ g) (g₀ M k) i) := by
  funext τ
  rw [coeffForm_apply, ← Q_map_evN g τ, coeff_map, evN_apply]

end Setup
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

end ChartMemAsm
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial CongruenceSubgroup SlashInvariantForm ChartMemNorm HahnSeries

section LaurentFacts

variable (K : Type*) [Field K]

theorem intSeriesC_pow (q : PowerSeries ℤ) (n : ℕ) : intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_X : intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
  rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem laurentMap_ofPowerSeries_int (q : PowerSeries ℤ) :
    laurentMap (Int.castRingHom K) (HahnSeries.ofPowerSeries ℤ ℤ q) = intSeriesC K q := by
  rw [laurentMap_ofPowerSeries]; rfl

def deltaInvInt : LaurentSeries ℤ :=
  HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem intSeriesC_delta_mul_deltaInv :
    intSeriesC K (PowerSeries.X * dedekindEtaUnit) * laurentMap (Int.castRingHom K) deltaInvInt = 1 := by
  rw [deltaInvInt, map_mul, laurentMap_single, map_one, laurentMap_ofPowerSeries_int, intSeriesC_mul,
    intSeriesC_X]
  calc HahnSeries.single (1 : ℤ) (1 : K) * intSeriesC K dedekindEtaUnit *
        (HahnSeries.single (-1 : ℤ) (1 : K) * intSeriesC K dedekindEtaUnitInv)
      = (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.single (-1 : ℤ) (1 : K)) *
          (intSeriesC K dedekindEtaUnit * intSeriesC K dedekindEtaUnitInv) := by ring
    _ = 1 := by
        rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, ← intSeriesC_mul, dedekindEtaUnit_mul_inv,
          intSeriesC_one, mul_one]
        rfl

theorem delta_ne_zero : intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (intSeriesC_delta_mul_deltaInv K)

theorem delta_inv_eq : (intSeriesC K (PowerSeries.X * dedekindEtaUnit))⁻¹ = laurentMap (Int.castRingHom K) deltaInvInt :=
  inv_eq_of_mul_eq_one_right (intSeriesC_delta_mul_deltaInv K)

theorem delta_coeff_one : (intSeriesC K (PowerSeries.X * dedekindEtaUnit)).coeff 1 = 1 := by
  rw [intSeriesC, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnit, map_one]

theorem delta_coeff_of_lt_one {n : ℤ} (hn : n < 1) : (intSeriesC K (PowerSeries.X * dedekindEtaUnit)).coeff n = 0 := by
  rcases lt_or_eq_of_le (show n ≤ 0 by omega) with hneg | rfl
  · exact ofPowerSeries_coeff_of_neg _ hneg
  · rw [intSeriesC, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_X_mul, map_zero]

theorem delta_order : (intSeriesC K (PowerSeries.X * dedekindEtaUnit)).order = 1 := by
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [delta_coeff_one]; exact one_ne_zero)
  · by_contra hlt
    push Not at hlt
    exact (mt HahnSeries.coeff_order_eq_zero.mp (delta_ne_zero K)) (delta_coeff_of_lt_one K hlt)

theorem order_pow' {x : LaurentSeries K} (hx : x ≠ 0) (n : ℕ) : (x ^ n).order = n • x.order := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

theorem order_nonneg_of_coeff_neg {x : LaurentSeries K} (h : ∀ n : ℤ, n < 0 → x.coeff n = 0) : 0 ≤ x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · by_contra hlt
    push Not at hlt
    exact (mt HahnSeries.coeff_order_eq_zero.mp hx) (h _ hlt)

theorem coeff_eq_qExpand_coeff (N : ℕ) [NeZero N] (x : LaurentSeries K) (n : ℤ) :
    x.coeff n = (qExpand K N x).coeff ((N : ℤ) * n) := (qExpand_coeff_mul N x n).symm

end LaurentFacts
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

section IntegralUpToM

variable (M : ℕ) [NeZero M]

def Rint : Subring ℂ :=
  let _ : ℕ := M
  (integralClosure ℤ ℂ).toSubring

theorem mem_Rint_iff {z : ℂ} : z ∈ Rint M ↔ IsIntegral ℤ z := Iff.rfl

theorem intCast_mem_Rint (n : ℤ) : (n : ℂ) ∈ Rint M := intCast_mem _ n

abbrev Tint : Subring (LaurentSeries ℂ) := ModularCurve.CharPReduction.integralCoeffs (Rint M)

theorem laurentMap_int_mem_Tint (z : LaurentSeries ℤ) : laurentMap (Int.castRingHom ℂ) z ∈ Tint M := fun n => by
  rw [laurentMap_coeff, eq_intCast]
  exact intCast_mem _ _

theorem intSeriesC_mem_Tint (q : PowerSeries ℤ) : intSeriesC ℂ q ∈ Tint M := by
  rw [← laurentMap_ofPowerSeries_int]; exact laurentMap_int_mem_Tint M _

theorem delta_inv_mem_Tint : (intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit))⁻¹ ∈ Tint M := by
  rw [delta_inv_eq]; exact laurentMap_int_mem_Tint M _

theorem mem_Tint_of_qExpand_mem {x : LaurentSeries ℂ} (h : qExpand ℂ M x ∈ Tint M) : x ∈ Tint M := fun n => by
  rw [coeff_eq_qExpand_coeff ℂ M x n]; exact h _

end IntegralUpToM
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

section Expansions

variable {M : ℕ} [NeZero M] {k : ℕ}
variable (g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
  (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)

local notation "Δ̂" => intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit)

theorem qExpHom_dN : qExpHom M (dN (M := M) (k := k)) = qExpand ℂ M (Δ̂ ^ k) := by
  rw [qExpHom_apply]
  show HahnSeries.ofPowerSeries ℤ ℂ (qExpansion (M : ℝ) (g₀ M k : ℍ → ℂ)) = _
  rw [ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods (g₀ M k)
    (one_mem_strictPeriods_Gamma1 M) M]
  congr 1
  have h1 : qExpansion 1 (g₀ M k : ℍ → ℂ) = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) ^ k := by
    rw [g₀, coe_restrictForm, deltaPow, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rfl
  rw [h1, ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, map_pow]
  rfl

include hg in

theorem ofPowerSeries_qExpansion_f₀ :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (f₀ g : ℍ → ℂ)) = intSeriesC ℂ (pg ^ 12) := by
  have h1 : qExpansion 1 (f₀ g : ℍ → ℂ) = qExpansion 1 (g : ℍ → ℂ) ^ 12 := by
    rw [f₀, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods_Gamma1 M)]
  unfold IsIntegralQExp at hg
  rw [h1, ← hg, ← map_pow]
  rfl

include hg in

theorem qExpHom_FN_one :
    qExpHom M (FN g (QuotientGroup.mk (1 : ↥𝒮ℒ))) = qExpand ℂ M (intSeriesC ℂ (pg ^ 12)) := by
  rw [qExpHom_apply, coe_FN_one,
    ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods (f₀ g)
      (one_mem_strictPeriods_Gamma1 M) M, ofPowerSeries_qExpansion_f₀ g pg hg]

noncomputable def ehat (i : ℕ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (coeffForm (f₀ g) (g₀ M k) i : ℍ → ℂ))

theorem qExpHom_Q_coeff (i : ℕ) : qExpHom M ((Q g).coeff i) = qExpand ℂ M (ehat g i) := by
  rw [qExpHom_apply, coe_Q_coeff, ehat,
    ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods _ one_mem_strictPeriods_SL M]

noncomputable def Tcoef (i : ℕ) : LaurentSeries ℂ := ehat g i / (Δ̂ ^ k) ^ i

theorem qExpand_ne_zero {x : LaurentSeries ℂ} (hx : x ≠ 0) : qExpand ℂ M x ≠ 0 :=
  fun h => hx (qExpand_injective M (h.trans (map_zero _).symm))

theorem qExpHom_Qt_coeff (i : ℕ) : qExpHom M ((Qt g).coeff i) = qExpand ℂ M (Tcoef g i) := by
  have h := congrArg (qExpHom M) (Q_coeff g i)
  rw [map_mul, map_pow, qExpHom_Q_coeff, qExpHom_dN] at h
  have hD : qExpand ℂ M (Δ̂ ^ k) ^ i ≠ 0 := pow_ne_zero _ (qExpand_ne_zero (pow_ne_zero _ (delta_ne_zero ℂ)))
  rw [Tcoef, map_div₀, map_pow, eq_div_iff hD, mul_comm]
  exact h.symm

include hg in

theorem rel_T :
    ∑ i ∈ Finset.range (Nat.card (Cos (Gamma1 M)) + 1), Tcoef g i * intSeriesC ℂ (pg ^ 12) ^ i = 0 ∧
      Tcoef g (Nat.card (Cos (Gamma1 M))) = 1 := by
  set μ := Nat.card (Cos (Gamma1 M)) with hμ
  have hmon : ((Qt g).map (qExpHom M)).Monic := (Qt_monic g).map _
  have hdeg : ((Qt g).map (qExpHom M)).natDegree = μ := by rw [(Qt_monic g).natDegree_map, Qt_natDegree]
  have hcoef : ∀ i, ((Qt g).map (qExpHom M)).coeff i = qExpand ℂ M (Tcoef g i) := fun i => by
    rw [coeff_map, qExpHom_Qt_coeff]

  have htop : Tcoef g μ = 1 := by
    apply qExpand_injective M
    rw [← hcoef, map_one]
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  refine ⟨?_, htop⟩

  have h0 := congrArg (qExpHom M) (Qt_eval_FN_one g)
  rw [map_zero, ← Polynomial.eval₂_hom, ← eval_map, qExpHom_FN_one g pg hg,
    eval_eq_sum_range' (lt_of_le_of_lt hdeg.le (Nat.lt_succ_self μ))] at h0
  simp_rw [hcoef, ← map_pow, ← map_mul] at h0
  rw [← map_sum] at h0
  exact qExpand_injective M (h0.trans (map_zero _).symm)

noncomputable def Scoef (i : ℕ) : LaurentSeries ℂ := ehat g i / (Δ̂ ^ k) ^ Nat.card (Cos (Gamma1 M))

noncomputable def Yhat : LaurentSeries ℂ := intSeriesC ℂ (pg ^ 12) / Δ̂ ^ k

include hg in

theorem rel_S :
    Yhat (k := k) pg ^ Nat.card (Cos (Gamma1 M)) +
      ∑ i ∈ Finset.range (Nat.card (Cos (Gamma1 M))), Scoef g i * Yhat (k := k) pg ^ i = 0 := by
  set μ := Nat.card (Cos (Gamma1 M)) with hμ
  obtain ⟨hrel, htop⟩ := rel_T g pg hg
  have hD : (Δ̂ : LaurentSeries ℂ) ^ k ≠ 0 := pow_ne_zero _ (delta_ne_zero ℂ)
  have hterm : ∀ i, Scoef g i * Yhat (k := k) pg ^ i = (Tcoef g i * intSeriesC ℂ (pg ^ 12) ^ i) / (Δ̂ ^ k) ^ μ := by
    intro i
    rw [Scoef, Yhat, Tcoef, div_pow, div_mul_div_comm, div_mul_eq_mul_div, div_div, mul_comm ((Δ̂ ^ k) ^ i)]
  have hS : Scoef g μ * Yhat (k := k) pg ^ μ = Yhat (k := k) pg ^ μ := by
    rw [hterm, htop, one_mul, Yhat, div_pow]
  have hsplit := Finset.sum_range_succ (fun i => Scoef g i * Yhat (k := k) pg ^ i) μ
  rw [hS] at hsplit
  rw [add_comm, ← hsplit, Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div, hrel, zero_div]

end Expansions
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

end ChartMemAsm
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial CongruenceSubgroup SlashInvariantForm ChartMemNorm HahnSeries

section Integrality

variable {M : ℕ} [NeZero M] {k : ℕ}
variable (g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
  (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
  (hint : ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
    ((qExpansion (M : ℝ) ((g : ℍ → ℂ) ∣[(k : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n))

local notation "Δ̂" => intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit)
local notation "μ" => Nat.card (Cos (Gamma1 M))

include hint in

theorem qExpHom_GN_mem (q : Cos (Gamma1 M)) : qExpHom M (GN g q) ∈ Tint M := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨r', hr'⟩ := r.2
    have hfun : ((GN g ⟦r⟧ : ↥(niceSubring M)) : ℍ → ℂ) = (g : ℍ → ℂ) ∣[(k : ℤ)] (r'⁻¹ : SL(2, ℤ)) := by
      show quotientFunc g ⟦r⟧ = _
      rw [quotientFunc_mk, show (r.val)⁻¹ = ((r'⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) by rw [← hr', ← map_inv]; rfl,
        ← ModularForm.SL_slash]
    have ha : ∀ n : ℕ, IsIntegral ℤ ((qExpansion (M : ℝ) ((g : ℍ → ℂ) ∣[(k : ℤ)] (r'⁻¹ : SL(2, ℤ)))).coeff n) := by
      intro n
      rw [ModularForm.SL_slash]
      exact hint (r'⁻¹) n
    intro n
    rw [qExpHom_apply, hfun]
    rcases lt_or_ge n 0 with hn | hn
    · rw [ofPowerSeries_coeff_of_neg _ hn]; exact zero_mem _
    · lift n to ℕ using hn
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact ha n

include hint in
theorem qExpHom_FN_mem (q : Cos (Gamma1 M)) : qExpHom M (FN g q) ∈ Tint M := by
  rw [FN_eq_GN_pow, map_pow]; exact pow_mem (qExpHom_GN_mem g hint q) 12

include hint in
theorem qExpHom_Qt_coeff_mem (i : ℕ) : qExpHom M ((Qt g).coeff i) ∈ Tint M := by
  classical
  let t : Cos (Gamma1 M) → ↥(Tint M) := fun q => ⟨qExpHom M (FN g q), qExpHom_FN_mem g hint q⟩
  have hmap : ((∏ q : Cos (Gamma1 M), (X - Polynomial.C (t q))).map (Tint M).subtype) = (Qt g).map (qExpHom M) := by
    rw [Qt, Polynomial.map_prod, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
    rfl
  have h := congrArg (fun p => Polynomial.coeff p i) hmap
  simp only [coeff_map] at h
  rw [← h]
  exact SetLike.coe_mem _

include hint in
theorem Tcoef_mem (i : ℕ) : Tcoef g i ∈ Tint M :=
  mem_Tint_of_qExpand_mem M (by rw [← qExpHom_Qt_coeff]; exact qExpHom_Qt_coeff_mem g hint i)

theorem Tcoef_order_nonneg (i : ℕ) : 0 ≤ (Tcoef g i).order := by
  apply order_nonneg_of_coeff_neg
  intro n hn
  rw [coeff_eq_qExpand_coeff ℂ M (Tcoef g i) n, ← qExpHom_Qt_coeff, qExpHom_apply]
  exact ofPowerSeries_coeff_of_neg _
    (Int.mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)) hn)

theorem Scoef_mul_pow {i : ℕ} (hi : i ≤ μ) : Scoef g i * (Δ̂ ^ k) ^ (μ - i) = Tcoef g i := by
  have hD : (Δ̂ : LaurentSeries ℂ) ^ k ≠ 0 := pow_ne_zero _ (delta_ne_zero ℂ)
  rw [Scoef, Tcoef, div_mul_eq_mul_div, div_eq_div_iff (pow_ne_zero _ hD) (pow_ne_zero _ hD), mul_assoc,
    pow_sub_mul_pow _ hi]

include hint in
theorem Scoef_mem {i : ℕ} (hi : i ≤ μ) : Scoef g i ∈ Tint M := by
  have hD : (Δ̂ : LaurentSeries ℂ) ^ k ≠ 0 := pow_ne_zero _ (delta_ne_zero ℂ)
  have h : Scoef g i = Tcoef g i * (Δ̂⁻¹) ^ (k * (μ - i)) := by
    rw [← Scoef_mul_pow g hi, inv_pow, pow_mul, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hD), mul_one]
  rw [h]
  exact mul_mem (Tcoef_mem g hint i) (pow_mem (delta_inv_mem_Tint M) _)

theorem Scoef_order {i : ℕ} (hi : i ≤ μ) (hS : Scoef g i ≠ 0) : -((k * (μ - i) : ℕ) : ℤ) ≤ (Scoef g i).order := by
  have hD : (Δ̂ : LaurentSeries ℂ) ^ k ≠ 0 := pow_ne_zero _ (delta_ne_zero ℂ)
  have h := Tcoef_order_nonneg (M := M) g i
  rw [← Scoef_mul_pow g hi, HahnSeries.order_mul hS (pow_ne_zero _ hD), order_pow' ℂ hD,
    order_pow' ℂ (delta_ne_zero ℂ), delta_order] at h
  simp only [nsmul_eq_mul, mul_one] at h
  have hc : ((k * (μ - i) : ℕ) : ℤ) = ((μ - i : ℕ) : ℤ) * (k : ℤ) := by push_cast; ring
  rw [hc]
  linarith

include hint in
theorem exists_poly {i : ℕ} (hi : i < μ) :
    ∃ P : Polynomial ℂ, (∀ j, P.coeff j ∈ Rint M) ∧ P.natDegree ≤ k * (μ - i) ∧
      Scoef g i = aeval (jqModC ℂ) P := by
  have hD1 : (Δ̂ : LaurentSeries ℂ) ≠ 0 := delta_ne_zero ℂ
  obtain ⟨P, -, hP⟩ :=
    ModularCurve.exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne (k * μ)
      (by push_cast; ring) (coeffForm (f₀ g) (g₀ M k) i)
  have hS : Scoef g i = aeval (jqModC ℂ) P := by
    rw [Scoef, show ehat g i = _ from hP, intSeriesC_pow, ← pow_mul,
      mul_div_assoc, div_self (pow_ne_zero _ hD1), mul_one]
  have hmem : ∀ n : ℤ, (aeval (jqModC ℂ) P).coeff n ∈ Rint M := by
    rw [← hS]; exact Scoef_mem g hint hi.le
  obtain ⟨hcoef, hord⟩ := ModularCurve.forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem (Rint M) P hmem
  refine ⟨P, hcoef, ?_, hS⟩
  by_cases hd : P.natDegree = 0
  · rw [hd]; exact Nat.zero_le _
  · have hP0 : P ≠ 0 := fun h0 => hd (by rw [h0, natDegree_zero])
    have hordP := hord hP0
    have hne : aeval (jqModC ℂ) P ≠ 0 := by
      intro h0
      rw [h0, HahnSeries.order_zero] at hordP
      omega
    have hbound := Scoef_order g hi.le (by rw [hS]; exact hne)
    rw [hS, hordP] at hbound
    generalize k * (μ - i) = N at hbound ⊢
    omega

end Integrality
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

section Tower

theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap ℂ (LaurentSeries ℂ) (c : ℂ) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
  simp

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem integral_pullback (x y : LaurentSeries ℚ) (n : ℕ) (P : ℕ → Polynomial ℂ)
    (hP : ∀ i < n, ∀ j, IsIntegral ℤ ((P i).coeff j))
    (hrel : (coeffEmb ℂ y) ^ n +
      ∑ i ∈ Finset.range n, aeval (coeffEmb ℂ x) (P i) * (coeffEmb ℂ y) ^ i = 0) :
    (eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) x).IsIntegralElem y := by
  classical
  set ψ : Polynomial ℤ →+* LaurentSeries ℚ := eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) x with hψ
  set ι : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffEmb ℂ with hι_def
  have hι : Function.Injective ι := ι.injective
  set B : Subring (LaurentSeries ℂ) := (ι.comp ψ).range with hB

  have hxB : ι x ∈ B := ⟨X, by simp [hψ]⟩

  have hRint : ∀ z : ℂ, IsIntegral ℤ z → IsIntegral ↥B (algebraMap ℂ (LaurentSeries ℂ) z) := by
    intro z hz
    obtain ⟨p, hp, hpx⟩ := hz
    refine ⟨p.map (algebraMap ℤ ↥B), hp.map _, ?_⟩
    rw [eval₂_map, RingHom.ext_int ((algebraMap ↥B (LaurentSeries ℂ)).comp (algebraMap ℤ ↥B))
      ((algebraMap ℂ (LaurentSeries ℂ)).comp (algebraMap ℤ ℂ)), ← Polynomial.hom_eval₂, hpx, map_zero]

  have hxC : ι x ∈ integralClosure (↥B) (LaurentSeries ℂ) := by
    show IsIntegral ↥B (ι x)
    exact isIntegral_algebraMap (R := ↥B) (x := (⟨ι x, hxB⟩ : ↥B))
  have hPC : ∀ i < n, aeval (ι x) (P i) ∈ integralClosure (↥B) (LaurentSeries ℂ) := by
    intro i hi
    rw [aeval_eq_sum_range]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    exact Subalgebra.mul_mem _ (show IsIntegral ↥B _ from hRint _ (hP i hi j)) (Subalgebra.pow_mem _ hxC j)

  set Cl := integralClosure (↥B) (LaurentSeries ℂ) with hCl
  let c : ℕ → ↥Cl := fun i => if h : i < n then ⟨aeval (ι x) (P i), hPC i h⟩ else 0
  let Pm : Polynomial ↥Cl := X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (c i) * X ^ i
  have hPmm : Pm.Monic := by
    apply monic_X_pow_add
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
    intro i hi
    refine lt_of_le_of_lt (degree_C_mul_X_pow_le i _) ?_
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi)
  have hPmy : eval₂ (algebraMap ↥Cl (LaurentSeries ℂ)) (ι y) Pm = 0 := by
    show eval₂ (algebraMap ↥Cl (LaurentSeries ℂ)) (ι y) (X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (c i) * X ^ i) = 0
    rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum, ← hrel]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [eval₂_mul, eval₂_C, eval₂_X_pow]
    congr 1
    show ((c i : ↥Cl) : LaurentSeries ℂ) = aeval (ι x) (P i)
    simp only [c, dif_pos (Finset.mem_range.mp hi)]
  have hint : IsIntegral ↥Cl (ι y) := ⟨Pm, hPmm, hPmy⟩
  have hintB : IsIntegral ↥B (ι y) := isIntegral_trans (ι y) hint

  obtain ⟨p, hpm, hpy⟩ := hintB
  set θ : Polynomial ℤ →+* ↥B := (ι.comp ψ).rangeRestrict with hθ
  have hθs : Function.Surjective θ := (ι.comp ψ).rangeRestrict_surjective
  obtain ⟨p', hp', -, hp'm⟩ := lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hθs p) hpm
  refine ⟨p', hp'm, hι ?_⟩
  have hcomp : (algebraMap ↥B (LaurentSeries ℂ)).comp θ = ι.comp ψ := RingHom.ext fun _ => rfl
  rw [map_zero, Polynomial.hom_eval₂, ← hcomp, ← eval₂_map, hp']
  exact hpy

end Tower
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

end ChartMemAsm
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

namespace ChartMemAsm

open ModularForm UpperHalfPlane ModularCurve Polynomial CongruenceSubgroup SlashInvariantForm ChartMemNorm HahnSeries

section Main

theorem coeffEmb_intSeriesC (q : PowerSeries ℤ) : coeffEmb ℂ (intSeriesC ℚ q) = intSeriesC ℂ q := by
  ext n
  rw [coeffEmb_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · lift n to ℕ using hn
    rw [intSeriesC, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

theorem coeffEmb_jq : coeffEmb ℂ jq = jqModC ℂ := by
  show (jq).map (algebraMap ℚ ℂ) = jqModC ℂ
  rw [← jqModC_rat]
  exact map_jqModC _

theorem jqModC_complex_ne_zero : jqModC ℂ ≠ 0 := by
  rw [← coeffEmb_jq]
  exact (map_ne_zero (coeffEmb ℂ)).mpr jq_ne_zero

theorem jqModC_mul_delta (K : Type*) [Field K] :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K eisenstein4 ^ 3 := by
  have hj : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * intSeriesC K jNum := rfl
  calc jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit)
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K)) *
          (intSeriesC K jNum * intSeriesC K dedekindEtaUnit) := by
        rw [hj, intSeriesC_mul, intSeriesC_X]; ring
    _ = intSeriesC K (jNum * dedekindEtaUnit) := by
        rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, ← intSeriesC_mul]
        rw [show (HahnSeries.single (0 : ℤ) (1 : K)) = 1 from rfl, one_mul]
    _ = intSeriesC K eisenstein4 ^ 3 := by
        rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, intSeriesC_pow]

theorem eisenstein4_series_ne_zero (K : Type*) [Field K] : intSeriesC K eisenstein4 ≠ 0 := by
  intro h0
  have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
  have h2 := congrArg (PowerSeries.coeff 0) h1
  rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eisenstein4, map_one, map_zero] at h2
  exact one_ne_zero h2

theorem div_delta_pow_mul_jqModC_inv_pow (K : Type*) [Field K] (pg : PowerSeries ℤ) (k : ℕ) :
    intSeriesC K (pg ^ 12) / intSeriesC K ((PowerSeries.X * dedekindEtaUnit) ^ k) * (jqModC K)⁻¹ ^ k =
      intSeriesC K (pg ^ 12) / intSeriesC K (eisenstein4 ^ (3 * k)) := by
  have hD := delta_ne_zero K
  have hE := eisenstein4_series_ne_zero K
  have hjinv : (jqModC K)⁻¹ = intSeriesC K (PowerSeries.X * dedekindEtaUnit) * (intSeriesC K eisenstein4 ^ 3)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, jqModC_mul_delta, mul_inv_cancel₀ (pow_ne_zero _ hE)]
  simp only [intSeriesC_pow]
  rw [hjinv, mul_pow (intSeriesC K (PowerSeries.X * dedekindEtaUnit)) ((intSeriesC K eisenstein4 ^ 3)⁻¹) k,
    inv_pow, ← pow_mul, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
    ← mul_assoc ((intSeriesC K (PowerSeries.X * dedekindEtaUnit) ^ k)⁻¹),
    inv_mul_cancel₀ (pow_ne_zero _ hD), one_mul]

variable (M : ℕ) [NeZero M] (k : ℕ)
  (g : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
  (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
  (hint : ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
    ((qExpansion (M : ℝ) ((g : ℍ → ℂ) ∣[(k : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n))

include hg hint in

theorem chartMem :
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) /
        ModularCurve.intSeriesC ℚ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k)) ∧
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq⁻¹).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) / ModularCurve.intSeriesC ℚ (ModularCurve.eisenstein4 ^ (3 * k))) := by
  classical
  set μ := Nat.card (Cos (Gamma1 M)) with hμ
  have hP : ∀ i, i < μ → ∃ P : Polynomial ℂ, (∀ j, P.coeff j ∈ Rint M) ∧ P.natDegree ≤ k * (μ - i) ∧
      Scoef g i = aeval (jqModC ℂ) P := fun i hi => exists_poly g hint hi
  choose! P hPc hPd hPS using hP
  set y : LaurentSeries ℚ := intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ k) with hy
  have hY : coeffEmb ℂ y = Yhat (k := k) pg := by
    rw [hy, Yhat, map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, intSeriesC_pow, intSeriesC_pow]
  have hrelS := rel_S g pg hg
  have hrel1 : (coeffEmb ℂ y) ^ μ +
      ∑ i ∈ Finset.range μ, aeval (coeffEmb ℂ jq) (P i) * (coeffEmb ℂ y) ^ i = 0 := by
    rw [hY, coeffEmb_jq, ← hrelS]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hPS i (Finset.mem_range.mp hi)]
  refine ⟨integral_pullback jq y μ P (fun i hi j => hPc i hi j) hrel1, ?_⟩

  have hj0 : jqModC ℂ ≠ 0 := jqModC_complex_ne_zero
  set y' : LaurentSeries ℚ := intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ (eisenstein4 ^ (3 * k)) with hy'
  have hyy' : y' = y * (jq⁻¹) ^ k := by
    have h := div_delta_pow_mul_jqModC_inv_pow ℚ pg k
    rw [jqModC_rat] at h
    rw [hy', hy, ← h]
  let P' : ℕ → Polynomial ℂ := fun i => reflect (k * (μ - i)) (P i)
  have hP'c : ∀ i < μ, ∀ j, (P' i).coeff j ∈ Rint M := fun i hi j => by
    show (reflect (k * (μ - i)) (P i)).coeff j ∈ Rint M
    rw [coeff_reflect]; exact hPc i hi _
  have haeval : ∀ i < μ, aeval (jqModC ℂ)⁻¹ (P' i) = aeval (jqModC ℂ) (P i) * ((jqModC ℂ)⁻¹) ^ (k * (μ - i)) := by
    intro i hi
    haveI : Invertible (jqModC ℂ) := invertibleOfNonzero hj0
    have h := eval₂_reflect_mul_pow (algebraMap ℂ (LaurentSeries ℂ)) (jqModC ℂ) (k * (μ - i)) (P i) (hPd i hi)
    rw [invOf_eq_inv] at h
    show eval₂ (algebraMap ℂ (LaurentSeries ℂ)) (jqModC ℂ)⁻¹ (reflect (k * (μ - i)) (P i)) = _
    rw [aeval_def, ← h, mul_assoc, ← mul_pow, mul_inv_cancel₀ hj0, one_pow, mul_one]
  have hw : coeffEmb ℂ (jq⁻¹) = (jqModC ℂ)⁻¹ := by rw [map_inv₀, coeffEmb_jq]
  have hy'c : coeffEmb ℂ y' = Yhat (k := k) pg * ((jqModC ℂ)⁻¹) ^ k := by
    rw [hyy', map_mul, map_pow, map_inv₀, hY, coeffEmb_jq]
  have key : ∀ i ≤ μ, ((jqModC ℂ)⁻¹) ^ (k * (μ - i)) * (Yhat (k := k) pg * ((jqModC ℂ)⁻¹) ^ k) ^ i =
      ((jqModC ℂ)⁻¹) ^ (k * μ) * Yhat (k := k) pg ^ i := by
    intro i hi
    rw [mul_pow, ← pow_mul, mul_comm (Yhat (k := k) pg ^ i), ← mul_assoc, ← _root_.pow_add,
      show k * (μ - i) + k * i = k * μ by rw [← Nat.mul_add, Nat.sub_add_cancel hi]]
  have hrel2 : (coeffEmb ℂ y') ^ μ +
      ∑ i ∈ Finset.range μ, aeval (coeffEmb ℂ (jq⁻¹)) (P' i) * (coeffEmb ℂ y') ^ i = 0 := by
    rw [hw, hy'c]
    have h1 : (Yhat (k := k) pg * ((jqModC ℂ)⁻¹) ^ k) ^ μ = ((jqModC ℂ)⁻¹) ^ (k * μ) * Yhat (k := k) pg ^ μ := by
      have := key μ le_rfl
      rwa [Nat.sub_self, mul_zero, pow_zero, one_mul] at this
    have h2 : ∀ i ∈ Finset.range μ, aeval (jqModC ℂ)⁻¹ (P' i) * (Yhat (k := k) pg * ((jqModC ℂ)⁻¹) ^ k) ^ i =
        ((jqModC ℂ)⁻¹) ^ (k * μ) * (Scoef g i * Yhat (k := k) pg ^ i) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [haeval i hi', ← hPS i hi', mul_assoc, key i hi'.le, ← mul_assoc, ← mul_assoc, mul_comm (Scoef g i)]
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← mul_add, hrelS, mul_zero]
  exact integral_pullback (jq⁻¹) y' μ P' (fun i hi j => hP'c i hi j) hrel2

end Main
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

end ChartMemAsm
p2m_reactivate "P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.ChartMemNorm"

theorem solution
    (M : ℕ) [NeZero M] (k : ℕ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (pg : PowerSeries ℤ) (hg : ModularCurve.IsIntegralQExp g pg)
    (hint : ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
      ((UpperHalfPlane.qExpansion (M : ℝ) ((⇑g : UpperHalfPlane → ℂ) ∣[(k : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n)) :
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) /
        ModularCurve.intSeriesC ℚ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k)) ∧
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq⁻¹).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) / ModularCurve.intSeriesC ℚ (ModularCurve.eisenstein4 ^ (3 * k))) :=
  ChartMemAsm.chartMem M k g pg hg hint

end
end S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
end P2MW
export P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral (solution)
