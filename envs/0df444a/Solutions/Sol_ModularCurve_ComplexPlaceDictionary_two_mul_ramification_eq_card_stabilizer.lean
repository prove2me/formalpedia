-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.two_mul_ramification_eq_card_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d2e45bc5-c8a7-5890-a8ef-a7e73a53009b

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
import Theorems.Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane Filter ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve"
open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary qExpand qExpand_coeff_mul jq coeff_jq_neg_one jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange realize_eq_div jqModC_eq_qExpansion_E4_cube_div_discriminant jqModC jqModC_rat map_jqModC coeffMap_qExpand meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two"
namespace ComplexPlaceDictionary
p2m_export "ModularCurve.ComplexPlaceDictionary" "ramification pt ramification_pos meromorphicOrderAt_realize"
namespace RamificationEqCard
p2m_open "ModularCurve.ComplexPlaceDictionary ModularCurve~coeffEmb_jq"

theorem coe_mul_GL (γ δ : SL(2, ℤ)) :
    ((γ * δ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * δ := by
  simp only [map_mul]

theorem denom_mul_of_smul_eq (γ δ : SL(2, ℤ)) (τ : ℍ) (hδ : δ • τ = τ) :
    denom ((γ * δ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = denom γ τ * denom δ τ := by
  have h := denom_cocycle (γ : GL (Fin 2) ℝ) (δ : GL (Fin 2) ℝ) τ.im_ne_zero
  have h2 : ((δ • τ : ℍ) : ℂ) = num (δ : GL (Fin 2) ℝ) τ / denom (δ : GL (Fin 2) ℝ) τ := by
    rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]
  rw [← h2, hδ] at h
  rw [coe_mul_GL]
  exact h

theorem bottom_row_eq {c d c' d' : ℤ} (τ : ℍ)
    (h : (c : ℂ) * τ + d = (c' : ℂ) * τ + d') : c = c' ∧ d = d' := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at him
  have hc : (c : ℝ) = c' := mul_right_cancel₀ τ.im_pos.ne' him
  have hc' : c = c' := by exact_mod_cast hc
  subst hc'
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

def chi (τ : ℍ) : MulAction.stabilizer SL(2, ℤ) τ →* ℂ where
  toFun γ := denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
  map_one' := by simp
  map_mul' γ δ := by
    rw [Subgroup.coe_mul, denom_mul_of_smul_eq _ _ _ δ.2]

theorem chi_apply (τ : ℍ) (γ : MulAction.stabilizer SL(2, ℤ) τ) :
    chi τ γ = denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := rfl

theorem eq_one_of_denom_eq_one (τ : ℍ) (γ : SL(2, ℤ)) (hγ : γ • τ = τ)
    (h1 : denom (γ : GL (Fin 2) ℝ) τ = 1) : γ = 1 := by
  have hrow : (γ 1 0 : ℤ) = 0 ∧ (γ 1 1 : ℤ) = 1 := by
    have := bottom_row_eq (c := γ 1 0) (d := γ 1 1) (c' := 0) (d' := 1) τ
      (by rw [ModularGroup.denom_apply] at h1; push_cast; simpa using h1)
    exact this
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two, hrow.1, hrow.2] at hdet
  simp only [mul_one, mul_zero, sub_zero] at hdet

  have hfix := congrArg (fun z : ℍ => (z : ℂ)) hγ
  simp only [coe_specialLinearGroup_apply] at hfix
  rw [hrow.1, hrow.2, hdet] at hfix
  simp only [eq_intCast, Int.cast_zero, Complex.ofReal_zero, zero_mul, Int.cast_one,
    Complex.ofReal_one, zero_add, div_one, one_mul] at hfix
  have h01 : ((γ 0 1 : ℤ) : ℂ) = 0 := by
    have := hfix

    have h' : (τ : ℂ) + ((γ 0 1 : ℤ) : ℝ) = τ := by exact_mod_cast this
    have h'' := add_left_cancel (h'.trans (add_zero (τ : ℂ)).symm)
    exact_mod_cast h''
  have h01' : (γ 0 1 : ℤ) = 0 := by exact_mod_cast h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hrow.1, hrow.2, hdet, h01']

theorem chi_injective (τ : ℍ) : Function.Injective (chi τ) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro γ hγ
  rw [MonoidHom.mem_ker, chi_apply] at hγ
  exact Subtype.ext (eq_one_of_denom_eq_one τ γ γ.2 hγ)

private theorem _root_.ModularCurve.ComplexPlaceDictionary.RamificationEqCard.finite_stabilizer (τ : ℍ) : Finite (MulAction.stabilizer SL(2, ℤ) τ) := by
  have hfin := ProperlyDiscontinuousSMul.finite_stabilizer (Γ := 𝒮ℒ) τ
  have : Finite (MulAction.stabilizer (𝒮ℒ) τ) := hfin
  refine Finite.of_injective
    (fun γ => (⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)), ⟨γ, rfl⟩⟩, γ.2⟩ :
      MulAction.stabilizer (𝒮ℒ) τ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer (𝒮ℒ) τ => ((x : 𝒮ℒ) : GL (Fin 2) ℝ)) h
  exact Subtype.ext (Matrix.SpecialLinearGroup.mapGL_injective this)

p2m_export "ModularCurve.ComplexPlaceDictionary.RamificationEqCard" "finite_stabilizer"
scoped instance (τ : ℍ) : Finite (MulAction.stabilizer SL(2, ℤ) τ) := finite_stabilizer τ

theorem isCyclic_stabilizer (τ : ℍ) : IsCyclic (MulAction.stabilizer SL(2, ℤ) τ) :=
  isCyclic_of_injective_ringHom (chi τ) (chi_injective τ)

def negOne (τ : ℍ) : MulAction.stabilizer SL(2, ℤ) τ :=
  ⟨-1, by rw [MulAction.mem_stabilizer_iff, ModularGroup.SL_neg_smul, one_smul]⟩

theorem orderOf_negOne (τ : ℍ) : orderOf (negOne τ) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simp [negOne]
  · intro h
    have := congrArg (fun γ : MulAction.stabilizer SL(2, ℤ) τ => ((γ : SL(2, ℤ)) 0 0)) h
    simp [negOne] at this

theorem two_dvd_card_stabilizer (τ : ℍ) :
    2 ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ) := by
  have h := orderOf_dvd_natCard (negOne τ)
  rwa [orderOf_negOne] at h

theorem card_stabilizer_pos (τ : ℍ) : 0 < Nat.card (MulAction.stabilizer SL(2, ℤ) τ) :=
  Nat.card_pos

theorem exists_orderOf_eq (τ : ℍ) {m : ℕ}
    (hm : m ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ)) :
    ∃ γ : MulAction.stabilizer SL(2, ℤ) τ, orderOf γ = m := by
  haveI := isCyclic_stabilizer τ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer SL(2, ℤ) τ)
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g ^ (orderOf g / m), orderOf_pow_orderOf_div ?_ (hord ▸ hm)⟩
  rw [hord]; exact (card_stabilizer_pos τ).ne'

theorem orderOf_chi (τ : ℍ) (γ : MulAction.stabilizer SL(2, ℤ) τ) :
    orderOf (chi τ γ) = orderOf γ :=
  orderOf_injective _ (chi_injective τ) γ

theorem two_mul_dvd_of_dvd_div_two {e s : ℕ} (h2 : 2 ∣ s) (he : e ∣ s / 2) : 2 * e ∣ s := by
  obtain ⟨t, rfl⟩ := h2
  rw [Nat.mul_div_cancel_left _ two_pos] at he
  exact Nat.mul_dvd_mul_left 2 he

def incl (N : ℕ) (τ : ℍ) :
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ →* MulAction.stabilizer SL(2, ℤ) τ where
  toFun g := ⟨((g : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem incl_injective (N : ℕ) (τ : ℍ) : Function.Injective (incl N τ) := by
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer SL(2, ℤ) τ => (x : SL(2, ℤ))) h
  exact Subtype.ext (Subtype.ext this)

theorem chi_heckeDiag_smul (N : ℕ) [NeZero N] (τ : ℍ)
    (δ : MulAction.stabilizer SL(2, ℤ) (ModularForm.heckeDiagMatrix N • τ)) :
    chi (ModularForm.heckeDiagMatrix N • τ) δ =
      (((δ : SL(2, ℤ)) 1 0 * N : ℤ) : ℂ) * τ + (((δ : SL(2, ℤ)) 1 1 : ℤ) : ℂ) := by
  rw [chi_apply, ModularGroup.denom_apply, ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne N)]
  push_cast
  ring

theorem two_mul_dvd_card_stabilizer_gamma0 (N : ℕ) [NeZero N] (τ : ℍ) (e : ℕ) (he : 0 < e)
    (h2 : e ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2)
    (h3 : e ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) (ModularForm.heckeDiagMatrix N • τ)) / 2) :
    2 * e ∣ Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
  set σ : ℍ := ModularForm.heckeDiagMatrix N • τ with hσ
  haveI : NeZero (2 * e) := ⟨by omega⟩
  obtain ⟨γ, hγ⟩ := exists_orderOf_eq τ (two_mul_dvd_of_dvd_div_two (two_dvd_card_stabilizer τ) h2)
  obtain ⟨δ, hδ⟩ := exists_orderOf_eq σ (two_mul_dvd_of_dvd_div_two (two_dvd_card_stabilizer σ) h3)
  have hu : IsPrimitiveRoot (chi τ γ) (2 * e) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_chi, hγ]
  have hw : chi σ δ ^ (2 * e) = 1 := by
    rw [← hδ, ← orderOf_chi, pow_orderOf_eq_one]
  obtain ⟨i, -, hi⟩ := hu.eq_pow_of_pow_eq_one hw
  rw [← map_pow] at hi

  set γ' : MulAction.stabilizer SL(2, ℤ) τ := γ ^ i with hγ'
  have hrow : ((γ' : SL(2, ℤ)) 1 0 : ℤ) = (δ : SL(2, ℤ)) 1 0 * N ∧
      ((γ' : SL(2, ℤ)) 1 1 : ℤ) = (δ : SL(2, ℤ)) 1 1 := by
    apply bottom_row_eq τ
    have h1 := hi
    rw [chi_apply, ModularGroup.denom_apply, chi_heckeDiag_smul] at h1
    exact_mod_cast h1
  have hmem : (γ' : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, hrow.1]
    push_cast
    simp
  have hord' : orderOf γ' = 2 * e := by
    rw [← orderOf_chi, hi, orderOf_chi, hδ]

  let G : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ :=
    ⟨⟨(γ' : SL(2, ℤ)), hmem⟩, γ'.2⟩
  have hG : incl N τ G = γ' := rfl
  have hordG : orderOf G = 2 * e := by
    rw [← orderOf_injective (incl N τ) (incl_injective N τ) G, hG, hord']
  rw [← hordG]
  exact orderOf_dvd_natCard G

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k) (h : Γ' ≤ Γ) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := by
    simpa using f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[scoped simp] theorem restrict_apply {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k)
    (h : Γ' ≤ Γ) (τ : ℍ) : restrict f h τ = f τ := rfl

theorem gamma0_le_SL (N : ℕ) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

theorem gamma0_le_conj (N : ℕ) [NeZero N] :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (ModularForm.heckeDiagMatrix N)⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]
  have hγ' : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N) * N := by
    rw [SetLike.mem_coe, CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    exact (Int.ediv_mul_cancel hγ).symm
  set e : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N with he
  have hdet : Matrix.det !![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
      N * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1; e, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1] = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hγ'] at this
    rw [Matrix.det_fin_two_of]
    linear_combination this
  refine ⟨⟨_, hdet⟩, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hγ', mul_comm,
      ModularForm.val_heckeDiagMatrix (NeZero.ne N)]

def res (N : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k :=
  restrict f (gamma0_le_SL N)

@[scoped simp] theorem res_apply (N : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    res N f τ = f τ := rfl

def liftN (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k :=
  ((N : ℂ) ^ (k - 1))⁻¹ • restrict (ModularForm.translate f (ModularForm.heckeDiagMatrix N))
    (gamma0_le_conj N)

theorem liftN_apply (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    liftN N f τ = f (ModularForm.heckeDiagMatrix N • τ) := by
  rw [liftN, ModularForm.IsGLPos.smul_apply, restrict_apply, ModularForm.coe_translate,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne N), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ (by exact_mod_cast NeZero.ne N)), one_mul]

theorem coe_liftN (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    (liftN N f : ℍ → ℂ) = fun τ => f (ModularForm.heckeDiagMatrix N • τ) :=
  funext (liftN_apply N f)

variable {N : ℕ}

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

abbrev qL₁ {k : ℤ} (f : ModularForm 𝒮ℒ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_sub {a : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (f - g) = qL f - qL g := by
  simp only [qL, ModularForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods N), PowerSeries.coe_sub]

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

theorem qL_smul {a : ℤ} (c : ℂ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (c • f) = HahnSeries.C c * qL f := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), Algebra.smul_def,
    PowerSeries.algebraMap_eq, PowerSeries.coe_mul, HahnSeries.ofPowerSeries_C]

theorem qL_mcast {a b : ℤ} (h : a = b) (f : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (ModularForm.mcast h f) = qL f := rfl

theorem qL_res (N : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : qL (res N f) = qL₁ f := rfl

theorem qL_liftN (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    qL (liftN N f) = qExpand ℂ N (qL₁ f) := by
  rw [qL, coe_liftN]
  exact ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne N f

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

def numer (A : ModularForm (CongruenceSubgroup.Gamma0 N) 4)
    (B : ModularForm (CongruenceSubgroup.Gamma0 N) 12) (c : ℂ) :
    ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  ModularForm.mcast (by norm_num) (A.mul (A.mul A)) - c • B

theorem numer_apply (A : ModularForm (CongruenceSubgroup.Gamma0 N) 4)
    (B : ModularForm (CongruenceSubgroup.Gamma0 N) 12) (c : ℂ) (τ : ℍ) :
    numer A B c τ = A τ ^ 3 - c * B τ := by
  simp only [numer, ModularForm.sub_apply, ModularForm.coe_mcast, ModularForm.coe_mul,
    Pi.mul_apply, ModularForm.IsGLPos.smul_apply, smul_eq_mul]
  ring

theorem qL_numer (A : ModularForm (CongruenceSubgroup.Gamma0 N) 4)
    (B : ModularForm (CongruenceSubgroup.Gamma0 N) 12) (c : ℂ) :
    qL (numer A B c) = qL A ^ 3 - HahnSeries.C c * qL B := by
  rw [numer, qL_sub, qL_mcast, qL_mul, qL_mul, qL_smul]
  ring

theorem pres_numer (A : ModularForm (CongruenceSubgroup.Gamma0 N) 4)
    (B : ModularForm (CongruenceSubgroup.Gamma0 N) 12) (hB : qL B ≠ 0) (c : ℂ) :
    (qL A ^ 3 / qL B - algebraMap ℂ (LaurentSeries ℂ) c) * qL B = qL (numer A B c) := by
  rw [qL_numer, sub_mul, div_mul_cancel₀ _ hB, algebraMap_laurentSeries_eq_C]

theorem realize_smul (N : ℕ) (x : LaurentSeries ℂ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    realize N x (γ • τ) = realize N x τ := by
  classical
  have key : ∀ {k : ℤ} (h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (h : ℍ → ℂ) (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * h τ := fun h =>
    SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
  by_cases H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
  · obtain ⟨⟨k, g, h⟩, hne, heq⟩ := H
    have hd : (denom (γ : GL (Fin 2) ℝ) τ : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
    have hne' : (h : ℍ → ℂ) (γ • τ) ≠ 0 := by rw [key h]; exact mul_ne_zero hd hne
    rw [realize_eq_div N g h x heq _ hne', realize_eq_div N g h x heq _ hne, key g, key h,
      mul_div_mul_left _ _ hd]
  · have H' : ¬ ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) (γ • τ) ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rintro ⟨⟨k, g, h⟩, hne, heq⟩
      refine H ⟨⟨k, g, h⟩, ?_, heq⟩
      intro h0
      apply hne
      show (h : ℍ → ℂ) (γ • τ) = 0
      rw [key h, show (h : ℍ → ℂ) τ = 0 from h0, mul_zero]
    unfold ModularCurve.realize
    rw [dif_neg H, dif_neg H']

section FunctionField

variable (N : ℕ) [NeZero N]

abbrev CF : Type := ↥(laurentBaseChange ℂ (modularFunctionFieldFull N))

theorem exists_ord_eq_one (D : ComplexPlaceDictionary N) (τ : ℍ) :
    ∃ x : CF N, x ≠ 0 ∧ (D.pt τ).ord x = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (D.pt τ).toValuationSubring
  refine ⟨π, ?_, (D.pt τ).ord_coe_irreducible hπ⟩
  intro h
  apply hπ.ne_zero
  exact_mod_cast h

def A4 : ModularForm (CongruenceSubgroup.Gamma0 N) 4 := res N ModularForm.E₄

def B12 : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  res N ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)

def A4' : ModularForm (CongruenceSubgroup.Gamma0 N) 4 := liftN N ModularForm.E₄

def B12' : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  liftN N ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)

omit [NeZero N] in
@[scoped simp] theorem A4_apply (τ : ℍ) : A4 N τ = ModularForm.E₄ τ := rfl
omit [NeZero N] in
@[scoped simp] theorem B12_apply (τ : ℍ) : B12 N τ = ModularForm.discriminant τ := rfl
@[scoped simp] theorem A4'_apply (τ : ℍ) :
    A4' N τ = ModularForm.E₄ (ModularForm.heckeDiagMatrix N • τ) := liftN_apply N _ τ
@[scoped simp] theorem B12'_apply (τ : ℍ) :
    B12' N τ = ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := liftN_apply N _ τ

omit [NeZero N] in
theorem B12_ne (τ : ℍ) : (B12 N : ℍ → ℂ) τ ≠ 0 := ModularForm.discriminant_ne_zero τ
theorem B12'_ne (τ : ℍ) : (B12' N : ℍ → ℂ) τ ≠ 0 := by
  show B12' N τ ≠ 0
  rw [B12'_apply]; exact ModularForm.discriminant_ne_zero _

omit [NeZero N] in
theorem qL_B12_ne : qL (B12 N) ≠ 0 :=
  qL_ne_zero _ (fun h => B12_ne N UpperHalfPlane.I (by rw [h]; rfl))
theorem qL_B12'_ne : qL (B12' N) ≠ 0 :=
  qL_ne_zero _ (fun h => B12'_ne N UpperHalfPlane.I (by rw [h]; rfl))

omit [NeZero N] in

theorem coeffEmb_jq : coeffEmb ℂ jq = qL (A4 N) ^ 3 / qL (B12 N) := by
  have h1 : coeffEmb ℂ jq = jqModC ℂ := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ ℂ)
  rw [h1, jqModC_eq_qExpansion_E4_cube_div_discriminant]
  rfl

theorem coeffEmb_jqN : coeffEmb ℂ (qExpand ℚ N jq) = qL (A4' N) ^ 3 / qL (B12' N) := by
  have h1 : coeffEmb ℂ (qExpand ℚ N jq) = qExpand ℂ N (coeffEmb ℂ jq) :=
    coeffMap_qExpand (algebraMap ℚ ℂ) N jq
  rw [h1, coeffEmb_jq N, map_div₀, map_pow, A4', B12', qL_liftN, qL_liftN]
  rfl

def Xj : CF N :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (modularFunctionField_le_full N (jq_mem N))⟩

def XjN : CF N :=
  ⟨coeffEmb ℂ (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange ℂ (jqd_mem_full N dvd_rfl)⟩

omit [NeZero N] in
theorem coe_algebraMap (c : ℂ) :
    ((algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c := rfl

theorem Xj_sub_ne (c : ℂ) : Xj N - algebraMap ℂ (CF N) c ≠ 0 := by
  intro h
  have h1 := congrArg (fun y : CF N => (y : LaurentSeries ℂ).coeff (-1)) (sub_eq_zero.mp h)
  simp only [Xj] at h1
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one, coe_algebraMap, algebraMap_laurentSeries_eq_C,
    HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num)] at h1
  exact one_ne_zero h1

theorem XjN_sub_ne (c : ℂ) : XjN N - algebraMap ℂ (CF N) c ≠ 0 := by
  intro h
  have h1 := congrArg (fun y : CF N => (y : LaurentSeries ℂ).coeff (-(N : ℤ)))
    (sub_eq_zero.mp h)
  simp only [XjN] at h1
  have hN : (-(N : ℤ)) = (N : ℤ) * (-1) := by ring
  rw [coeffEmb_coeff, hN, qExpand_coeff_mul, coeff_jq_neg_one, map_one, coe_algebraMap,
    algebraMap_laurentSeries_eq_C, HahnSeries.C_apply,
    HahnSeries.coeff_single_of_ne] at h1
  · exact one_ne_zero h1
  · have : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    omega

theorem realize_Xj_sub (c : ℂ) (z : ℍ) :
    realize N ((Xj N - algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) z =
      (ModularForm.E₄ : ℍ → ℂ) z ^ 3 / ModularForm.discriminant z - c := by
  have hx : ((Xj N - algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) =
      qL (A4 N) ^ 3 / qL (B12 N) - algebraMap ℂ (LaurentSeries ℂ) c := by
    show coeffEmb ℂ jq - algebraMap ℂ (LaurentSeries ℂ) c = _
    rw [coeffEmb_jq N]
  rw [hx, realize_eq_div N (numer (A4 N) (B12 N) c) (B12 N) _
    (pres_numer _ _ (qL_B12_ne N) c) z (B12_ne N z)]
  simp only [numer_apply, A4_apply, B12_apply]
  show _ / ModularForm.discriminant z = _
  rw [sub_div, mul_div_cancel_right₀ _ (ModularForm.discriminant_ne_zero z)]

theorem realize_XjN_sub (c : ℂ) (z : ℍ) :
    realize N ((XjN N - algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) z =
      (ModularForm.E₄ : ℍ → ℂ) (ModularForm.heckeDiagMatrix N • z) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix N • z) - c := by
  have hx : ((XjN N - algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) =
      qL (A4' N) ^ 3 / qL (B12' N) - algebraMap ℂ (LaurentSeries ℂ) c := by
    show coeffEmb ℂ (qExpand ℚ N jq) - algebraMap ℂ (LaurentSeries ℂ) c = _
    rw [coeffEmb_jqN N]
  rw [hx, realize_eq_div N (numer (A4' N) (B12' N) c) (B12' N) _
    (pres_numer _ _ (qL_B12'_ne N) c) z (B12'_ne N z)]
  simp only [numer_apply, A4'_apply, B12'_apply]
  show _ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • z) = _
  rw [sub_div, mul_div_cancel_right₀ _ (ModularForm.discriminant_ne_zero _)]

variable {N}

abbrev s1 (τ : ℍ) : ℕ := Nat.card (MulAction.stabilizer SL(2, ℤ) τ)

theorem ram_dvd_of_order_eq (D : ComplexPlaceDictionary N) (τ : ℍ) (x : CF N) (hx : x ≠ 0)
    (m : ℕ)
    (h : meromorphicOrderAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ)
      = ((m : ℤ) : WithTop ℤ)) :
    D.ramification τ ∣ m := by
  rw [D.meromorphicOrderAt_realize τ x hx] at h
  have h' : (D.ramification τ : ℤ) * (D.pt τ).ord x = m := by exact_mod_cast h
  have : (D.ramification τ : ℤ) ∣ (m : ℤ) := ⟨_, h'.symm⟩
  exact_mod_cast this

theorem ram_dvd_card_div_two (D : ComplexPlaceDictionary N) (τ : ℍ) :
    D.ramification τ ∣ s1 τ / 2 := by
  set c : ℂ := (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ
  refine ram_dvd_of_order_eq D τ (Xj N - algebraMap ℂ (CF N) c) (Xj_sub_ne N c) _ ?_
  have hfun : (fun z : ℂ => realize N ((Xj N - algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ)
      (ofComplex z)) = fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 /
            ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ := by
    funext z; exact realize_Xj_sub N c (ofComplex z)
  rw [hfun]
  exact meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two τ

theorem ram_dvd_card_smul_div_two (D : ComplexPlaceDictionary N) (τ : ℍ) :
    D.ramification τ ∣ s1 (ModularForm.heckeDiagMatrix N • τ) / 2 := by
  set σ : ℍ := ModularForm.heckeDiagMatrix N • τ
  set c : ℂ := (ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ
  refine ram_dvd_of_order_eq D τ (XjN N - algebraMap ℂ (CF N) c) (XjN_sub_ne N c) _ ?_
  let G : ℍ → ℂ := fun w => (ModularForm.E₄ : ℍ → ℂ) w ^ 3 / ModularForm.discriminant w - c
  have hfun : (fun z : ℂ => realize N ((XjN N - algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ)
      (ofComplex z)) = fun z : ℂ => G (ModularForm.heckeDiagMatrix N • ofComplex z) := by
    funext z; exact realize_XjN_sub N c (ofComplex z)
  rw [hfun, meromorphicOrderAt_comp_smul (f := G) (ModularForm.det_heckeDiagMatrix_pos N)]
  exact meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two σ

theorem card_dvd_two_mul_ram (D : ComplexPlaceDictionary N) (τ : ℍ) :
    Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) ∣ 2 * D.ramification τ := by
  obtain ⟨x, hx, hord⟩ := exists_ord_eq_one N D τ
  have h := D.meromorphicOrderAt_realize τ x hx
  rw [hord, mul_one] at h
  have := UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
    (CongruenceSubgroup.Gamma0 N) (fun z => realize N (x : LaurentSeries ℂ) z)
    (fun γ hγ z => realize_smul N _ hγ z) τ _ h
  exact_mod_cast this

theorem two_mul_ramification_eq (D : ComplexPlaceDictionary N) (τ : ℍ) :
    2 * D.ramification τ = Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) :=
  Nat.dvd_antisymm
    (two_mul_dvd_card_stabilizer_gamma0 N τ _ (D.ramification_pos τ)
      (ram_dvd_card_div_two D τ) (ram_dvd_card_smul_div_two D τ))
    (card_dvd_two_mul_ram D τ)

end FunctionField

end ModularCurve.ComplexPlaceDictionary.RamificationEqCard
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionary P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionary.RamificationEqCard"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionary"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionary P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionary.RamificationEqCard"

open scoped MatrixGroups in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (τ : UpperHalfPlane) :
    2 * D.ramification τ =
      Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) :=
  ModularCurve.ComplexPlaceDictionary.RamificationEqCard.two_mul_ramification_eq D τ

end S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer (solution)
