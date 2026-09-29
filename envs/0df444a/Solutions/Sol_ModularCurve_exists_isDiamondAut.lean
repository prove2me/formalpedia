-- Prove2me | solution 1 for ModularCurve.exists_isDiamondAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4178554a-280f-584a-91c6-224df761520a

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isDiamondAut

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries
open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondPullback

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {M : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem qC_mul {a b : ℤ} (f : ModularForm Γ₁(M) a) (g : ModularForm Γ₁(M) b) :
    qC ((⇑f : ℍ → ℂ) * ⇑g) = qC ⇑f * qC ⇑g := by
  rw [qC, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) f g, map_mul]
  rfl

theorem qC_coe_mul {a b : ℤ} (f : ModularForm Γ₁(M) a) (g : ModularForm Γ₁(M) b) :
    qC (⇑(f.mul g)) = qC ⇑f * qC ⇑g := by
  rw [ModularForm.coe_mul, qC_mul]

theorem qC_add {a : ℤ} (f g : ModularForm Γ₁(M) a) :
    qC (⇑(f + g)) = qC ⇑f + qC ⇑g := by
  rw [ModularForm.coe_add, qC, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) f g,
    map_add]
  rfl

theorem qC_neg {a : ℤ} (f : ModularForm Γ₁(M) a) : qC (⇑(-f)) = -qC ⇑f := by
  rw [ModularForm.coe_neg, qC, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods M) f,
    map_neg]
  rfl

theorem qC_smul {a : ℤ} (c : ℂ) (f : ModularForm Γ₁(M) a) : qC (⇑(c • f)) = c • qC ⇑f := by
  rw [ModularForm.IsGLPos.coe_smul, qC,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f, qC,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by
  rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by
  rw [qC, qExpansion_one, map_one]

theorem qC_coe_zero {a : ℤ} : qC (⇑(0 : ModularForm Γ₁(M) a)) = 0 := by
  rw [ModularForm.coe_zero]; exact qC_zero

theorem qC_coe_one : qC (⇑(1 : ModularForm Γ₁(M) 0)) = 1 := by
  rw [ModularForm.one_coe_eq_one]; exact qC_one

variable [NeZero M]

theorem hasSum_qC {a : ℤ} (f : ModularForm Γ₁(M) a) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M))
    f.holo' (ModularFormClass.bdd_at_infty f) τ

theorem coe_eq_of_qC_eq {a b : ℤ} (f : ModularForm Γ₁(M) a) (g : ModularForm Γ₁(M) b)
    (h : qC ⇑f = qC ⇑g) : (⇑f : ℍ → ℂ) = ⇑g := by
  have h' : qExpansion 1 (⇑f) = qExpansion 1 (⇑g) := HahnSeries.ofPowerSeries_injective h
  funext τ
  have hf := hasSum_qC f τ
  have hg := hasSum_qC g τ
  rw [h'] at hf
  exact hf.unique hg

omit [NeZero M] in
theorem qC_eq_zero_iff {a : ℤ} (f : ModularForm Γ₁(M) a) : qC ⇑f = 0 ↔ f = 0 := by
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M) f, qC]
  constructor
  · intro h
    exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

end QExp

section Slash

variable {M : ℕ} {k : ℤ}

theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    show ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

theorem isBoundedAt_slash [NeZero M] (f : ModularForm Γ₁(M) k) (γ : SL(2, ℤ)) {c : OnePoint ℝ}
    (hc : IsCusp c Γ₁(M)) : IsBoundedAt c ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) k := by
  have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₁(M)).mp hc
  have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) Γ₁(M) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact hcSL.smul_of_mem ⟨γ, rfl⟩
  exact IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

def diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁(M) k) :
    ModularForm Γ₁(M) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Gamma1 M := conj_mem_Gamma1 hγ hA
    have hGL : (γ : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((γ * A * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    show ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    exact isBoundedAt_slash f γ hc

@[scoped simp] theorem coe_diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm Γ₁(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem coe_diamondSlash_SL [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm Γ₁(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [coe_diamondSlash, ModularForm.SL_slash]

theorem slash_inv_slash (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ⁻¹) ∣[k] γ = F := by
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem slash_slash_inv (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ) ∣[k] γ⁻¹ = F := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem diamondSlash_ne_zero [NeZero M] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    {f : ModularForm Γ₁(M) k} (hf : f ≠ 0) : diamondSlash γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h1 : (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = 0 := by rw [h]; rfl
  rw [coe_diamondSlash_SL] at h1
  have h2 : (⇑f : ℍ → ℂ) = 0 := by
    rw [← slash_slash_inv (k := k) (⇑f) γ, h1, SlashAction.zero_slash]
  exact DFunLike.ext' (h2.trans ModularForm.coe_zero.symm)

theorem mul_inv_mem_Gamma1 {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 0 0 : ℤ) : ZMod M) = ((γ' 0 0 : ℤ) : ZMod M)) : γ * γ'⁻¹ ∈ Gamma1 M := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ'
  have hdet : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) h1
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  have hdet' : ((γ' 0 0 : ℤ) : ZMod M) * ((γ' 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : (γ' 0 0 : ℤ) * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by
      have := γ'.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) h1
    push_cast at this
    rw [hc', mul_zero, sub_zero] at this
    exact this
  have hinv : (γ'⁻¹ : SL(2, ℤ)) = ⟨!![γ' 1 1, -(γ' 0 1); -(γ' 1 0), γ' 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ'.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ'
  rw [Gamma1_mem, hinv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_add, Int.cast_mul, Int.cast_neg, hc, hc',
    Fin.isValue]
  refine ⟨?_, ?_, ?_⟩
  · rw [h, neg_zero, mul_zero, add_zero, hdet']
  · rw [zero_mul, zero_add, ← h, mul_comm, hdet]
  · simp

theorem slash_eq_of_apply_eq [NeZero M] (f : ModularForm Γ₁(M) k) {γ γ' : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 0 0 : ℤ) : ZMod M) = ((γ' 0 0 : ℤ) : ZMod M)) :
    (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] γ' := by
  have hmem := mul_inv_mem_Gamma1 hγ hγ' h
  have hinv : (⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
  calc (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹ * γ') := by rw [inv_mul_cancel_right]
    _ = ((⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹)) ∣[k] γ' := SlashAction.slash_mul _ _ _ _
    _ = (⇑f : ℍ → ℂ) ∣[k] γ' := by rw [hinv]

end Slash

section Ratio

variable (M : ℕ) [NeZero M]

def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm Γ₁(M) k), qC ⇑g ≠ 0 ∧ x = qC ⇑f / qC ⇑g

variable {M}

omit [NeZero M] in
theorem isRatio_of_eq {k : ℤ} (f g : ModularForm Γ₁(M) k) (hg : qC ⇑g ≠ 0) :
    IsRatio M (qC ⇑f / qC ⇑g) :=
  ⟨k, f, g, hg, rfl⟩

theorem qC_coe_one_ne_zero : qC (⇑(1 : ModularForm Γ₁(M) 0)) ≠ 0 := by
  rw [qC_coe_one]; exact one_ne_zero

theorem isRatio_zero : IsRatio M 0 :=
  ⟨0, 0, 1, qC_coe_one_ne_zero, by rw [qC_coe_zero, zero_div]⟩

theorem isRatio_one : IsRatio M 1 :=
  ⟨0, 1, 1, qC_coe_one_ne_zero, by rw [qC_coe_one, div_one]⟩

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio M x) (hy : IsRatio M y) :
    IsRatio M (x + y) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  obtain ⟨k', f', g', hg', rfl⟩ := hy
  refine ⟨k + k', f.mul g' + g.mul f', g.mul g', ?_, ?_⟩
  · rw [qC_coe_mul]; exact mul_ne_zero hg hg'
  · rw [qC_add, qC_coe_mul, qC_coe_mul, qC_coe_mul, div_add_div _ _ hg hg']

omit [NeZero M] in
theorem IsRatio.neg {x : LaurentSeries ℂ} (hx : IsRatio M x) : IsRatio M (-x) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  exact ⟨k, -f, g, hg, by rw [qC_neg]; ring⟩

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio M x) (hy : IsRatio M y) :
    IsRatio M (x * y) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  obtain ⟨k', f', g', hg', rfl⟩ := hy
  refine ⟨k + k', f.mul f', g.mul g', ?_, ?_⟩
  · rw [qC_coe_mul]; exact mul_ne_zero hg hg'
  · rw [qC_coe_mul, qC_coe_mul, div_mul_div_comm]

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio M x) : IsRatio M x⁻¹ := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  by_cases hf : qC ⇑f = 0
  · rw [hf, zero_div, inv_zero]; exact isRatio_zero
  · exact ⟨k, g, f, hf, by rw [inv_div]⟩

theorem isRatio_C (c : ℂ) : IsRatio M (HahnSeries.C c) := by
  refine ⟨0, c • (1 : ModularForm Γ₁(M) 0), 1, qC_coe_one_ne_zero, ?_⟩
  rw [qC_smul, qC_coe_one, div_one, ← HahnSeries.C_mul_eq_smul, mul_one]

variable (M) in

def ratioField : Subfield (LaurentSeries ℂ) where
  carrier := {x | IsRatio M x}
  mul_mem' := IsRatio.mul
  one_mem' := isRatio_one
  add_mem' := IsRatio.add
  zero_mem' := isRatio_zero
  neg_mem' := IsRatio.neg
  inv_mem' _ := IsRatio.inv

theorem mem_ratioField {x : LaurentSeries ℂ} : x ∈ ratioField M ↔ IsRatio M x := Iff.rfl

theorem qC_slash_ne_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k : ℤ} {g : ModularForm Γ₁(M) k} (hg : qC ⇑g ≠ 0) :
    qC ((⇑g : ℍ → ℂ) ∣[k] γ) ≠ 0 := by
  rw [← coe_diamondSlash_SL γ hγ, Ne, qC_eq_zero_iff]
  exact diamondSlash_ne_zero hγ (fun h => hg ((qC_eq_zero_iff g).mpr h))

theorem cross (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {k k' : ℤ} (f g : ModularForm Γ₁(M) k) (f' g' : ModularForm Γ₁(M) k')
    (hg : qC ⇑g ≠ 0) (hg' : qC ⇑g' ≠ 0) (h : qC ⇑f / qC ⇑g = qC ⇑f' / qC ⇑g') :
    qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ)
      = qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) / qC ((⇑g' : ℍ → ℂ) ∣[k'] γ) := by
  rw [div_eq_div_iff hg hg'] at h

  have hfun : (⇑(f.mul g') : ℍ → ℂ) = ⇑(f'.mul g) := by
    apply coe_eq_of_qC_eq
    rw [qC_coe_mul, qC_coe_mul, h, mul_comm]
  rw [ModularForm.coe_mul, ModularForm.coe_mul] at hfun

  have hsl : ((⇑f : ℍ → ℂ) * ⇑g') ∣[k + k'] γ = ((⇑f' : ℍ → ℂ) * ⇑g) ∣[k' + k] γ := by
    rw [hfun, add_comm]
  rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2] at hsl

  have hq : qC ((⇑f : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) * qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    have := congrArg qC hsl
    rwa [← coe_diamondSlash_SL γ hγ f, ← coe_diamondSlash_SL γ hγ g',
      ← coe_diamondSlash_SL γ hγ f', ← coe_diamondSlash_SL γ hγ g, qC_mul, qC_mul,
      coe_diamondSlash_SL, coe_diamondSlash_SL, coe_diamondSlash_SL, coe_diamondSlash_SL] at this
  rw [div_eq_div_iff (qC_slash_ne_zero γ hγ hg) (qC_slash_ne_zero γ hγ hg')]
  exact hq

def pull (γ : SL(2, ℤ)) (x : ratioField M) : LaurentSeries ℂ :=
  qC ((⇑(x.2.choose_spec.choose) : ℍ → ℂ) ∣[x.2.choose] γ)
    / qC ((⇑(x.2.choose_spec.choose_spec.choose) : ℍ → ℂ) ∣[x.2.choose] γ)

theorem pull_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : ratioField M) {k : ℤ} (f g : ModularForm Γ₁(M) k) (hg : qC ⇑g ≠ 0)
    (hx : (x : LaurentSeries ℂ) = qC ⇑f / qC ⇑g) :
    pull γ x = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  have hspec := x.2.choose_spec.choose_spec.choose_spec
  exact cross γ hγ _ _ f g hspec.1 hg (hspec.2.symm.trans hx)

theorem pull_one (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : pull γ (1 : ratioField M) = 1 := by
  rw [pull_eq γ hγ 1 (1 : ModularForm Γ₁(M) 0) 1 qC_coe_one_ne_zero
    (by rw [qC_coe_one, div_one]; rfl)]
  exact div_self (qC_slash_ne_zero γ hγ qC_coe_one_ne_zero)

theorem pull_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : pull γ (0 : ratioField M) = 0 := by
  rw [pull_eq γ hγ 0 (0 : ModularForm Γ₁(M) 0) 1 qC_coe_one_ne_zero
    (by rw [qC_coe_zero, zero_div]; rfl), ModularForm.coe_zero, SlashAction.zero_slash, qC_zero,
    zero_div]

theorem pull_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x y : ratioField M) : pull γ (x * y) = pull γ x * pull γ y := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  obtain ⟨k', f', g', hg', hy⟩ := y.2
  have hxy : ((x * y : ratioField M) : LaurentSeries ℂ) = qC ⇑(f.mul f') / qC ⇑(g.mul g') := by
    rw [Subfield.coe_mul, hx, hy, qC_coe_mul, qC_coe_mul, div_mul_div_comm]
  rw [pull_eq γ hγ x f g hg hx, pull_eq γ hγ y f' g' hg' hy,
    pull_eq γ hγ (x * y) (f.mul f') (g.mul g') (by rw [qC_coe_mul]; exact mul_ne_zero hg hg') hxy,
    ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2]
  rw [← coe_diamondSlash_SL γ hγ f, ← coe_diamondSlash_SL γ hγ f', ← coe_diamondSlash_SL γ hγ g,
    ← coe_diamondSlash_SL γ hγ g', qC_mul, qC_mul, div_mul_div_comm]

theorem pull_add (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x y : ratioField M) : pull γ (x + y) = pull γ x + pull γ y := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  obtain ⟨k', f', g', hg', hy⟩ := y.2
  have hxy : ((x + y : ratioField M) : LaurentSeries ℂ)
      = qC ⇑(f.mul g' + g.mul f') / qC ⇑(g.mul g') := by
    rw [Subfield.coe_add, hx, hy, qC_add, qC_coe_mul, qC_coe_mul, qC_coe_mul,
      div_add_div _ _ hg hg']
  rw [pull_eq γ hγ x f g hg hx, pull_eq γ hγ y f' g' hg' hy,
    pull_eq γ hγ (x + y) _ (g.mul g') (by rw [qC_coe_mul]; exact mul_ne_zero hg hg') hxy,
    ModularForm.coe_add, SlashAction.add_slash, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
    ModularForm.mul_slash_SL2]
  have e1 : qC ((⇑f : ℍ → ℂ) ∣[k] γ * (⇑g' : ℍ → ℂ) ∣[k'] γ + (⇑g : ℍ → ℂ) ∣[k] γ * (⇑f' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ)
        + qC ((⇑g : ℍ → ℂ) ∣[k] γ) * qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) := by
    rw [← coe_diamondSlash_SL γ hγ f, ← coe_diamondSlash_SL γ hγ f', ← coe_diamondSlash_SL γ hγ g,
      ← coe_diamondSlash_SL γ hγ g', ← ModularForm.coe_mul, ← ModularForm.coe_mul,
      ← ModularForm.coe_add, qC_add, qC_coe_mul, qC_coe_mul]
  have e2 : qC ((⇑g : ℍ → ℂ) ∣[k] γ * (⇑g' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑g : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ) := by
    rw [← coe_diamondSlash_SL γ hγ g, ← coe_diamondSlash_SL γ hγ g', qC_mul]
  rw [e1, e2, div_add_div _ _ (qC_slash_ne_zero γ hγ hg) (qC_slash_ne_zero γ hγ hg')]

def pullHom (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) : ratioField M →+* LaurentSeries ℂ where
  toFun := pull γ
  map_one' := pull_one γ hγ
  map_mul' := pull_mul γ hγ
  map_zero' := pull_zero γ hγ
  map_add' := pull_add γ hγ

theorem pullHom_apply (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : ratioField M) : pullHom γ hγ x = pull γ x := rfl

theorem pull_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : ratioField M) : pull γ x ∈ ratioField M := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  rw [pull_eq γ hγ x f g hg hx, ← coe_diamondSlash_SL γ hγ f, ← coe_diamondSlash_SL γ hγ g]
  exact isRatio_of_eq _ _ (by rw [coe_diamondSlash_SL]; exact qC_slash_ne_zero γ hγ hg)

theorem pull_pull_inv (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (x : ratioField M) :
    pull γ ⟨pull γ⁻¹ x, pull_mem γ⁻¹ (inv_mem hγ) x⟩ = x := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  have hg' : qC (⇑(diamondSlash γ⁻¹ (inv_mem hγ) g)) ≠ 0 := by
    rw [coe_diamondSlash_SL]; exact qC_slash_ne_zero γ⁻¹ (inv_mem hγ) hg
  rw [pull_eq γ hγ _ (diamondSlash γ⁻¹ (inv_mem hγ) f) (diamondSlash γ⁻¹ (inv_mem hγ) g) hg'
    (by rw [coe_diamondSlash_SL, coe_diamondSlash_SL]; exact pull_eq γ⁻¹ (inv_mem hγ) x f g hg hx),
    coe_diamondSlash_SL, coe_diamondSlash_SL, slash_inv_slash, slash_inv_slash, hx]

end Ratio

section Rational

open ModularCurve IntermediateField

variable (M : ℕ) [NeZero M]

abbrev toC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

omit [NeZero M] in
theorem toC_injective : Function.Injective toC := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact (algebraMap ℚ ℂ).injective this

variable {M}

omit [NeZero M] in

theorem toC_intSeriesC {k : ℤ} {f : ModularForm Γ₁(M) k} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) : toC (intSeriesC ℚ p) = qC ⇑f := by
  ext n
  rw [coeffMap_coeff, intSeriesC, qC, ← hp, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · exact map_zero _
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

omit [NeZero M] in
theorem toC_ratio {k : ℤ} {f g : ModularForm Γ₁(M) k} {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    toC (intSeriesC ℚ pf / intSeriesC ℚ pg) = qC ⇑f / qC ⇑g := by
  rw [map_div₀, toC_intSeriesC hf, toC_intSeriesC hg]

omit [NeZero M] in
theorem qC_ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm Γ₁(M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC ⇑g ≠ 0 := by
  rw [← toC_intSeriesC hg]
  exact fun h => hg0 (toC_injective (by rw [h, map_zero]))

omit [NeZero M] in
theorem toC_algebraMap (c : ℚ) :
    toC (algebraMap ℚ (LaurentSeries ℚ) c) = HahnSeries.C (algebraMap ℚ ℂ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

omit [NeZero M] in
theorem toC_comp_algebraMap :
    toC.comp (algebraMap ℚ (LaurentSeries ℚ)) = algebraMap ℚ (LaurentSeries ℂ) :=
  Subsingleton.elim _ _

theorem toC_mem_ratioField {x : LaurentSeries ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M))) :
    toC x ∈ ratioField M := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      rw [toC_ratio hf hg]
      exact isRatio_of_eq f g (qC_ne_zero_of_intSeriesC_ne_zero hg hg0)
  | algebraMap c => rw [toC_algebraMap]; exact isRatio_C _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def iota : x1FunctionField M →+* ratioField M :=
  (toC.comp (algebraMap (x1FunctionField M) (LaurentSeries ℚ))).codRestrict (ratioField M)
    (fun x => toC_mem_ratioField x.2)

@[scoped simp] theorem coe_iota (x : x1FunctionField M) : ((iota x : ratioField M) : LaurentSeries ℂ) = toC x :=
  rfl

def jC : x1FunctionField M →+* LaurentSeries ℂ :=
  toC.comp (algebraMap (x1FunctionField M) (LaurentSeries ℚ))

omit [NeZero M] in
theorem jC_apply (x : x1FunctionField M) : jC x = toC x := rfl

omit [NeZero M] in
theorem jC_injective : Function.Injective (jC (M := M)) :=
  toC_injective.comp Subtype.val_injective

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)

def psi : x1FunctionField M →+* LaurentSeries ℂ :=
  (pullHom γ hγ).comp iota

theorem psi_apply (x : x1FunctionField M) : psi γ hγ x = pull γ (iota x) := rfl

theorem exists_psi_generator_eq {k : ℤ} (f g : ModularForm Γ₁(M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ y : x1FunctionField M,
      psi γ hγ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
        = toC y := by
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M f hf γ hγ
  obtain ⟨D', g₁, p₁', hD', hp₁', hg₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M g hg γ hγ

  have hqf₁ : qC ⇑f₁ = (D : ℂ) • qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    have : (⇑f₁ : ℍ → ℂ) = ⇑((D : ℂ) • diamondSlash γ hγ f) := by
      rw [hf₁, ModularForm.IsGLPos.coe_smul, coe_diamondSlash_SL]
    rw [this, qC_smul, coe_diamondSlash_SL]
  have hqg₁ : qC ⇑g₁ = (D' : ℂ) • qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    have : (⇑g₁ : ℍ → ℂ) = ⇑((D' : ℂ) • diamondSlash γ hγ g) := by
      rw [hg₁, ModularForm.IsGLPos.coe_smul, coe_diamondSlash_SL]
    rw [this, qC_smul, coe_diamondSlash_SL]

  have hF : IsIntegralQExp (⇑(((D' : ℤ) : ℂ) • f₁)) (PowerSeries.C (D' : ℤ) * p₁) := by
    unfold IsIntegralQExp at hp₁ ⊢
    rw [map_mul, PowerSeries.map_C, hp₁, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) _ f₁, PowerSeries.smul_eq_C_mul,
      eq_intCast]
  have hG : IsIntegralQExp (⇑(((D : ℤ) : ℂ) • g₁)) (PowerSeries.C (D : ℤ) * p₁') := by
    unfold IsIntegralQExp at hp₁' ⊢
    rw [map_mul, PowerSeries.map_C, hp₁', ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) _ g₁, PowerSeries.smul_eq_C_mul,
      eq_intCast]
  have hqG : qC (⇑(((D : ℤ) : ℂ) • g₁)) = ((D : ℂ) * D') • qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    rw [qC_smul, hqg₁, smul_smul]
  have hqF : qC (⇑(((D' : ℤ) : ℂ) • f₁)) = ((D' : ℂ) * D) • qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    rw [qC_smul, hqf₁, smul_smul]
  have hG0 : intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁') ≠ 0 := by
    intro h0
    have h1 : qC (⇑(((D : ℤ) : ℂ) • g₁)) = 0 := by rw [← toC_intSeriesC hG, h0, map_zero]
    rw [hqG, ← HahnSeries.C_mul_eq_smul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact HahnSeries.C_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD')) h1
    · exact qC_slash_ne_zero γ hγ hqg h1
  refine ⟨⟨intSeriesC ℚ (PowerSeries.C (D' : ℤ) * p₁) / intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁'),
    div_mem_qExpFunctionFieldC _ _ hF hG hG0⟩, ?_⟩
  rw [psi_apply, pull_eq γ hγ _ f g hqg (by rw [coe_iota]; exact toC_ratio hf hg)]
  show _ = toC (intSeriesC ℚ (PowerSeries.C (D' : ℤ) * p₁) / intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁'))
  rw [toC_ratio hF hG, hqF, hqG, mul_comm (D' : ℂ) (D : ℂ), ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul, mul_div_mul_left _ _ ?_]
  exact HahnSeries.C_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD'))

theorem exists_psi_eq (x : x1FunctionField M) : ∃ y : x1FunctionField M, psi γ hγ x = toC y := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M)) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      exact exists_psi_generator_eq γ hγ f g hf hg hg0
  | algebraMap c =>
      refine ⟨⟨algebraMap ℚ (LaurentSeries ℚ) c, IntermediateField.algebraMap_mem _ c⟩, ?_⟩
      let j₁ : ℚ →+* x1FunctionField M := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (x1FunctionField M) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun
        (Subsingleton.elim ((psi γ hγ).comp j₁) (toC.comp (algebraMap ℚ (LaurentSeries ℚ)))) c
  | add y z hy hz ihy ihz =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      obtain ⟨z₁, hz₁⟩ := ihz hz
      refine ⟨y₁ + z₁, ?_⟩
      have : (⟨y + z, add_mem hy hz⟩ : x1FunctionField M) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, hy₁, hz₁, ← map_add]
      rfl
  | inv y hy ihy =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      refine ⟨y₁⁻¹, ?_⟩
      have : (⟨y⁻¹, inv_mem hy⟩ : x1FunctionField M) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, hy₁, ← map_inv₀]
      rfl
  | mul y z hy hz ihy ihz =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      obtain ⟨z₁, hz₁⟩ := ihz hz
      refine ⟨y₁ * z₁, ?_⟩
      have : (⟨y * z, mul_mem hy hz⟩ : x1FunctionField M) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, hy₁, hz₁, ← map_mul]
      rfl

theorem psi_mem_range (x : x1FunctionField M) : psi γ hγ x ∈ (jC (M := M)).range := by
  obtain ⟨y, hy⟩ := exists_psi_eq γ hγ x
  exact ⟨y, hy.symm⟩

def eC : x1FunctionField M ≃+* (jC (M := M)).range :=
  RingEquiv.ofBijective (jC (M := M)).rangeRestrict
    ⟨fun x y h => jC_injective (by
        have := congrArg (fun z : (jC (M := M)).range => (z : LaurentSeries ℂ)) h
        simpa only [RingHom.coe_rangeRestrict] using this),
      RingHom.rangeRestrict_surjective _⟩

omit [NeZero M] in
theorem coe_eC (x : x1FunctionField M) : ((eC x : (jC (M := M)).range) : LaurentSeries ℂ) = jC x :=
  rfl

omit [NeZero M] in
theorem jC_eC_symm (z : (jC (M := M)).range) : jC ((eC (M := M)).symm z) = (z : LaurentSeries ℂ) := by
  conv_rhs => rw [← (eC (M := M)).apply_symm_apply z]
  rfl

def sigma0 : x1FunctionField M →+* x1FunctionField M :=
  (eC (M := M)).symm.toRingHom.comp ((psi γ hγ).codRestrict (jC (M := M)).range (psi_mem_range γ hγ))

theorem jC_sigma0 (x : x1FunctionField M) : jC (sigma0 γ hγ x) = psi γ hγ x := by
  show jC ((eC (M := M)).symm _) = _
  rw [jC_eC_symm]
  rfl

theorem sigma0_injective : Function.Injective (sigma0 γ hγ) := by
  intro x y h
  have h1 : psi γ hγ x = psi γ hγ y := by rw [← jC_sigma0, ← jC_sigma0, h]
  exact (psi γ hγ).injective h1

theorem sigma0_surjective : Function.Surjective (sigma0 γ hγ) := by
  intro x
  refine ⟨sigma0 γ⁻¹ (inv_mem hγ) x, jC_injective ?_⟩
  rw [jC_sigma0, psi_apply]
  have hι : iota (sigma0 γ⁻¹ (inv_mem hγ) x)
      = ⟨pull γ⁻¹ (iota x), pull_mem γ⁻¹ (inv_mem hγ) (iota x)⟩ := by
    apply Subtype.ext
    show jC (sigma0 γ⁻¹ (inv_mem hγ) x) = pull γ⁻¹ (iota x)
    rw [jC_sigma0, psi_apply]
  rw [hι, pull_pull_inv γ hγ]
  rfl

def sigma : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (sigma0 γ hγ)
      ⟨sigma0_injective γ hγ, sigma0_surjective γ hγ⟩)
    (fun c => RingHom.congr_fun
      (Subsingleton.elim ((sigma0 γ hγ).comp (algebraMap ℚ (x1FunctionField M)))
        (algebraMap ℚ (x1FunctionField M))) c)

theorem sigma_apply (x : x1FunctionField M) : sigma γ hγ x = sigma0 γ hγ x := rfl

theorem toC_sigma_generator {k : ℤ} (f g : ModularForm Γ₁(M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    toC ((sigma γ hγ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        x1FunctionField M) : LaurentSeries ℚ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  rw [sigma_apply, ← jC_apply, jC_sigma0, psi_apply,
    pull_eq γ hγ _ f g (qC_ne_zero_of_intSeriesC_ne_zero hg hg0) (by rw [coe_iota]; exact toC_ratio hf hg)]

end Rational

section Assembly

open ModularCurve

variable (M : ℕ) [NeZero M]

omit [NeZero M] in

theorem exists_gamma0_apply_eq {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hd
  have hdet : Matrix.det !![(d : ℤ), -v; (M : ℤ), u] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination huv
  refine ⟨⟨_, hdet⟩, ?_, ?_⟩
  · rw [Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  · show (((d : ℤ)) : ZMod M) = (d : ZMod M)
    rw [Int.cast_natCast]

theorem isDiamondAut_sigma {d : ℕ} (hd : Nat.Coprime d M) {γd : SL(2, ℤ)} (hγd : γd ∈ Gamma0 M)
    (hγd00 : ((γd 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    IsDiamondAut M d (sigma γd hγd) := by
  refine ⟨hd, ?_⟩
  intro k f g pf pg hf hg hg0 γ hγ hγ00
  have hslash : ∀ (F : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
      (⇑F : ℍ → ℂ) ∣[k] γd = (⇑F : ℍ → ℂ) ∣[k] γ := fun F =>
    slash_eq_of_apply_eq F hγd hγ (hγd00.trans hγ00.symm)
  have hval := toC_sigma_generator γd hγd f g hf hg hg0
  rw [hslash f, hslash g] at hval
  show toC _ * slashQExpC k g γ = slashQExpC k f γ
  rw [hval]
  have e1 : slashQExpC k (⇑g) γ = qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    rw [slashQExpC, ModularForm.SL_slash]; rfl
  have e2 : slashQExpC k (⇑f) γ = qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    rw [slashQExpC, ModularForm.SL_slash]; rfl
  rw [e1, e2, div_mul_cancel₀]
  exact qC_slash_ne_zero γ hγ (qC_ne_zero_of_intSeriesC_ne_zero hg hg0)

end Assembly

end X1DiamondPullback
p2m_reactivate "P2MW.S_ModularCurve_exists_isDiamondAut.X1DiamondPullback"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isDiamondAut.X1DiamondPullback"

theorem solution (M : ℕ) [NeZero M] {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
      ModularCurve.IsDiamondAut M d σ := by
  obtain ⟨γd, hγd, hγd00⟩ := X1DiamondPullback.exists_gamma0_apply_eq M hd
  exact ⟨X1DiamondPullback.sigma γd hγd, X1DiamondPullback.isDiamondAut_sigma M hd hγd hγd00⟩

end S_ModularCurve_exists_isDiamondAut
end P2MW
export P2MW.S_ModularCurve_exists_isDiamondAut (solution)
