-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7703356c-4ec5-53a2-8d12-02dc69d17722

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries
open scoped MatrixGroups ModularForm Manifold

namespace XHDiamondLift

local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

class IsLevel (Γ : Subgroup SL(2, ℤ)) : Prop where
  T_mem : ModularGroup.T ∈ Γ

class Normalizes (Δ Γ : Subgroup SL(2, ℤ)) : Prop where
  conj_mem : ∀ ⦃γ A : SL(2, ℤ)⦄, γ ∈ Δ → A ∈ Γ → γ * A * γ⁻¹ ∈ Γ

section QExp

variable {Γ : Subgroup SL(2, ℤ)}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem one_mem_strictPeriods [IsLevel Γ] : (1 : ℝ) ∈ (GL↑(Γ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (IsLevel.T_mem (Γ := Γ))]
  exact AddSubgroup.mem_zmultiples 1

variable [IsLevel Γ]

theorem qC_mul {a b : ℤ} (f : ModularForm GL↑(Γ) a) (g : ModularForm GL↑(Γ) b) :
    qC ((⇑f : ℍ → ℂ) * ⇑g) = qC ⇑f * qC ⇑g := by
  rw [qC, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods f g, map_mul]
  rfl

theorem qC_coe_mul {a b : ℤ} (f : ModularForm GL↑(Γ) a) (g : ModularForm GL↑(Γ) b) :
    qC (⇑(f.mul g)) = qC ⇑f * qC ⇑g := by
  rw [ModularForm.coe_mul, qC_mul]

theorem qC_add {a : ℤ} (f g : ModularForm GL↑(Γ) a) :
    qC (⇑(f + g)) = qC ⇑f + qC ⇑g := by
  rw [ModularForm.coe_add, qC, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g,
    map_add]
  rfl

theorem qC_neg {a : ℤ} (f : ModularForm GL↑(Γ) a) : qC (⇑(-f)) = -qC ⇑f := by
  rw [ModularForm.coe_neg, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f,
    map_neg]
  rfl

theorem qC_smul {a : ℤ} (c : ℂ) (f : ModularForm GL↑(Γ) a) : qC (⇑(c • f)) = c • qC ⇑f := by
  rw [ModularForm.IsGLPos.coe_smul, qC,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f, qC,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by
  rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by
  rw [qC, qExpansion_one, map_one]

theorem qC_coe_zero {a : ℤ} : qC (⇑(0 : ModularForm GL↑(Γ) a)) = 0 := by
  rw [ModularForm.coe_zero]; exact qC_zero

theorem qC_coe_one : qC (⇑(1 : ModularForm GL↑(Γ) 0)) = 1 := by
  rw [ModularForm.one_coe_eq_one]; exact qC_one

variable [Γ.FiniteIndex]

theorem hasSum_qC {a : ℤ} (f : ModularForm GL↑(Γ) a) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods)
    f.holo' (ModularFormClass.bdd_at_infty f) τ

theorem coe_eq_of_qC_eq {a b : ℤ} (f : ModularForm GL↑(Γ) a) (g : ModularForm GL↑(Γ) b)
    (h : qC ⇑f = qC ⇑g) : (⇑f : ℍ → ℂ) = ⇑g := by
  have h' : qExpansion 1 (⇑f) = qExpansion 1 (⇑g) := HahnSeries.ofPowerSeries_injective h
  funext τ
  have hf := hasSum_qC f τ
  have hg := hasSum_qC g τ
  rw [h'] at hf
  exact hf.unique hg

theorem qC_eq_zero_iff {a : ℤ} (f : ModularForm GL↑(Γ) a) : qC ⇑f = 0 ↔ f = 0 := by
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f, qC]
  constructor
  · intro h
    exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

end QExp

section Slash

variable {Γ Δ : Subgroup SL(2, ℤ)} {k : ℤ}

theorem isBoundedAt_slash [Γ.FiniteIndex] (f : ModularForm GL↑(Γ) k) (γ : SL(2, ℤ))
    {c : OnePoint ℝ} (hc : IsCusp c GL↑(Γ)) : IsBoundedAt c ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) k := by
  have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z GL↑(Γ)).mp hc
  have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) GL↑(Γ) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact hcSL.smul_of_mem ⟨γ, rfl⟩
  exact IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

def slashForm [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) : ModularForm GL↑(Γ) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Γ := Normalizes.conj_mem hγ hA
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

@[scoped simp] theorem coe_slashForm [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem coe_slashForm_SL [Γ.FiniteIndex] [Normalizes Δ Γ] (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)
    (f : ModularForm GL↑(Γ) k) :
    (⇑(slashForm γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [coe_slashForm, ModularForm.SL_slash]

theorem slash_inv_slash (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ⁻¹) ∣[k] γ = F := by
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

theorem slash_slash_inv (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ) ∣[k] γ⁻¹ = F := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem slashForm_ne_zero [Γ.FiniteIndex] [Normalizes Δ Γ] {γ : SL(2, ℤ)} (hγ : γ ∈ Δ)
    {f : ModularForm GL↑(Γ) k} (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h1 : (⇑(slashForm γ hγ f) : ℍ → ℂ) = 0 := by rw [h]; rfl
  rw [coe_slashForm_SL] at h1
  have h2 : (⇑f : ℍ → ℂ) = 0 := by
    rw [← slash_slash_inv (k := k) (⇑f) γ, h1, SlashAction.zero_slash]
  exact DFunLike.ext' (h2.trans ModularForm.coe_zero.symm)

end Slash

section Ratio

variable (Γ : Subgroup SL(2, ℤ)) {Δ : Subgroup SL(2, ℤ)} [IsLevel Γ] [Γ.FiniteIndex]

def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm GL↑(Γ) k), qC ⇑g ≠ 0 ∧ x = qC ⇑f / qC ⇑g

variable {Γ}

theorem isRatio_of_eq {k : ℤ} (f g : ModularForm GL↑(Γ) k) (hg : qC ⇑g ≠ 0) :
    IsRatio Γ (qC ⇑f / qC ⇑g) :=
  ⟨k, f, g, hg, rfl⟩

theorem qC_coe_one_ne_zero : qC (⇑(1 : ModularForm GL↑(Γ) 0)) ≠ 0 := by
  rw [qC_coe_one]; exact one_ne_zero

theorem isRatio_zero : IsRatio Γ 0 :=
  ⟨0, 0, 1, qC_coe_one_ne_zero, by rw [qC_coe_zero, zero_div]⟩

theorem isRatio_one : IsRatio Γ 1 :=
  ⟨0, 1, 1, qC_coe_one_ne_zero, by rw [qC_coe_one, div_one]⟩

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x + y) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  obtain ⟨k', f', g', hg', rfl⟩ := hy
  refine ⟨k + k', f.mul g' + g.mul f', g.mul g', ?_, ?_⟩
  · rw [qC_coe_mul]; exact mul_ne_zero hg hg'
  · rw [qC_add, qC_coe_mul, qC_coe_mul, qC_coe_mul, div_add_div _ _ hg hg']

theorem IsRatio.neg {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ (-x) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  exact ⟨k, -f, g, hg, by rw [qC_neg]; ring⟩

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x * y) := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  obtain ⟨k', f', g', hg', rfl⟩ := hy
  refine ⟨k + k', f.mul f', g.mul g', ?_, ?_⟩
  · rw [qC_coe_mul]; exact mul_ne_zero hg hg'
  · rw [qC_coe_mul, qC_coe_mul, div_mul_div_comm]

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ x⁻¹ := by
  obtain ⟨k, f, g, hg, rfl⟩ := hx
  by_cases hf : qC ⇑f = 0
  · rw [hf, zero_div, inv_zero]; exact isRatio_zero
  · exact ⟨k, g, f, hf, by rw [inv_div]⟩

theorem isRatio_C (c : ℂ) : IsRatio Γ (HahnSeries.C c) := by
  refine ⟨0, c • (1 : ModularForm GL↑(Γ) 0), 1, qC_coe_one_ne_zero, ?_⟩
  rw [qC_smul, qC_coe_one, div_one, ← HahnSeries.C_mul_eq_smul, mul_one]

variable (Γ) in

def ratioField : Subfield (LaurentSeries ℂ) where
  carrier := {x | IsRatio Γ x}
  mul_mem' := IsRatio.mul
  one_mem' := isRatio_one
  add_mem' := IsRatio.add
  zero_mem' := isRatio_zero
  neg_mem' := IsRatio.neg
  inv_mem' _ := IsRatio.inv

variable [Normalizes Δ Γ]

theorem qC_slash_ne_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) {k : ℤ} {g : ModularForm GL↑(Γ) k}
    (hg : qC ⇑g ≠ 0) : qC ((⇑g : ℍ → ℂ) ∣[k] γ) ≠ 0 := by
  rw [← coe_slashForm_SL γ hγ, Ne, qC_eq_zero_iff]
  exact slashForm_ne_zero hγ (fun h => hg ((qC_eq_zero_iff g).mpr h))

theorem cross (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) {k k' : ℤ} (f g : ModularForm GL↑(Γ) k)
    (f' g' : ModularForm GL↑(Γ) k') (hg : qC ⇑g ≠ 0) (hg' : qC ⇑g' ≠ 0)
    (h : qC ⇑f / qC ⇑g = qC ⇑f' / qC ⇑g') :
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
    rwa [← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ g',
      ← coe_slashForm_SL γ hγ f', ← coe_slashForm_SL γ hγ g, qC_mul, qC_mul,
      coe_slashForm_SL, coe_slashForm_SL, coe_slashForm_SL, coe_slashForm_SL] at this
  rw [div_eq_div_iff (qC_slash_ne_zero γ hγ hg) (qC_slash_ne_zero γ hγ hg')]
  exact hq

def pull (γ : SL(2, ℤ)) (x : ratioField Γ) : LaurentSeries ℂ :=
  qC ((⇑(x.2.choose_spec.choose) : ℍ → ℂ) ∣[x.2.choose] γ)
    / qC ((⇑(x.2.choose_spec.choose_spec.choose) : ℍ → ℂ) ∣[x.2.choose] γ)

theorem pull_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x : ratioField Γ) {k : ℤ}
    (f g : ModularForm GL↑(Γ) k) (hg : qC ⇑g ≠ 0)
    (hx : (x : LaurentSeries ℂ) = qC ⇑f / qC ⇑g) :
    pull γ x = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  have hspec := x.2.choose_spec.choose_spec.choose_spec
  exact cross γ hγ _ _ f g hspec.1 hg (hspec.2.symm.trans hx)

theorem pull_one (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) : pull γ (1 : ratioField Γ) = 1 := by
  rw [pull_eq γ hγ 1 (1 : ModularForm GL↑(Γ) 0) 1 qC_coe_one_ne_zero
    (by rw [qC_coe_one, div_one]; rfl)]
  exact div_self (qC_slash_ne_zero γ hγ qC_coe_one_ne_zero)

theorem pull_zero (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) : pull γ (0 : ratioField Γ) = 0 := by
  rw [pull_eq γ hγ 0 (0 : ModularForm GL↑(Γ) 0) 1 qC_coe_one_ne_zero
    (by rw [qC_coe_zero, zero_div]; rfl), ModularForm.coe_zero, SlashAction.zero_slash, qC_zero,
    zero_div]

theorem pull_mul (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x y : ratioField Γ) :
    pull γ (x * y) = pull γ x * pull γ y := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  obtain ⟨k', f', g', hg', hy⟩ := y.2
  have hxy : ((x * y : ratioField Γ) : LaurentSeries ℂ) = qC ⇑(f.mul f') / qC ⇑(g.mul g') := by
    rw [Subfield.coe_mul, hx, hy, qC_coe_mul, qC_coe_mul, div_mul_div_comm]
  rw [pull_eq γ hγ x f g hg hx, pull_eq γ hγ y f' g' hg' hy,
    pull_eq γ hγ (x * y) (f.mul f') (g.mul g') (by rw [qC_coe_mul]; exact mul_ne_zero hg hg') hxy,
    ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2]
  rw [← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ f', ← coe_slashForm_SL γ hγ g,
    ← coe_slashForm_SL γ hγ g', qC_mul, qC_mul, div_mul_div_comm]

theorem pull_add (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x y : ratioField Γ) :
    pull γ (x + y) = pull γ x + pull γ y := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  obtain ⟨k', f', g', hg', hy⟩ := y.2
  have hxy : ((x + y : ratioField Γ) : LaurentSeries ℂ)
      = qC ⇑(f.mul g' + g.mul f') / qC ⇑(g.mul g') := by
    rw [Subfield.coe_add, hx, hy, qC_add, qC_coe_mul, qC_coe_mul, qC_coe_mul,
      div_add_div _ _ hg hg']
  rw [pull_eq γ hγ x f g hg hx, pull_eq γ hγ y f' g' hg' hy,
    pull_eq γ hγ (x + y) _ (g.mul g') (by rw [qC_coe_mul]; exact mul_ne_zero hg hg') hxy,
    ModularForm.coe_add, SlashAction.add_slash, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
    ModularForm.mul_slash_SL2]
  have e1 : qC ((⇑f : ℍ → ℂ) ∣[k] γ * (⇑g' : ℍ → ℂ) ∣[k'] γ
        + (⇑g : ℍ → ℂ) ∣[k] γ * (⇑f' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ)
        + qC ((⇑g : ℍ → ℂ) ∣[k] γ) * qC ((⇑f' : ℍ → ℂ) ∣[k'] γ) := by
    rw [← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ f', ← coe_slashForm_SL γ hγ g,
      ← coe_slashForm_SL γ hγ g', ← ModularForm.coe_mul, ← ModularForm.coe_mul,
      ← ModularForm.coe_add, qC_add, qC_coe_mul, qC_coe_mul]
  have e2 : qC ((⇑g : ℍ → ℂ) ∣[k] γ * (⇑g' : ℍ → ℂ) ∣[k'] γ)
      = qC ((⇑g : ℍ → ℂ) ∣[k] γ) * qC ((⇑g' : ℍ → ℂ) ∣[k'] γ) := by
    rw [← coe_slashForm_SL γ hγ g, ← coe_slashForm_SL γ hγ g', qC_mul]
  rw [e1, e2, div_add_div _ _ (qC_slash_ne_zero γ hγ hg) (qC_slash_ne_zero γ hγ hg')]

def pullHom (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) : ratioField Γ →+* LaurentSeries ℂ where
  toFun := pull γ
  map_one' := pull_one γ hγ
  map_mul' := pull_mul γ hγ
  map_zero' := pull_zero γ hγ
  map_add' := pull_add γ hγ

theorem pull_mem (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x : ratioField Γ) : pull γ x ∈ ratioField Γ := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  rw [pull_eq γ hγ x f g hg hx, ← coe_slashForm_SL γ hγ f, ← coe_slashForm_SL γ hγ g]
  exact isRatio_of_eq _ _ (by rw [coe_slashForm_SL]; exact qC_slash_ne_zero γ hγ hg)

theorem pull_pull_inv (γ : SL(2, ℤ)) (hγ : γ ∈ Δ) (x : ratioField Γ) :
    pull γ ⟨pull γ⁻¹ x, pull_mem γ⁻¹ (inv_mem hγ) x⟩ = x := by
  obtain ⟨k, f, g, hg, hx⟩ := x.2
  have hg' : qC (⇑(slashForm γ⁻¹ (inv_mem hγ) g)) ≠ 0 := by
    rw [coe_slashForm_SL]; exact qC_slash_ne_zero γ⁻¹ (inv_mem hγ) hg
  rw [pull_eq γ hγ _ (slashForm γ⁻¹ (inv_mem hγ) f) (slashForm γ⁻¹ (inv_mem hγ) g) hg'
    (by rw [coe_slashForm_SL, coe_slashForm_SL]; exact pull_eq γ⁻¹ (inv_mem hγ) x f g hg hx),
    coe_slashForm_SL, coe_slashForm_SL, slash_inv_slash, slash_inv_slash, hx]

end Ratio

section Rational

open ModularCurve IntermediateField

variable {Γ Δ : Subgroup SL(2, ℤ)}

abbrev toC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem toC_injective : Function.Injective toC := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact (algebraMap ℚ ℂ).injective this

theorem toC_intSeriesC {f : ℍ → ℂ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) : toC (intSeriesC ℚ p) = qC f := by
  ext n
  rw [coeffMap_coeff, intSeriesC, qC, ← hp, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · exact map_zero _
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

theorem toC_ratio {f g : ℍ → ℂ} {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    toC (intSeriesC ℚ pf / intSeriesC ℚ pg) = qC f / qC g := by
  rw [map_div₀, toC_intSeriesC hf, toC_intSeriesC hg]

theorem qC_ne_zero_of_intSeriesC_ne_zero {g : ℍ → ℂ} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← toC_intSeriesC hg]
  exact fun h => hg0 (toC_injective (by rw [h, map_zero]))

theorem toC_algebraMap (c : ℚ) :
    toC (algebraMap ℚ (LaurentSeries ℚ) c) = HahnSeries.C (algebraMap ℚ ℂ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

variable [IsLevel Γ] [Γ.FiniteIndex]

theorem toC_mem_ratioField {x : LaurentSeries ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ)) :
    toC x ∈ ratioField Γ := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      rw [toC_ratio hf hg]
      exact isRatio_of_eq f g (qC_ne_zero_of_intSeriesC_ne_zero hg hg0)
  | algebraMap c => rw [toC_algebraMap]; exact isRatio_C _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def iota : qExpFunctionFieldC ℚ Γ →+* ratioField Γ :=
  (toC.comp (algebraMap (qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ))).codRestrict (ratioField Γ)
    (fun x => toC_mem_ratioField x.2)

@[scoped simp] theorem coe_iota (x : qExpFunctionFieldC ℚ Γ) :
    ((iota x : ratioField Γ) : LaurentSeries ℂ) = toC x :=
  rfl

def jC : qExpFunctionFieldC ℚ Γ →+* LaurentSeries ℂ :=
  toC.comp (algebraMap (qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ))

theorem jC_apply (x : qExpFunctionFieldC ℚ Γ) : jC x = toC x := rfl

theorem jC_injective : Function.Injective (jC (Γ := Γ)) :=
  toC_injective.comp Subtype.val_injective

variable (Γ Δ) in

def RationalSlash : Prop :=
  ∀ (k : ℤ) (f : ModularForm GL↑(Γ) k) (p : PowerSeries ℤ), IsIntegralQExp f p → ∀ γ ∈ Δ,
    ∃ (D : ℤ) (f₁ : ModularForm GL↑(Γ) k) (p₁ : PowerSeries ℤ), D ≠ 0 ∧ IsIntegralQExp f₁ p₁ ∧
      (⇑f₁ : ℍ → ℂ) = (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] γ)

variable [Normalizes Δ Γ] (hR : RationalSlash Γ Δ) (γ : SL(2, ℤ)) (hγ : γ ∈ Δ)

def psi : qExpFunctionFieldC ℚ Γ →+* LaurentSeries ℂ :=
  (pullHom γ hγ).comp iota

theorem psi_apply (x : qExpFunctionFieldC ℚ Γ) : psi γ hγ x = pull γ (iota x) := rfl

include hR in

theorem exists_psi_generator_eq {k : ℤ} (f g : ModularForm GL↑(Γ) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ y : qExpFunctionFieldC ℚ Γ,
      psi γ hγ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
        = toC y := by
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ := hR k f pf hf γ hγ
  obtain ⟨D', g₁, p₁', hD', hp₁', hg₁⟩ := hR k g pg hg γ hγ
  have hqf₁ : qC ⇑f₁ = (D : ℂ) • qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    have : (⇑f₁ : ℍ → ℂ) = ⇑((D : ℂ) • slashForm γ hγ f) := by
      rw [hf₁, ModularForm.IsGLPos.coe_smul, coe_slashForm_SL]
    rw [this, qC_smul, coe_slashForm_SL]
  have hqg₁ : qC ⇑g₁ = (D' : ℂ) • qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    have : (⇑g₁ : ℍ → ℂ) = ⇑((D' : ℂ) • slashForm γ hγ g) := by
      rw [hg₁, ModularForm.IsGLPos.coe_smul, coe_slashForm_SL]
    rw [this, qC_smul, coe_slashForm_SL]
  have hF : IsIntegralQExp (⇑(((D' : ℤ) : ℂ) • f₁)) (PowerSeries.C (D' : ℤ) * p₁) := by
    unfold IsIntegralQExp at hp₁ ⊢
    rw [map_mul, PowerSeries.map_C, hp₁, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ f₁, PowerSeries.smul_eq_C_mul,
      eq_intCast]
  have hG : IsIntegralQExp (⇑(((D : ℤ) : ℂ) • g₁)) (PowerSeries.C (D : ℤ) * p₁') := by
    unfold IsIntegralQExp at hp₁' ⊢
    rw [map_mul, PowerSeries.map_C, hp₁', ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods _ g₁, PowerSeries.smul_eq_C_mul,
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
    · exact HahnSeries.C_ne_zero
        (mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD')) h1
    · exact qC_slash_ne_zero γ hγ hqg h1
  refine ⟨⟨intSeriesC ℚ (PowerSeries.C (D' : ℤ) * p₁) / intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁'),
    div_mem_qExpFunctionFieldC _ _ hF hG hG0⟩, ?_⟩
  rw [psi_apply, pull_eq γ hγ _ f g hqg (by rw [coe_iota]; exact toC_ratio hf hg)]
  show _ = toC (intSeriesC ℚ (PowerSeries.C (D' : ℤ) * p₁)
    / intSeriesC ℚ (PowerSeries.C (D : ℤ) * p₁'))
  rw [toC_ratio hF hG, hqF, hqG, mul_comm (D' : ℂ) (D : ℂ), ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul, mul_div_mul_left _ _ ?_]
  exact HahnSeries.C_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD'))

include hR in

theorem exists_psi_eq (x : qExpFunctionFieldC ℚ Γ) :
    ∃ y : qExpFunctionFieldC ℚ Γ, psi γ hγ x = toC y := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      exact exists_psi_generator_eq hR γ hγ f g hf hg hg0
  | algebraMap c =>
      refine ⟨⟨algebraMap ℚ (LaurentSeries ℚ) c, IntermediateField.algebraMap_mem _ c⟩, ?_⟩
      let j₁ : ℚ →+* qExpFunctionFieldC ℚ Γ := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (qExpFunctionFieldC ℚ Γ) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun
        (Subsingleton.elim ((psi γ hγ).comp j₁) (toC.comp (algebraMap ℚ (LaurentSeries ℚ)))) c
  | add y z hy hz ihy ihz =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      obtain ⟨z₁, hz₁⟩ := ihz hz
      refine ⟨y₁ + z₁, ?_⟩
      have : (⟨y + z, add_mem hy hz⟩ : qExpFunctionFieldC ℚ Γ) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, hy₁, hz₁, ← map_add]
      rfl
  | inv y hy ihy =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      refine ⟨y₁⁻¹, ?_⟩
      have : (⟨y⁻¹, inv_mem hy⟩ : qExpFunctionFieldC ℚ Γ) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, hy₁, ← map_inv₀]
      rfl
  | mul y z hy hz ihy ihz =>
      obtain ⟨y₁, hy₁⟩ := ihy hy
      obtain ⟨z₁, hz₁⟩ := ihz hz
      refine ⟨y₁ * z₁, ?_⟩
      have : (⟨y * z, mul_mem hy hz⟩ : qExpFunctionFieldC ℚ Γ) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, hy₁, hz₁, ← map_mul]
      rfl

include hR in
theorem psi_mem_range (x : qExpFunctionFieldC ℚ Γ) : psi γ hγ x ∈ (jC (Γ := Γ)).range := by
  obtain ⟨y, hy⟩ := exists_psi_eq hR γ hγ x
  exact ⟨y, hy.symm⟩

def eC : qExpFunctionFieldC ℚ Γ ≃+* (jC (Γ := Γ)).range :=
  RingEquiv.ofBijective (jC (Γ := Γ)).rangeRestrict
    ⟨fun x y h => jC_injective (by
        have := congrArg (fun z : (jC (Γ := Γ)).range => (z : LaurentSeries ℂ)) h
        simpa only [RingHom.coe_rangeRestrict] using this),
      RingHom.rangeRestrict_surjective _⟩

theorem jC_eC_symm (z : (jC (Γ := Γ)).range) :
    jC ((eC (Γ := Γ)).symm z) = (z : LaurentSeries ℂ) := by
  conv_rhs => rw [← (eC (Γ := Γ)).apply_symm_apply z]
  rfl

def sigma0 : qExpFunctionFieldC ℚ Γ →+* qExpFunctionFieldC ℚ Γ :=
  (eC (Γ := Γ)).symm.toRingHom.comp
    ((psi γ hγ).codRestrict (jC (Γ := Γ)).range (psi_mem_range hR γ hγ))

theorem jC_sigma0 (x : qExpFunctionFieldC ℚ Γ) : jC (sigma0 hR γ hγ x) = psi γ hγ x := by
  show jC ((eC (Γ := Γ)).symm _) = _
  rw [jC_eC_symm]
  rfl

theorem sigma0_injective : Function.Injective (sigma0 hR γ hγ) := by
  intro x y h
  have h1 : psi γ hγ x = psi γ hγ y := by rw [← jC_sigma0 hR, ← jC_sigma0 hR, h]
  exact (psi γ hγ).injective h1

theorem sigma0_surjective : Function.Surjective (sigma0 hR γ hγ) := by
  intro x
  refine ⟨sigma0 hR γ⁻¹ (inv_mem hγ) x, jC_injective ?_⟩
  rw [jC_sigma0, psi_apply]
  have hι : iota (sigma0 hR γ⁻¹ (inv_mem hγ) x)
      = ⟨pull γ⁻¹ (iota x), pull_mem γ⁻¹ (inv_mem hγ) (iota x)⟩ := by
    apply Subtype.ext
    show jC (sigma0 hR γ⁻¹ (inv_mem hγ) x) = pull γ⁻¹ (iota x)
    rw [jC_sigma0, psi_apply]
  rw [hι, pull_pull_inv γ hγ]
  rfl

def sigma : qExpFunctionFieldC ℚ Γ ≃+* qExpFunctionFieldC ℚ Γ :=
  RingEquiv.ofBijective (sigma0 hR γ hγ) ⟨sigma0_injective hR γ hγ, sigma0_surjective hR γ hγ⟩

theorem sigma_apply (x : qExpFunctionFieldC ℚ Γ) : sigma hR γ hγ x = sigma0 hR γ hγ x := rfl

theorem toC_sigma (x : qExpFunctionFieldC ℚ Γ) :
    toC ((sigma hR γ hγ x : qExpFunctionFieldC ℚ Γ) : LaurentSeries ℚ) = pull γ (iota x) := by
  rw [sigma_apply, ← jC_apply, jC_sigma0, psi_apply]

theorem toC_sigma_generator {k : ℤ} (f g : ModularForm GL↑(Γ) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    toC ((sigma hR γ hγ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        qExpFunctionFieldC ℚ Γ) : LaurentSeries ℚ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  rw [toC_sigma,
    pull_eq γ hγ _ f g (qC_ne_zero_of_intSeriesC_ne_zero hg hg0) (by rw [coe_iota]; exact toC_ratio hf hg)]

end Rational

section Stretch

variable {Γ Γ' Δ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {ℓ : ℕ} {k : ℤ}

private theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem heckeDiagMatrix_mul_eq (hℓ : ℓ ≠ 0) {γ γ₁ : SL(2, ℤ)}
    (h00 : γ₁ 0 0 = γ 0 0) (h01 : γ₁ 0 1 = (ℓ : ℤ) * γ 0 1)
    (h10 : (ℓ : ℤ) * γ₁ 1 0 = γ 1 0) (h11 : γ₁ 1 1 = γ 1 1) :
    heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ₁ * heckeDiagMatrix ℓ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, mapGL_coe_eq, mapGL_coe_eq, val_heckeDiagMatrix hℓ]
  have e10 : ((γ 1 0 : ℤ) : ℝ) = (ℓ : ℝ) * ((γ₁ 1 0 : ℤ) : ℝ) := by
    rw [← h10]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h11, e10, mul_comm]

theorem isCusp_heckeDiagMatrix_smul (hℓ : ℓ ≠ 0) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (heckeDiagMatrix ℓ • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  let gQ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hℓ)
  have hg : gQ.map (Rat.castHom ℝ) = heckeDiagMatrix ℓ := by
    apply Units.ext
    rw [val_heckeDiagMatrix hℓ]
    show (gQ : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
    ext i j; fin_cases i <;> fin_cases j <;> simp [gQ]
  refine ⟨gQ • c₀, ?_⟩
  rw [← hg, ← Rat.coe_castHom, OnePoint.map_smul]

variable (hΓ' : ∀ γ ∈ Γ', ∃ γ₁ ∈ Γ,
  γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1)

def stretchSlash (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) : ModularForm GL↑(Γ') k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    obtain ⟨γ₁, hγ₁, h00, h01, h10, h11⟩ := hΓ' γ hγ
    rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_eq hℓ h00 h01 h10 h11,
      SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₁)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := by
      refine hc.mono ?_
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩
    have hc' : IsCusp (heckeDiagMatrix ℓ • c) GL↑(Γ) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact isCusp_heckeDiagMatrix_smul hℓ hcSL
    exact IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

@[scoped simp] theorem coe_stretchSlash (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) :
    (⇑(stretchSlash hΓ' hℓ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ := rfl

theorem stretchSlash_apply (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) (τ : ℍ) :
    stretchSlash hΓ' hℓ f τ = (ℓ : ℂ) ^ (k - 1) * f (heckeDiagMatrix ℓ • τ) :=
  slash_heckeDiagMatrix_apply k hℓ _ τ

def stretch (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) : ModularForm GL↑(Γ') k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ • stretchSlash hΓ' hℓ f

theorem coe_stretch_eq_smul (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) :
    (⇑(stretch hΓ' hℓ f) : ℍ → ℂ) = ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ) := by
  rw [stretch, ModularForm.IsGLPos.coe_smul, coe_stretchSlash]

theorem stretch_apply (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) (τ : ℍ) :
    stretch hΓ' hℓ f τ = f (heckeDiagMatrix ℓ • τ) := by
  have hpk : ((ℓ : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ)
  rw [stretch, ModularForm.IsGLPos.smul_apply, stretchSlash_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hpk, one_mul]

theorem coe_stretch (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) :
    (⇑(stretch hΓ' hℓ f) : ℍ → ℂ) = fun τ => f (heckeDiagMatrix ℓ • τ) :=
  funext (stretch_apply hΓ' hℓ f)

theorem stretch_slash [Normalizes Δ Γ] (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k)
    {γ γ' : SL(2, ℤ)} (hγ' : γ' ∈ Δ)
    (hc : heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ) :
    (⇑(stretch hΓ' hℓ f) : ℍ → ℂ) ∣[k] γ = ⇑(stretch hΓ' hℓ (slashForm γ' hγ' f)) := by
  rw [coe_stretch_eq_smul, coe_stretch_eq_smul, ModularForm.SL_smul_slash, ModularForm.SL_slash,
    ← SlashAction.slash_mul, coe_slashForm, ← SlashAction.slash_mul]
  exact congrArg (fun A => ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f : ℍ → ℂ) ∣[k] A)) hc

theorem qCoeff_stretch [IsLevel Γ] (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(stretch hΓ' hℓ f)) n
      = if ℓ ∣ n then ModularFormClass.qCoeff (⇑f) (n / ℓ) else 0 := by
  rw [coe_stretch]
  exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods) f.holo'
    (ModularFormClass.bdd_at_infty f) hℓ n

omit [Γ.FiniteIndex] in

theorem ofPowerSeries_eq_qExpand {R : Type*} [CommRing R] (ℓ : ℕ) [NeZero ℓ]
    (p q : PowerSeries R)
    (h : ∀ n : ℕ, PowerSeries.coeff n p = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) q else 0) :
    HahnSeries.ofPowerSeries ℤ R p = ModularCurve.qExpand R ℓ (HahnSeries.ofPowerSeries ℤ R q) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    rw [ModularCurve.qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    by_cases hm' : m' < 0
    · have : (ℓ : ℤ) * m' < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hℓ) hm'
      rw [if_pos this, if_pos hm']
    · have hm'0 : 0 ≤ m' := le_of_not_gt hm'
      have hprod : ¬ (ℓ : ℤ) * m' < 0 := not_lt.mpr (mul_nonneg (by positivity) hm'0)
      rw [if_neg hprod, if_neg hm', h]
      have habs : ((ℓ : ℤ) * m').natAbs = ℓ * m'.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [habs, if_pos (dvd_mul_right ℓ _), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h]
      have : ¬ ℓ ∣ m.natAbs := by
        intro h'
        apply hdvd
        have hm0 : 0 ≤ m := le_of_not_gt hm
        rw [← Int.natAbs_of_nonneg hm0]
        exact_mod_cast h'
      rw [if_neg this]

theorem qC_stretch [IsLevel Γ] [NeZero ℓ] (f : ModularForm GL↑(Γ) k) :
    qC (⇑(stretch hΓ' (NeZero.ne ℓ) f)) = ModularCurve.qExpand ℂ ℓ (qC ⇑f) := by
  refine ofPowerSeries_eq_qExpand ℓ _ _ (fun n => ?_)
  have h := qCoeff_stretch hΓ' (NeZero.ne ℓ) f n
  simp only [ModularFormClass.qCoeff] at h
  exact h

def expandPS (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

omit [Γ.FiniteIndex] in
@[scoped simp] theorem coeff_expandPS (ℓ : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandPS ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 :=
  PowerSeries.coeff_mk _ _

theorem isIntegralQExp_stretch [IsLevel Γ] (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(Γ) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p) :
    ModularCurve.IsIntegralQExp (stretch hΓ' hℓ f) (expandPS ℓ p) := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  have h := qCoeff_stretch hΓ' hℓ f n
  simp only [ModularFormClass.qCoeff] at h
  rw [h, coeff_expandPS]
  split_ifs with hdvd
  · exact hp.coeff (n / ℓ)
  · simp

omit [Γ.FiniteIndex] in

theorem intSeriesC_expandPS (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] (p : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (expandPS ℓ p)
      = ModularCurve.qExpand K ℓ (ModularCurve.intSeriesC K p) := by
  refine ofPowerSeries_eq_qExpand ℓ _ _ (fun n => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_expandPS]
  split_ifs
  · rfl
  · exact map_zero _

end Stretch

section Level

open ModularCurve IntermediateField

theorem Gamma0_mul_le (M ℓ : ℕ) : Gamma0 (M * ℓ) ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom (dvd_mul_right M ℓ) (ZMod M)) hA
  rwa [map_intCast, map_zero] at this

scoped instance isLevel_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : IsLevel (CohCarrier.GammaH M H) :=
  ⟨translation_mem_GammaH M H⟩

scoped instance isLevel_GammaH_inf_Gamma0 (M : ℕ) (H : Subgroup (ZMod M)ˣ) (t : ℕ) :
    IsLevel (CohCarrier.GammaH M H ⊓ Gamma0 t) :=
  ⟨⟨IsLevel.T_mem, by simp [Gamma0_mem, ModularGroup.T]⟩⟩

private theorem _root_.XHDiamondLift.conj_mem_GammaH {M : ℕ} {H : Subgroup (ZMod M)ˣ} {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (hA : A ∈ CohCarrier.GammaH M H) : γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H :=
  CohCarrier.conj_mem_GammaH M H (⟨γ, hγ⟩ : Gamma0 M) ⟨A, hA⟩

p2m_export "XHDiamondLift" "conj_mem_GammaH"
scoped instance normalizes_Gamma0_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    Normalizes (Gamma0 M) (CohCarrier.GammaH M H) :=
  ⟨fun _ _ hγ hA => conj_mem_GammaH hγ hA⟩

scoped instance normalizes_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :
    Normalizes (Gamma0 (M * ℓ)) (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) :=
  ⟨fun _ _ hγ hA => ⟨conj_mem_GammaH (Gamma0_mul_le M ℓ hγ) hA.1,
    (Gamma0 (M * ℓ)).mul_mem ((Gamma0 (M * ℓ)).mul_mem hγ hA.2) ((Gamma0 (M * ℓ)).inv_mem hγ)⟩⟩

theorem neZero_mul (M ℓ : ℕ) [NeZero M] [NeZero ℓ] : NeZero (M * ℓ) :=
  ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩

scoped instance finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance finiteIndex_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI := neZero_mul M ℓ
  infer_instance

theorem Gamma1_mul_le_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :
    Gamma1 (M * ℓ) ≤ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) :=
  le_inf ((Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (Gamma1_le_GammaH M H)) (Gamma1_in_Gamma0 _)

theorem cocycle (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ∀ γ ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ CohCarrier.GammaH M H,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨hγ0M, hunit⟩ := CohCarrier.mem_GammaH_iff.mp hγH
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  have h0 : (⟨_, hdet'⟩ : SL(2, ℤ)) ∈ Gamma0 M := by
    apply Gamma0_mem.mpr
    show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CohCarrier.mem_GammaH_iff]
    refine ⟨h0, ?_⟩
    have : CohCarrier.gamma0Units M ⟨_, h0⟩ = CohCarrier.gamma0Units M ⟨γ, hγ0M⟩ := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
      rfl
    rw [this]
    exact hunit
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

theorem exists_coprime_lift (M ℓ : ℕ) [NeZero M] [NeZero ℓ] {d : ℕ} (hd : d.Coprime M) :
    ∃ d' : ℕ, d'.Coprime (M * ℓ) ∧ (d' : ZMod M) = d := by
  haveI := neZero_mul M ℓ
  obtain ⟨u', hu'⟩ := ZMod.unitsMap_surjective (dvd_mul_right M ℓ) (ZMod.unitOfCoprime d hd)
  refine ⟨(u' : ZMod (M * ℓ)).val, ZMod.val_coe_unit_coprime u', ?_⟩
  rw [ZMod.natCast_val, ← ZMod.unitsMap_val (dvd_mul_right M ℓ), hu', ZMod.coe_unitOfCoprime]

theorem exists_gammas (M ℓ : ℕ) [NeZero M] [NeZero ℓ] {d : ℕ} (hd : d.Coprime M) :
    ∃ γ γ' : SL(2, ℤ), γ ∈ Gamma0 (M * ℓ) ∧ γ' ∈ Gamma0 M ∧
      ((γ 0 0 : ℤ) : ZMod M) = d ∧ ((γ' 0 0 : ℤ) : ZMod M) = d ∧
      heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
        = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ := by
  obtain ⟨d', hd', hdd⟩ := exists_coprime_lift M ℓ hd
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hd'
  rw [Nat.cast_mul] at huv
  have hdet : Matrix.det !![(d' : ℤ), -v; (M : ℤ) * ℓ, u] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination huv
  have hdet' : Matrix.det !![(d' : ℤ), -(v * ℓ); (M : ℤ), u] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination huv
  refine ⟨⟨_, hdet⟩, ⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    show ((((M : ℤ) * ℓ : ℤ)) : ZMod (M * ℓ)) = 0
    rw [← Nat.cast_mul, Int.cast_natCast, ZMod.natCast_self]
  · rw [Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  · show (((d' : ℤ)) : ZMod M) = (d : ZMod M)
    rw [Int.cast_natCast, hdd]
  · show (((d' : ℤ)) : ZMod M) = (d : ZMod M)
    rw [Int.cast_natCast, hdd]
  · refine heckeDiagMatrix_mul_eq (NeZero.ne ℓ) rfl ?_ ?_ rfl
    · show -((v : ℤ) * ℓ) = (ℓ : ℤ) * (-v)
      ring
    · show (ℓ : ℤ) * (M : ℤ) = (M : ℤ) * ℓ
      ring

theorem rationalSlash_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    RationalSlash (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (Gamma0 (M * ℓ)) := by
  intro k f p hp γ hγ
  haveI := neZero_mul M ℓ
  have hle : Gamma1 (M * ℓ) ≤ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) := Gamma1_mul_le_level M H ℓ
  have hle' : GL↑(Gamma1 (M * ℓ)) ≤ GL↑(CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) := Subgroup.map_mono hle
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * ℓ) (restrictForm hle' f)
      (by rw [IsIntegralQExp, coe_restrictForm]; exact hp) γ hγ
  refine ⟨D, (D : ℂ) • slashForm γ hγ f, p₁, hD, ?_, ?_⟩
  · have : (⇑((D : ℂ) • slashForm γ hγ f) : ℍ → ℂ) = ⇑f₁ := by
      rw [ModularForm.IsGLPos.coe_smul, coe_slashForm_SL, hf₁, coe_restrictForm]
    rw [IsIntegralQExp, this]
    exact hp₁
  · rw [ModularForm.IsGLPos.coe_smul, coe_slashForm_SL]

example : True := trivial

theorem ringHom_ext_adjoin {S : Set (LaurentSeries ℚ)} {R : Type*} [DivisionRing R]
    (φ ψ : IntermediateField.adjoin ℚ S →+* R)
    (h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ S),
      φ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩ = ψ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩) :
    φ = ψ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap c =>
      let j₁ : ℚ →+* IntermediateField.adjoin ℚ S := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (IntermediateField.adjoin ℚ S) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun (Subsingleton.elim (φ.comp j₁) (ψ.comp j₁)) c
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

abbrev FB (M : ℕ) (H : Subgroup (ZMod M)ˣ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)

abbrev FT (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))

theorem FB_le_FT (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : FB M H ≤ FT M H ℓ :=
  qExpFunctionFieldC_mono ℚ inf_le_left

theorem toC_qExpand (ℓ : ℕ) [NeZero ℓ] (x : LaurentSeries ℚ) :
    toC (qExpand ℚ ℓ x) = qExpand ℂ ℓ (toC x) := by
  ext n
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeffMap_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn,
      ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn, map_zero]

section Genuine

local notation "ℚbar" => AlgebraicClosure ℚ

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {H : Subgroup (ZMod M)ˣ} {d : (ZMod M)ˣ}
  {σd : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσd : IsDiamondAutHBar M H d σd)
  {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hγ' : γ' ∈ Gamma0 M)
  (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) (hγ'd : ((γ' 0 0 : ℤ) : ZMod M) = (d : ZMod M))
  (hc : heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
    = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ)

def genH {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    xHFunctionFieldBar M H :=
  ⟨coeffEmb ℚbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange ℚbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

include hσd in

theorem witness {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ ∈ Gamma0 M) (hγ₀d : ((γ₀ 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ y : LaurentSeries ℚ, y ∈ FB M H ∧
      ((σd (genH f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y ∧
      toC y = qC ((⇑f : ℍ → ℂ) ∣[k] γ₀) / qC ((⇑g : ℍ → ℂ) ∣[k] γ₀) := by
  obtain ⟨y, hyF, hy, hrel⟩ := hσd k f g pf pg hf hg hg0 γ₀ hγ₀ hγ₀d
  refine ⟨y, hyF, hy, ?_⟩
  rw [eq_div_iff (qC_slash_ne_zero (Γ := CohCarrier.GammaH M H) γ₀ hγ₀
    (qC_ne_zero_of_intSeriesC_ne_zero hg hg0))]
  exact hrel

theorem coeffEmb_injective' : Function.Injective (coeffEmb ℚbar) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℚbar => z.coeff n) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ ℚbar).injective this

include hσd hγd in

theorem tau0_incl_generator {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) {y : LaurentSeries ℚ}
    (hy : ((σd (genH f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y) :
    ((sigma (rationalSlash_level M H ℓ) γ hγ
        ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, FB_le_FT M H ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          FT M H ℓ) : LaurentSeries ℚ) = y := by
  obtain ⟨y', -, hy', hrel'⟩ := witness hσd (Gamma0_mul_le M ℓ hγ) hγd f g hf hg hg0
  have hyy : y = y' := coeffEmb_injective' (hy.symm.trans hy')
  apply toC_injective
  have hle' : GL↑(CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≤ GL↑(CohCarrier.GammaH M H) :=
    Subgroup.map_mono inf_le_left
  have hf' : IsIntegralQExp (restrictForm hle' f) pf := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hf
  have hg' : IsIntegralQExp (restrictForm hle' g) pg := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hg
  have h1 := toC_sigma_generator (rationalSlash_level M H ℓ) γ hγ (restrictForm hle' f)
    (restrictForm hle' g) hf' hg' hg0
  rw [coe_restrictForm, coe_restrictForm] at h1
  rw [hyy, hrel']
  exact h1

include hσd hγ' hγ'd hc in

theorem tau0_qExpand_generator {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0)
    (hmem : qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ FT M H ℓ) {y : LaurentSeries ℚ}
    (hy : ((σd (genH f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y) :
    ((sigma (rationalSlash_level M H ℓ) γ hγ ⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ :
          FT M H ℓ) : LaurentSeries ℚ) = qExpand ℚ ℓ y := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨y', -, hy', hrel'⟩ := witness hσd hγ' hγ'd f g hf hg hg0
  have hyy : y = y' := coeffEmb_injective' (hy.symm.trans hy')
  apply toC_injective

  have hSf : IsIntegralQExp (stretch (Γ' := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (cocycle M H ℓ) hℓ f)
      (expandPS ℓ pf) := isIntegralQExp_stretch _ hℓ f hf
  have hSg : IsIntegralQExp (stretch (Γ' := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (cocycle M H ℓ) hℓ g)
      (expandPS ℓ pg) := isIntegralQExp_stretch _ hℓ g hg
  have hSg0 : intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (ModularCurve.qExpand_injective ℓ (by rw [h, map_zero]))
  have hx : (⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ : FT M H ℓ)
      = ⟨intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg),
          div_mem_qExpFunctionFieldC _ _ hSf hSg hSg0⟩ := by
    apply Subtype.ext
    show qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg)
      = intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)
    rw [map_div₀, intSeriesC_expandPS, intSeriesC_expandPS]
  rw [hx, toC_sigma_generator (rationalSlash_level M H ℓ) γ hγ _ _ hSf hSg hSg0]

  rw [stretch_slash (cocycle M H ℓ) hℓ f hγ' hc, stretch_slash (cocycle M H ℓ) hℓ g hγ' hc,
    qC_stretch, qC_stretch, ← map_div₀, coe_slashForm_SL, coe_slashForm_SL, ← hrel', toC_qExpand, hyy]

end Genuine

end Level

section BaseChange

open ModularCurve IntermediateField AlgebraicCurve

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ ℓ x) = qExpand L ℓ (coeffEmb L x) := by
  ext n
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeffEmb_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn,
      ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hn, map_zero]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem laurentBaseChange_eq_adjoin_ratios (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    laurentBaseChange ℚbar (FB M H)
      = IntermediateField.adjoin ℚbar (⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H)) := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    show coeffEmb ℚbar y ∈ IntermediateField.adjoin ℚbar (⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H))
    have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hy
    clear hy
    induction hy' using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin ℚbar _ ⟨x, hx, rfl⟩
    | algebraMap r =>
        rw [eq_ratCast, map_ratCast]
        exact SubfieldClass.ratCast_mem _ r
    | add x x' _ _ ihx ihx' => rw [map_add]; exact add_mem ihx ihx'
    | inv x _ ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x x' _ _ ihx ihx' => rw [map_mul]; exact mul_mem ihx ihx'
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange ℚbar (intFormRatiosC_subset ℚ _ hx)

section Main

variable (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ)
  {σd : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσd : IsDiamondAutHBar M H d σd)
  {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hγ' : γ' ∈ Gamma0 M)
  (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) (hγ'd : ((γ' 0 0 : ℤ) : ZMod M) = (d : ZMod M))
  (hc : heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
    = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ)
  (τ : laurentBaseChange ℚbar (FT M H ℓ) ≃ₐ[ℚbar] laurentBaseChange ℚbar (FT M H ℓ))
  (hτ : ∀ y : FT M H ℓ,
    ((τ ⟨coeffEmb ℚbar (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚbar y.2⟩ :
        laurentBaseChange ℚbar (FT M H ℓ)) : LaurentSeries ℚbar)
      = coeffEmb ℚbar ((sigma (rationalSlash_level M H ℓ) γ hγ y : FT M H ℓ) : LaurentSeries ℚ))

include hσd hγd hτ in

theorem comp_alpha_eq :
    (τ : laurentBaseChange ℚbar (FT M H ℓ) →ₐ[ℚbar] laurentBaseChange ℚbar (FT M H ℓ)).comp
        (heckeAlphaHBar ℚbar M H ℓ)
      = (heckeAlphaHBar ℚbar M H ℓ).comp
          (σd : xHFunctionFieldBar M H →ₐ[ℚbar] xHFunctionFieldBar M H) := by
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H))
    (laurentBaseChange_eq_adjoin_ratios M H) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨y, hyF, hy, -⟩ := witness hσd (Gamma0_mul_le M ℓ hγ) hγd f g hf hg hg0
  apply Subtype.ext
  show ((τ (heckeAlphaHBar ℚbar M H ℓ (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
    = ((heckeAlphaHBar ℚbar M H ℓ (σd (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
  have e1 : heckeAlphaHBar ℚbar M H ℓ (genH f g hf hg hg0)
      = (⟨coeffEmb ℚbar ((⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            FB_le_FT M H ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : FT M H ℓ) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange ℚbar
            (⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
              FB_le_FT M H ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : FT M H ℓ).2⟩ :
            laurentBaseChange ℚbar (FT M H ℓ)) := by
    apply Subtype.ext
    rw [coe_heckeAlphaHBar]
    rfl
  rw [e1, hτ, coe_heckeAlphaHBar, hy, tau0_incl_generator hσd hγ hγd f g hf hg hg0 hy]

include hσd hγd hγ' hγ'd hc hτ in

theorem comp_beta_eq (Kβ : HeckeBetaHDefined M H ℓ) :
    (τ : laurentBaseChange ℚbar (FT M H ℓ) →ₐ[ℚbar] laurentBaseChange ℚbar (FT M H ℓ)).comp
        (heckeBetaHBar ℚbar M H ℓ)
      = (heckeBetaHBar ℚbar M H ℓ).comp
          (σd : xHFunctionFieldBar M H →ₐ[ℚbar] xHFunctionFieldBar M H) := by
  have Kβ' : ∀ y ∈ FB M H, qExpand ℚ ℓ y ∈ FT M H ℓ := Kβ
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H))
    (laurentBaseChange_eq_adjoin_ratios M H) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨y, hyF, hy, -⟩ := witness hσd hγ' hγ'd f g hf hg hg0
  apply Subtype.ext
  show ((τ (heckeBetaHBar ℚbar M H ℓ (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
    = ((heckeBetaHBar ℚbar M H ℓ (σd (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
  have hmem : qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ FT M H ℓ :=
    Kβ' _ (div_mem_qExpFunctionFieldC f g hf hg hg0)
  have e1 : heckeBetaHBar ℚbar M H ℓ (genH f g hf hg hg0)
      = (⟨coeffEmb ℚbar ((⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ : FT M H ℓ) :
            LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚbar hmem⟩ :
          laurentBaseChange ℚbar (FT M H ℓ)) := by
    apply Subtype.ext
    rw [coe_heckeBetaHBar M H ℓ Kβ]
    exact (coeffEmb_qExpand ℚbar ℓ _).symm
  rw [e1, hτ, coe_heckeBetaHBar M H ℓ Kβ, hy, ← coeffEmb_qExpand,
    tau0_qExpand_generator hσd hγ hγ' hγ'd hc f g hf hg hg0 hmem hy]

end Main

theorem main (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) :
    ∃ τ : laurentBaseChange ℚbar (xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃ₐ[ℚbar]
        laurentBaseChange ℚbar (xHTopFunctionFieldC ℚ M H (M * ℓ)),
      SemilinearAut.IntertwinesAlong (heckeAlphaHBar ℚbar M H ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut τ) ∧
        SemilinearAut.IntertwinesAlong (heckeBetaHBar ℚbar M H ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut τ) := by
  by_cases hex : ∃ σ : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H, IsDiamondAutHBar M H d σ
  · have hσd : IsDiamondAutHBar M H d (diamondAutHBar M H d) := isDiamondAutHBar_diamondAutHBar hex
    obtain ⟨γ, γ', hγ, hγ', hγd, hγ'd, hc⟩ := exists_gammas M ℓ (ZMod.val_coe_unit_coprime d)
    rw [ZMod.natCast_zmod_val] at hγd hγ'd
    obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover ℚbar (FT M H ℓ)
      (sigma (rationalSlash_level M H ℓ) γ hγ)
    have Iα : SemilinearAut.IntertwinesAlong (heckeAlphaHBar ℚbar M H ℓ).toRingHom
        (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut τ) := by
      intro x
      rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
      exact AlgHom.congr_fun (comp_alpha_eq M ℓ H d hσd hγ hγd τ hτ) x
    refine ⟨τ, Iα, ?_⟩
    by_cases Kβ : HeckeBetaHDefined M H ℓ
    · intro x
      rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
      exact AlgHom.congr_fun (comp_beta_eq M ℓ H d hσd hγ hγ' hγd hγ'd hc τ hτ Kβ) x
    · rw [heckeBetaHBar_of_not M H ℓ Kβ]
      exact Iα
  · have h0 : diamondAutHBar M H d = AlgEquiv.refl := diamondAutHBar_of_not hex
    refine ⟨AlgEquiv.refl, fun x => ?_, fun x => ?_⟩ <;>
      simp only [h0, SemilinearAut.ofAlgAut_smul, AlgEquiv.coe_refl, id_eq]

end BaseChange

end XHDiamondLift
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.XHDiamondLift"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.XHDiamondLift"

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) :=
  XHDiamondLift.main M ℓ H d

end S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar (solution)
