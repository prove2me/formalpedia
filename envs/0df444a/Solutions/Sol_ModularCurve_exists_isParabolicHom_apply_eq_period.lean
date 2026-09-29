-- Prove2me | solution 1 for ModularCurve.exists_isParabolicHom_apply_eq_period
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e634fbc1-cfb0-5f6c-b5cc-f112493b2760

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_period

open scoped MatrixGroups
open UpperHalfPlane Filter Topology

namespace ModularCurve
p2m_export "ModularCurve" "period Period.IsParabolicHom HasEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace PeriodParabolic
p2m_open "ModularCurve"

open ModularCurve.Period

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

theorem const_eq_zero_of_tendsto_sub {α : Type*} {l : Filter α} [l.NeBot]
    {g h : α → ℂ} {L c : ℂ} (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hc : ∀ a, g a - h a = c) : c = 0 := by
  have hsub : Tendsto (fun a => g a - h a) l (𝓝 (L - L)) := hg.sub hh
  rw [sub_self] at hsub
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun a => (hc a).symm) hsub

theorem period_conj_T_zpow_eq_zero {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F) (δ : SL(2, ℤ)) {L : ℂ}
    (hlim : Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) (n : ℤ) (ε : SL(2, ℤ))
    (hε : ε = 1 ∨ ε = -1) (hγ : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ) :
    hF.period ⟨ε * (δ * ModularGroup.T ^ n * δ⁻¹), hγ⟩ = 0 := by
  refine const_eq_zero_of_tendsto_sub
    (g := fun w : ℍ => F ((ε * (δ * ModularGroup.T ^ n * δ⁻¹)) • ((δ : SL(2, ℤ)) • w)))
    (h := fun w : ℍ => F (δ • w)) (L := L) ?_ hlim
    fun w => hF.sub_eq_period ⟨ε * (δ * ModularGroup.T ^ n * δ⁻¹), hγ⟩ (δ • w)
  have hkey : ∀ w : ℍ, (ε * (δ * ModularGroup.T ^ n * δ⁻¹)) • ((δ : SL(2, ℤ)) • w)
      = δ • (ModularGroup.T ^ n • w) := by
    intro w
    have hcentral : (ε * (δ * ModularGroup.T ^ n * δ⁻¹)) • ((δ : SL(2, ℤ)) • w)
        = (δ * ModularGroup.T ^ n * δ⁻¹) • ((δ : SL(2, ℤ)) • w) := by
      rcases hε with hε | hε
      · rw [hε, one_mul]
      · rw [hε, neg_one_mul]
        exact ModularGroup.SL_neg_smul _ _
    rw [hcentral, ← mul_smul, ← mul_smul]
    congr 1
    group
  have hfun : (fun w : ℍ =>
        F ((ε * (δ * ModularGroup.T ^ n * δ⁻¹)) • ((δ : SL(2, ℤ)) • w)))
      = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => ((n : ℤ) : ℝ) +ᵥ w := by
    funext w
    simp only [Function.comp_apply, hkey w, ← UpperHalfPlane.modular_T_zpow_smul]
  rw [hfun]
  exact hlim.comp (tendsto_vadd_atImInfty ((n : ℤ) : ℝ))

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_entries (A : SL(2, ℤ)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  have h : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

theorem exists_col_eq {p r : ℤ} (h : IsCoprime p r) :
    ∃ δ : SL(2, ℤ), δ 0 0 = p ∧ δ 1 0 = r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![p, -v; r, u], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination huv

theorem eq_T_zpow_of_col {M : SL(2, ℤ)} (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) :
    M = ModularGroup.T ^ (M 0 1) := by
  have hdet := det_entries M
  rw [h00, h10, one_mul, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [ModularGroup.coe_T_zpow]

theorem exists_isCoprime_fixed {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hc : γ 1 0 ≠ 0) :
    ∃ p r : ℤ, IsCoprime p r ∧
      γ 0 0 * p + γ 0 1 * r = p ∧ γ 1 0 * p + γ 1 1 * r = r := by
  rw [Matrix.trace_fin_two] at htr
  have hdet := det_entries γ
  have hgcd_pos : 0 < Int.gcd (γ 0 0 - 1) (γ 1 0) := by
    rcases Nat.eq_zero_or_pos (Int.gcd (γ 0 0 - 1) (γ 1 0)) with h | h
    · exact absurd (Int.gcd_eq_zero_iff.mp h).2 hc
    · exact h
  obtain ⟨p, r, hpr, hp, hr⟩ := Int.exists_gcd_one hgcd_pos
  set g : ℤ := (Int.gcd (γ 0 0 - 1) (γ 1 0) : ℤ) with hgdef
  have hgne : g ≠ 0 := by
    rw [hgdef]
    exact_mod_cast hgcd_pos.ne'
  refine ⟨p, r, Int.isCoprime_iff_gcd_eq_one.mpr hpr, ?_, ?_⟩
  · have key : g * (γ 0 0 * p + γ 0 1 * r - p) = 0 := by
      linear_combination (-(γ 0 0 - 1)) * hp - γ 0 1 * hr + γ 0 0 * htr - hdet
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith
  · have key : g * (γ 1 0 * p + γ 1 1 * r - r) = 0 := by
      linear_combination (-(γ 1 0)) * hp - (γ 1 1 - 1) * hr + γ 1 0 * htr
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith

theorem exists_conj_T_zpow_of_trace_eq_two {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) :
    ∃ (δ : SL(2, ℤ)) (n : ℤ), γ = δ * ModularGroup.T ^ n * δ⁻¹ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [Matrix.trace_fin_two] at htr
    have hsq : (γ 0 0 - 1) ^ 2 = 0 := by
      linear_combination γ 0 0 * htr - hdet
    have ha : γ 0 0 = 1 := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    refine ⟨1, γ 0 1, ?_⟩
    rw [inv_one, mul_one, one_mul]
    exact eq_T_zpow_of_col ha hc
  · obtain ⟨p, r, hpr, hfix1, hfix2⟩ := exists_isCoprime_fixed htr hc
    obtain ⟨δ, hδ00, hδ10⟩ := exists_col_eq hpr
    obtain ⟨hi00, hi01, hi10, hi11⟩ := inv_entries δ
    have hδdet := det_entries δ
    rw [hδ00, hδ10] at hδdet
    have hγδ0 : (γ * δ) 0 0 = δ 0 0 := by
      rw [mul_entry γ δ 0 0, hδ00, hδ10]; exact hfix1
    have hγδ1 : (γ * δ) 1 0 = δ 1 0 := by
      rw [mul_entry γ δ 1 0, hδ00, hδ10]; exact hfix2
    have hM00 : (δ⁻¹ * (γ * δ)) 0 0 = 1 := by
      rw [mul_entry δ⁻¹ (γ * δ) 0 0, hγδ0, hγδ1, hi00, hi01, hδ00, hδ10]
      linear_combination hδdet
    have hM10 : (δ⁻¹ * (γ * δ)) 1 0 = 0 := by
      rw [mul_entry δ⁻¹ (γ * δ) 1 0, hγδ0, hγδ1, hi10, hi11, hδ00, hδ10]
      ring
    refine ⟨δ, (δ⁻¹ * (γ * δ)) 0 1, ?_⟩
    rw [← eq_T_zpow_of_col hM00 hM10]
    group

theorem parabolic_classification (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (n : ℤ), (ε = 1 ∨ ε = -1) ∧
      γ = ε * (δ * ModularGroup.T ^ n * δ⁻¹) := by
  have hsplit : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination hγ
  rcases mul_eq_zero.mp hsplit with h | h
  · obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two (γ := γ) (by linarith)
    exact ⟨1, δ, n, Or.inl rfl, by rw [one_mul]; exact hδ⟩
  · have htrneg : ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
      linarith
    obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two htrneg
    refine ⟨-1, δ, n, Or.inr rfl, ?_⟩
    rw [neg_one_mul, ← hδ, neg_neg]

theorem isParabolicHom_periodHom {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    IsParabolicHom Γ hF.periodHom := by
  intro γ hγ
  obtain ⟨ε, δ, n, hε, hγeq⟩ := parabolic_classification (γ : SL(2, ℤ)) hγ
  obtain ⟨L, hL⟩ := hlim δ
  have hmem : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ := hγeq ▸ γ.2
  have hsub : γ = ⟨ε * (δ * ModularGroup.T ^ n * δ⁻¹), hmem⟩ := Subtype.ext hγeq
  rw [IsEquivariantPrimitive.periodHom_apply, hsub]
  exact period_conj_T_zpow_eq_zero hF δ hL n ε hε hmem

section Main

variable (N : ℕ) [NeZero N]

local notation "Γ" => CongruenceSubgroup.Gamma0 N
local notation "V" => CuspForm (CongruenceSubgroup.Gamma0 N) 2

noncomputable def prim (f : V) : ℍ → ℂ :=
  (ModularCurve.exists_hasEquivariantPrimitive N f).choose

theorem prim_spec (f : V) : ModularCurve.HasEquivariantPrimitive N f (prim N f) :=
  (ModularCurve.exists_hasEquivariantPrimitive N f).choose_spec

theorem period_apply_eq (γ : Γ) (f : V) :
    ModularCurve.period N γ f = (prim_spec N f).2.2.1.period γ := by
  rw [ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive N f (prim_spec N f) γ]
  rfl

private theorem _root_.ModularCurve.PeriodParabolic.period_one : ModularCurve.period N (1 : Γ) = 0 := by
  ext f
  rw [period_apply_eq, IsEquivariantPrimitive.period_one]
  rfl

p2m_export "ModularCurve.PeriodParabolic" "period_one"
private theorem _root_.ModularCurve.PeriodParabolic.period_mul (γ δ : Γ) :
    ModularCurve.period N (γ * δ) = ModularCurve.period N γ + ModularCurve.period N δ := by
  ext f
  rw [LinearMap.add_apply, period_apply_eq, period_apply_eq, period_apply_eq,
    IsEquivariantPrimitive.period_mul]

p2m_export "ModularCurve.PeriodParabolic" "period_mul"

noncomputable def periodHomDual : Additive Γ →+ Module.Dual ℂ V where
  toFun γ := ModularCurve.period N (Additive.toMul γ)
  map_zero' := period_one N
  map_add' γ δ := period_mul N (Additive.toMul γ) (Additive.toMul δ)

theorem periodHomDual_apply (γ : Γ) :
    periodHomDual N (Additive.ofMul γ) = ModularCurve.period N γ := rfl

theorem isParabolicHom_periodHomDual : IsParabolicHom Γ (periodHomDual N) := by
  intro γ hγ
  rw [periodHomDual_apply]
  ext f
  rw [period_apply_eq, LinearMap.zero_apply]
  have h := isParabolicHom_periodHom (prim_spec N f).2.2.1 (prim_spec N f).2.2.2 γ hγ
  rwa [IsEquivariantPrimitive.periodHom_apply] at h

theorem main :
    ∃ Φ : Additive Γ →+ Module.Dual ℂ V,
      IsParabolicHom Γ Φ ∧ ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.period N γ :=
  ⟨periodHomDual N, isParabolicHom_periodHomDual N, periodHomDual_apply N⟩

end Main

end ModularCurve.PeriodParabolic

theorem solution (N : ℕ) [NeZero N] :
    ∃ Φ : Additive (CongruenceSubgroup.Gamma0 N) →+
        Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) Φ ∧
        ∀ γ : CongruenceSubgroup.Gamma0 N, Φ (Additive.ofMul γ) = ModularCurve.period N γ :=
  ModularCurve.PeriodParabolic.main N

end S_ModularCurve_exists_isParabolicHom_apply_eq_period
end P2MW
export P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_period (solution)
