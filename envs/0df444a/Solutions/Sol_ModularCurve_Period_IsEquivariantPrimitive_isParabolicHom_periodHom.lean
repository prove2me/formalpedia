-- Prove2me | solution 1 for ModularCurve.Period.IsEquivariantPrimitive.isParabolicHom_periodHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/70b50b75-7004-582c-94bb-41ee271b72e5

import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsEquivariantPrimitive Period.IsParabolicHom"
namespace Period
p2m_export "ModularCurve.Period" "IsEquivariantPrimitive IsParabolicHom"
p2m_open "ModularCurve.Period ModularCurve"

open UpperHalfPlane Filter Topology

open scoped MatrixGroups

variable {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

namespace IsEquivariantPrimitive
p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period sub_eq_period period_one period_mul periodHom"
p2m_open "ModularCurve.Period.IsEquivariantPrimitive"

theorem period_inv (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    hF.period γ⁻¹ = -hF.period γ := by
  have h := hF.period_mul γ⁻¹ γ
  rw [inv_mul_cancel, period_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.period_pow (hF : IsEquivariantPrimitive Γ F) (γ : Γ) (n : ℕ) :
    hF.period (γ ^ n) = (n : ℂ) * hF.period γ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, period_mul, ih]; push_cast; ring

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period_pow"

theorem period_congr {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (c : ℂ) (h : ∀ z, F z - F' z = c) (γ : Γ) :
    hF.period γ = hF'.period γ := by
  rw [← hF.sub_eq_period γ UpperHalfPlane.I, ← hF'.sub_eq_period γ UpperHalfPlane.I]
  have h1 := h ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h2 := h UpperHalfPlane.I
  linear_combination h1 - h2

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.add {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') : IsEquivariantPrimitive Γ (F + F') := by
  intro γ
  refine ⟨hF.period γ + hF'.period γ, fun z => ?_⟩
  have h1 := hF.sub_eq_period γ z
  have h2 := hF'.sub_eq_period γ z
  simp only [Pi.add_apply]
  linear_combination h1 + h2

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "add"

theorem period_add {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (γ : Γ) :
    (hF.add hF').period γ = hF.period γ + hF'.period γ := by
  rw [← (hF.add hF').sub_eq_period γ UpperHalfPlane.I]
  have h1 := hF.sub_eq_period γ UpperHalfPlane.I
  have h2 := hF'.sub_eq_period γ UpperHalfPlane.I
  simp only [Pi.add_apply]
  linear_combination h1 + h2

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.smul (a : ℂ) (hF : IsEquivariantPrimitive Γ F) :
    IsEquivariantPrimitive Γ (a • F) := by
  intro γ
  refine ⟨a * hF.period γ, fun z => ?_⟩
  have h := hF.sub_eq_period γ z
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination a * h

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "smul"

theorem period_smul (a : ℂ) (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    (hF.smul a).period γ = a * hF.period γ := by
  rw [← (hF.smul a).sub_eq_period γ UpperHalfPlane.I]
  have h := hF.sub_eq_period γ UpperHalfPlane.I
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination a * h

theorem period_eq_zero_of_isOfFinOrder (hF : IsEquivariantPrimitive Γ F) {γ : Γ}
    (h : IsOfFinOrder γ) : hF.period γ = 0 := by
  have hpos : 0 < orderOf γ := h.orderOf_pos
  have hpow := hF.period_pow γ (orderOf γ)
  rw [pow_orderOf_eq_one, period_one] at hpow
  exact (mul_eq_zero.mp hpow.symm).resolve_left
    (Nat.cast_ne_zero.mpr hpos.ne')

theorem period_neg_one (hF : IsEquivariantPrimitive Γ F) (h : (-1 : SL(2, ℤ)) ∈ Γ) :
    hF.period ⟨-1, h⟩ = 0 := by
  rw [← hF.sub_eq_period ⟨-1, h⟩ UpperHalfPlane.I]
  have h1 : ((⟨-1, h⟩ : Γ) : SL(2, ℤ)) • UpperHalfPlane.I = UpperHalfPlane.I := by
    show (-(1 : SL(2, ℤ))) • UpperHalfPlane.I = UpperHalfPlane.I
    rw [ModularGroup.SL_neg_smul, one_smul]
  rw [h1, sub_self]

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

private theorem const_eq_zero_of_tendsto_sub {α : Type*} {l : Filter α} [l.NeBot]
    {g h : α → ℂ} {L c : ℂ} (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hc : ∀ a, g a - h a = c) : c = 0 := by
  have hsub : Tendsto (fun a => g a - h a) l (𝓝 (L - L)) := hg.sub hh
  rw [sub_self] at hsub
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun a => (hc a).symm) hsub

theorem period_T_zpow_eq_zero (hF : IsEquivariantPrimitive Γ F) {L : ℂ}
    (hlim : Tendsto F atImInfty (𝓝 L)) (n : ℤ) (hT : ModularGroup.T ^ n ∈ Γ) :
    hF.period ⟨ModularGroup.T ^ n, hT⟩ = 0 := by
  refine const_eq_zero_of_tendsto_sub
    (g := fun z : ℍ => F (ModularGroup.T ^ n • z)) (h := F) (L := L) ?_ hlim
    fun z => hF.sub_eq_period ⟨ModularGroup.T ^ n, hT⟩ z
  have hfun : (fun z : ℍ => F (ModularGroup.T ^ n • z))
      = F ∘ fun z : ℍ => ((n : ℤ) : ℝ) +ᵥ z := by
    funext z
    simp only [Function.comp_apply, UpperHalfPlane.modular_T_zpow_smul]
  rw [hfun]
  exact hlim.comp (tendsto_vadd_atImInfty ((n : ℤ) : ℝ))

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.period_conj_T_zpow_eq_zero (hF : IsEquivariantPrimitive Γ F) (δ : SL(2, ℤ)) {L : ℂ}
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

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period_conj_T_zpow_eq_zero"
end IsEquivariantPrimitive

def ParabolicConjugacyClassification : Prop :=
  ∀ γ : SL(2, ℤ), ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 →
    ∃ (ε δ : SL(2, ℤ)) (n : ℤ), (ε = 1 ∨ ε = -1) ∧
      γ = ε * (δ * ModularGroup.T ^ n * δ⁻¹)

namespace IsEquivariantPrimitive p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period sub_eq_period period_one period_mul periodHom" end IsEquivariantPrimitive
namespace IsEquivariantPrimitive
p2m_open_scoped "ModularCurve.Period.IsEquivariantPrimitive" in

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.period_parabolic_of_classification
    (hF : IsEquivariantPrimitive Γ F)
    (hclass : ParabolicConjugacyClassification)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L))
    (γ : Γ) (hγ : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    hF.period γ = 0 := by
  obtain ⟨ε, δ, n, hε, hγeq⟩ := hclass (γ : SL(2, ℤ)) hγ
  obtain ⟨L, hL⟩ := hlim δ
  have hmem : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ := hγeq ▸ γ.2
  have hsub : γ = ⟨ε * (δ * ModularGroup.T ^ n * δ⁻¹), hmem⟩ := Subtype.ext hγeq
  rw [hsub]
  exact hF.period_conj_T_zpow_eq_zero δ hL n ε hε hmem

end IsEquivariantPrimitive
p2m_export "ModularCurve.Period" "IsEquivariantPrimitive.period_parabolic_of_classification"
namespace IsEquivariantPrimitive
p2m_open_scoped "ModularCurve.Period.IsEquivariantPrimitive" in

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.isParabolicHom_periodHom_of_classification
    (hF : IsEquivariantPrimitive Γ F)
    (hclass : ParabolicConjugacyClassification)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    IsParabolicHom Γ hF.periodHom :=
  fun γ hγ => hF.period_parabolic_of_classification hclass hlim γ hγ

end IsEquivariantPrimitive
p2m_export "ModularCurve.Period" "IsEquivariantPrimitive.isParabolicHom_periodHom_of_classification"

open Matrix Matrix.SpecialLinearGroup ModularGroup

private theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

private theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem inv_entries (A : SL(2, ℤ)) :
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

theorem parabolicConjugacyClassification : ParabolicConjugacyClassification := by
  intro γ hγ

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

p2m_open_scoped "ModularCurve.Period.IsEquivariantPrimitive" in

theorem IsEquivariantPrimitive.period_parabolic {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L))
    (γ : Γ) (hγ : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    hF.period γ = 0 :=
  hF.period_parabolic_of_classification parabolicConjugacyClassification hlim γ hγ

end ModularCurve.Period

open scoped MatrixGroups in

theorem solution {Γ : Subgroup SL(2, ℤ)}
    {F : UpperHalfPlane → ℂ} (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Filter.Tendsto (fun w : UpperHalfPlane => F (δ • w)) UpperHalfPlane.atImInfty (nhds L)) :
    ModularCurve.Period.IsParabolicHom Γ hF.periodHom :=
  hF.isParabolicHom_periodHom_of_classification ModularCurve.Period.parabolicConjugacyClassification hlim

#print axioms solution

end S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom
end P2MW
export P2MW.S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom (solution)
