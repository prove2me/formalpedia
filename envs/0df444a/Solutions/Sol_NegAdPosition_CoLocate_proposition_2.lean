-- Prove2me | solution 1 for NegAdPosition.CoLocate.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T18:56:20.091956+00:00
-- url     : https://prove2.me/submissions/6d144c6c-8dba-4304-8edf-f987f56c55a6

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

set_option autoImplicit false

namespace NAPHelp
open NegAdPosition.CoLocate

def fb (a b : Bool) : Firm → Bool
  | .inc => a
  | .ent => b

def T (p1 p2 n1 n2 : Bool) : Types := ⟨fb p1 p2, fb n1 n2⟩

def eqv : Bool × Bool × Bool × Bool ≃ Types where
  toFun q := T q.1 q.2.1 q.2.2.1 q.2.2.2
  invFun θ := (θ.P .inc, θ.P .ent, θ.N .inc, θ.N .ent)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by
    rintro ⟨p, n⟩
    simp only [T, Types.mk.injEq]
    constructor <;> funext j <;> cases j <;> rfl

theorem sum_types (f : Types → ℝ) :
    ∑ θ, f θ = ∑ p1 : Bool, ∑ p2 : Bool, ∑ n1 : Bool, ∑ n2 : Bool, f (T p1 p2 n1 n2) := by
  rw [← eqv.sum_comp]
  simp [Fintype.sum_prod_type, eqv]

theorem pairPmf_pos (σ r : ℝ) (h0 : 0 < σ) (h1 : σ < 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (a b : Bool) : 0 < pairPmf σ r a b := by
  have hs : 0 < 1 - σ := by linarith
  have hr : 0 < 1 - r := by linarith
  cases a <;> cases b <;> simp only [pairPmf] <;> positivity

theorem prior_pos (P : Params) (hS : P.Standing) (x : Loc) (θ : Types) : 0 < prior P x θ := by
  obtain ⟨_, _, _, h1, h2, h3, h4, h5, h6, _, _⟩ := hS
  have hc0 : 0 ≤ corrAt P x := by cases x <;> simp [corrAt] <;> linarith
  have hc1 : corrAt P x < 1 := by cases x <;> simp [corrAt] <;> linarith
  unfold prior
  exact mul_pos (pairPmf_pos _ _ h1 h2 hc0 hc1 _ _) (pairPmf_pos _ _ h3 h4 hc0 hc1 _ _)

theorem mass_pos (P : Params) (hS : P.Standing) (s : AdStrategy) (x : Loc) (a1 a2 : Ad)
    (θ0 : Types) (h : s .inc x θ0 = a1 ∧ s .ent x θ0 = a2) : 0 < outcomeMass P s x a1 a2 := by
  unfold outcomeMass
  have hle : (if s .inc x θ0 = a1 ∧ s .ent x θ0 = a2 then prior P x θ0 else 0) ≤
      ∑ θ, if s .inc x θ = a1 ∧ s .ent x θ = a2 then prior P x θ else 0 := by
    apply Finset.single_le_sum (f := fun θ => if s .inc x θ = a1 ∧ s .ent x θ = a2
      then prior P x θ else 0) _ (Finset.mem_univ θ0)
    intro θ _
    split_ifs
    · exact (prior_pos P hS x θ).le
    · exact le_refl _
  rw [if_pos h] at hle
  exact lt_of_lt_of_le (prior_pos P hS x θ0) hle

theorem all_mass_pos (P : Params) (hS : P.Standing) (x : Loc) (a1 a2 : Ad) :
    0 < outcomeMass P copnAd x a1 a2 := by
  cases x <;> cases a1 <;> cases a2
  · exact mass_pos P hS _ _ _ _ (T true true false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T true false true false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T true false false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false true false true) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false true true) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false false true) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false true false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false true false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T true true false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T true false true false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T true false false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false true false true) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false true true) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false false true) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false true false false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false true false) (by decide)
  · exact mass_pos P hS _ _ _ _ (T false false false false) (by decide)

/-- Posterior expectation from a numerator identity. -/
theorem expAttr_bayes (P : Params) (s : AdStrategy) (x : Loc) (a1 a2 : Ad) (j : Firm) (v : ℝ)
    (hm : outcomeMass P s x a1 a2 ≠ 0)
    (hnum : (∑ θ, (if s .inc x θ = a1 ∧ s .ent x θ = a2 then prior P x θ else 0) * attr P θ j)
      = v * outcomeMass P s x a1 a2) :
    expAttr P (bayes P s x a1 a2) j = v := by
  unfold expAttr bayes
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hnum]
  field_simp

theorem eL_pp_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .pos .pos) .inc = P.Pi - P.σB * P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_pp_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .pos .pos) .ent = P.Pi - P.σB * P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_pn_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .pos .neg) .inc = P.Pi - P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_pn_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .pos .neg) .ent = -(P.β * (P.σB + P.ρ * (1 - P.σB))) := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_pz_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .pos .none) .inc = P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_pz_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .pos .none) .ent = -(P.β * P.σB * (1 - P.ρ)) := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_np_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .neg .pos) .inc = -(P.β * (P.σB + P.ρ * (1 - P.σB))) := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_np_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .neg .pos) .ent = P.Pi - P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_nn_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .neg .neg) .inc = -P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_nn_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .neg .neg) .ent = -P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_nz_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .neg .none) .inc = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_nz_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .neg .none) .ent = -P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_zp_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .none .pos) .inc = -(P.β * P.σB * (1 - P.ρ)) := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_zp_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .none .pos) .ent = P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_zn_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .none .neg) .inc = -P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_zn_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .none .neg) .ent = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_zz_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .none .none) .inc = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eL_zz_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .L .none .none) .ent = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_pp_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .pos .pos) .inc = P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_pp_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .pos .pos) .ent = P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_pn_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .pos .neg) .inc = P.Pi - P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_pn_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .pos .neg) .ent = P.σP * P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_pz_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .pos .none) .inc = P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_pz_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .pos .none) .ent = -(P.σB * P.β) := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_np_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .neg .pos) .inc = P.σP * P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_np_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .neg .pos) .ent = P.Pi - P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_nn_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .neg .neg) .inc = P.σP * P.Pi - P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_nn_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .neg .neg) .ent = P.σP * P.Pi - P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_nz_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .neg .none) .inc = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_nz_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .neg .none) .ent = -P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_zp_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .none .pos) .inc = -(P.σB * P.β) := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_zp_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .none .pos) .ent = P.Pi := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_zn_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .none .neg) .inc = -P.β := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_zn_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .none .neg) .ent = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_zz_inc (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .none .none) .inc = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem eR_zz_ent (P : Params) (hS : P.Standing) :
    expAttr P (bayes P copnAd .R .none .none) .ent = 0 := by
  apply expAttr_bayes _ _ _ _ _ _ _ (all_mass_pos P hS _ _ _).ne'
  unfold outcomeMass
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, attr]
  try ring

theorem facts (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    0 < P.δ ∧ 0 < P.Pi ∧ 0 < P.β ∧ 0 < P.σB * P.β ∧ P.σB * P.β < P.β ∧
    0 < P.σP * P.Pi ∧ P.σP * P.Pi < P.Pi ∧
    0 < P.β * P.σB * (1 - P.ρ) ∧ P.β * P.σB * (1 - P.ρ) < P.β ∧
    0 < P.β * (P.σB + P.ρ * (1 - P.σB)) ∧ P.β * (P.σB + P.ρ * (1 - P.σB)) < P.β ∧
    P.δ + P.β < P.γhi ∧ P.γlo < -P.Pi ∧ (1 - P.σP) * P.Pi + P.δ < P.β ∧
    (1 - P.ρ) * (1 - P.σB) * P.β < P.Pi ∧ P.δ < P.Pi + P.σB * P.β ∧ P.σP * P.Pi = P.σB * P.β := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, _, h10⟩ := hS
  obtain ⟨g1, g2⟩ := hA1
  have k1 : 0 < 1 - P.σB := by linarith
  have k2 : 0 < 1 - P.ρ := by linarith
  have k3 : 0 < 1 - P.σP := by linarith
  refine ⟨h0, h1, h2, by positivity, by nlinarith, by positivity, by nlinarith, by positivity, ?_,
    by positivity, ?_, ?_, g1, ha, hc, hδ, h10⟩
  · have : P.σB * (1 - P.ρ) < 1 := by nlinarith
    nlinarith
  · have : P.σB + P.ρ * (1 - P.σB) < 1 := by nlinarith
    nlinarith
  · nlinarith

theorem buyers_eq (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) (m : ℝ) (hlo : -P.β - P.δ ≤ m) (hhi : m ≤ P.Pi) :
    1 - Γ P (-m) = (P.γhi + m) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, -, -, -, -, -, -, -, -, f11, f12, -⟩ := facts P hS hA1 ha hc hδ
  have hW : 0 < P.γhi - P.γlo := by linarith
  have r0 : 0 ≤ (-m - P.γlo) / (P.γhi - P.γlo) := div_nonneg (by linarith) hW.le
  have r1 : (-m - P.γlo) / (P.γhi - P.γlo) ≤ 1 := by
    rw [div_le_one hW]; linarith
  unfold Γ
  rw [min_eq_right r1, max_eq_right r0]
  field_simp
  ring

theorem locDemand_eq (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a)
    (hc : P.A1c) (hδ : P.δ < P.Pi + P.σB * P.β) (x2 : Loc) (e : Firm → ℝ)
    (he : ∀ j, -P.β ≤ e j ∧ e j ≤ P.Pi) (i : Firm) (χ : Loc) :
    locDemand P x2 e i χ =
      (if e i.other - NegAdPosition.CoLocate.dist P x2 i.other χ < e i - NegAdPosition.CoLocate.dist P x2 i χ then (1 : ℝ)
        else if e i - NegAdPosition.CoLocate.dist P x2 i χ < e i.other - NegAdPosition.CoLocate.dist P x2 i.other χ then 0
        else if x2 = .L then 1 / 2
        else if position x2 i = χ then 1 else 0) *
      ((P.γhi + max (e .inc - NegAdPosition.CoLocate.dist P x2 .inc χ) (e .ent - NegAdPosition.CoLocate.dist P x2 .ent χ)) /
        (P.γhi - P.γlo)) := by
  obtain ⟨f0, -⟩ := facts P hS hA1 ha hc hδ
  have hd : ∀ j, 0 ≤ NegAdPosition.CoLocate.dist P x2 j χ ∧ NegAdPosition.CoLocate.dist P x2 j χ ≤ P.δ := by
    intro j; unfold NegAdPosition.CoLocate.dist; split_ifs <;> constructor <;> linarith
  unfold locDemand
  simp only
  rw [buyers_eq P hS hA1 ha hc hδ]
  · obtain ⟨a1, a2⟩ := he .inc
    obtain ⟨-, b1⟩ := hd .inc
    exact le_max_of_le_left (by linarith)
  · obtain ⟨a1, a2⟩ := he .inc
    obtain ⟨b1, b2⟩ := he .ent
    obtain ⟨c1, -⟩ := hd .inc
    obtain ⟨d1, -⟩ := hd .ent
    exact max_le (by linarith) (by linarith)

theorem dL_pp_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .pos .pos .inc =
      ((2*P.γhi + 2*(P.Pi - P.σB*P.β) - P.δ)/2) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .pos .pos) j ∧
      expAttr P (bayes P copnAd .L .pos .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_pp_inc P hS, eL_pp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_pp_inc P hS, eL_pp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_pp_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .pos .pos .ent =
      ((2*P.γhi + 2*(P.Pi - P.σB*P.β) - P.δ)/2) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .pos .pos) j ∧
      expAttr P (bayes P copnAd .L .pos .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_pp_inc P hS, eL_pp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_pp_inc P hS, eL_pp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_pn_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .pos .neg .inc =
      (2*P.γhi + 2*(P.Pi - P.β) - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .pos .neg) j ∧
      expAttr P (bayes P copnAd .L .pos .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_pn_inc P hS, eL_pn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_pn_inc P hS, eL_pn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_pn_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .pos .neg .ent =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .pos .neg) j ∧
      expAttr P (bayes P copnAd .L .pos .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_pn_inc P hS, eL_pn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_pn_inc P hS, eL_pn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_pz_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .pos .none .inc =
      (2*P.γhi + 2*P.Pi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .pos .none) j ∧
      expAttr P (bayes P copnAd .L .pos .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_pz_inc P hS, eL_pz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_pz_inc P hS, eL_pz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_pz_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .pos .none .ent =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .pos .none) j ∧
      expAttr P (bayes P copnAd .L .pos .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_pz_inc P hS, eL_pz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_pz_inc P hS, eL_pz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_np_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .neg .pos .inc =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .neg .pos) j ∧
      expAttr P (bayes P copnAd .L .neg .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_np_inc P hS, eL_np_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_np_inc P hS, eL_np_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_np_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .neg .pos .ent =
      (2*P.γhi + 2*(P.Pi - P.β) - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .neg .pos) j ∧
      expAttr P (bayes P copnAd .L .neg .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_np_inc P hS, eL_np_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_np_inc P hS, eL_np_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_nn_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .neg .neg .inc =
      ((2*P.γhi - 2*P.β - P.δ)/2) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .neg .neg) j ∧
      expAttr P (bayes P copnAd .L .neg .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_nn_inc P hS, eL_nn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_nn_inc P hS, eL_nn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_nn_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .neg .neg .ent =
      ((2*P.γhi - 2*P.β - P.δ)/2) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .neg .neg) j ∧
      expAttr P (bayes P copnAd .L .neg .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_nn_inc P hS, eL_nn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_nn_inc P hS, eL_nn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_nz_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .neg .none .inc =
      (2*P.γhi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .neg .none) j ∧
      expAttr P (bayes P copnAd .L .neg .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_nz_inc P hS, eL_nz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_nz_inc P hS, eL_nz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_nz_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .neg .none .ent =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .neg .none) j ∧
      expAttr P (bayes P copnAd .L .neg .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_nz_inc P hS, eL_nz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_nz_inc P hS, eL_nz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_zp_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .none .pos .inc =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .none .pos) j ∧
      expAttr P (bayes P copnAd .L .none .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_zp_inc P hS, eL_zp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_zp_inc P hS, eL_zp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_zp_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .none .pos .ent =
      (2*P.γhi + 2*P.Pi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .none .pos) j ∧
      expAttr P (bayes P copnAd .L .none .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_zp_inc P hS, eL_zp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_zp_inc P hS, eL_zp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_zn_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .none .neg .inc =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .none .neg) j ∧
      expAttr P (bayes P copnAd .L .none .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_zn_inc P hS, eL_zn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_zn_inc P hS, eL_zn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_zn_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .none .neg .ent =
      (2*P.γhi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .none .neg) j ∧
      expAttr P (bayes P copnAd .L .none .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_zn_inc P hS, eL_zn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_zn_inc P hS, eL_zn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_zz_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .none .none .inc =
      ((2*P.γhi - P.δ)/2) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .none .none) j ∧
      expAttr P (bayes P copnAd .L .none .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_zz_inc P hS, eL_zz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_zz_inc P hS, eL_zz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dL_zz_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .L .none .none .ent =
      ((2*P.γhi - P.δ)/2) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .L .none .none) j ∧
      expAttr P (bayes P copnAd .L .none .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eL_zz_inc P hS, eL_zz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eL_zz_inc P hS, eL_zz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_pp_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .pos .pos .inc =
      (P.γhi + P.Pi) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .pos .pos) j ∧
      expAttr P (bayes P copnAd .R .pos .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_pp_inc P hS, eR_pp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_pp_inc P hS, eR_pp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_pp_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .pos .pos .ent =
      (P.γhi + P.Pi) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .pos .pos) j ∧
      expAttr P (bayes P copnAd .R .pos .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_pp_inc P hS, eR_pp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_pp_inc P hS, eR_pp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_pn_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .pos .neg .inc =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .pos .neg) j ∧
      expAttr P (bayes P copnAd .R .pos .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_pn_inc P hS, eR_pn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_pn_inc P hS, eR_pn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_pn_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .pos .neg .ent =
      (2*P.γhi + 2*P.σP*P.Pi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .pos .neg) j ∧
      expAttr P (bayes P copnAd .R .pos .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_pn_inc P hS, eR_pn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_pn_inc P hS, eR_pn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_pz_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .pos .none .inc =
      (2*P.γhi + 2*P.Pi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .pos .none) j ∧
      expAttr P (bayes P copnAd .R .pos .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_pz_inc P hS, eR_pz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_pz_inc P hS, eR_pz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_pz_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .pos .none .ent =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .pos .none) j ∧
      expAttr P (bayes P copnAd .R .pos .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_pz_inc P hS, eR_pz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_pz_inc P hS, eR_pz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_np_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .neg .pos .inc =
      (2*P.γhi + 2*P.σP*P.Pi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .neg .pos) j ∧
      expAttr P (bayes P copnAd .R .neg .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_np_inc P hS, eR_np_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_np_inc P hS, eR_np_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_np_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .neg .pos .ent =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .neg .pos) j ∧
      expAttr P (bayes P copnAd .R .neg .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_np_inc P hS, eR_np_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_np_inc P hS, eR_np_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_nn_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .neg .neg .inc =
      (P.γhi + P.σP*P.Pi - P.β) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .neg .neg) j ∧
      expAttr P (bayes P copnAd .R .neg .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_nn_inc P hS, eR_nn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_nn_inc P hS, eR_nn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_nn_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .neg .neg .ent =
      (P.γhi + P.σP*P.Pi - P.β) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .neg .neg) j ∧
      expAttr P (bayes P copnAd .R .neg .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_nn_inc P hS, eR_nn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_nn_inc P hS, eR_nn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_nz_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .neg .none .inc =
      (2*P.γhi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .neg .none) j ∧
      expAttr P (bayes P copnAd .R .neg .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_nz_inc P hS, eR_nz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_nz_inc P hS, eR_nz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_nz_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .neg .none .ent =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .neg .none) j ∧
      expAttr P (bayes P copnAd .R .neg .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_nz_inc P hS, eR_nz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_nz_inc P hS, eR_nz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_zp_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .none .pos .inc =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .none .pos) j ∧
      expAttr P (bayes P copnAd .R .none .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_zp_inc P hS, eR_zp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_zp_inc P hS, eR_zp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_zp_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .none .pos .ent =
      (2*P.γhi + 2*P.Pi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .none .pos) j ∧
      expAttr P (bayes P copnAd .R .none .pos) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_zp_inc P hS, eR_zp_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_zp_inc P hS, eR_zp_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_zn_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .none .neg .inc =
      (0) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .none .neg) j ∧
      expAttr P (bayes P copnAd .R .none .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_zn_inc P hS, eR_zn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_zn_inc P hS, eR_zn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_zn_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .none .neg .ent =
      (2*P.γhi - P.δ) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .none .neg) j ∧
      expAttr P (bayes P copnAd .R .none .neg) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_zn_inc P hS, eR_zn_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_zn_inc P hS, eR_zn_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_zz_inc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .none .none .inc =
      (P.γhi) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .none .none) j ∧
      expAttr P (bayes P copnAd .R .none .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_zz_inc P hS, eR_zz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_zz_inc P hS, eR_zz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)

theorem dR_zz_ent (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    outcomeDemand P (bayes P copnAd) .R .none .none .ent =
      (P.γhi) / (P.γhi - P.γlo) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have he : ∀ j, -P.β ≤ expAttr P (bayes P copnAd .R .none .none) j ∧
      expAttr P (bayes P copnAd .R .none .none) j ≤ P.Pi := by
    intro j; cases j <;> simp only [eR_zz_inc P hS, eR_zz_ent P hS] <;> constructor <;> linarith
  unfold outcomeDemand demand
  rw [locDemand_eq P hS hA1 ha hc hδ _ _ he, locDemand_eq P hS hA1 ha hc hδ _ _ he]
  simp [eR_zz_inc P hS, eR_zz_ent P hS, NegAdPosition.CoLocate.dist, position, Firm.other, max_def]
  all_goals (try split_ifs)
  all_goals first | ring1 | (exfalso; linarith)


set_option maxHeartbeats 1000000 in
theorem br (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) :
    ∀ (x : Loc) (θ : Types) (i : Firm) (a : Ad), Feasible θ i a →
      outcomeDemand P (bayes P copnAd) x (outcomeOf i a (copnAd i.other x θ)).1
          (outcomeOf i a (copnAd i.other x θ)).2 i
        ≤ outcomeDemand P (bayes P copnAd) x (copnAd .inc x θ) (copnAd .ent x θ) i := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have hW : 0 < P.γhi - P.γlo := by linarith
  intro x θ i a hf
  obtain ⟨⟨p1, p2, n1, n2⟩, rfl⟩ := eqv.surjective θ
  change Feasible (T p1 p2 n1 n2) i a at hf
  change outcomeDemand P (bayes P copnAd) x (outcomeOf i a (copnAd i.other x (T p1 p2 n1 n2))).1
          (outcomeOf i a (copnAd i.other x (T p1 p2 n1 n2))).2 i
        ≤ outcomeDemand P (bayes P copnAd) x (copnAd .inc x (T p1 p2 n1 n2))
          (copnAd .ent x (T p1 p2 n1 n2)) i
  cases x <;> cases i <;> cases a <;> cases p1 <;> cases p2 <;> cases n1 <;> cases n2 <;>
    simp [Feasible, T, fb, Firm.other] at hf <;>
    simp [copnAd, outcomeOf, T, fb, Firm.other, dL_pp_inc P hS hA1 ha hc hδ, dL_pp_ent P hS hA1 ha hc hδ, dL_pn_inc P hS hA1 ha hc hδ, dL_pn_ent P hS hA1 ha hc hδ, dL_pz_inc P hS hA1 ha hc hδ, dL_pz_ent P hS hA1 ha hc hδ, dL_np_inc P hS hA1 ha hc hδ, dL_np_ent P hS hA1 ha hc hδ, dL_nn_inc P hS hA1 ha hc hδ, dL_nn_ent P hS hA1 ha hc hδ, dL_nz_inc P hS hA1 ha hc hδ, dL_nz_ent P hS hA1 ha hc hδ, dL_zp_inc P hS hA1 ha hc hδ, dL_zp_ent P hS hA1 ha hc hδ, dL_zn_inc P hS hA1 ha hc hδ, dL_zn_ent P hS hA1 ha hc hδ, dL_zz_inc P hS hA1 ha hc hδ, dL_zz_ent P hS hA1 ha hc hδ, dR_pp_inc P hS hA1 ha hc hδ, dR_pp_ent P hS hA1 ha hc hδ, dR_pn_inc P hS hA1 ha hc hδ, dR_pn_ent P hS hA1 ha hc hδ, dR_pz_inc P hS hA1 ha hc hδ, dR_pz_ent P hS hA1 ha hc hδ, dR_np_inc P hS hA1 ha hc hδ, dR_np_ent P hS hA1 ha hc hδ, dR_nn_inc P hS hA1 ha hc hδ, dR_nn_ent P hS hA1 ha hc hδ, dR_nz_inc P hS hA1 ha hc hδ, dR_nz_ent P hS hA1 ha hc hδ, dR_zp_inc P hS hA1 ha hc hδ, dR_zp_ent P hS hA1 ha hc hδ, dR_zn_inc P hS hA1 ha hc hδ, dR_zn_ent P hS hA1 ha hc hδ, dR_zz_inc P hS hA1 ha hc hδ, dR_zz_ent P hS hA1 ha hc hδ,
      div_le_div_iff_of_pos_right hW] <;>
    first | linarith | (refine div_nonneg ?_ hW.le; linarith)

set_option maxHeartbeats 1000000 in
theorem loc (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a) (hc : P.A1c)
    (hδ : P.δ < P.Pi + P.σB * P.β) (hd : P.A1dCorr) :
    ∀ x, expEntrantDemand P copnAd (bayes P copnAd) x ≤
      expEntrantDemand P copnAd (bayes P copnAd) .L := by
  intro x
  cases x
  · exact le_refl _
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    facts P hS hA1 ha hc hδ
  have hW : 0 < P.γhi - P.γlo := by linarith
  have hW' : P.γhi - P.γlo ≠ 0 := hW.ne'
  have hσP : P.σP ≠ 0 := hS.2.2.2.1.ne'
  have hPi : P.Pi = P.σB * P.β / P.σP := by
    field_simp
    linarith
  have h2 : 0 ≤ ((P.σB * (1 - P.σB) * (1 - P.σP) * (1 - P.ρ) * (1 - P.σP + P.ρ * P.σP) * P.β
      + (1 - P.σP) * P.σP * (1 - P.ρ) * P.Pi - P.δ / 2) -
      (P.σB * (1 - P.σB) * P.β + (1 - P.σP) * P.σP * (1 - P.σB) ^ 2 * P.Pi
      - (1 - P.σB) * (P.σB + (1 - P.σB) * P.σP * (1 - P.σP)) * P.δ)) / (P.γhi - P.γlo) := by
    unfold Params.A1dCorr at hd
    exact div_nonneg (by linarith) hW.le
  rw [← sub_nonneg]
  convert h2 using 1
  unfold expEntrantDemand
  simp only [sum_types, Fintype.sum_bool]
  simp [copnAd, T, fb, Firm.other, prior, pairPmf, corrAt, dL_pp_ent P hS hA1 ha hc hδ, dL_pn_ent P hS hA1 ha hc hδ, dL_pz_ent P hS hA1 ha hc hδ, dL_np_ent P hS hA1 ha hc hδ, dL_nn_ent P hS hA1 ha hc hδ, dL_nz_ent P hS hA1 ha hc hδ, dL_zp_ent P hS hA1 ha hc hδ, dL_zn_ent P hS hA1 ha hc hδ, dL_zz_ent P hS hA1 ha hc hδ, dR_pp_ent P hS hA1 ha hc hδ, dR_pn_ent P hS hA1 ha hc hδ, dR_pz_ent P hS hA1 ha hc hδ, dR_np_ent P hS hA1 ha hc hδ, dR_nn_ent P hS hA1 ha hc hδ, dR_nz_ent P hS hA1 ha hc hδ, dR_zp_ent P hS hA1 ha hc hδ, dR_zn_ent P hS hA1 ha hc hδ, dR_zz_ent P hS hA1 ha hc hδ]
  rw [hPi]
  field_simp
  ring

theorem feas_all : ∀ (i : Firm) (x : Loc) (θ : Types), Feasible θ i (copnAd i x θ) := by
  intro i x θ
  obtain ⟨⟨p1, p2, n1, n2⟩, rfl⟩ := eqv.surjective θ
  change Feasible (T p1 p2 n1 n2) i (copnAd i x (T p1 p2 n1 n2))
  cases i <;> cases x <;> cases p1 <;> cases p2 <;> cases n1 <;> cases n2 <;>
    simp [Feasible, copnAd, T, fb, Firm.other]

end NAPHelp

open NegAdPosition.CoLocate in
theorem solution (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (ha : P.A1a) (hb : P.A1b) (hc : P.A1c) (hδ : P.δ < P.Pi + P.σB * P.β) (hd : P.A1dCorr) :
    ∃ σ : Profile, IsPBE P σ ∧ σ.x2 = Loc.L ∧
      (∀ i θ, θ.P i = true → σ.ad i Loc.L θ = Ad.pos) ∧
      (∀ i θ, θ.P i = true → θ.N i.other = true → (θ.P i.other = true ∨ θ.N i = true) →
        σ.ad i Loc.R θ = Ad.neg) := by
  refine ⟨⟨Loc.L, copnAd, bayes P copnAd⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · exact NAPHelp.feas_all
  · intro x a1 a2
    have hm := NAPHelp.all_mass_pos P hS x a1 a2
    refine ⟨?_, ?_, ?_⟩
    · intro θ
      show 0 ≤ bayes P copnAd x a1 a2 θ
      unfold bayes
      apply div_nonneg _ hm.le
      split_ifs
      · exact (NAPHelp.prior_pos P hS x θ).le
      · exact le_refl _
    · show ∑ θ, bayes P copnAd x a1 a2 θ = 1
      unfold bayes
      rw [← Finset.sum_div]
      exact div_self hm.ne'
    · intro θ hθ
      change bayes P copnAd x a1 a2 θ ≠ 0 at hθ
      unfold bayes at hθ
      by_cases h : copnAd .inc x θ = a1 ∧ copnAd .ent x θ = a2
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨NAPHelp.feas_all _ _ _, NAPHelp.feas_all _ _ _⟩
      · rw [if_neg h, zero_div] at hθ
        exact absurd rfl hθ
  · intro x a1 a2 _ θ
    rfl
  · exact NAPHelp.br P hS hA1 ha hc hδ
  · exact NAPHelp.loc P hS hA1 ha hc hδ hd
  · intro i θ h
    show copnAd i Loc.L θ = Ad.pos
    simp [copnAd, h]
  · intro i θ h1 h2 h3
    show copnAd i Loc.R θ = Ad.neg
    rcases h3 with h3 | h3 <;> simp [copnAd, h1, h2, h3]
