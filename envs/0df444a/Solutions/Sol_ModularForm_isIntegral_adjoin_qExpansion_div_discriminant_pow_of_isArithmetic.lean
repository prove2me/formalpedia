-- Prove2me | solution 1 for ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4e485c8d-c717-58a8-adf5-7304e067d430

import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Theorems.Thm_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups

namespace PenA
namespace ALG

open Polynomial SlashInvariantForm

variable {ι : Type*}

lemma natDegree_prod_linear_le (s : Finset ι) (a b : ι → ℂ) :
    (∏ q ∈ s, (C (a q) - C (b q) * X)).natDegree ≤ s.card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.card_cons]
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hfac : (C (a j) - C (b j) * X).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · simp [Polynomial.natDegree_C]
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le
    omega

lemma coeff_card_prod_linear (s : Finset ι) (a b : ι → ℂ) :
    (∏ q ∈ s, (C (a q) - C (b q) * X)).coeff s.card = ∏ q ∈ s, (-(b q)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Finset.card_cons]
    have hre : (C (a j) - C (b j) * X) * (∏ q ∈ s, (C (a q) - C (b q) * X))
        = C (a j) * (∏ q ∈ s, (C (a q) - C (b q) * X))
          - C (b j) * (X * (∏ q ∈ s, (C (a q) - C (b q) * X))) := by ring
    rw [hre, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_prod_linear_le s a b) (Nat.lt_succ_self _)), ih]
    ring

lemma aux_scalar (co x y : ℂ) (hy : y ≠ 0) {r c : ℕ} (hr : r ≤ c) :
    co * x ^ r * y ^ (c - r) = co * (x / y) ^ r * y ^ c := by
  rw [div_pow, pow_sub₀ _ hy hr]
  field_simp

lemma key_vanish (s : Finset ι) (a b : ι → ℂ) (j0 : ι) (hj0 : j0 ∈ s) :
    ∑ r ∈ Finset.range (s.card + 1),
      (∏ q ∈ s, (C (a q) - C (b q) * X)).coeff r * (a j0) ^ r * (b j0) ^ (s.card - r) = 0 := by
  set p : Polynomial ℂ := ∏ q ∈ s, (C (a q) - C (b q) * X) with hp
  by_cases hy : b j0 = 0
  · refine Finset.sum_eq_zero fun r hr => ?_
    have hr' : r ≤ s.card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rcases lt_or_eq_of_le hr' with hlt | rfl
    · rw [hy, zero_pow (by omega), mul_zero]
    · rw [hp, coeff_card_prod_linear, Finset.prod_eq_zero hj0 (by rw [hy, neg_zero]), zero_mul,
        zero_mul]
  · have hdeg : p.natDegree < s.card + 1 :=
      lt_of_le_of_lt (hp ▸ natDegree_prod_linear_le s a b) (Nat.lt_succ_self _)
    calc ∑ r ∈ Finset.range (s.card + 1), p.coeff r * (a j0) ^ r * (b j0) ^ (s.card - r)
        = ∑ r ∈ Finset.range (s.card + 1), p.coeff r * (a j0 / b j0) ^ r * (b j0) ^ s.card := by
          refine Finset.sum_congr rfl fun r hr => ?_
          exact aux_scalar _ _ _ hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      _ = (∑ r ∈ Finset.range (s.card + 1), p.coeff r * (a j0 / b j0) ^ r) * (b j0) ^ s.card := by
          rw [Finset.sum_mul]
      _ = p.eval (a j0 / b j0) * (b j0) ^ s.card := by
          rw [Polynomial.eval_eq_sum_range' hdeg]
      _ = 0 := by
          rw [hp, Polynomial.eval_prod, Finset.prod_eq_zero hj0 (by
            rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X, mul_div_cancel₀ _ hy, sub_self]), zero_mul]

noncomputable def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {w : ℤ}
    (f : ModularForm Γ w) : ModularForm Γ' w where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (hle hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono hle)

@[scoped simp] lemma coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {w : ℤ}
    (f : ModularForm Γ w) : ⇑(restrict hle f) = ⇑f := rfl

lemma sigma_eq_id {A : GL (Fin 2) ℝ} (hA : A ∈ 𝒮ℒ) (c : ℂ) : σ A c = c := by
  have hdet : (0 : ℝ) < (↑A : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.HasDetOne.det_eq hA]
    simp
  simp [UpperHalfPlane.σ, hdet]

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)}

lemma quotientFunc_sub_smul [𝒢.HasDetOne] (c : ℂ) {w : ℤ} (g₁ h₁ : ModularForm 𝒢 w)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) (τ : ℍ) :
    quotientFunc (g₁ - c • h₁) q τ = quotientFunc g₁ q τ - quotientFunc h₁ q τ * c := by
  induction q using Quotient.inductionOn with
  | h r =>
    have hA : (r.val)⁻¹ ∈ 𝒮ℒ := inv_mem r.2
    rw [quotientFunc_mk, quotientFunc_mk, quotientFunc_mk, ModularForm.coe_sub,
      ModularForm.IsGLPos.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.smul_slash, sigma_eq_id hA]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring

lemma norm_apply_eq {w : ℤ} [𝒢.IsArithmetic] (f : ModularForm 𝒢 w) (τ : ℍ)
    [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] :
    ModularForm.norm 𝒮ℒ f τ = ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, quotientFunc f q τ := by
  have h1 : ModularForm.norm 𝒮ℒ f τ = (∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, quotientFunc f q) τ := by
    rw [show ⇑(ModularForm.norm 𝒮ℒ f) = _ from ModularForm.coe_norm 𝒮ℒ f]
    congr!
  rw [h1, Finset.prod_apply]

lemma quotientFunc_one {w : ℤ} (f : ModularForm 𝒢 w) :
    quotientFunc f (⟦1⟧ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) = ⇑f := by
  rw [quotientFunc_mk]
  simp

lemma one_mem_strictPeriods_inf (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) :
    (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact Subgroup.mem_inf.mpr ⟨h1, Subgroup.mem_strictPeriods_iff.mp one_mem_strictPeriods_SL⟩

lemma coeff_eq_sum_lagrange {n : ℕ} (p : Polynomial ℂ) (hdeg : p.natDegree < n + 1) (r : ℕ)
    (v : Fin (n + 1) → ℂ) (hv : Set.InjOn v ↑(Finset.univ : Finset (Fin (n + 1)))) :
    p.coeff r = ∑ i : Fin (n + 1), p.eval (v i) * (Lagrange.basis Finset.univ v i).coeff r := by
  have hdeg' : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hdeg)
  conv_lhs => rw [Lagrange.eq_interpolate hv hdeg', Lagrange.interpolate_apply]
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_C_mul]

noncomputable def nodes (m : ℕ) : Fin m → ℂ := fun j => ((j : ℕ) : ℂ)

lemma nodes_injOn (m : ℕ) : Set.InjOn (nodes m) ↑(Finset.univ : Finset (Fin m)) :=
  fun _ _ _ _ hij => Fin.ext (Nat.cast_injective hij)

noncomputable def Pp [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} (g₁ h₁ : ModularForm 𝒢 w)
    (τ : ℍ) : Polynomial ℂ :=
  ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ,
    (C (quotientFunc g₁ q τ) - C (quotientFunc h₁ q τ) * X)

lemma natDegree_Pp_le [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} (g₁ h₁ : ModularForm 𝒢 w)
    (τ : ℍ) : (Pp g₁ h₁ τ).natDegree ≤ Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := by
  refine le_trans (natDegree_prod_linear_le _ _ _) ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card]

lemma norm_eval_Pp [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 w) (c : ℂ) (τ : ℍ) :
    ModularForm.norm 𝒮ℒ (g₁ - c • h₁) τ = (Pp g₁ h₁ τ).eval c := by
  rw [norm_apply_eq]
  unfold Pp
  rw [Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun q _ => by
    rw [quotientFunc_sub_smul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]

noncomputable def Aform {w : ℤ} [𝒢.IsArithmetic] [𝒢.HasDetOne] (g₁ h₁ : ModularForm 𝒢 w)
    (r : ℕ) : ModularForm 𝒮ℒ (w * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) :=
  ∑ i : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
    ((Lagrange.basis Finset.univ (nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) i).coeff r) •
      ModularForm.norm 𝒮ℒ (g₁ - nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1) i • h₁)

lemma Aform_apply [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {w : ℤ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 w) (r : ℕ) (τ : ℍ) :
    Aform g₁ h₁ r τ = (Pp g₁ h₁ τ).coeff r := by
  have hdeg : (Pp g₁ h₁ τ).natDegree < Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1 :=
    Nat.lt_succ_of_le (natDegree_Pp_le g₁ h₁ τ)
  have hcoe : ⇑(Aform g₁ h₁ r) = ∑ i : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
      ((Lagrange.basis Finset.univ (nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) i).coeff r) •
        ⇑(ModularForm.norm 𝒮ℒ (g₁ - nodes (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1) i • h₁)) :=
    map_sum (FunLike.coeAddMonoidHom (ModularForm _ _) UpperHalfPlane ℂ) _ _
  rw [show Aform g₁ h₁ r τ = ⇑(Aform g₁ h₁ r) τ from rfl, hcoe, Finset.sum_apply,
    coeff_eq_sum_lagrange (Pp g₁ h₁ τ) hdeg r _ (nodes_injOn _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_eval_Pp, mul_comm]

noncomputable def Tform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ)))
    (r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) :
    ModularForm (𝒢 ⊓ 𝒮ℒ) (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) :=
  ModularForm.mcast (by rw [Nat.cast_sub (Nat.lt_succ_iff.mp r.2)]; ring)
    (((restrict inf_le_right (Aform g₁ h₁ (r : ℕ))).mul
        ((restrict inf_le_left g₁).pow (r : ℕ))).mul
      ((restrict inf_le_left h₁).pow (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ))))

lemma Tform_apply [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ)))
    (r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) (τ : ℍ) :
    Tform g₁ h₁ r τ = (Pp g₁ h₁ τ).coeff (r : ℕ) * (g₁ τ) ^ (r : ℕ)
      * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) := by
  show (⇑(Tform g₁ h₁ r)) τ = _
  unfold Tform
  simp only [ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow, coe_restrict,
    Pi.mul_apply, Pi.pow_apply]
  rw [Aform_apply]

lemma qExpansion_Tform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (h1' : (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods) (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ)))
    (r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)) :
    qExpansion 1 (Tform g₁ h₁ r : ℍ → ℂ)
      = qExpansion 1 (Aform g₁ h₁ (r : ℕ) : ℍ → ℂ)
        * (qExpansion 1 (g₁ : ℍ → ℂ)) ^ (r : ℕ)
        * (qExpansion 1 (h₁ : ℍ → ℂ)) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) := by
  unfold Tform
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos h1',
    ModularForm.qExpansion_mul one_pos h1', ModularForm.qExpansion_pow one_pos h1',
    ModularForm.qExpansion_pow one_pos h1', coe_restrict, coe_restrict, coe_restrict]

noncomputable def Sform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ))) :
    ModularForm (𝒢 ⊓ 𝒮ℒ) (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) :=
  ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1), Tform g₁ h₁ r

lemma Sform_eq_zero [Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)] {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ))) : Sform g₁ h₁ = 0 := by
  have hcard : (Finset.univ : Finset (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).card
      = Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  ext τ
  have hcoe : ⇑(Sform g₁ h₁) = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
      ⇑(Tform g₁ h₁ r) := map_sum (FunLike.coeAddMonoidHom (ModularForm _ _) UpperHalfPlane ℂ) _ _
  rw [show Sform g₁ h₁ τ = ⇑(Sform g₁ h₁) τ from rfl, hcoe, Finset.sum_apply]
  have hkv := key_vanish (Finset.univ : Finset (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))
    (fun q => quotientFunc g₁ q τ) (fun q => quotientFunc h₁ q τ) ⟦1⟧ (Finset.mem_univ _)
  simp only [quotientFunc_one] at hkv
  rw [hcard] at hkv
  calc ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1), Tform g₁ h₁ r τ
      = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
          (Pp g₁ h₁ τ).coeff (r : ℕ) * (g₁ τ) ^ (r : ℕ)
            * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) :=
        Finset.sum_congr rfl fun r _ => Tform_apply g₁ h₁ r τ
    _ = ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
          (Pp g₁ h₁ τ).coeff r * (g₁ τ) ^ r
            * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - r) :=
        Fin.sum_univ_eq_sum_range
          (fun m => (Pp g₁ h₁ τ).coeff m * (g₁ τ) ^ m
            * (h₁ τ) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - m))
          (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1)
    _ = 0 := by
        unfold Pp
        exact hkv
    _ = (0 : ModularForm (𝒢 ⊓ 𝒮ℒ) (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ))) τ :=
        by simp

lemma qExpansion_Sform {K : ℕ} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (h1' : (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods) (g₁ h₁ : ModularForm 𝒢 (12 * (K : ℤ))) :
    qExpansion 1 (Sform g₁ h₁ : ℍ → ℂ)
      = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1),
          qExpansion 1 (Aform g₁ h₁ (r : ℕ) : ℍ → ℂ)
            * (qExpansion 1 (g₁ : ℍ → ℂ)) ^ (r : ℕ)
            * (qExpansion 1 (h₁ : ℍ → ℂ)) ^ (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) - (r : ℕ)) := by
  rw [show qExpansion 1 (Sform g₁ h₁ : ℍ → ℂ)
      = ModularForm.qExpansionAddHom one_pos h1'
          (24 * (K : ℤ) * (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ)) (Sform g₁ h₁) from rfl]
  unfold Sform
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => qExpansion_Tform h1' g₁ h₁ r

end PenA.ALG
p2m_reactivate "P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.PenA P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.PenA.ALG"
p2m_reactivate "P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.PenA"

open PenA.ALG SlashInvariantForm in
theorem solution {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (m : ℕ) {k : ℤ} (hk : k = 12 * m) (g : ModularForm 𝒢 k) : IsIntegral (Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ))) (((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m) := by
  classical
  subst hk

  set Δmf : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12) with hΔmfdef
  have hΔcoe : ⇑Δmf = (ModularForm.discriminant : ℍ → ℂ) := rfl
  set Dsl : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
    ModularForm.mcast (by ring) (Δmf.pow m) with hDSLdef
  have hDSLq : qExpansion 1 (Dsl : ℍ → ℂ)
      = (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ m := by
    rw [hDSLdef, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hΔcoe]
  set g' : ModularForm (𝒢 ⊓ 𝒮ℒ) (12 * (m : ℤ)) := restrict inf_le_left g with hg'def
  set D' : ModularForm (𝒢 ⊓ 𝒮ℒ) (12 * (m : ℤ)) := restrict inf_le_right Dsl with hD'def
  have hg'q : qExpansion 1 (g' : ℍ → ℂ) = qExpansion 1 (g : ℍ → ℂ) := by
    rw [hg'def, coe_restrict]
  have hD'q : qExpansion 1 (D' : ℍ → ℂ)
      = (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ m := by
    rw [hD'def, coe_restrict]
    exact hDSLq
  have hΔ0 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) ≠ 0 := fun h0 => by
    simpa [h0] using ModularForm.discriminant_qExpansion_coeff_one
  have hΔL : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [Ne, ← PowerSeries.coe_zero]
    exact fun h0 => hΔ0 (HahnSeries.ofPowerSeries_injective h0)
  have hΔmL : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m ≠ 0 := pow_ne_zero m hΔL
  letI : Fintype (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  have h1' : (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods := one_mem_strictPeriods_inf h1
  have h1'' : (1 : ℝ) ∈ ((𝒢 ⊓ 𝒮ℒ) ⊓ 𝒮ℒ).strictPeriods := one_mem_strictPeriods_inf h1'

  have hq0 : ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ)
        * (qExpansion 1 (g' : ℍ → ℂ)) ^ (r : ℕ)
        * (qExpansion 1 (D' : ℍ → ℂ)) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ)) = 0 := by
    rw [← qExpansion_Sform h1'' g' D', Sform_eq_zero g' D', ModularForm.coe_zero, qExpansion_zero]
  have hq0L : ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      ((qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        * ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (r : ℕ)
        * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
            ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ)) = 0 := by
    have h2 := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hq0
    rw [map_zero, map_sum] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul, map_mul, map_pow, map_pow]

  have hVP : ∀ r : ℕ, ∃ Pco : Polynomial ℂ,
      ((qExpansion 1 (Aform g' D' r : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        = Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) Pco * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
    intro r
    obtain ⟨Pco, -, hPc⟩ := ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne
      (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      (ModularForm.mcast (by push_cast; ring) (Aform g' D' r))
    refine ⟨Pco, ?_⟩
    rw [← hPc, ModularForm.qExpansion_mcast]
  choose Pc hP using hVP

  set FL : LaurentSeries ℂ := ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m with hFLdef
  have hgL : ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by rw [hg'q]
  have hDqL : ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m := by
    rw [hD'q, PowerSeries.coe_pow]

  have hkey : (∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (r : ℕ)) * FL ^ (r : ℕ))
      * (((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
          * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
        ((qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
          * ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (r : ℕ)
          * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
              ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hP (r : ℕ)]
    have hr : (r : ℕ) ≤ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := Nat.lt_succ_iff.mp r.2
    have hexp : ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (r : ℕ)
        * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
            ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ))
        = FL ^ (r : ℕ)
          * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := by
      rw [hgL, hDqL, pow_sub₀ _ hΔmL hr, hFLdef, div_pow]
      field_simp
    linear_combination (-(Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (r : ℕ))
      * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)))) * hexp
  have hDne : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) ≠ 0 := by
    rw [hDqL]
    exact mul_ne_zero (pow_ne_zero _ hΔL) (pow_ne_zero _ hΔmL)
  have hsum0 : ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (r : ℕ)) * FL ^ (r : ℕ) = 0 := by
    have h3 := hkey.trans hq0L
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact h'
    · exact absurd h' hDne
  have hsum0r : ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r = 0 := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun rr => Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc rr) * FL ^ rr) (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1)]
    exact hsum0
  have hsum1 : (∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r)
      + Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * FL ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) = 0 := by
    rw [← Finset.sum_range_succ
      (fun r => Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r) (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))]
    exact hsum0r

  have hcard : (Finset.univ : Finset (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)).card = Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hAn : Aform g' D' (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      = ((-1 : ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) • ModularForm.norm 𝒮ℒ D' := by
    ext τ
    rw [Aform_apply, ModularForm.IsGLPos.smul_apply, norm_apply_eq, smul_eq_mul]
    unfold Pp
    conv_lhs => rw [← hcard]
    rw [coeff_card_prod_linear, Finset.prod_neg, hcard]
  have hqfD : ∀ (q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) (τ : ℍ), quotientFunc D' q τ = Dsl τ := by
    intro q τ
    induction q using Quotient.inductionOn with
    | h r =>
      rw [quotientFunc_mk, hD'def, coe_restrict, slash_action_eqn Dsl _ (inv_mem r.2)]
  have hnormD : ModularForm.norm 𝒮ℒ D' = ModularForm.mcast (by ring)
      (Dsl.pow (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) := by
    ext τ
    calc ModularForm.norm 𝒮ℒ D' τ
        = ∏ q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ, quotientFunc D' q τ := norm_apply_eq D' τ
      _ = ∏ _q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ, Dsl τ := Finset.prod_congr rfl fun q _ => hqfD q τ
      _ = (Dsl τ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by rw [Finset.prod_const, hcard]
      _ = (ModularForm.mcast (by ring) (Dsl.pow (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) : ModularForm 𝒮ℒ (12 * (m : ℤ) * (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) : ℤ))) τ := by
          simp only [ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]
  have hqAnL : ((qExpansion 1 (Aform g' D' (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = (-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
    have hps : qExpansion 1 (Aform g' D' (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) : ℍ → ℂ)
        = PowerSeries.C ((-1 : ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)))
          * (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
      rw [hAn, ModularForm.IsGLPos.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hnormD,
        ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hDSLq, ← pow_mul,
        PowerSeries.smul_eq_C_mul]
    rw [hps, PowerSeries.coe_mul, PowerSeries.coe_pow, PowerSeries.coe_C, map_pow, map_neg,
      map_one]
  have hPn : Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) = (-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
    have h4 := (hP (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))).symm.trans hqAnL
    exact mul_right_cancel₀ (pow_ne_zero _ hΔL) h4
  rw [hPn] at hsum1

  have hmem : ∀ r : ℕ, ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r))
      ∈ Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ)) := fun r =>
    Subalgebra.mul_mem _ (pow_mem (neg_mem (one_mem _)) _)
      (Polynomial.aeval_mem_adjoin_singleton ℂ _)
  refine ⟨Polynomial.X ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) + ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
    Polynomial.C (⟨_, hmem r⟩ : Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ)))
      * Polynomial.X ^ r, ?_, ?_⟩
  ·
    refine Polynomial.monic_X_pow_add ?_
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro r hr
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le r _)
      (by exact_mod_cast Finset.mem_range.mp hr)
  ·
    rw [← Polynomial.aeval_def, map_add, map_pow, Polynomial.aeval_X, map_sum]
    have hterm : ∀ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
        Polynomial.aeval FL
          (Polynomial.C (⟨_, hmem r⟩ : Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ)))
            * Polynomial.X ^ r)
          = ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r)) * FL ^ r := by
      intro r _
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rfl
    rw [Finset.sum_congr rfl hterm]
    have hdist : ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
        ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r)) * FL ^ r
        = (-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
          * ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)), Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hdist]
    have h11 : ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    linear_combination ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * hsum1 - (FL ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * h11

end S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
end P2MW
export P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic (solution)
