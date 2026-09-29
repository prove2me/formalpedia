-- Prove2me | solution 1 for ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/595e6c0e-da22-55a0-9bf1-328f56ebbb79

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even

set_option autoImplicit false

open UpperHalfPlane Complex ConjAct Pointwise
open scoped MatrixGroups ModularForm Manifold Topology

namespace ALRATEVEN

theorem coeff_mem_of_mul_eq {S : Subfield ℂ} {x a b : PowerSeries ℂ}
    (hb : ∀ n, b.coeff n ∈ S) (hb0 : b.coeff 0 = 1) (ha : ∀ n, a.coeff n ∈ S) (h : x * b = a) :
    ∀ n, x.coeff n ∈ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := congrArg (fun s : PowerSeries ℂ => s.coeff n) h
    simp only [PowerSeries.coeff_mul] at hn
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Nat.sub_self, hb0, mul_one] at hn
    have : x.coeff n = a.coeff n - ∑ i ∈ Finset.range n, x.coeff i * b.coeff (n - i) := by
      rw [← hn]; ring
    rw [this]
    exact sub_mem (ha n) (sum_mem fun i hi => mul_mem (ih i (Finset.mem_range.mp hi)) (hb _))

private theorem _root_.ALRATEVEN.ratCast_mem (S : Subfield ℂ) (r : ℚ) : (r : ℂ) ∈ S := SubfieldClass.ratCast_mem S r

p2m_export "ALRATEVEN" "ratCast_mem"

theorem qParam_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam (p : ℝ) ((ModularForm.heckeDiagMatrix p • τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) := by
  rw [ModularForm.coe_heckeDiagMatrix_smul hp]
  simp only [Function.Periodic.qParam, ofReal_natCast, ofReal_one, div_one]
  congr 1
  have : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  field_simp

theorem qExpansion_eq_of_coe_eq_comp {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (F : ModularForm Γ k)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (g : ℍ → ℂ)
    (hgper : Function.Periodic (g ∘ ofComplex) (p : ℝ)) (hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hgbdd : IsBoundedAtImInfty g)
    (hF : (⇑F : ℍ → ℂ) = fun τ : ℍ => g (ModularForm.heckeDiagMatrix p • τ)) :
    qExpansion 1 (⇑F : ℍ → ℂ) = qExpansion (p : ℝ) g := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
  ext n
  symm
  refine UpperHalfPlane.qExpansion_coeff_unique F (c := fun m => (qExpansion (p : ℝ) g).coeff m) one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero F one_pos hΓ) ?_ n
  intro τ
  have := UpperHalfPlane.hasSum_qExpansion hp' hgper hghol hgbdd (ModularForm.heckeDiagMatrix p • τ)
  rw [qParam_heckeDiagMatrix_smul hp] at this
  rwa [hF]

section G

theorem exists_weight (k : ℤ) (hk : Even k) : ∃ (m w : ℕ), 3 ≤ w ∧ Even w ∧ k + (w : ℤ) = 12 * (m : ℤ) := by
  obtain ⟨t, rfl⟩ := hk
  refine ⟨t.natAbs + 1, (12 * ((t.natAbs : ℤ) + 1) - (t + t)).toNat, ?_, ?_, ?_⟩
  · omega
  · exact ⟨(6 * ((t.natAbs : ℤ) + 1) - t).toNat, by omega⟩
  · omega

variable {N : ℕ} {k : ℤ}

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_Γ1 : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by simp [Γ1]

theorem coe_mem_SL (α : SL(2, ℤ)) : (α : GL (Fin 2) ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨α, rfl⟩

theorem apply_smul_eq_slash_mul (k : ℤ) (f : ℍ → ℂ) (α : SL(2, ℤ)) (τ : ℍ) :
    f (α • τ) = (f ∣[k] α) τ * denom (α : GL (Fin 2) ℝ) τ ^ k := by
  rw [ModularForm.SL_slash_apply, mul_assoc, ← zpow_add₀ (denom_ne_zero _ τ), neg_add_cancel, zpow_zero, mul_one]

variable [NeZero N] (f : ModularForm (Γ1 N) k) {w : ℕ} (hw : 3 ≤ w) (m : ℕ)

noncomputable def G : ℍ → ℂ := fun τ => f τ * ModularForm.E hw τ / ModularForm.discriminant τ ^ m

theorem G_smul_mul (hkw : k + (w : ℤ) = 12 * (m : ℤ)) (α : SL(2, ℤ)) (τ : ℍ) :
    G f hw m (α • τ) * ModularForm.discriminant τ ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) τ * ModularForm.E hw τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  have hΔ' : ModularForm.discriminant (α • τ) ≠ 0 := ModularForm.discriminant_ne_zero _
  have hE : ModularForm.E hw (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (w : ℤ) * ModularForm.E hw τ :=
    SlashInvariantForm.slash_action_eqn'' (ModularForm.E hw) (coe_mem_SL α) τ
  have hD : ModularForm.discriminant (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (coe_mem_SL α) τ
    simpa [CuspForm.coe_discriminant] using this
  rw [G, apply_smul_eq_slash_mul k (⇑f) α τ, hE, hD]
  set d := denom (α : GL (Fin 2) ℝ) τ with hdd
  have hpow : d ^ k * d ^ (w : ℤ) = (d ^ (12 : ℕ)) ^ m := by
    rw [← zpow_add₀ hd, hkw, ← pow_mul, ← zpow_natCast]; push_cast; rfl
  have hpow' : d ^ k * d ^ (w : ℤ) = (d ^ (12 : ℤ)) ^ m := by
    rw [hpow, zpow_ofNat]
  rw [mul_pow, ← hpow']
  field_simp

theorem G_inv (hkw : k + (w : ℤ) = 12 * (m : ℤ)) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N) (τ : ℍ) :
    G f hw m (g • τ) = G f hw m τ := by
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  have key := G_smul_mul f hw m hkw g τ
  have hf : ((⇑f : ℍ → ℂ) ∣[k] g) = ⇑f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hg)
  rw [hf] at key
  have : G f hw m τ * ModularForm.discriminant τ ^ m = f τ * ModularForm.E hw τ := by
    rw [G, div_mul_cancel₀ _ (pow_ne_zero _ hΔ)]
  exact mul_right_cancel₀ (pow_ne_zero _ hΔ) (key.trans this.symm)

theorem G_comp_mul_eq (hkw : k + (w : ℤ) = 12 * (m : ℤ)) (α : SL(2, ℤ)) :
    (fun τ : ℍ => G f hw m (α • τ)) * ModularForm.discriminant ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) * ⇑(ModularForm.E hw) := by
  ext τ
  simp only [Pi.mul_apply, Pi.pow_apply]
  exact G_smul_mul f hw m hkw α τ

theorem G_mul_eq (hkw : k + (w : ℤ) = 12 * (m : ℤ)) :
    G f hw m * ModularForm.discriminant ^ m = (⇑f : ℍ → ℂ) * ⇑(ModularForm.E hw) := by
  have := G_comp_mul_eq f hw m hkw 1
  simpa [SlashAction.slash_one] using this

theorem G_bdd (hkw : k + (w : ℤ) = 12 * (m : ℤ)) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty ((fun τ : ℍ => G f hw m (α • τ)) * ModularForm.discriminant ^ m) := by
  rw [G_comp_mul_eq f hw m hkw α]
  have hE : IsBoundedAtImInfty (⇑(ModularForm.E hw) : ℍ → ℂ) := by
    have := ModularFormClass.bdd_at_infty_slash (ModularForm.E hw) (1 : SL(2, ℤ))
    simpa using this
  exact (ModularFormClass.bdd_at_infty_slash f α).mul hE

theorem G_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G f hw m) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ * ModularForm.E hw τ) := f.holo'.mul (ModularForm.E hw).holo'
  have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => (ModularForm.discriminant τ ^ m)⁻¹) := by
    have hΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ModularForm.discriminant := by
      rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
    rw [UpperHalfPlane.mdifferentiable_iff] at hΔ ⊢
    exact (hΔ.pow m).inv fun z hz => pow_ne_zero _ (ModularForm.discriminant_ne_zero _)
  have hG : G f hw m = fun τ : ℍ => (f τ * ModularForm.E hw τ) * (ModularForm.discriminant τ ^ m)⁻¹ := by
    ext τ; simp [G, div_eq_mul_inv]
  rw [hG]
  exact h1.mul h2

end G

section Pieces

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M]

theorem p_mem_strictPeriods_conj (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (p : ℝ) ∈ (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ1 (M * p)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, toConjAct_smul]

  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c', hc'⟩ := hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  let δ' : SL(2, ℤ) := ⟨!![1 - p * γ 0 0 * γ 1 0, p * γ 0 0 * γ 0 0; -(p * γ 1 0 * γ 1 0), 1 + p * γ 0 0 * γ 1 0], by
    rw [Matrix.det_fin_two_of]; ring⟩
  have hmem : δ' ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [δ', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    refine ⟨?_, ?_, ?_⟩
    · rw [show (1 - (p : ℤ) * γ 0 0 * γ 1 0 : ℤ) = 1 + (M * p : ℕ) * (-(γ 0 0 * c')) by rw [hc']; push_cast; ring]
      simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, Int.cast_neg, ZMod.natCast_self, zero_mul, add_zero]
    · rw [show (1 + (p : ℤ) * γ 0 0 * γ 1 0 : ℤ) = 1 + (M * p : ℕ) * (γ 0 0 * c') by rw [hc']; push_cast; ring]
      simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
    · rw [show (-((p : ℤ) * γ 1 0 * γ 1 0) : ℤ) = (M * p : ℕ) * (-(c' * γ 1 0)) by rw [hc']; push_cast; ring]
      simp only [Int.cast_mul, Int.cast_natCast, Int.cast_neg, ZMod.natCast_self, zero_mul]
  have hdetR : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
  have hconj : (γ : GL (Fin 2) ℝ) * Matrix.GeneralLinearGroup.upperRightHom (p : ℝ)
      = (δ' : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    simp only [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [δ', Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.upperRightHom,
        Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map] <;> push_cast <;>
      first | ring1 | linear_combination (-(((γ 0 0 : ℤ) : ℝ) * (p : ℝ))) * hdetR
            | linear_combination (-(((γ 1 0 : ℤ) : ℝ) * (p : ℝ))) * hdetR
  rw [show (γ : GL (Fin 2) ℝ) * Matrix.GeneralLinearGroup.upperRightHom (p : ℝ) * (γ : GL (Fin 2) ℝ)⁻¹ = (δ' : GL (Fin 2) ℝ)
    from by rw [mul_inv_eq_iff_eq_mul]; exact hconj]
  exact Subgroup.mem_map_of_mem _ hmem

theorem Γ1_le_conj_heckeDiagMatrix : Γ1 (M * p) ≤ toConjAct (ModularForm.heckeDiagMatrix p)⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  intro x hx
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, toConjAct_smul]
  obtain ⟨-, -, hκ⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hκ
  obtain ⟨c', hc'⟩ := (Dvd.dvd.trans (by exact ⟨M, by push_cast; ring⟩ : (p : ℤ) ∣ ((M * p : ℕ) : ℤ)) hκ)
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := δ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  let δ'' : SL(2, ℤ) := ⟨!![δ 0 0, p * δ 0 1; c', δ 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hc'] at hdet; linear_combination hdet⟩
  have hconj : ModularForm.heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ)
      = (δ'' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p := by
    have hcR : ((δ 1 0 : ℤ) : ℝ) = p * c' := by exact_mod_cast hc'
    apply Units.ext
    ext i j
    simp only [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [δ'', Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hp0,
        Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, hcR] <;> ring
  rw [show ModularForm.heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) * (ModularForm.heckeDiagMatrix p)⁻¹
    = (δ'' : GL (Fin 2) ℝ) from by rw [mul_inv_eq_iff_eq_mul]; exact hconj]
  exact ⟨δ'', rfl⟩

variable {w : ℕ} (hw : 3 ≤ w)

noncomputable def ED : ModularForm (Γ1 (M * p)) w :=
  ((p : ℂ) ^ ((w : ℤ) - 1))⁻¹ • ModularCurve.restrictForm Γ1_le_conj_heckeDiagMatrix
    (ModularForm.translate (ModularForm.E hw) (ModularForm.heckeDiagMatrix p))

theorem coe_ED : (⇑(ED (p := p) (M := M) hw) : ℍ → ℂ) = fun τ : ℍ => ModularForm.E hw (ModularForm.heckeDiagMatrix p • τ) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  ext τ
  simp only [ED, ModularForm.IsGLPos.coe_smul, ModularCurve.coe_restrictForm, ModularForm.coe_translate, Pi.smul_apply,
    smul_eq_mul, ModularForm.slash_heckeDiagMatrix_apply _ hp0]
  rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hpC), one_mul]

theorem ED_qExpansion_coeff (n : ℕ) :
    (qExpansion 1 (⇑(ED (p := p) (M := M) hw) : ℍ → ℂ)).coeff n =
      if (p : ℤ) ∣ (n : ℤ) then (qExpansion 1 (⇑(ModularForm.E hw) : ℍ → ℂ)).coeff (n / p) else 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne p (ModularForm.E hw)
  rw [← coe_ED (M := M) hw] at h
  have hn := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) h
  simp only [HahnSeries.ofPowerSeries_apply_coeff] at hn
  rw [hn]
  by_cases hd : (p : ℤ) ∣ (n : ℤ)
  · obtain ⟨q, hq⟩ := hd
    rw [if_pos ⟨q, hq⟩, hq, ModularCurve.qExpand_coeff_mul]
    have hq0 : 0 ≤ q := by
      have : (0 : ℤ) ≤ p * q := by rw [← hq]; exact Int.natCast_nonneg n
      exact nonneg_of_mul_nonneg_right this (by exact_mod_cast (Fact.out : p.Prime).pos)
    obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le hq0
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    congr 1
    have : n = p * q' := by exact_mod_cast hq
    rw [this, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]
  · rw [if_neg hd, ModularCurve.qExpand_coeff_of_not_dvd p _ hd]

theorem E_qExpansion_coeff_rat (hwe : Even w) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑(ModularForm.E hw) : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [EisensteinSeries.E_qExpansion_coeff hw hwe n]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * w / bernoulli w) * (ArithmeticFunction.sigma (w - 1) n : ℚ), ?_⟩
    simp [hn]

theorem ED_qExpansion_coeff_rat (hwe : Even w) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑(ED (p := p) (M := M) hw) : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ED_qExpansion_coeff]
  split_ifs
  · exact E_qExpansion_coeff_rat hw hwe _
  · exact ⟨0, by simp⟩

theorem ED_qExpansion_coeff_zero (hwe : Even w) :
    (qExpansion 1 (⇑(ED (p := p) (M := M) hw) : ℍ → ℂ)).coeff 0 = 1 := by
  rw [ED_qExpansion_coeff, Nat.cast_zero, if_pos (dvd_zero _), Nat.zero_div, EisensteinSeries.E_qExpansion_coeff_zero hw hwe]

end Pieces

end ALRATEVEN

open ALRATEVEN UpperHalfPlane in
open scoped MatrixGroups ModularForm Manifold in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Even k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
      IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set K := IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) with hKdef

  obtain ⟨m, w, hw3, hwe, hkw⟩ := exists_weight k hk

  have hkey : ∀ n' : ℕ, (qExpansion (p : ℝ) (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑(ModularForm.E hw3))).coeff n' ∈ K := by
    intro n'
    have hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (G f hw3 m * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) := by
      intro n
      rw [G_mul_eq f hw3 m hkw,
        UpperHalfPlane.qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_Γ1)
          (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hw3) one_pos (by simp)),
        PowerSeries.coeff_mul]
      have : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ∃ r : ℚ,
          (qExpansion 1 (⇑f : ℍ → ℂ)).coeff ij.1 * (qExpansion 1 (⇑(ModularForm.E hw3) : ℍ → ℂ)).coeff ij.2 = (r : ℂ) := by
        intro ij _
        obtain ⟨r₂, hr₂⟩ := E_qExpansion_coeff_rat hw3 hwe ij.2
        refine ⟨(PowerSeries.coeff ij.1 p₀ : ℤ) * r₂, ?_⟩
        rw [← hf.coeff ij.1, hr₂]; push_cast; ring
      choose r hr using this
      refine ⟨∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal n).attach, r ij.1 ij.2, ?_⟩
      push_cast
      rw [← Finset.sum_attach]
      exact Finset.sum_congr rfl fun ij _ => hr ij.1 ij.2
    have := ModularCurve.qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul M p hpM m (G f hw3 m)
      (G_mdifferentiable f hw3 m) (fun g hg τ => G_inv f hw3 m hkw g hg τ) (fun α => G_bdd f hw3 m hkw α) hrat γ hγ hγp n'
    rwa [G_comp_mul_eq f hw3 m hkw γ] at this

  obtain ⟨F, hF⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM f γ hγ hγp
  let FE : ModularForm (Γ1 (M * p)) (k + w) := F.mul (ED hw3)

  set g : ℍ → ℂ := ((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑(ModularForm.E hw3) with hgdef
  have hT : (⇑(ModularForm.translate f (γ : GL (Fin 2) ℝ)) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
    rw [ModularForm.coe_translate, ModularForm.SL_slash]
  have hgper : Function.Periodic (g ∘ ofComplex) (p : ℝ) := by
    have h1 : Function.Periodic (((⇑f : ℍ → ℂ) ∣[k] γ) ∘ ofComplex) (p : ℝ) := by
      rw [← hT]
      exact SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.translate f (γ : GL (Fin 2) ℝ))
        (p_mem_strictPeriods_conj γ hγ)
    have h2 : Function.Periodic ((⇑(ModularForm.E hw3) : ℍ → ℂ) ∘ ofComplex) (p : ℝ) := by
      have := (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hw3) (show (1 : ℝ) ∈ (𝒮ℒ).strictPeriods by simp)).nat_mul p
      simpa using this
    exact h1.mul h2
  have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    have := (ModularFormClass.holo (ModularForm.translate f (γ : GL (Fin 2) ℝ))).mul (ModularFormClass.holo (ModularForm.E hw3))
    rwa [hT] at this
  have hgbdd : IsBoundedAtImInfty g := by
    have hE : IsBoundedAtImInfty (⇑(ModularForm.E hw3) : ℍ → ℂ) := by
      have := ModularFormClass.bdd_at_infty_slash (ModularForm.E hw3) (1 : SL(2, ℤ))
      simpa using this
    exact (ModularFormClass.bdd_at_infty_slash f γ).mul hE
  have hFE : (⇑FE : ℍ → ℂ) = fun τ : ℍ => g (ModularForm.heckeDiagMatrix p • τ) := by
    ext τ
    simp only [FE, ModularForm.coe_mul, Pi.mul_apply, hF, coe_ED, hgdef]

  have hqFE : qExpansion 1 (⇑FE : ℍ → ℂ) = qExpansion (p : ℝ) g :=
    qExpansion_eq_of_coe_eq_comp FE one_mem_strictPeriods_Γ1 hp0 g hgper hghol hgbdd hFE
  have hmul : qExpansion 1 (⇑F : ℍ → ℂ) * qExpansion 1 (⇑(ED (p := p) (M := M) hw3) : ℍ → ℂ) = qExpansion (p : ℝ) g := by
    rw [← hqFE]
    exact (ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ1 F (ED hw3)).symm

  have hdiv := coeff_mem_of_mul_eq (S := K.toSubfield) (x := qExpansion 1 (⇑F : ℍ → ℂ))
    (a := qExpansion (p : ℝ) g) (b := qExpansion 1 (⇑(ED (p := p) (M := M) hw3) : ℍ → ℂ))
    (fun n => by obtain ⟨r, hr⟩ := ED_qExpansion_coeff_rat (p := p) (M := M) hw3 hwe n; rw [hr]; exact ratCast_mem _ r)
    (ED_qExpansion_coeff_zero hw3 hwe) (fun n => hkey n) hmul
  have := hdiv n
  rwa [hF] at this

end S_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
end P2MW
export P2MW.S_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even (solution)
