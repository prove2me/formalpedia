-- Prove2me | solution 1 for ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1099ed0b-5834-5390-80aa-88501e92519f

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open ConjAct Pointwise

namespace ALFORM

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M]

theorem intCast_zmod_eq_one_iff (N : ℕ) (x : ℤ) : ((x : ZMod N) = 1) ↔ (N : ℤ) ∣ x - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero]

theorem exists_conj (hpM : ¬ p ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma1 (M * p)) :
    ∃ δ' : SL(2, ℤ), δ' ∈ CongruenceSubgroup.Gamma1 (M * p) ∧
      ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * (δ : GL (Fin 2) ℝ)
        = (δ' : GL (Fin 2) ℝ) * ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hcop : IsCoprime (M : ℤ) (p : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM)).symm

  set a := γ 0 0 with ha; set b := γ 0 1 with hb; set c := γ 1 0 with hc; set d := γ 1 1 with hd
  set α := δ 0 0 with hα0; set β := δ 0 1 with hβ0; set κ := δ 1 0 with hκ0; set l := δ 1 1 with hl0
  obtain ⟨d', hd'⟩ := hγp
  have hcM : (M : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c', hc'⟩ := hcM
  obtain ⟨hα, hl, hκ⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hδ
  rw [intCast_zmod_eq_one_iff] at hα hl
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hκ
  obtain ⟨tα, htα⟩ := hα
  obtain ⟨tl, htl⟩ := hl
  obtain ⟨κ', hκ'⟩ := hκ
  push_cast at htα htl hκ'
  change α - 1 = M * p * tα at htα
  change l - 1 = M * p * tl at htl
  change κ = M * p * κ' at hκ'
  have hdet : a * d - b * c = 1 := by
    have h := γ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  have hδdet : α * l - β * κ = 1 := by
    have h := δ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  have hu : a * (p * d') - b * (M * c') = 1 := by rw [← hd', ← hc']; exact hdet
  have hδ' : α * l - β * (M * p * κ') = 1 := by rw [← hκ']; exact hδdet

  let e00 : ℤ := p * d' * (a * α + b * (M * κ')) - a * p * (M * c') * β - b * (M * c') * l
  let e01 : ℤ := -a * b * α - b * b * (M * κ') + a * a * p * β + a * b * l
  let e10 : ℤ := p * (d' * ((M * c') * α + d' * (M * p * κ')) - (M * c') * (M * c') * β - (M * c') * d' * l)
  let e11 : ℤ := -b * (M * c') * α - b * d' * (M * p * κ') + a * (M * c') * p * β + a * (p * d') * l
  have hdet' : e00 * e11 - e01 * e10 = 1 := by
    simp only [e00, e01, e10, e11]
    linear_combination (a * (p * d') - b * (M * c')) ^ 2 * hδ' + ((a * (p * d') - b * (M * c')) + 1) * hu
  refine ⟨⟨!![e00, e01; e10, e11], by rw [Matrix.det_fin_two_of]; exact hdet'⟩, ?_, ?_⟩
  ·
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    refine ⟨?_, ?_, ?_⟩
    · rw [intCast_zmod_eq_one_iff]; push_cast
      refine hcop.mul_dvd ⟨p * tα + b * c' * α + p * d' * b * κ' - a * p * c' * β - b * c' * l, ?_⟩
        ⟨d' * (a * α + b * M * κ') - a * M * c' * β - a * d' * l + M * tl, ?_⟩
      · simp only [e00]; linear_combination α * hu + htα
      · simp only [e00]; linear_combination l * hu + htl
    · rw [intCast_zmod_eq_one_iff]; push_cast
      refine hcop.mul_dvd ⟨-b * c' * α - b * d' * p * κ' + a * c' * p * β + b * c' * l + p * tl, ?_⟩
        ⟨M * tα - a * d' * α - b * d' * M * κ' + a * M * c' * β + a * d' * l, ?_⟩
      · simp only [e11]; linear_combination l * hu + htl
      · simp only [e11]; linear_combination α * hu + htα
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
      exact ⟨d' * c' * α + d' * d' * p * κ' - M * c' * c' * β - c' * d' * l, by simp only [e10]; ring⟩
  ·
    have haR : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = (a : ℝ) := by simp [ha]
    have hbR : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = (b : ℝ) := by simp [hb]
    have hcR : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = (M : ℝ) * c' := by
      rw [show ((M : ℝ) * c' : ℝ) = ((M * c' : ℤ) : ℝ) by push_cast; ring, ← hc']; simp [hc]
    have hdR : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) = (p : ℝ) * d' := by
      rw [show ((p : ℝ) * d' : ℝ) = ((p * d' : ℤ) : ℝ) by push_cast; ring, ← hd']; simp [hd]
    have hαR : (((δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = (α : ℝ) := by simp [hα0]
    have hβR : (((δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = (β : ℝ) := by simp [hβ0]
    have hκR : (((δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = (M : ℝ) * p * κ' := by
      rw [show ((M : ℝ) * p * κ' : ℝ) = ((M * p * κ' : ℤ) : ℝ) by push_cast; ring, ← hκ']; simp [hκ0]
    have hlR : (((δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) = (l : ℝ) := by simp [hl0]
    have huR : (a : ℝ) * (p * d') - b * (M * c') = 1 := by exact_mod_cast hu
    set δ' : SL(2, ℤ) := ⟨!![e00, e01; e10, e11], by rw [Matrix.det_fin_two_of]; exact hdet'⟩ with hδ'def
    have h00 : (((δ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = (e00 : ℝ) := by simp [δ']
    have h01 : (((δ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = (e01 : ℝ) := by simp [δ']
    have h10 : (((δ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = (e10 : ℝ) := by simp [δ']
    have h11 : (((δ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) = (e11 : ℝ) := by simp [δ']
    have D00 : (((ModularForm.heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = (p : ℝ) := by
      simp [ModularForm.val_heckeDiagMatrix hp0]
    have D01 : (((ModularForm.heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = 0 := by
      simp [ModularForm.val_heckeDiagMatrix hp0]
    have D10 : (((ModularForm.heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = 0 := by
      simp [ModularForm.val_heckeDiagMatrix hp0]
    have D11 : (((ModularForm.heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) = 1 := by
      simp [ModularForm.val_heckeDiagMatrix hp0]
    apply Units.ext
    ext i j
    simp only [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Fin.zero_eta, Fin.mk_one, haR, hbR, hcR, hdR, hαR, hβR,
        hκR, hlR, h00, h01, h10, h11, D00, D01, D10, D11, e00, e01, e10, e11] <;> push_cast
    · linear_combination (-((a : ℝ) * p * α + b * (M * p * κ'))) * huR
    · linear_combination (-((a : ℝ) * p * β + b * l)) * huR
    · linear_combination (-((M : ℝ) * c' * p * α + p * d' * (M * p * κ'))) * huR
    · linear_combination (-((M : ℝ) * c' * p * β + p * d' * l)) * huR

theorem exists_opposite (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ' 1 1 ∧
      ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
        = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨d', hd'⟩ := hγp
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  have hu : γ 0 0 * (p * d') - γ 0 1 * γ 1 0 = 1 := by rw [← hd']; exact hdet
  refine ⟨⟨!![d', -γ 0 1; -γ 1 0, γ 0 0 * p], by rw [Matrix.det_fin_two_of]; linear_combination hu⟩, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    have := CongruenceSubgroup.Gamma0_mem.mp hγ
    simp [this]
  · simp
  · apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
    have hdR : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) = (p : ℝ) * d' := by
      rw [show ((p : ℝ) * d' : ℝ) = ((p * d' : ℤ) : ℝ) by push_cast; ring, ← hd']; simp
    have huR : ((γ 0 0 : ℤ) : ℝ) * (p * d') - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hu
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hp0, Matrix.SpecialLinearGroup.toGL,
        Matrix.SpecialLinearGroup.map, Units.val_mul, Matrix.natCast_apply, hd'] <;>
      first | ring1 | linear_combination (p : ℝ) * huR

variable (p M) in

theorem conj_Γ1_eq (hpM : ¬ p ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    toConjAct ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)⁻¹ • Γ1 (M * p) = Γ1 (M * p) := by
  set W : GL (Fin 2) ℝ := (γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p with hW
  set S : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) with hS
  have hcentral : ∀ y : GL (Fin 2) ℝ, S * y = y * S := fun y => Units.ext (by
    rw [Units.val_mul, Units.val_mul, hS, Matrix.GeneralLinearGroup.scalar, Units.coe_map]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') (y : Matrix (Fin 2) (Fin 2) ℝ)).eq)
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, toConjAct_smul]
  constructor
  · intro hx
    obtain ⟨δ, hδ, hδx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ', hγ', hγ'p, hsc⟩ := exists_opposite (p := p) γ hγ hγp
    obtain ⟨δ', hδ', hconj⟩ := exists_conj hpM γ' hγ' hγ'p δ hδ
    set W' : GL (Fin 2) ℝ := (γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p with hW'
    have hW'eq : W' = W⁻¹ * S := by rw [eq_inv_mul_iff_mul_eq]; exact hsc
    set D : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ δ with hD
    have e1 : x = W⁻¹ * D * W := by rw [hδx]; group
    have e2 : W' * D * W'⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ δ' := by
      rw [mul_inv_eq_iff_eq_mul]; exact hconj
    have e3 : W' * D * W'⁻¹ = W⁻¹ * D * W := by
      have hSD : S * D * S⁻¹ = D := by rw [hcentral, mul_inv_cancel_right]
      calc W' * D * W'⁻¹ = W⁻¹ * (S * D * S⁻¹) * W := by rw [hW'eq]; group
        _ = W⁻¹ * D * W := by rw [hSD]
    rw [e1, ← e3, e2]
    exact Subgroup.mem_map_of_mem _ hδ'
  · intro hx
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨δ', hδ', hconj⟩ := exists_conj hpM γ hγ hγp δ hδ
    have : W * Matrix.SpecialLinearGroup.mapGL ℝ δ * W⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ δ' := by
      rw [mul_inv_eq_iff_eq_mul]; exact hconj
    rw [this]
    exact Subgroup.mem_map_of_mem _ hδ'

end ALFORM

open ALFORM ConjAct Pointwise in
open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ F : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F : UpperHalfPlane → ℂ) = fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  set W : GL (Fin 2) ℝ := (γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p with hW
  have hΓ : Γ1 (M * p) = toConjAct W⁻¹ • Γ1 (M * p) := (conj_Γ1_eq p M hpM γ hγ hγp).symm
  let G : ModularForm (Γ1 (M * p)) k := (ModularForm.translate f W).mcast rfl hΓ
  have hG : (⇑G : UpperHalfPlane → ℂ) = (⇑f : UpperHalfPlane → ℂ) ∣[k] W := rfl
  refine ⟨((p : ℂ) ^ (k - 1))⁻¹ • G, ?_⟩
  ext τ
  rw [ModularForm.IsGLPos.coe_smul, Pi.smul_apply, hG, hW, SlashAction.slash_mul, ModularForm.SL_slash,
    ModularForm.slash_heckeDiagMatrix_apply k hp0, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hpC), one_mul]

end S_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul (solution)
