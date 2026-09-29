-- Prove2me | solution 1 for LocalGL2.Kirillov.exists_isBump
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a9d32d6d-076b-596e-b11b-768edd4df569

import Mathlib
import Definitions.Def_LocalGL2_Kirillov
import Theorems.Thm_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_Kirillov_exists_isBump

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped Classical

noncomputable section

namespace LocalGL2
p2m_export "LocalGL2" "Kirillov.defectSpan Kirillov.coinv Kirillov.Ch Kirillov.IsBump exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span"
namespace Kirillov
p2m_export "LocalGL2.Kirillov" "defectSpan rT coinv dg exists_dg_mem_of_isOpen UF Um mem_Um_iff Qm rep mk_rep Ch chv chv_rep_mk kirillov kirillov_one kirillov_rT_dg shell shell_smul shell_sum IsBump v_pi_zpow_ne eq_of_v_sub_lt v_sub_lt_iff_mk_eq"
namespace BumpExistence
p2m_open "LocalGL2.Kirillov LocalGL2"

p2m_open "AutomorphicForm IsDedekindDomain NumberField LocalGL2.Kirillov P2MW.S_LocalGL2_Kirillov_exists_isBump.LocalGL2.Kirillov"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "Fx" => (HeightOneSpectrum.adicCompletion K v)ˣ
local notation "Γ" => (WithZero (Multiplicative ℤ))ˣ

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (hψ : ψ ≠ 1)
  (hψ0 : ∀ᶠ t in nhds (0 : HeightOneSpectrum.adicCompletion K v), ψ t = 1)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K₀ : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)),
    IsOpen (K₀ : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
  (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

include hsm in

theorem exists_forall_kirillov_mul_eq {V : G → ℂ} (hV : V ∈ S) :
    ∃ δ : Γ, ∀ (a u : Fx), Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) →
      kirillov v ψ S V (a * u) = kirillov v ψ S V a := by
  obtain ⟨K₀, hKo, hKV⟩ := hsm V hV
  obtain ⟨δ, hδ⟩ := exists_dg_mem_of_isOpen v K₀ hKo
  refine ⟨δ, fun a u hu => ?_⟩
  rw [← kirillov_rT_dg]
  have h : rT v (dg v u) V = V := hKV _ (hδ u hu)
  rw [h]

include hψ hψ0 hstab hsm in

theorem exists_cut {V : G → ℂ} (hV : V ∈ S) (a₀ : F) (δ : Γ) :
    ∃ V' ∈ S, ∀ a : Fx, kirillov v ψ S V' a =
      if Valued.v ((a : F) - a₀) < (δ : WithZero (Multiplicative ℤ)) then kirillov v ψ S V a else 0 := by
  obtain ⟨V', hV'S, h⟩ :=
    LocalGL2.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span K v ψ hψ hψ0 S hstab V hV
      (hsm V hV) a₀ δ
  refine ⟨V', hV'S, fun a => ?_⟩
  obtain ⟨h1, h2⟩ := h (dg v a) (by simp) (by simp) (by simp)
  have e : (dg v a : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F) := by simp
  rw [e] at h1 h2
  split_ifs with ha
  · unfold kirillov
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h1 ha
  · unfold kirillov
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h2 ha

include hψ hψ0 hstab hsm hϖ in

theorem exists_charBump {V₀ : G → ℂ} (hV₀ : V₀ ∈ S) (n : ℤ) {δ₁ : Γ} (χ : Ch v δ₁) :
    ∃ E ∈ S, (∀ u : UF v, shell v ψ S ϖ E n u = chv χ u • (defectSpan v ψ S).mkQ V₀) ∧
      ∀ k : ℤ, k ≠ n → ∀ u : UF v, shell v ψ S ϖ E k u = 0 := by
  obtain ⟨δ₀, hδ₀⟩ := exists_forall_kirillov_mul_eq v ψ S hsm hV₀

  set δ : Γ := min (min δ₀ δ₁) 1 with hδdef
  have hδ0 : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hδle1 : δ ≤ 1 := min_le_right _ _

  set ρ : Γ := δ * Units.mk0 (Valued.v (((ϖ ^ n : Fx) : F))) (v_pi_zpow_ne v ϖ hϖ n) with hρdef
  have hρval : (ρ : WithZero (Multiplicative ℤ)) =
      (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F)) := by
    rw [hρdef, Units.val_mul, Units.val_mk0]

  have hbump : ∀ q : Qm v δ, ∃ B ∈ S, ∀ (k : ℤ) (u : UF v), shell v ψ S ϖ B k u =
      if k = n ∧ (u : Qm v δ) = q then (defectSpan v ψ S).mkQ V₀ else 0 := by
    intro q
    set c : Fx := ϖ ^ n * (rep v δ q : Fx) with hcdef
    obtain ⟨B, hBS, hB⟩ := exists_cut v ψ hψ hψ0 S hstab hsm (hstab V₀ hV₀ (dg v c⁻¹)) (c : F) ρ
    refine ⟨B, hBS, fun k u => ?_⟩
    unfold shell
    rw [hB]
    have hkir : kirillov v ψ S (fun g => V₀ (g * dg v c⁻¹)) (ϖ ^ k * (u : Fx)) =
        kirillov v ψ S V₀ (ϖ ^ k * (u : Fx) * c⁻¹) :=
      kirillov_rT_dg v ψ S V₀ c⁻¹ _
    rw [hkir, hρval]
    by_cases hk : k = n
    · rw [hk]
      by_cases hq : (u : Qm v δ) = q
      · rw [if_pos (show n = n ∧ (u : Qm v δ) = q from ⟨rfl, hq⟩), if_pos]
        · have hmem : (rep v δ q)⁻¹ * u ∈ Um v δ := by
            rw [← QuotientGroup.eq, mk_rep]
            exact hq.symm
          have harg : ϖ ^ n * (u : Fx) * c⁻¹ = 1 * (((rep v δ q)⁻¹ * u : UF v) : Fx) := by
            rw [hcdef, one_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
              mul_comm ((rep v δ q : Fx))⁻¹ (ϖ ^ n)⁻¹, mul_comm (ϖ ^ n) (u : Fx), mul_assoc, mul_inv_cancel_left,
              mul_comm]
          rw [harg, hδ₀ 1 _ (((mem_Um_iff v δ _).mp hmem).trans_le (Units.val_le_val.mpr hδ0)), kirillov_one]
        · have hclose := (v_sub_lt_iff_mk_eq v δ u (rep v δ q)).mpr (by rw [hq, mk_rep])
          have e : ((ϖ ^ n * (u : Fx) : Fx) : F) - (c : F) =
              ((ϖ ^ n : Fx) : F) * (((u : Fx) : F) - ((rep v δ q : Fx) : F)) := by
            rw [hcdef, Units.val_mul, Units.val_mul, mul_sub]
          rw [e, map_mul, mul_comm]
          exact mul_lt_mul_of_pos_right hclose (zero_lt_iff.mpr (v_pi_zpow_ne v ϖ hϖ n))
      · rw [if_neg (show ¬ (n = n ∧ (u : Qm v δ) = q) from fun h => hq h.2), ite_eq_right_iff]
        intro hlt
        exfalso
        apply hq
        have e : ((ϖ ^ n * (u : Fx) : Fx) : F) - (c : F) =
            ((ϖ ^ n : Fx) : F) * (((u : Fx) : F) - ((rep v δ q : Fx) : F)) := by
          rw [hcdef, Units.val_mul, Units.val_mul, mul_sub]
        rw [e, map_mul, mul_comm] at hlt
        have hclose : Valued.v (((u : Fx) : F) - ((rep v δ q : Fx) : F)) < (δ : WithZero (Multiplicative ℤ)) :=
          lt_of_mul_lt_mul_right hlt zero_le
        rw [(v_sub_lt_iff_mk_eq v δ u (rep v δ q)).mp hclose, mk_rep]
    · rw [if_neg (show ¬ (k = n ∧ (u : Qm v δ) = q) from fun h => hk h.1), ite_eq_right_iff]
      intro hlt
      exfalso
      rw [hcdef] at hlt
      exact hk (eq_of_v_sub_lt v ϖ hϖ u (rep v δ q) hδle1 hlt)
  choose B hBS hB using hbump
  refine ⟨∑ q : Qm v δ, chv χ (rep v δ q) • B q, Submodule.sum_mem _ fun q _ => S.smul_mem _ (hBS q), ?_, ?_⟩
  · intro u
    rw [shell_sum]
    simp only [shell_smul, hB, true_and, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [chv_rep_mk v hδ1]
  · intro k hk u
    rw [shell_sum]
    simp only [shell_smul, hB, hk, false_and, if_false, smul_zero, Finset.sum_const_zero]

end LocalGL2.Kirillov.BumpExistence

end

open IsDedekindDomain NumberField _root_.LocalGL2.Kirillov _root_.P2MW.S_LocalGL2_Kirillov_exists_isBump.LocalGL2.Kirillov in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : v.adicCompletion K), ψ t = 1)
    (S : Submodule ℂ (GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (v.adicCompletion K), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (δ : (WithZero (Multiplicative ℤ))ˣ) (n : ℤ) (τ : LocalGL2.Kirillov.Ch v δ)
    (ξ : (GL (Fin 2) (v.adicCompletion K) → ℂ) ⧸ LocalGL2.Kirillov.defectSpan v ψ S)
    (hξ : ξ ∈ LocalGL2.Kirillov.coinv v ψ S) :
    ∃ E ∈ S, LocalGL2.Kirillov.IsBump v ψ S ϖ n τ ξ E := by
  obtain ⟨V₀, hV₀, hV₀ξ⟩ := Submodule.mem_map.mp hξ
  obtain ⟨E, hE, h1, h2⟩ :=
    LocalGL2.Kirillov.BumpExistence.exists_charBump v ψ hψ hψ0 S hstab hsm ϖ hϖ hV₀ n τ
  refine ⟨E, hE, fun k u => ?_⟩
  split_ifs with hk
  · subst hk
    rw [h1 u, hV₀ξ]
  · exact h2 k hk u

end S_LocalGL2_Kirillov_exists_isBump
end P2MW
export P2MW.S_LocalGL2_Kirillov_exists_isBump (solution)
