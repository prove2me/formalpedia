-- Prove2me | solution 1 for GlobalTheory.exists_integral_model_of_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:39.113377+00:00
-- url     : https://prove2.me/submissions/e9186795-67ba-4920-a31d-f73a1e0d4153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Theorems.Thm_P2M_GlobalTheory_j_mul___a77416e24072
import Theorems.Thm_GlobalTheory_mem_powSaturation
import Theorems.Thm_GlobalTheory_mem_of_mem_powSaturation
import Theorems.Thm_GlobalTheory_coeff_mem_variableChange
import Theorems.Thm_GlobalTheory_mem_range_of_quartic
import Theorems.Thm_P2M_GlobalTheory_deuringCurve___056d131758c7
import Theorems.Thm_P2M_GlobalTheory_deuringCurve_c__6d8748b3be6c
import Theorems.Thm_P2M_GlobalTheory_splitCurve___21d0522b5d77
import Theorems.Thm_P2M_GlobalTheory_splitCurve_c__d8bdd509b04e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]
variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
namespace GlobalTheory
theorem _root_.solution (hj : W.j ∈ (algebraMap A K).range) (hΔ : W.Δ = 1)
    {C₂ C₃ : VariableChange K} (hu₂ : C₂.u = 1) (hu₃ : C₃.u = 1) {P Q a b : K}
    (e₂ : C₂ • W = splitCurve P Q) (e₃ : C₃ • W = deuringCurve a b) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by
  have hinj : Function.Injective (algebraMap A K) := IsIntegralClosure.algebraMap_injective A A K
  set S := (algebraMap A K).range with hS
  have hjΔ := j_mul_Δ W
  have hrel := W.c_relation
  rw [hΔ] at hjΔ hrel
  have hc₄ : W.c₄ ∈ S := mem_range_of_quartic (zero_mem _) (neg_mem hj) (zero_mem _) (zero_mem _)
    (by linear_combination -W.c₄ * hjΔ)
  have hc₆ : W.c₆ ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _)
    (sub_mem (ofNat_mem _ 1728) (pow_mem hc₄ 3)) (zero_mem _)
    (by linear_combination W.c₆ ^ 2 * hrel)
  have p₄ := variableChange_c₄ W C₂
  have pΔ := variableChange_Δ W C₂
  have q₄ := variableChange_c₄ W C₃
  have q₆ := variableChange_c₆ W C₃
  have qΔ := variableChange_Δ W C₃
  rw [e₂, hu₂] at p₄ pΔ
  rw [e₃, hu₃] at q₄ q₆ qΔ
  simp only [inv_one, Units.val_one, one_pow, one_mul, hΔ, splitCurve_Δ, splitCurve_c₄,
    deuringCurve_Δ, deuringCurve_c₄] at p₄ pΔ q₄ q₆ qΔ
  replace q₆ : -a ^ 6 + 36 * a ^ 3 * b - 216 * b ^ 2 = W.c₆ := by
    rw [← q₆]
    simp only [deuringCurve, c₆, b₂, b₄, b₆]
    ring
  have hN : 16 * (P * Q) ∈ S := mem_range_of_quartic (zero_mem _) (ofNat_mem _ 256) (zero_mem _)
    (neg_mem hc₄) (by rw [← p₄]; linear_combination -256 * 16 * (P * Q) * pΔ)
  have hM : 4 * (P + Q) ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _)
    (neg_mem (add_mem hc₄ (mul_mem (ofNat_mem _ 3) hN))) (zero_mem _) (by rw [← p₄]; ring)
  have ha₂ : a ^ 2 ∈ S := mem_range_of_quartic (mul_mem (neg_mem (ofNat_mem _ 3)) (pow_mem hc₄ 2))
    (mul_mem (neg_mem (ofNat_mem _ 8)) hc₆) (mul_mem (neg_mem (ofNat_mem _ 6)) hc₄) (zero_mem _)
    (by rw [← q₄, ← q₆]; ring)
  have ha : a ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _) (neg_mem ha₂) (zero_mem _)
    (by ring)
  have hb : 27 * b ∈ S := mem_range_of_quartic (ofNat_mem _ 19683) (zero_mem _) (zero_mem _)
    (neg_mem (pow_mem ha 3)) (by linear_combination -19683 * qΔ)
  obtain ⟨r, s, t, hD⟩ : ∃ r s t : K, C₃ * C₂⁻¹ = ⟨1, r, s, t⟩ :=
    ⟨_, _, _, VariableChange.ext (by simp [VariableChange.mul_def, VariableChange.inv_def, hu₂, hu₃])
      rfl rfl rfl⟩
  have eD : (⟨1, r, s, t⟩ : VariableChange K) • splitCurve P Q = deuringCurve a b := by
    rw [← hD, ← e₂, ← e₃, mul_smul, inv_smul_smul]
  have d₁ := congrArg WeierstrassCurve.a₁ eD
  have d₂ := congrArg WeierstrassCurve.a₂ eD
  have d₃ := congrArg WeierstrassCurve.a₃ eD
  simp only [variableChange_def, splitCurve, deuringCurve, inv_one, Units.val_one] at d₁ d₂ d₃
  have hr : 12 * r ∈ S := by
    convert add_mem ha₂ hM using 1
    linear_combination 4 * d₂ + (2 * s + a) * d₁
  have ht : 54 * (t - 4 * r * s) ∈ S := by
    convert sub_mem hb (mul_mem (ofNat_mem _ 9) (mul_mem hr ha)) using 1
    linear_combination 27 * d₃ - 108 * r * d₁
  set W' := (⟨1, -4 * r, 0, -28 * (t - 4 * r * s)⟩ : VariableChange K) • deuringCurve a b with hW'
  have e' : (⟨1, -3 * r, s, -27 * (t - 4 * r * s)⟩ : VariableChange K) • splitCurve P Q = W' := by
    rw [hW', ← eD, ← mul_smul]
    congr 1
    simp only [VariableChange.mul_def, Units.val_one, mul_one]
    ext <;> dsimp only <;> ring
  have m₃ := coeff_mem_variableChange (powSaturation S 3) (W := deuringCurve a b)
    (mem_powSaturation 0 ha (by simp [deuringCurve])) (zero_mem _)
    (mem_powSaturation 3 hb (by simp only [deuringCurve]; norm_num)) (zero_mem _) (zero_mem _)
    (mem_powSaturation 1 (neg_mem hr) (by push_cast; ring)) (zero_mem _)
    (mem_powSaturation 3 (mul_mem (neg_mem (ofNat_mem _ 14)) ht) (by push_cast; ring)) hW'.symm
  have m₂ := coeff_mem_variableChange (powSaturation S 2) (W := splitCurve P Q)
    (zero_mem _) (mem_powSaturation 2 (neg_mem hM) (by simp only [splitCurve]; push_cast; ring))
    (zero_mem _) (mem_powSaturation 4 hN (by simp only [splitCurve]; push_cast; ring)) (zero_mem _)
    (mem_powSaturation 2 (neg_mem hr) (by push_cast; ring))
    (mem_powSaturation 1 ha (by push_cast; linear_combination d₁))
    (mem_powSaturation 1 (neg_mem ht) (by push_cast; ring)) e'
  have hc : Nat.Coprime 2 3 := by norm_num
  obtain ⟨W₀, hW₀⟩ := (isIntegral_of_exists_lift A
    (mem_of_mem_powSaturation hc m₂.1 m₃.1) (mem_of_mem_powSaturation hc m₂.2.1 m₃.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.1 m₃.2.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.2.1 m₃.2.2.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.2.2 m₃.2.2.2.2)).integral
  refine ⟨⟨1, -4 * r, 0, -28 * (t - 4 * r * s)⟩ * C₃, W₀, by rw [mul_smul, e₃, ← hW₀], hinj ?_⟩
  rw [← map_Δ, ← WeierstrassCurve.baseChange, ← hW₀, hW', variableChange_Δ, deuringCurve_Δ, qΔ]
  simp
end GlobalTheory
