-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.exists_deuringCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:06.025017+00:00
-- url     : https://prove2.me/submissions/63994ad4-880c-46e7-a324-f6385fe2ca36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_HasRationalTorsion_variableChange
import Theorems.Thm_P2M_GlobalTheory_deuringCurve___056d131758c7
import Theorems.Thm_GlobalTheory_deuringCurve_map
import Theorems.Thm_GlobalTheory_exists_root_cubic
import Theorems.Thm_GlobalTheory_exists_flex_slope
import Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_point_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L 3) :
    ∃ (C : VariableChange K) (a b d : K), C.u = 1 ∧ C • W = deuringCurve a b ∧
      d ^ 3 = a ^ 3 - 27 * b := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.baseChange L).Ψ₃
    (degree_ne_of_natDegree_ne ((W.baseChange L).natDegree_Ψ₃_pos three_ne_zero).ne')
  obtain ⟨x₀, y₀, -, h₀, h₃⟩ := h.exists_point_of_root hx
  obtain ⟨l, h₁, h₂⟩ := exists_flex_slope h₀ h₃
  have hE := (equation_iff' ..).mp h₀.1
  obtain ⟨a, b, e⟩ : ∃ a b : K,
      (⟨1, x₀, l, y₀⟩ : VariableChange K) • W = deuringCurve a b := by
    refine ⟨W.a₁ + 2 * l, 2 * y₀ + W.a₁ * x₀ + W.a₃, ?_⟩
    simp only [variableChange_def, deuringCurve, inv_one, Units.val_one]
    ext <;> dsimp only
    · ring
    · linear_combination -h₂
    · ring
    · linear_combination -h₁
    · linear_combination -hE
  have h' := h.variableChange ⟨1, x₀, l, y₀⟩
  have hell : ((⟨1, x₀, l, y₀⟩ : VariableChange K) • W).IsElliptic := inferInstance
  rw [e] at h' hell
  have hb : b ≠ 0 := by
    intro hb
    have := (deuringCurve a b).isUnit_Δ.ne_zero
    rw [deuringCurve_Δ, hb] at this
    simp at this
  obtain ⟨z, hz⟩ := exists_root_cubic (three_ne_zero : (3 : L) ≠ 0) (algebraMap K L a ^ 2)
    (3 * algebraMap K L a * algebraMap K L b) (3 * algebraMap K L b ^ 2)
  obtain ⟨z₀, -, rfl, -, -⟩ := h'.exists_point_of_root (x := z) (by
    simp only [WeierstrassCurve.baseChange, deuringCurve_map]
    simp only [deuringCurve, Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X,
      eval_ofNat]
    linear_combination z * hz)
  have hz₀ : 3 * z₀ ^ 3 + a ^ 2 * z₀ ^ 2 + 3 * a * b * z₀ + 3 * b ^ 2 = 0 := by
    apply (algebraMap K L).injective
    simpa [map_ofNat] using hz
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    simp [hb] at hz₀
  refine ⟨_, a, b, a + 3 * b / z₀, rfl, e, ?_⟩
  field_simp
  linear_combination 9 * b * hz₀
end HasRationalTorsion
end GlobalTheory
