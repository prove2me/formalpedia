-- Prove2me | solution 1 for GlobalTheory.SW.twist_move_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:13.402487+00:00
-- url     : https://prove2.me/submissions/fce4716d-7345-4a98-a7e2-8ad9a4b2dc9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
import Theorems.Thm_GlobalTheory_SW_TwistMove_mem_imL
import Theorems.Thm_GlobalTheory_SW_TwistMove_gidx_mul_le
import Theorems.Thm_GlobalTheory_SW_TwistMove_exists_frame
import Theorems.Thm_GlobalTheory_SW_TwistMove_admissibleLatticeFamily_moved_by_rational_matrix
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_TwistAdm_nat_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory.SW.TwistMove
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ N
  obtain ⟨c, hc, H⟩ := exists_frame E N
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine ⟨c, |(Algebra.norm ℚ ((c : E) ^ N) : ℝ)|, hc, fun n M R φ 𝔛 hφ _ hA => ?_⟩
  obtain ⟨t, ht, -, h1, h2⟩ := id hA
  obtain ⟨b, hb, hb1, hb2⟩ := H 𝔛 t ht h1 h2
  have hu : IsUnit b.det := hb.isUnit
  have ha : b⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det b hu).ne_zero
  have k2 : ∀ ξ ∈ 𝔛, (c : E) • (b⁻¹ *ᵥ ξ) ∈ stdL E N := fun ξ hξ => hb2 _ (by
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec])
  refine ⟨b⁻¹, ha, ?_, admissibleLatticeFamily_moved_by_rational_matrix hφ hA b⁻¹ hc (fun v hv => ⟨b *ᵥ ((c : E) • v),
    hb1 _ (TwistAdm.nat_smul_mem _ c hv), by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]⟩) k2⟩
  have hd : ((c : E)⁻¹ • b).det * ((c : E) ^ N * b⁻¹.det) = 1 := by
    rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, inv_pow]
    field_simp
  have hle := gidx_mul_le ht h2 (left_ne_zero_of_mul_eq_one hd) (fun ξ hξ => mem_imL.2
    ⟨_, k2 ξ hξ, by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩)
  have hn := congrArg (fun z : E => |((Algebra.norm ℚ z : ℚ) : ℝ)|) hd
  simp only [map_mul, Rat.cast_mul, abs_mul, map_one, Rat.cast_one, abs_one] at hn
  have := mul_le_mul_of_nonneg_right hle (mul_nonneg
    (abs_nonneg (Algebra.norm ℚ ((c : E) ^ N) : ℝ)) (abs_nonneg (Algebra.norm ℚ b⁻¹.det : ℝ)))
  rwa [mul_assoc, hn, mul_one, one_mul] at this
end GlobalTheory.SW
