-- Prove2me | solution 1 for GlobalTheory.SW.TwistMove.gidx_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:42.700498+00:00
-- url     : https://prove2.me/submissions/f246f202-41e6-4ebd-bd48-1d38ffd75dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
import Theorems.Thm_GlobalTheory_SW_TwistMove_mem_imL
import Theorems.Thm_GlobalTheory_SW_TwistMove_relIndex_imL
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistMove
open GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistMove
theorem _root_.solution {𝔛 : Lt E N} {t : ℕ} (ht : 0 < t) (h : ∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛)
    {b : Matrix (Fin N) (Fin N) E} (hb : b.det ≠ 0) (hX : 𝔛.toAddSubgroup ≤ imL b) :
    gidx 𝔛 * |(Algebra.norm ℚ b.det : ℝ)| ≤ 1 := by
  have hs : ((t : E) • (1 : Matrix (Fin N) (Fin N) E)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 ht.ne')
  set s := (t : E) • (1 : Matrix (Fin N) (Fin N) E) with hsd
  have h1 : imL (1 : Matrix (Fin N) (Fin N) E) = (stdL E N).toAddSubgroup := by
    ext x; simp [mem_imL]
  have hKX : imL s ≤ 𝔛.toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using h v hv
  have hKL : imL s ≤ (stdL E N).toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using nat_smul_mem _ t hv
  have e1 := relIndex_imL hs hb (hKX.trans hX)
  have e2 := relIndex_imL hs (b₂ := 1) (by simp) (h1 ▸ hKL)
  rw [h1, Matrix.det_one, map_one, abs_one, mul_one] at e2
  have hn : 0 < |Algebra.norm ℚ s.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hs)
  have n1 : (imL s).relIndex (imL b) ≠ 0 := fun h0 => by
    rw [h0] at e1; simp at e1; exact hn.ne' (by simpa using e1.symm)
  have l1 := AddSubgroup.relIndex_le_of_le_right (H := imL s) hX n1
  have m1 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_right : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  have m2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_left : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  rw [AddSubgroup.inf_relIndex_right] at m1
  rw [AddSubgroup.inf_relIndex_left] at m2
  rw [← m1] at l1
  rw [← m2] at e2
  unfold gidx
  generalize (imL s).relIndex ((stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup) = k at *
  generalize (stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup = p at *
  generalize 𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup = q at *
  have hkq : (0 : ℚ) < (k * q : ℕ) := e2 ▸ hn
  have hk : 0 < k := Nat.pos_of_mul_pos_right (by exact_mod_cast hkq)
  have hq : 0 < q := Nat.pos_of_mul_pos_left (by exact_mod_cast hkq)
  have l2 : ((k * p : ℕ) : ℚ) * |Algebra.norm ℚ b.det| ≤ (k * q : ℕ) := by
    rw [e2, ← e1]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast l1) (abs_nonneg _)
  have l3 : (p : ℚ) * |Algebra.norm ℚ b.det| ≤ q := by
    push_cast at l2
    rw [mul_assoc] at l2
    exact le_of_mul_le_mul_left l2 (by exact_mod_cast hk)
  rw [div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq)]
  exact_mod_cast l3
end GlobalTheory.SW.TwistMove
