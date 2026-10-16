-- Prove2me | solution 1 for OAI.GAD.convexOn_blockLogDet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:29:07.703558+00:00
-- url     : https://prove2.me/submissions/39e813c1-d7f9-4b1f-9df9-e7f4d5bce04e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean:L161-L178
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.convexOn_blockLogDet. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Theorems.Thm_OAI_GAD_convexOn_skewLogDet
import Theorems.Thm_OAI_GAD_posDef_fromBlocks_zero

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetConvexity ----
namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity is preserved throughout a segment, including both endpoints. -/
theorem posDef_segment {D E : Matrix ι ι ℂ} (hD : D.PosDef) (hE : E.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • D + b • E).PosDef := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · have : b = 1 := by linarith
    simpa [this] using hE
  · exact (hD.smul ha).add_posSemidef (hE.posSemidef.smul hb)

end GAD

open scoped ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem skewLogDet_fromBlocks (Z : Matrix ι κ ℂ)
    {D : Matrix ι ι ℂ} {E : Matrix κ κ ℂ} (hD : D.PosDef) (hE : E.PosDef) :
    skewLogDet (Matrix.fromBlocks 0 Z (-Zᴴ) 0) (Matrix.fromBlocks D 0 0 E) =
      blockLogDet Z D E := by
  have hS : (D + Z * E⁻¹ * Zᴴ).PosDef :=
    hD.add_posSemidef (hE.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hnD : ‖D.det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit))
  have hnE : ‖E.det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hE.isUnit))
  have hnS : ‖(D + Z * E⁻¹ * Zᴴ).det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit))
  let := hE.isUnit.invertible
  simp only [skewLogDet, blockLogDet, Matrix.fromBlocks_add, add_zero, zero_add]
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    Matrix.mul_neg, sub_neg_eq_add, Matrix.det_fromBlocks_zero₁₂, norm_mul, norm_mul,
    Real.log_mul hnE hnS, Real.log_mul hnD hnE]
  ring

/-- Main log-determinant lemma, in all finite rectangular block dimensions. -/
theorem convexOn_blockLogDet (Z : Matrix ι κ ℂ) :
    ConvexOn ℝ {p : Matrix ι ι ℂ × Matrix κ κ ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p ↦ blockLogDet Z p.1 p.2) := by
  have hc := convexOn_skewLogDet (Matrix.fromBlocks 0 Z (-Zᴴ) 0) (by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg])
  refine ⟨?_, ?_⟩
  · intro D hD E hE a b ha hb hab
    exact ⟨posDef_segment hD.1 hE.1 ha hb hab, posDef_segment hD.2 hE.2 ha hb hab⟩
  intro D hD E hE a b ha hb hab
  have h := hc.2 (posDef_fromBlocks_zero hD.1 hD.2)
    (posDef_fromBlocks_zero hE.1 hE.2) ha hb hab
  change blockLogDet Z (a • D.1 + b • E.1) (a • D.2 + b • E.2) ≤ _
  simpa only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, smul_zero, add_zero,
    skewLogDet_fromBlocks Z hD.1 hD.2, skewLogDet_fromBlocks Z hE.1 hE.2,
    skewLogDet_fromBlocks Z (posDef_segment hD.1 hE.1 ha hb hab)
      (posDef_segment hD.2 hE.2 ha hb hab), Prod.fst_add, Prod.snd_add,
    Prod.fst_smul, Prod.snd_smul] using h
end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open Matrix Set


theorem solution : type_of% @_root_.OAI.GAD.convexOn_blockLogDet := @_root_.OAI.GAD.convexOn_blockLogDet
