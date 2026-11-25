-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.mem_symGrp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:27.578194+00:00
-- url     : https://prove2.me/submissions/d3b6afa4-043f-48e1-80f3-fa082d280a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable (F : Type*) [Field F] [Finite F] (κ ρ : ℕ)
variable {F κ ρ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
theorem _root_.solution {g : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F} :
    g ∈ symGrp F κ ρ ↔ ∃ n ∈ radN F κ ρ, ∃ u ∈ epsU F κ ρ, g = n * u := by
  constructor
  · intro hg
    have hg' := mem_patGrp.1 hg
    have ht : g.val.toBlocks₁₁.BlockTriangular id := fun i j hij => by
      have : ¬ i < j := not_lt.2 (le_of_lt hij)
      have hne : i ≠ j := ne_of_gt hij
      simpa [toBlocks₁₁, Matrix.one_apply, hne] using hg' (.inl i) (.inl j) (by simpa [SymFree, EpsLt, symmetricBlockIndex] using hij.le)
    have hd : (fromBlocks g.val.toBlocks₁₁ 0 0 1 : Matrix (Fin κ ⊕ Fin (2 * ρ + 1)) _ F).det ≠ 0 := by
      rw [det_fromBlocks_zero₂₁, det_of_upperTriangular ht, det_one, mul_one]
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      have := hg' (.inl i) (.inl i) (symFree_irrefl κ ρ _)
      simp only [toBlocks₁₁, of_apply, this]; simp
    let u : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd
    have uv : u.val = fromBlocks g.val.toBlocks₁₁ 0 0 1 := rfl
    have hu : u ∈ epsU F κ ρ := mem_patGrp.2 <| by
      rintro (i | i) (j | j) h
      · rw [uv]; exact hg' _ _ (by simpa [SymFree, symmetricBlockIndex] using h)
      · simp [uv]
      · simp [uv]
      · simp [uv, Matrix.one_apply]
    have hu' : u⁻¹ ∈ symGrp F κ ρ :=
      mem_patGrp.2 fun r s h => mem_patGrp.1 (inv_mem hu) r s fun h' => h (Or.inr h')
    refine ⟨g * u⁻¹, mem_patGrp.2 fun r s h => ?_, u, hu, by simp⟩
    by_cases h2 : EpsLt κ ρ r s
    · rcases r with i | i <;> rcases s with j | j <;> try exact h2.elim
      rw [← u.mul_inv, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl ?_
      rintro (l | l) -
      · rfl
      · rw [mem_patGrp.1 (inv_mem hu) (.inr l) (.inl j) (by simp [EpsLt])]; simp
    · exact mem_patGrp.1 (mul_mem hg hu') r s fun h' => h'.elim h h2
  · rintro ⟨n, hn, u, hu, rfl⟩
    exact mul_mem (mem_patGrp.2 fun r s h => mem_patGrp.1 hn r s fun h' => h (Or.inl h'))
      (mem_patGrp.2 fun r s h => mem_patGrp.1 hu r s fun h' => h (Or.inr h'))
end GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
