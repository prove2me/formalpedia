-- Prove2me | solution 1 for GlobalTheory.SymSupport.mem_R_of_inR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:13.450786+00:00
-- url     : https://prove2.me/submissions/f4250f74-0b45-4901-bb7c-eec929b475b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymSupport
theorem _root_.solution {g : GL (n ⊕ Fin c) k} (h : InR g.val) : g ∈ R k n c 1 := by
  have e : g.val = fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂ 0 g.val.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks g.val]
    congr 1
    ext l s; exact h.1 l s
  have hd : g.val.toBlocks₁₁.det ≠ 0 := by
    have := g.det_ne_zero
    rw [e, det_fromBlocks_zero₂₁] at this
    exact left_ne_zero_of_mul this
  set γ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd with hγ
  have hv : γ.val = g.val.toBlocks₁₁ := rfl
  have e2 : (embX c γ⁻¹ * g).val = fromBlocks 1 ((γ⁻¹).val * g.val.toBlocks₁₂) 0 g.val.toBlocks₂₂ := by
    change fromBlocks (γ⁻¹).val 0 0 1 * g.val = _
    rw [e, fromBlocks_multiply]
    simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, ← hv, Units.inv_mul]
    simp
  have hn : InN 1 (embX c γ⁻¹ * g) := by
    rintro (r | r) (s | s) hl <;> rw [e2]
    · simp [Matrix.one_apply]
    · have : ∀ b, g.val (.inl b) (.inr s) = 0 := fun b => by simpa using h.2 (.inl b) s hl
      simp [Matrix.mul_apply, toBlocks₁₂, this]
    · simp
    · exact h.2 (.inr r) s hl
  have : g = embX c γ * (embX c γ⁻¹ * g) := by simp
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hn))
end GlobalTheory.SymSupport
