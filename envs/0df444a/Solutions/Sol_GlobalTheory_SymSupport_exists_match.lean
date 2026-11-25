-- Prove2me | solution 1 for GlobalTheory.SymSupport.exists_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:24.212282+00:00
-- url     : https://prove2.me/submissions/661f7b02-af9b-4ec2-9db7-6f5170bfc3c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_embTop_val
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_maxM_zero
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_reGL_val


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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymSupport
theorem _root_.solution {a t Y : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] [Fintype Y] [DecidableEq Y]
    (Q : TypeDatum k a) (μ : kˣ →* ℂˣ) (e : a ⊕ t ≃ Y) {G : GL Y k} (hG : G ∈ KO k Y) (Z : Matrix Y a k)
    (h : Q.Phi t μ (((G⁻¹).val * Z).submatrix e id) ≠ 0) :
    ∃ κ : GL Y k, (reGL e).symm κ ∈ Q.stepJ t ∧ ∀ r b, valuation k ((G * κ).val r (e (.inl b)) - Z r b) < 1 := by
  obtain ⟨⟨g, hg, eg⟩, hb⟩ := (Q.Phi_ne_zero_iff μ).1 h
  refine ⟨reGL e (embTop t g), ?_, ?_⟩
  · rw [MulEquiv.symm_apply_apply]
    refine Q.mem_stepJ_iff.2 ⟨?_, ⟨g, hg, by simp [embTop_val]⟩, by simpa [embTop_val] using maxM_zero⟩
    obtain ⟨g1, g2⟩ := mem_KO.1 (Q.le_KO hg)
    refine mem_KO.2 ⟨?_, ?_⟩
    · rw [embTop_val]; exact intM_fromBlocks.2 ⟨g1, intM_zero, intM_zero, intM_one⟩
    · rw [← map_inv, embTop_val]; exact intM_fromBlocks.2 ⟨g2, intM_zero, intM_zero, intM_one⟩
  · have m : MaxM ((reGL e (embTop t g)).val.submatrix id (fun b => e (.inl b)) - (G⁻¹).val * Z) := by
      intro r b
      obtain ⟨r, rfl⟩ := e.surjective r
      rcases r with r | r
      · have : g.val r b = ((G⁻¹).val * Z) (e (.inl r)) b := by rw [eg]; rfl
        simp only [Matrix.sub_apply, ← this]
        simp [reGL_val, embTop_val]
      · have : valuation k (((G⁻¹).val * Z) (e (.inr r)) b) < 1 := hb r b
        rw [Matrix.sub_apply, Valuation.map_sub_swap]
        simpa [reGL_val, embTop_val] using this
    have := (intM_of_mem_KO hG).mul_maxM m
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at this
    exact this
end GlobalTheory.SymSupport
