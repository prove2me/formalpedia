-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.exists_embX_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:13.069298+00:00
-- url     : https://prove2.me/submissions/846c7244-0f2e-41bd-a583-73ebcbb77999

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_blockTriangular_inv
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.Unram
theorem _root_.solution (m : GL (n ⊕ Fin c) k) (h1 : ∀ i r, m.val (Sum.inr i) r ∈ 𝒪[k])
    (h2 : ∀ i r, (m⁻¹).val r (Sum.inr i) ∈ 𝒪[k]) :
    ∃ g : GL n k, ∃ w ∈ KO k (n ⊕ Fin c), m = embX c g * w := by
  obtain ⟨b, hb, w, hw, rfl⟩ := iwasawa_blockTriangular k _ (Sum.elim (fun _ => 0) (fun _ => 1)) m
  have hi := BlockLevi.blockTriangular_inv _ b hb
  obtain ⟨w1, w2⟩ := mem_KO.1 hw
  have b1 : ∀ i r, b.val (Sum.inr i) r ∈ 𝒪[k] := fun i r => by
    have : b.val = (b * w).val * (w⁻¹).val := by rw [← Units.val_mul]; simp
    rw [this, Matrix.mul_apply]
    exact sum_mem fun s _ => mul_mem (h1 i s) (w2 s r)
  have b2 : ∀ i r, (b⁻¹).val r (Sum.inr i) ∈ 𝒪[k] := fun i r => by
    have : (b⁻¹).val = w.val * ((b * w)⁻¹).val := by rw [← Units.val_mul]; simp
    rw [this, Matrix.mul_apply]
    exact sum_mem fun s _ => mul_mem (w1 r s) (h2 i s)
  have z1 : b.val.toBlocks₂₁ = 0 := by
    ext i j; exact hb (show Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inl j : n ⊕ Fin c) <
      Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inr i : n ⊕ Fin c) by simp)
  have z2 : (b⁻¹).val.toBlocks₂₁ = 0 := by
    ext i j; exact hi (show Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inl j : n ⊕ Fin c) <
      Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inr i : n ⊕ Fin c) by simp)
  have e1 := b.mul_inv
  have e2 := b.inv_mul
  have hD : IntM b.val.toBlocks₂₂ := fun i j => b1 i _
  have hB' : IntM (b⁻¹).val.toBlocks₁₂ := fun i j => b2 j _
  have hD' : IntM (b⁻¹).val.toBlocks₂₂ := fun i j => b2 j _
  have f1 := fromBlocks_toBlocks b.val
  have f2 := fromBlocks_toBlocks (b⁻¹).val
  rw [z1] at f1
  rw [z2] at f2
  generalize b.val.toBlocks₁₁ = A, b.val.toBlocks₁₂ = B, b.val.toBlocks₂₂ = D at *
  generalize (b⁻¹).val.toBlocks₁₁ = A', (b⁻¹).val.toBlocks₁₂ = B', (b⁻¹).val.toBlocks₂₂ = D' at *
  rw [← f1, ← f2, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at e1 e2
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1 e2
  let g : GL n k := ⟨A, A', e1.1, e2.1⟩
  refine ⟨g, (embX c g)⁻¹ * b * w, mul_mem (mem_KO.2 ⟨?_, ?_⟩) hw, by group⟩
  · have : ((embX c g)⁻¹ * b).val = fromBlocks 1 (-(B' * D)) 0 D := by
      rw [← map_inv, Units.val_mul, ← f1]
      change fromBlocks A' 0 0 1 * _ = _
      simp [fromBlocks_multiply, e2.1, eq_neg_of_add_eq_zero_left e2.2.1]
    rw [this]
    rintro (r | r) (s | s)
    exacts [intM_one r s, (hB'.mul hD).neg r s, zero_mem _, hD r s]
  · have : (((embX c g)⁻¹ * b)⁻¹).val = fromBlocks 1 B' 0 D' := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← f2]
      change _ * fromBlocks A 0 0 1 = _
      simp [fromBlocks_multiply, e2.1]
    rw [this]
    rintro (r | r) (s | s)
    exacts [intM_one r s, hB' r s, zero_mem _, hD' r s]
end GlobalTheory.RootEx.Unram
