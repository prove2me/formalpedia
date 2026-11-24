-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.mem_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:38.173803+00:00
-- url     : https://prove2.me/submissions/b0b4fc73-d28c-450c-ac67-5666b34020fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_RootEx_Unram_exists_embX_mul
import Theorems.Thm_GlobalTheory_RootEx_Unram_tri_mul_affPt
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_blockTriangular_inv
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_diagPart_mul_diagPart
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_mul_diagPart_apply
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
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
omit [Fintype n']
namespace GlobalTheory.RootEx.Unram
theorem _root_.solution {p : ℕ} (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k)
    (e) (hA : IntM ((h⁻¹).val * affPt (c := c) p x₀ e))
    (hB : ∀ D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, (∀ r s, ¬ Free p (r, s) → D r s = 0) →
      IntM ((h⁻¹).val * D) → ch D ∈ 𝒪[k]) :
    ∃ r ∈ R k n c p, ∃ w ∈ KO k (n ⊕ Fin c), h = r * w := by
  obtain ⟨b, hb, w, hw, rfl⟩ := iwasawa_blockTriangular k _ (lev p) h
  have hi := BlockLevi.blockTriangular_inv _ b hb
  obtain ⟨w1, w2⟩ := mem_KO.1 hw
  have hA' : IntM ((b⁻¹).val * affPt (c := c) p x₀ e) := by
    have : (b⁻¹).val = w.val * ((b * w)⁻¹).val := by rw [← Units.val_mul]; simp
    rw [this, Matrix.mul_assoc]
    exact w1.mul hA
  let m : GL (n ⊕ Fin c) k := ⟨BlockLevi.diagPart (lev p) b.val, BlockLevi.diagPart (lev p) (b⁻¹).val,
    BlockLevi.diagPart_mul_diagPart _ hb hi b.mul_inv, BlockLevi.diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  have hu : b * m⁻¹ ∈ N k n c p := by
    refine Subgroup.subset_closure fun r s h => ?_
    have : (b * m⁻¹).val = b.val * BlockLevi.diagPart (lev p) (b⁻¹).val := rfl
    rw [this, BlockLevi.mul_diagPart_apply _ hb hi h, b.mul_inv]
  obtain ⟨g, w', hw', hm⟩ := exists_embX_mul m (fun i r => by
    change (if lev p (Sum.inr i : n ⊕ Fin c) = lev p r then b.val (Sum.inr i) r else 0) ∈ _
    split_ifs with hr
    · have hr' : lev p r = i.val + 1 := hr.symm
      let E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := Matrix.single r (Sum.inr i.succ) 1
      have hE : IntM E := fun a a' => by
        simp only [E, Matrix.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _]
      have hbE : ∀ a a', (b.val * E) a a' = if a' = Sum.inr i.succ then b.val a r else 0 := by
        intro a a'
        split_ifs with h
        · subst h; simp [E]
        · simp [E, Matrix.mul_single_apply_of_ne, h]
      have := hB (b.val * E) (fun a a' ha => ?_) ?_
      · simpa [ch, hbE] using this
      · rw [hbE]
        split_ifs with h
        · subst h
          apply hb
          rw [hr']
          rcases a with a | a <;> simp [Free, lev] at ha ⊢ <;> omega
        · rfl
      · rw [← Matrix.mul_assoc, ← Units.val_mul]
        simp only [_root_.mul_inv_rev, inv_mul_cancel_right]
        exact w2.mul hE
    · exact zero_mem _) (fun i r => by
    change (if lev p r = lev p (Sum.inr i : n ⊕ Fin c) then (b⁻¹).val r (Sum.inr i) else 0) ∈ _
    split_ifs with hr
    · rw [← tri_mul_affPt hi x₀ e i r hr.ge]
      exact hA' _ _
    · exact zero_mem _)
  refine ⟨b * m⁻¹ * embX c g, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩),
    w' * w, mul_mem hw' hw, ?_⟩
  rw [mul_assoc, ← mul_assoc (embX c g), ← hm]; group
end GlobalTheory.RootEx.Unram
