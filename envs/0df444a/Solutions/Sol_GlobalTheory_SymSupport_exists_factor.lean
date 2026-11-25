-- Prove2me | solution 1 for GlobalTheory.SymSupport.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:15.677138+00:00
-- url     : https://prove2.me/submissions/b2a028f6-7096-4625-9a8f-9e64034b0b41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_SymSupport_exists_int_inv
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO


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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymSupport
theorem _root_.solution {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (T : n → Prop)
    (h1 : ∀ l s, T s → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ r : GL (n ⊕ Fin c) k, InR r.val ∧ ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∃ u ∈ KOne k (n ⊕ Fin c), g = r * lowU D * u := by
  classical
  let P : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s =>
    Sum.elim (fun s => T s ∧ ∃ l, r = .inr l) (fun i => lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r) s
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s
  obtain ⟨u, hu, e⟩ := exists_mul_KOne hg (M := M) (fun r s => by
    by_cases hP : P r s
    · rw [Matrix.sub_apply, Valuation.map_sub_swap, show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]
      rcases s with s | i
      · obtain ⟨hT, l, rfl⟩ := hP
        simpa using h1 l s hT
      · exact h2 r i hP
    · rw [Matrix.sub_apply, show M r s = g.val r s from if_neg hP]; simp)
  have hM : IntM M := e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))
  have m2 : ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r → M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) :=
    fun r i hl => if_pos hl
  have hd : M.toBlocks₂₂.det = 1 := by
    rw [det_of_upperTriangular, Finset.prod_eq_one]
    · intro i _
      simpa [toBlocks₂₂] using m2 (.inr i) i le_rfl
    · intro i j hij
      have := m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)
      simpa [toBlocks₂₂, (show j < i from hij).ne'] using this
  obtain ⟨V, hV, hUV⟩ := exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd
  have e2 : (g * u * (lowU (V * M.toBlocks₂₁))⁻¹).val =
      fromBlocks (M.toBlocks₁₁ - M.toBlocks₁₂ * (V * M.toBlocks₂₁)) M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [Units.val_mul, e]
    change M * fromBlocks 1 0 (-(V * M.toBlocks₂₁)) 1 = _
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply]
    simp [← Matrix.mul_assoc, hUV, sub_eq_add_neg]
  refine ⟨g * u * (lowU (V * M.toBlocks₂₁))⁻¹, ?_, V * M.toBlocks₂₁, hV.mul fun i j => hM _ _, fun l s hT => ?_,
    u⁻¹, inv_mem hu, by simp⟩
  · rw [e2]
    refine ⟨fun l s => rfl, ?_⟩
    rintro (r | r) i hl
    · exact m2 _ i hl
    · exact m2 _ i hl
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    have : M (.inr m) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr m) (.inl s) := if_pos ⟨hT, m, rfl⟩
    simp [toBlocks₂₁, this]
end GlobalTheory.SymSupport
