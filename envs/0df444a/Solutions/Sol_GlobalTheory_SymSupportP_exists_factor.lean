-- Prove2me | solution 1 for GlobalTheory.SymSupportP.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:00.712533+00:00
-- url     : https://prove2.me/submissions/4eb1738f-1818-4138-8d4b-6a0faaeec34b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruencStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPattern
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_SymSupport_exists_int_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport
noncomputable section
open GlobalTheory GlobalTheory.SymSupportP
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymSupportP
theorem _root_.solution {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (p : ℕ) (T : n → Prop)
    (h1 : ∀ l s, T s → p ≤ l.val + 1 → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ u ∈ KOne k (n ⊕ Fin c), ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∀ a b, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
        (g * u * lowU D).val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b := by
  classical
  let P : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s =>
    Sum.elim (fun s => T s ∧ ∃ l : Fin c, r = .inr l ∧ p ≤ l.val + 1)
      (fun i => lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r) s
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
    Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s
  obtain ⟨u, hu, e⟩ := exists_mul_KOne hg (M := M) (fun r s => by
    by_cases hP : P r s
    · rw [Matrix.sub_apply, Valuation.map_sub_swap,
        show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]
      rcases s with s | i
      · obtain ⟨hT, l, rfl, hl⟩ := hP
        simpa using h1 l s hT hl
      · exact h2 r i hP
    · rw [Matrix.sub_apply, show M r s = g.val r s from if_neg hP]; simp)
  have hM : IntM M := e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))
  have m2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) :=
    fun r i hl => if_pos hl
  have m1 : ∀ (l : Fin c) s, T s → p ≤ l.val + 1 → M (.inr l) (.inl s) = 0 := fun l s hT hl => by
    have : M (.inr l) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr l) (.inl s) :=
      if_pos ⟨hT, l, rfl, hl⟩
    simpa using this
  have hd : M.toBlocks₂₂.det = 1 := by
    rw [det_of_upperTriangular, Finset.prod_eq_one]
    · intro i _
      simpa [toBlocks₂₂] using m2 (.inr i) i le_rfl
    · intro i j hij
      have := m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)
      simpa [toBlocks₂₂, (show j < i from hij).ne'] using this
  obtain ⟨V, hV, hUV⟩ := exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd
  let D : Matrix (Fin c) n k := Matrix.of fun l s => if T s then 0 else -(V * M.toBlocks₂₁) l s
  have hVM : IntM (V * M.toBlocks₂₁) := hV.mul fun i j => hM _ _
  refine ⟨u, hu, D, fun i j => ?_, fun l s hT => if_pos hT, ?_⟩
  · by_cases hT : T j
    · simp [D, hT, zero_mem]
    · simpa [D, hT] using neg_mem (hVM i j)
  · intro a b hl hab
    rw [Units.val_mul, e]
    change (M * (fromBlocks 1 0 D 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) a b = _
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply]
    rcases b with x | i
    · rcases a with y | l
      · simp at hab
      · have hl' : p ≤ l.val + 1 := by simpa [lev] using hl
        simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₁, Matrix.add_apply]
        by_cases hT : T x
        · have : (M.toBlocks₂₂ * D) l x = 0 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_eq_zero fun m _ => by simp [D, hT]
          rw [this, add_zero]
          simpa [toBlocks₂₁] using m1 l x hT hl'
        · have : (M.toBlocks₂₂ * D) l x = (M.toBlocks₂₂ * (-(V * M.toBlocks₂₁))) l x := by
            simp only [Matrix.mul_apply]
            exact Finset.sum_congr rfl fun m _ => by simp [D, hT]
          rw [this, Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
          simp
    · rcases a with y | l
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₁₂]
        simpa [toBlocks₁₂] using m2 (.inl y) i hl
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₂]
        simpa [toBlocks₂₂] using m2 (.inr l) i hl
end GlobalTheory.SymSupportP
