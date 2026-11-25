-- Prove2me | solution 1 for GlobalTheory.ThetaJet.spans_mod_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:15:22.57299+00:00
-- url     : https://prove2.me/submissions/07335438-0942-4541-b3d5-f753c7351f32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace GlobalTheory.ThetaJet
theorem _root_.solution (m : Ideal R) (J A B : Submodule k R) (D : ℕ)
    (hJ : ∀ x, ∃ s ∈ J, x - s ∈ m ^ 2) (hA : ∀ x, ∃ a ∈ A, x - a ∈ m ^ (D + 1))
    (hB : ∀ a ∈ A, ∀ s ∈ J, a * s ∈ B) (x : R) : ∃ b ∈ B, x - b ∈ m ^ (D + 2) := by
  set I : Ideal R := Ideal.span {s | s ∈ J ∧ s ∈ m} with hI
  have h2 : m ^ 2 ≤ m := Ideal.pow_le_self two_ne_zero
  have hm1 : m ≤ I ⊔ m ^ 2 := by
    intro y hy
    obtain ⟨s, hs, hs'⟩ := hJ y
    have : s ∈ m := by simpa using m.sub_mem hy (h2 hs')
    have e : y = s + (y - s) := by ring
    rw [e]
    exact Submodule.add_mem_sup (Ideal.subset_span ⟨hs, this⟩) hs'
  have hm : ∀ n, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc m ^ (n + 1) = m * m ^ n := pow_succ' _ _
        _ ≤ (I ⊔ m ^ 2) * m ^ n := Ideal.mul_mono_left hm1
        _ = I * m ^ n ⊔ m ^ (n + 1 + 1) := by
          rw [Ideal.sup_mul, ← pow_add]; congr 2; omega
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le_sup_right Ideal.mul_le_left _
  have hIB : ∀ z ∈ I, ∀ y, ∃ b ∈ B, y * z - b ∈ m ^ (D + 2) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem s hs =>
      intro y
      obtain ⟨a, ha, ha'⟩ := hA y
      refine ⟨a * s, hB a ha s hs.1, ?_⟩
      rw [← sub_mul, pow_succ]
      exact Ideal.mul_mem_mul ha' hs.2
    | zero => intro y; exact ⟨0, B.zero_mem, by simp⟩
    | add z w _ _ hz hw =>
      intro y
      obtain ⟨b, hb, hb'⟩ := hz y
      obtain ⟨c, hc, hc'⟩ := hw y
      refine ⟨b + c, B.add_mem hb hc, ?_⟩
      have e : y * (z + w) - (b + c) = (y * z - b) + (y * w - c) := by ring
      rw [e]
      exact Ideal.add_mem _ hb' hc'
    | smul c z _ hz =>
      intro y
      rw [smul_eq_mul, ← mul_assoc]
      exact hz _
  obtain ⟨s, hs, hs'⟩ := hJ 1
  obtain ⟨a, ha, ha'⟩ := hA x
  have h1 : x - a * s ∈ m := by
    have e : x - a * s = (x - a) + a * (1 - s) := by ring
    rw [e]
    exact m.add_mem (Ideal.pow_le_self (Nat.succ_ne_zero _) ha') (m.mul_mem_left _ (h2 hs'))
  obtain ⟨z, hz, w, hw, e⟩ := Submodule.mem_sup.1 (hm (D + 1) h1)
  obtain ⟨b, hb, hb'⟩ := hIB z hz 1
  refine ⟨a * s + b, B.add_mem (hB a ha s hs) hb, ?_⟩
  have e' : x - (a * s + b) = (1 * z - b) + w := by linear_combination -e
  rw [e']
  exact Ideal.add_mem _ hb' hw
end GlobalTheory.ThetaJet
