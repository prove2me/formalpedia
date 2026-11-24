-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.exists_sum_of_mem_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:08.9395+00:00
-- url     : https://prove2.me/submissions/23da93e6-4b76-4a02-8954-07947663124d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module K A]
    [Module K B] (f : Fin g → A →ₗ[K] B) (t : Fin g) (y : B)
    (hy : y ∈ ⨆ (i : Fin g) (_ : i < t), LinearMap.range (f i)) :
    ∃ z : Fin g → A, y = ∑ i : Fin g, if i.val < t.val then f i (z i) else 0 := by
  refine Submodule.iSup_induction (fun i => ⨆ (_ : i < t), LinearMap.range (f i))
    (motive := fun y => ∃ z : Fin g → A, y = ∑ i : Fin g, if i.val < t.val then f i (z i) else 0)
    hy ?_ ?_ ?_
  · intro i y hy
    by_cases hi : i < t
    · rw [iSup_pos hi] at hy
      obtain ⟨a, rfl⟩ := hy
      refine ⟨Pi.single i a, ?_⟩
      rw [Finset.sum_eq_single i]
      · rw [if_pos (Fin.lt_def.mp hi), Pi.single_eq_same]
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk, map_zero, ite_self]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [iSup_neg hi, Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · exact ⟨0, by simp⟩
  · rintro y₁ y₂ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩
    refine ⟨z₁ + z₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
end GlobalTheory.KeyKa.KosGr
