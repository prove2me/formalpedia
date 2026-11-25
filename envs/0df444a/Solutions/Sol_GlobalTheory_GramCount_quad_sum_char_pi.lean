-- Prove2me | solution 1 for GlobalTheory.GramCount.quad_sum_char_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:32:09.003899+00:00
-- url     : https://prove2.me/submissions/cc4c7c48-7927-4cc0-920f-9ff7f11731d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B] [Fintype B]
namespace GlobalTheory.GramCount
theorem _root_.solution (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {m : ℕ} (w : Fin m → B) :
    ∑ s : Fin m → B, χ (∑ i, s i * w i) =
      if w = 0 then (Fintype.card B : ℂ) ^ m else 0 := by
  have h1 : ∀ s : Fin m → B, χ (∑ i, s i * w i) = ∏ i, χ (s i * w i) := by
    intro s
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  simp only [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset B))
    (fun i b => χ (b * w i))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp only [AddChar.sum_mulShift _ hχ]
  split_ifs with hw
  · simp [hw]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [show w i ≠ 0 from hi])
end GlobalTheory.GramCount
