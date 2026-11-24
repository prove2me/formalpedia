-- Prove2me | solution 1 for GlobalTheory.FlatRed.fill_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:50.070808+00:00
-- url     : https://prove2.me/submissions/18de40bc-5532-4084-b21a-0ceeefa134e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero
import Theorems.Thm_GlobalTheory_FlatRed_mem_evAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {k : Type} [Field k]
namespace GlobalTheory.FlatRed
theorem _root_.solution (ρ : ℕ) (h : ρ < c + 1) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (a : {e // e ∈ itFree n n' c ρ} → k) :
    fill (evAll n n' c ρ) (itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) t a =
      affPt (ρ + 1) (readPart ρ h t).toCols₁ (fun e => a ⟨e.1, (mem_itFree ρ e.1).2 e.2⟩) +
        colAt n' c (ρ + 1) (fun r => readPart ρ h t r (Sum.inr ())) := by
  ext r q
  simp only [fill, affPt, Matrix.of_apply, Matrix.add_apply]
  by_cases hF : Free (ρ + 1) (r, q)
  · rw [dif_pos ((mem_itFree ρ _).2 hF), dif_pos hF]
    rcases r with r | l <;> rcases q with s | i
    · exact hF.elim
    · have h1 : ρ + 1 < i.val + 1 := hF
      have h2 : i.val ≠ ρ := by omega
      simp [basePt, colAt, h2]
    · simp [basePt, colAt]
    · have h1 : l.val < i.val := hF
      have h2 : l.val ≠ i.val := by omega
      simp [basePt, colAt, h2]
  · rw [dif_neg (fun hh => hF ((mem_itFree ρ _).1 hh)), dif_neg hF]
    by_cases hR : IsRead n n' c ρ (r, q)
    · rw [if_neg (fun hh => ((mem_evAll ρ _).1 hh).2 hR)]
      rcases r with r | l <;> rcases q with s | i
      · simp [basePt, colAt, readPart]
      · have h1 : i.val = ρ := hR
        obtain rfl : i = ⟨ρ, h⟩ := Fin.ext h1
        simp [basePt, colAt, readPart]
      · exact hR.elim
      · exact hR.elim
    · rw [if_pos ((mem_evAll ρ _).2 ⟨hF, hR⟩)]
      rcases r with r | l <;> rcases q with s | i
      · exact (hR trivial).elim
      · have h1 : i.val ≠ ρ := hR
        simp [basePt, colAt, h1]
      · simp [basePt, colAt]
      · simp [basePt, colAt]
end GlobalTheory.FlatRed
