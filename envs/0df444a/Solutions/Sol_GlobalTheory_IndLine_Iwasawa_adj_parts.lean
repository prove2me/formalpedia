-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.adj_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:43.845727+00:00
-- url     : https://prove2.me/submissions/94fe5bc8-c381-44d1-b098-b41476099f97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Adj_mul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Adj_add
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Adj_sub
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Adj_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {m : Type} [Fintype m] [DecidableEq m]
variable {N A B A' B' : Matrix m m ℂ}
variable {p r q θ Z : Matrix m m ℂ}
namespace GlobalTheory.IndLine.Iwasawa
theorem _root_.solution (h : Grading p r q θ) (hp : Adj N p q) (hq : Adj N q p) (hθ : Adj N θ θ) (hZ : Adj N Z (-Z)) :
    Adj N (up p r q (Z - θ * Z * θ)) (-up p r q (Z - θ * Z * θ)) ∧ Adj N (mid p r q Z) (-mid p r q Z) ∧
      Adj N (low p r q Z + θ * low p r q Z * θ) (-(low p r q Z + θ * low p r q Z * θ)) := by
  have hr : Adj N r r := by
    have := (Adj.one.sub hp).sub hq
    rwa [sub_sub 1 q p, add_comm q p, ← sub_sub, ← h.sum] at this
  have hl : Adj N (low p r q Z) (-low p r q Z) := by
    have := (((hr.mul hZ).mul hp).add ((hq.mul hZ).mul hp)).add ((hq.mul hZ).mul hr)
    convert this using 1 <;> (simp only [low]; try noncomm_ring)
  refine ⟨?_, ?_, ?_⟩
  · have hZ' := hZ.sub ((hθ.mul hZ).mul hθ)
    have := (((hp.mul hZ').mul hr).add ((hp.mul hZ').mul hq)).add ((hr.mul hZ').mul hq)
    convert this using 1 <;> (simp only [up]; try noncomm_ring)
  · have := (((hp.mul hZ).mul hp).add ((hr.mul hZ).mul hr)).add ((hq.mul hZ).mul hq)
    convert this using 1 <;> (simp only [mid]; try noncomm_ring)
  · have := hl.add ((hθ.mul hl).mul hθ)
    convert this using 1
    noncomm_ring
end GlobalTheory.IndLine.Iwasawa
