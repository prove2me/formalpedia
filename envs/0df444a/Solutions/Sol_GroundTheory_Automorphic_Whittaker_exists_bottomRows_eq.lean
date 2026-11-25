-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_bottomRows_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:32.502874+00:00
-- url     : https://prove2.me/submissions/3843671d-7895-40e3-a0ee-7bf27db467ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {k : Fin n} {a : Fin (k.val + 1)} {s : Fin n}
    (h : bottomRows k a ≤ s) : ∃ b, bottomRows k b = s := by
  rw [Fin.le_def] at h
  simp only [bottomRows] at h
  refine ⟨⟨s.val - (n - (k.val + 1)), by have := s.isLt; have := k.isLt; omega⟩, ?_⟩
  ext
  simp only [bottomRows]
  omega
end GroundTheory.Automorphic.Whittaker
