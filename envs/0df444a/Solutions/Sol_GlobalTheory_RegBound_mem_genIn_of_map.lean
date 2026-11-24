-- Prove2me | solution 1 for GlobalTheory.RegBound.mem_genIn_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:20.098317+00:00
-- url     : https://prove2.me/submissions/83ef8d6b-2468-42bd-9330-e21a74e96ea0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_contr_map
import Theorems.Thm_GlobalTheory_RegBound_contr_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution {I : Ideal (MvPolynomial σ K)} {e : ℕ} {F : MvPolynomial σ K}
    (h : map (algebraMap K L) F ∈ genIn (extIdeal L I) e) : F ∈ genIn I e := by
  have h1 : genIn (extIdeal L I) e ≤ extIdeal L (genIn I e) :=
    Ideal.span_le.2 fun G hG φ => Ideal.subset_span ⟨hG.1 φ, contr_isHomogeneous φ hG.2⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  have := h1 h φ
  rwa [contr_map, hφ, one_smul] at this
end GlobalTheory.RegBound
