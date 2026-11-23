-- Prove2me | solution 1 for GlobalTheory.ofList_map_C_append_map_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:50.215809+00:00
-- url     : https://prove2.me/submissions/4352cfd2-c132-40ee-ab79-d089a4eaef53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution (rs : List R) (l : List σ) :
    Ideal.ofList (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) =
      (Ideal.ofList rs).map C ⊔ Ideal.span (X '' {x | x ∈ l}) := by
  rw [Ideal.ofList_append, Ideal.map_ofList]
  congr 1
  unfold Ideal.ofList
  congr 1
  ext p
  simp
end GlobalTheory
