-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.htupW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:26.054228+00:00
-- url     : https://prove2.me/submissions/d5c47a34-e44e-4d1e-88b0-a3883c8ff340

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution (L : (noPlaces p O Kf).Tup) :
    (noPlaces p O Kf).HtupW L = Submodule.span O {1} := by
  unfold Places.HtupW Places.tenV
  congr 1
  ext X
  constructor
  · rintro ⟨F, -, rfl⟩
    rw [Fintype.prod_empty]
    rfl
  · rintro rfl
    exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, by rw [Fintype.prod_empty]⟩
end GlobalTheory.PrescribedRank
