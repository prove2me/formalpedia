-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.range_constMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:21.155907+00:00
-- url     : https://prove2.me/submissions/f3484a01-3b51-423d-b092-d92149fa504d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
import Theorems.Thm_GlobalTheory_PrescribedRank_tup_eq
import Theorems.Thm_GlobalTheory_PrescribedRank_htupW_eq
import Theorems.Thm_GlobalTheory_PrescribedRank_mem_funMod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution (d : ℕ) :
    LinearMap.range (constMap p O Kf d) =
      Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW := by
  ext F
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_imp_iff, mem_funMod, htupW_eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ i L
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    refine ⟨fun i => c i (fun v => isEmptyElim v), ?_⟩
    funext i L
    rw [tup_eq p O Kf L (fun v => isEmptyElim v)]
    exact hc i _
end GlobalTheory.PrescribedRank
