-- Prove2me | solution 1 for GlobalTheory.AnArc.l_eq_zero_of_forall_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:20.155306+00:00
-- url     : https://prove2.me/submissions/e153002a-2130-41aa-a8cd-05fa3c5856c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_smul_mem_countable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {v : A.La} (hv : v.y = 0) (h : ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂) : v.l = 0 := by
  have hc : Countable A.abelian₂ := Finsupp.Countable.of_moduleFinite (R := ℤ)
  refine Subtype.ext (eq_zero_of_forall_smul_mem_countable (S := (A.abelian₂ : Set _)) (Set.countable_coe_iff.1 hc) fun s => ?_)
  simpa [hv] using h s
end GlobalTheory.AnArc
