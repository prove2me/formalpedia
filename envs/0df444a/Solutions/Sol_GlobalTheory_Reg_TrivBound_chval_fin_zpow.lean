-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.chval_fin_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:54.310182+00:00
-- url     : https://prove2.me/submissions/c9bd7a87-ab46-4941-a715-b3fbf5957dab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_fin_pow
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_fin_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.TrivBound
theorem _root_.solution (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal))
    (Z : ℤ) : ChV φ e (f ^ Z) (((Z : ℝ) * u : ℝ) : EReal) := by
  rcases Int.eq_nat_or_neg Z with ⟨N, rfl | rfl⟩
  · rw [zpow_natCast]
    exact_mod_cast chval_fin_pow φ e h N
  · rw [zpow_neg, zpow_natCast]
    have := chval_fin_inv φ e (chval_fin_pow φ e h N)
    convert this using 2
    push_cast
    ring
end GlobalTheory.Reg.TrivBound
