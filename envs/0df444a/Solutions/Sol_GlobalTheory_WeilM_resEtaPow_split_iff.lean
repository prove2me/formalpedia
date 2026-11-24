-- Prove2me | solution 1 for GlobalTheory.WeilM.resEtaPow_split_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:44.60322+00:00
-- url     : https://prove2.me/submissions/d2fc61eb-b255-4610-81ea-ea8682a0fcd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Theorems.Thm_GlobalTheory_WeilM_norm_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]
variable {R : Type} [CommRing R]
namespace GlobalTheory.WeilM
theorem _root_.solution (χ : (R × R)ˣ →* Circle) (n : ℕ) :
    ResEtaPow (⊥ : Subgroup Rˣ) χ n ↔ ∀ a : Rˣ, χ (Units.map (algebraMap R (R × R) : R →* R × R) a) = 1 := by
  refine forall_congr' fun a => ?_
  have : a ∈ (⊥ : Subgroup Rˣ) ⊔ (Units.map (Algebra.norm R : R × R →* R)).range :=
    Subgroup.mem_sup_right ⟨Units.map (MonoidHom.inl R R) a, Units.ext ((norm_pair _).trans (mul_one _))⟩
  rw [if_pos this, Circle.coe_eq_one]
end GlobalTheory.WeilM
