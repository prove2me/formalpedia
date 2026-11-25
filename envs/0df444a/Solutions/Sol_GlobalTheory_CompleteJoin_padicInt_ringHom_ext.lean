-- Prove2me | solution 1 for GlobalTheory.CompleteJoin.padicInt_ringHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:43.597841+00:00
-- url     : https://prove2.me/submissions/d98354c1-0f5f-4031-a5ed-a3ccfb2615ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompleteNormalSubringJoin
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.CompleteJoin
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CompleteJoin
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp : ‖(p : C)‖ < 1) (a b : ℤ_[p] →+* C)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1) : a = b := by
  refine RingHom.ext fun x => ?_
  have key : ∀ k : ℕ, ‖a x - b x‖ ≤ ‖(p : C)‖ ^ k := fun k => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = y * (p : ℤ_[p]) ^ k + (x.appr k : ℤ_[p]) := by rw [hy]; ring
    have : a x - b x = (a y - b y) * (p : C) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y) (by simpa using hb y))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
end GlobalTheory.CompleteJoin
