-- Prove2me | solution 1 for GlobalTheory.HL.DivisibleGauss.sq_norm_sum_mul_relIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:51.471628+00:00
-- url     : https://prove2.me/submissions/0f99fb8d-23a1-4bb4-8e53-4698f720f053

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
import Theorems.Thm_GlobalTheory_HL_GaussSum_sq_norm_sum_reps_mul_index_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DivisibleGauss
namespace GlobalTheory.HL.DivisibleGauss
theorem _root_.solution {V : Type*} [AddCommGroup V] (M P Q : AddSubgroup V)
    (hPQ : P ≤ Q) (R : Finset V) (hRM : ∀ u ∈ R, u ∈ M)
    (hR : ∀ u ∈ M, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : V → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u ∈ M, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h ∈ M, h ∉ Q → ∃ v ∈ M, ∃ c : ℂ, c ≠ 1 ∧
      ∀ u ∈ M, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.relIndex M : ℝ) ≤ (R.card : ℝ) ^ 2 := by
  have hinj : Function.Injective (Subtype.val : M → V) := Subtype.val_injective
  have hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : M → V) := fun u hu => ⟨⟨u, hRM u hu⟩, rfl⟩
  have key := GaussSum.sq_norm_sum_reps_mul_index_le (P.addSubgroupOf M) (Q.addSubgroupOf M)
    (AddSubgroup.comap_mono hPQ) (R.preimage Subtype.val hinj.injOn) ?_ (fun m => f m)
    (fun m => hf m) (fun u p hp => hP u u.2 p hp) ?_
  · rwa [Finset.sum_preimage Subtype.val R hinj.injOn f
      (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage,
      Finset.filter_true_of_mem hrange] at key
  · intro u
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR u u.2
    refine ⟨⟨w, hRM w hw⟩, ⟨Finset.mem_preimage.2 hw, hw'⟩, fun y hy => hinj ?_⟩
    exact huniq _ ⟨Finset.mem_preimage.1 hy.1, hy.2⟩
  · intro h hh
    obtain ⟨v, hv, c, hc, H⟩ := hQ h h.2 hh
    exact ⟨⟨v, hv⟩, c, hc, fun u => H u u.2⟩
end GlobalTheory.HL.DivisibleGauss
