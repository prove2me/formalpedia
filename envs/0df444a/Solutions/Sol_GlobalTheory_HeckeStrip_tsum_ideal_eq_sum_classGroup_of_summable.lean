-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.tsum_ideal_eq_sum_classGroup_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:16:03.834188+00:00
-- url     : https://prove2.me/submissions/77c6abd9-116f-4d7a-b4a0-5a01ac444c4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_existsUnique_isPrincipal_mul_classRep
import Theorems.Thm_GlobalTheory_tsum_isPrincipal_mul_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
open Classical
namespace GlobalTheory.HeckeStrip
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (G : Ideal (𝓞 K) → ℂ) (H : ClassGroup (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (h0 : G ⊥ = 0) (hsum : Summable G)
    (hH : ∀ c I, I ≠ ⊥ → H c (I * b c) = G I) :
    ∑' I, G I = ∑ c, ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ (b c : Ideal (𝓞 K))}, H c J := by
  let S : ClassGroup (𝓞 K) → Set (Ideal (𝓞 K)) :=
    fun c => {I | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal}
  have h1 : ∀ I, G I = ∑ c, (S c).indicator G I := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]
      exact (Finset.sum_eq_zero fun c _ => Set.indicator_of_notMem (fun h => h.1 rfl) _).symm
    · obtain ⟨c, hc, hu⟩ := GlobalTheory.existsUnique_isPrincipal_mul_classRep b hb I hI
      rw [Finset.sum_eq_single c]
      · exact (Set.indicator_of_mem (show I ∈ S c from ⟨hI, hc⟩) _).symm
      · intro c' _ hne
        exact Set.indicator_of_notMem (fun h => hne (hu c' h.2)) _
      · simp
  rw [tsum_congr h1, Summable.tsum_finsetSum (fun c _ => hsum.indicator (S c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← tsum_subtype, ← GlobalTheory.tsum_isPrincipal_mul_eq (b c : Ideal (𝓞 K))
    (mem_nonZeroDivisors_iff_ne_zero.mp (b c).2) (H c)]
  exact tsum_congr fun I => (hH c I.1 I.2.1).symm
end GlobalTheory.HeckeStrip
