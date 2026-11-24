-- Prove2me | solution 1 for GlobalTheory.TateSeq.tower_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:37.933305+00:00
-- url     : https://prove2.me/submissions/82d097e5-7827-4646-8770-adfa0ce48e0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Theorems.Thm_GlobalTheory_TateSeq_tower_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.TateSeq
theorem _root_.solution {l r : ℕ} {e : ℕ → Fin r → M} (he : ∀ n i, l • e (n + 1) i = e n i)
    (h1 : ∀ a : Fin r → ℤ, ∑ i, a i • e 1 i = 0 → ∀ i, (l : ℤ) ∣ a i) (n : ℕ) :
    ∀ a : Fin r → ℤ, ∑ i, a i • e n i = 0 → ∀ i, (l : ℤ) ^ n ∣ a i := by
  induction n with
  | zero => intro a _ i; simp
  | succ n ih =>
    intro a ha
    have h2 : ∑ i, a i • e 1 i = 0 := by
      have := congrArg (fun x => l ^ n • x) ha
      simp only [Finset.smul_sum, smul_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, add_comm n 1, tower_pow (e := fun n => e n i) (fun n => he n i)]
    choose c hc using h1 a h2
    have h3 : ∑ i, c i • e n i = 0 := by
      rw [← ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, mul_comm, mul_smul, natCast_zsmul, he]
    intro i
    rw [hc, pow_succ']
    exact mul_dvd_mul_left _ (ih c h3 i)
end GlobalTheory.TateSeq
