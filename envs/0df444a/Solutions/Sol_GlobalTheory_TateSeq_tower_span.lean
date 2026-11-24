-- Prove2me | solution 1 for GlobalTheory.TateSeq.tower_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:38.696853+00:00
-- url     : https://prove2.me/submissions/ac2ada26-4571-46d8-9932-fead8bc09050

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
    (h1 : ∀ y : M, l • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • e 1 i = y) (n : ℕ) :
    ∀ y : M, l ^ n • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • e n i = y := by
  induction n with
  | zero => intro y hy; exact ⟨0, by simpa using (by simpa using hy : y = 0).symm⟩
  | succ n ih =>
    intro y hy
    obtain ⟨a, ha⟩ := h1 (l ^ n • y) (by rw [← mul_smul, ← pow_succ']; exact hy)
    obtain ⟨c, hc⟩ := ih (y - ∑ i, a i • e (n + 1) i) (by
      rw [smul_sub, ← ha, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, add_comm n 1, tower_pow (e := fun n => e n i) (fun n => he n i)])
    refine ⟨fun i => a i + c i * l, ?_⟩
    simp only [add_smul, mul_smul, natCast_zsmul, he, Finset.sum_add_distrib, hc]
    abel
end GlobalTheory.TateSeq
