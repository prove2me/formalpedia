-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.int_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:34.799298+00:00
-- url     : https://prove2.me/submissions/f7d4f810-7935-49e6-ada2-c42205e4b214

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_exists_prim
import Theorems.Thm_GlobalTheory_Cyc_TateS_mem_Xalg
import Theorems.Thm_GlobalTheory_T_integers_eq_sum_zeta_pow_unique
import Theorems.Thm_GlobalTheory_TateDecomp_exists_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) (c : ℕ) : ∀ x : Om l, x ∈ Ks K (j + c) →
    ‖x‖ ≤ 1 → ∃ o ∈ Ks K j, ∃ d ∈ Xalg K j,
      algebraMap (Om l) (PadicComplex l) x = algebraMap (Om l) (PadicComplex l) o + d := by
  induction c with
  | zero => exact fun x hx _ => ⟨x, hx, 0, zero_mem _, (add_zero _).symm⟩
  | succ c ih =>
    intro x hx hx1
    have hp : l.Prime := Fact.out
    haveI : NeZero l := ⟨hp.ne_zero⟩
    obtain ⟨z, hz⟩ := exists_prim (l := l) (l ^ (j + (c + 1))) (pow_ne_zero _ hp.ne_zero)
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K (j + (c + 1)) (by omega) z hz).1 x hx hx1
    obtain ⟨o, ho, d, hd, hod⟩ := ih (y 0) (hy 0).1 (hy 0).2
    refine ⟨o, ho, d + ∑ a ∈ Finset.univ.erase (0 : Fin l),
      algebraMap (Om l) (PadicComplex l) (z ^ (a : ℕ) * y a), add_mem hd (sum_mem fun a ha => ?_), ?_⟩
    · refine mem_Xalg K (i := j + (c + 1)) (by omega) (hz.pow_of_coprime _ ?_) (hy a).1 (hy a).2
      apply Nat.Coprime.pow_right
      have ha0 : (a : ℕ) ≠ 0 := fun h => (Finset.ne_of_mem_erase ha) (Fin.ext h)
      exact (Nat.coprime_of_lt_prime ha0 a.2 hp).symm
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin l)), map_add, map_sum, ← add_assoc,
        ← hod]
      simp
end GlobalTheory.Cyc.TateS
