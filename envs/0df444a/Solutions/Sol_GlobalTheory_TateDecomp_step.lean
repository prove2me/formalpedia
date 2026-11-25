-- Prove2me | solution 1 for GlobalTheory.TateDecomp.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:44.414358+00:00
-- url     : https://prove2.me/submissions/12df8e16-606f-48b0-9add-0af22d5433ea

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_norm_io
import Theorems.Thm_GlobalTheory_TateDecomp_exists_prim
import Theorems.Thm_GlobalTheory_T_integers_eq_sum_zeta_pow_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution (K : FinExt l) {i : ℕ} (hi : 2 ≤ i) {z : PadicComplex l} (hz : z ∈ intC (Ks K i)) :
    ∃ y ∈ intC (Ks K (i - 1)), z - y ∈ Xlev K i := by
  have hp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) i
  obtain ⟨⟨w, hw, rfl⟩, hn⟩ := intC_iff.1 hz
  rw [norm_io] at hn
  obtain ⟨y, h1, h2⟩ := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K i hi ζ hζ).1 w hw hn
  have h3 : ∀ a, io l (y a) ∈ intC (Ks K (i - 1)) := fun a =>
    ⟨⟨y a, (h1 a).1, rfl⟩, (norm_io _).le.trans (h1 a).2⟩
  refine ⟨io l (y ⟨0, hp.pos⟩), h3 _, ?_⟩
  rw [h2, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hp.pos⟩)]
  simp only [pow_zero, one_mul, map_add, add_sub_cancel_left, map_sum, map_mul]
  refine sum_mem fun a ha => AddSubgroup.subset_closure ⟨_, _, ?_, h3 a, rfl⟩
  refine (hζ.pow_of_coprime a ?_).map_of_injective (io l).injective
  refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_))
  refine Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero fun h => ?_) a.2
  exact (Finset.mem_erase.1 ha).1 (Fin.ext h)
end GlobalTheory.TateDecomp
