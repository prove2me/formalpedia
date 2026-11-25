-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xlev_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:22.56352+00:00
-- url     : https://prove2.me/submissions/9b400c20-0045-426b-b2d4-49659b54117f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_exists_prim
import Theorems.Thm_GlobalTheory_TateDecomp_Xlev_form
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
theorem _root_.solution (K : FinExt l) {i : ℕ} (hi : 2 ≤ i) {x : PadicComplex l} (hx : x ∈ Xlev K i)
    (hx' : x ∈ subC (Ks K (i - 1))) : x = 0 := by
  have hp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) i
  obtain ⟨y, h1, h2, h3⟩ := Xlev_form K (by omega) hζ hx
  obtain ⟨w, hw, rfl⟩ := hx'
  have h4 := (io l).injective h3
  have h5 := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K i hi ζ hζ).2 (y - Pi.single ⟨0, hp.pos⟩ w) (fun a => by
    refine sub_mem (h1 a) ?_
    rw [Pi.single_apply]
    split_ifs
    · exact hw
    · exact zero_mem _) (by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [← h4, Finset.sum_eq_single ⟨0, hp.pos⟩]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · simp) ⟨0, hp.pos⟩
  have h6 : w = 0 := by
    rwa [Pi.sub_apply, h2, Pi.single_eq_same, zero_sub, neg_eq_zero] at h5
  rw [h6, map_zero]
end GlobalTheory.TateDecomp
