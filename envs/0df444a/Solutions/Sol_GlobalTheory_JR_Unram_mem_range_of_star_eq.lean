-- Prove2me | solution 1 for GlobalTheory.JR.Unram.mem_range_of_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:14.665957+00:00
-- url     : https://prove2.me/submissions/6dbf7741-7132-4dbe-9fc5-ebba64681c71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeAlgebraMapOfStarEq
import Theorems.Thm_GlobalTheory_JR_Unram_exists_basis_antifixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
namespace Unram
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  intro F E _ _ _ _ h y hy
  haveI := h.charZero
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨b, d, hb0, hs, -, -⟩ := Unram.exists_basis_antifixed F E
  have hsum := b.sum_repr y
  rw [Fin.sum_univ_two, hb0] at hsum
  set a := b.repr y 0
  set c := b.repr y 1
  have hst : star y = a • (1 : E) - c • b 1 := by
    rw [← hsum]
    simp only [Algebra.smul_def, star_add, star_mul', h.star_fix, hs, star_one]
    ring
  have h2 : (2 : E) * (c • b 1) = 0 := by linear_combination hsum + hst - hy
  have hc : c • b 1 = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨a, ?_⟩
  rw [← hsum, hc, add_zero, Algebra.algebraMap_eq_smul_one]
end Unram
end GlobalTheory.JR
