-- Prove2me | solution 1 for GlobalTheory.UniformCocycle.proj_liftE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:30.796173+00:00
-- url     : https://prove2.me/submissions/73e8ceae-7601-4e19-b59e-497478bfef4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreVanishingCechCocycles
import Theorems.Thm_GlobalTheory_UniformCocycle_coeff_proj
import Theorems.Thm_GlobalTheory_UniformCocycle_coeff_liftE
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformCocycle
variable {R : Type} [CommRing R] {σ : Type}
namespace GlobalTheory.UniformCocycle
theorem _root_.solution {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, coeff m F ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by
  ext m
  rw [coeff_proj, coeff_liftE, liftCoeff, dif_pos (h m)]
  simp only [Polynomial.coeff_monomial]
  by_cases h1 : e' = e
  · subst h1; simp
  · rw [if_neg (Ne.symm h1), if_neg h1, coeff_zero]
end GlobalTheory.UniformCocycle
