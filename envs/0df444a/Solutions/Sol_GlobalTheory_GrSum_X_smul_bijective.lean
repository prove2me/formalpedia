-- Prove2me | solution 1 for GlobalTheory.GrSum.X_smul_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:59:27.56811+00:00
-- url     : https://prove2.me/submissions/bbcaf5d8-2a9b-44ba-82b5-6e88e77349d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
import Theorems.Thm_GlobalTheory_IsGradedMap_injective_iff
import Theorems.Thm_GlobalTheory_IsGradedMap_surjective_iff
import Theorems.Thm_GlobalTheory_X_mem_polyGrading
import Theorems.Thm_GlobalTheory_isGradedMap_lsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R]
namespace GlobalTheory
namespace GrSum
theorem _root_.solution {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) {i : ι}
    (h : ∀ t, Function.Bijective (x i t)) :
    Function.Bijective fun m : GrSum hx => (X i : MvPolynomial ι R) • m := by
  have hg := isGradedMap_lsmul (GrSum.grading hx) (X_mem_polyGrading (R := R) i)
  refine ⟨hg.injective_iff.2 fun n => ?_, hg.surjective_iff.2 fun n => ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ e
    have e' : (X i : MvPolynomial ι R) • GrSum.of hx n a = (X i : MvPolynomial ι R) • GrSum.of hx n b :=
      congrArg Subtype.val e
    rw [GrSum.X_smul_of, GrSum.X_smul_of] at e'
    obtain rfl := (h n).1 (GrSum.of_injective hx _ e')
    rfl
  · rintro ⟨_, b, rfl⟩
    obtain ⟨a, rfl⟩ := (h n).2 b
    exact ⟨⟨_, a, rfl⟩, Subtype.ext (GrSum.X_smul_of hx i n a)⟩
end GrSum
end GlobalTheory
