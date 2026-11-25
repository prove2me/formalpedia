-- Prove2me | solution 1 for GlobalTheory.exists_specOver_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:02.129858+00:00
-- url     : https://prove2.me/submissions/98cc5675-af60-4a3e-a97c-efbc87fcaded

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution (T : Over (Spec (.of R))) {t : T.left} {V : T.left.Opens}
    (ht : t ∈ V) : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (j : specOver R A ⟶ T),
      IsOpenImmersion j.left ∧ t ∈ Set.range j.left ∧ j.left ⁻¹ᵁ V = ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, htU, hUV⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open ht V.2
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, U) := ρ.hom.toAlgebra
  refine ⟨Γ(T.left, U), inferInstance, inferInstance, Over.homMk hU.fromSpec hρ.symm,
    IsAffineOpen.isOpenImmersion_fromSpec hU, hU.range_fromSpec.ge htU, ?_⟩
  exact top_le_iff.mp fun y _ => hUV (hU.range_fromSpec.le ⟨y, rfl⟩)
end GlobalTheory
