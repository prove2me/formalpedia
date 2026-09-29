-- Prove2me | solution 1 for IsRegularLocalRing.localization_atPrime_tensor_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8fc3c6b4-3bf5-55fb-a5e6-3b1b70e866ad

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_localization_atPrime_tensor_of_isAlgClosed
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem solution
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (R : Type u) [CommRing R] [Algebra k₀ R]
    [Algebra.FiniteType k₀ R] (n : ℕ)
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p) ∧
        ringKrullDim (Localization.AtPrime p) = (n : ℕ∞))
    (k : Type u) [Field k] [Algebra k₀ k] (q : Ideal (k ⊗[k₀] R)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI hP1 := AlgebraicGeometry.SmoothOfRelativeDimension.of_forall_isRegularLocalRing_of_isAlgClosed
    k₀ R n hreg
  have hS : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k₀ R))) :=
    SmoothOfRelativeDimension.smooth n _
  have e : Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[k₀] R))) =
      (pullbackSpecIso k₀ k R).inv ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ R))) :=
    (Iso.eq_inv_comp _).mpr (pullbackSpecIso_hom_fst' k₀ k R)
  haveI h2 : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[k₀] R)))) := by
    rw [e, MorphismProperty.cancel_left_of_respectsIso @Smooth]
    exact MorphismProperty.pullback_fst _ _ hS
  let x : Spec (CommRingCat.of (k ⊗[k₀] R)) := ⟨q, inferInstance⟩
  haveI hst := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
    (f := Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[k₀] R)))) x
  have hst' : IsRegularLocalRing ((structurePresheafInCommRingCat (k ⊗[k₀] R)).stalk x) := hst
  exact @IsRegularLocalRing.of_ringEquiv _ _ hst' _ _
    (StructureSheaf.stalkIso (k ⊗[k₀] R) x).toRingEquiv.symm

end S_IsRegularLocalRing_localization_atPrime_tensor_of_isAlgClosed
end P2MW
export P2MW.S_IsRegularLocalRing_localization_atPrime_tensor_of_isAlgClosed (solution)
