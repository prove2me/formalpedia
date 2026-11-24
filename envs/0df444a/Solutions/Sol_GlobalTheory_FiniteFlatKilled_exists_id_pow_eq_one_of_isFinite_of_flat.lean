-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.exists_id_pow_eq_one_of_isFinite_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:17.969414+00:00
-- url     : https://prove2.me/submissions/f453ce93-f9de-41ce-aaf0-593fd49a4b96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_exists_id_pow_eq_one
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_isCocomm_of_mul_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution (R : Type) [CommRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H] (hf : IsFinite H.hom)
    (hfl : Flat H.hom) : ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra R B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of R)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of R) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  haveI : IsMonHom i.hom := e.hom.hom.isMonHom_hom
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap R B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI : Module.Finite R B := by
    have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [hw]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact RingHom.finite_algebraMap.1 h1
  haveI : Module.Flat R B := by
    have h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [hw]; infer_instance
    rw [Flat.SpecMap_iff] at h1
    exact RingHom.flat_algebraMap_iff.1 h1
  haveI : Coalgebra.IsCocomm R B := isCocomm_of_mul_comm fun f g => by
    let φ := (Spec.mapMulEquiv (R := R) (S := B) (T := B ⊗[R] B)).trans
      (Hom.mulEquivCongrRight i _)
    apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  obtain ⟨N, hN, h⟩ := exists_id_pow_eq_one (R := R) (B := B)
  refine ⟨N, hN, ?_⟩
  have h1 := congrArg (Spec.mapMulEquiv (R := R) (S := B) (T := B)) h
  rw [map_pow, map_one] at h1
  have h2 : Spec.mapMulEquiv (R := R) (S := B) (T := B) (toConv (AlgHom.id R B)) = 𝟙 G := by
    ext1
    exact Spec.map_id _
  have h3 : 𝟙 G ^ N = 1 := h2 ▸ h1
  rw [← cancel_epi i.hom, MonObj.comp_pow, MonObj.comp_one, Category.comp_id,
    ← Category.id_comp i.hom, ← MonObj.pow_comp, h3, MonObj.one_comp]
end GlobalTheory.FiniteFlatKilled
