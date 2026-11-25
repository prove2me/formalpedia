-- Prove2me | solution 1 for GlobalTheory.GrpTangent.etale_hom_and_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:45.875538+00:00
-- url     : https://prove2.me/submissions/127e030d-28c3-4f54-9d85-0006304deca9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_formallyUnramified_of_tangentMap_injective
import Theorems.Thm_GlobalTheory_GrpTangent_smooth_of_tangentMap_surjective
import Theorems.Thm_GlobalTheory_GrpTangent_etale_of_tangentMap_bijective
import Theorems.Thm_GlobalTheory_GrpTangent_comp_mulN_left_of_isTangent
import Theorems.Thm_GlobalTheory_GrpTangent_etale_mulN
import Theorems.Thm_GlobalTheory_GrpTangent_etale_torsion
import Theorems.Thm_GlobalTheory_GrpTangent_finiteEtale_mulN_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
namespace GlobalTheory.GrpTangent
theorem _root_.solution :
    (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] [Smooth G.hom] [Smooth H.hom]
      (f : G ⟶ H) [IsMonHom f],
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Bijective (tangentMap ((Over.pullback p).map f))) → Etale f.left) ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Injective (tangentMap ((Over.pullback p).map f))) → FormallyUnramified f.left) ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Surjective (tangentMap ((Over.pullback p).map f))) → Smooth f.left)) ∧
    (∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (n : ℕ) (w : epsR R ⟶ G),
      IsTangent w → (w ≫ mulN G n).left = spMap (epsScaleR (n : R)) ≫ w.left) ∧
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (n : ℕ),
      IsUnit (n : Γ(S, ⊤)) → Etale (mulN G n).left ∧ Etale (torsion G n).hom) ∧
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsAbelianScheme G] (n : ℕ),
      IsUnit (n : Γ(S, ⊤)) → (IsFinite (mulN G n).left ∧ Etale (mulN G n).left) ∧
        IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom) := by
  refine ⟨fun S G H _ _ _ _ f _ => ⟨etale_of_tangentMap_bijective f, fun h => ?_,
      smooth_of_tangentMap_surjective f⟩,
    fun R _ G _ n w hw => comp_mulN_left_of_isTangent hw n,
    fun S G _ _ _ n hn => ⟨etale_mulN G hn, etale_torsion G hn⟩,
    fun S G _ _ n hn => finiteEtale_mulN_torsion G hn⟩
  have : LocallyOfFiniteType (f.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp f.left H.hom
  exact formallyUnramified_of_tangentMap_injective f h
end GlobalTheory.GrpTangent
