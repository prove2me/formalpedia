-- Prove2me | solution 1 for GlobalTheory.TorusConst.val_eq_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:29.203965+00:00
-- url     : https://prove2.me/submissions/372291eb-a317-4247-b2cd-7a9390d9dd4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_natDegree_eq_zero_of_inv
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.TorusConst
theorem _root_.solution {A : Type} [Field A] [Algebra K A] {F G : sp K A[X] ⟶ B} (h : Glue F G)
    (V : B.left.Opens) (hV : IsAffineOpen V) (hF : ∀ q, F.left q ∈ V) (hG : ∀ q, G.left q ∈ V)
    (x y : A) : val F (AlgHom.id K A) x = val F (AlgHom.id K A) y := by
  have lift : ∀ H : sp K A[X] ⟶ B, (∀ q, H.left q ∈ V) →
      ∃ φ : Γ(B.left, V) ⟶ CommRingCat.of A[X], Spec.map φ ≫ hV.fromSpec = H.left := by
    intro H hH
    have hr : Set.range H.left ⊆ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      rintro _ ⟨q, rfl⟩
      exact hH q
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec H.left hr)
    exact ⟨φ, by rw [hφ]; exact IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨φ, hφ⟩ := lift F hF
  obtain ⟨ψ, hψ⟩ := lift G hG
  let E := FractionRing A[X]
  let t : E := algebraMap A[X] E X
  have ht : t ≠ 0 := fun h0 => X_ne_zero (IsFractionRing.injective A[X] E
    (h0.trans (map_zero _).symm))
  let c : A →ₐ[K] E := IsScalarTower.toAlgHom K A E
  have h1 : Spec.map (CommRingCat.ofHom (aevalTower c t).toRingHom) ≫ F.left =
      Spec.map (CommRingCat.ofHom (aevalTower c t⁻¹).toRingHom) ≫ G.left :=
    congrArg CommaMorphism.left (h E c t ht)
  rw [← hφ, ← hψ, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp,
    ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  have h3 : ∀ s, (φ.hom s).natDegree = 0 := by
    intro s
    apply natDegree_eq_zero_of_inv _ (ψ.hom s)
    have h4 : eval₂ (algebraMap A E) t (φ.hom s) = eval₂ (algebraMap A E) t⁻¹ (ψ.hom s) :=
      congrArg (fun g : Γ(B.left, V) ⟶ CommRingCat.of E => g.hom s) h2
    rw [← h4, ← aeval_def, aeval_algebraMap_apply, aeval_X_left_apply]
  ext1
  change Spec.map (CommRingCat.ofHom (aevalTower (AlgHom.id K A) x).toRingHom) ≫ F.left =
    Spec.map (CommRingCat.ofHom (aevalTower (AlgHom.id K A) y).toRingHom) ≫ F.left
  rw [← hφ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext s
  change aevalTower (AlgHom.id K A) x (φ.hom s) = aevalTower (AlgHom.id K A) y (φ.hom s)
  rw [eq_C_of_natDegree_eq_zero (h3 s), aevalTower_C, aevalTower_C]
end GlobalTheory.TorusConst
