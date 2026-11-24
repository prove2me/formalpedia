-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.pushout_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:18.052978+00:00
-- url     : https://prove2.me/submissions/9d6507bb-aab6-4522-9da2-67f66b298727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution {K : Type} [Field K] {A B C : CommRingCat.{0}} (f : CommRingCat.of K ⟶ A)
    (g : CommRingCat.of K ⟶ B) (i : A ⟶ C) (j : B ⟶ C) (po : IsPushout f g i j) :
    (∀ (α : A →+ K) (β : B →+ K), (∀ c a, α (f.hom c * a) = c * α a) → (∀ c b, β (g.hom c * b) = c * β b) →
      ∃ F : C →+ K, ∀ a b, F (i.hom a * j.hom b) = α a * β b) ∧
    ∀ G : C →+ K, (∀ a b, G (i.hom a * j.hom b) = 0) → ∀ w, G w = 0 := by
  letI : Algebra K A := f.hom.toAlgebra
  letI : Algebra K B := g.hom.toAlgebra
  have hw : f ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := B)) =
      g ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := B)).toRingHom := by
    ext c
    show f.hom c ⊗ₜ[K] (1 : B) = (1 : A) ⊗ₜ[K] g.hom c
    have h1 : f.hom c = c • (1 : A) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
    have h2 : g.hom c = c • (1 : B) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  obtain ⟨φ, hφi', hφj'⟩ : ∃ φ : C ⟶ CommRingCat.of (A ⊗[K] B),
      i ≫ φ = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ∧
      j ≫ φ = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := B)).toRingHom :=
    ⟨po.desc _ _ hw, po.inl_desc _ _ hw, po.inr_desc _ _ hw⟩
  have hφi : ∀ a, φ.hom (i.hom a) = a ⊗ₜ[K] (1 : B) := fun a => by
    have := congrArg (fun m => m.hom a) hφi'
    exact this
  have hφj : ∀ b, φ.hom (j.hom b) = (1 : A) ⊗ₜ[K] b := fun b => by
    have := congrArg (fun m => m.hom b) hφj'
    exact this
  refine ⟨fun α β hα hβ => ?_, fun G hG w => ?_⟩
  · let α' : A →ₗ[K] K :=
      { toFun := α, map_add' := α.map_add, map_smul' := fun c a => by rw [Algebra.smul_def]; exact hα c a }
    let β' : B →ₗ[K] K :=
      { toFun := β, map_add' := β.map_add, map_smul' := fun c b => by rw [Algebra.smul_def]; exact hβ c b }
    refine ⟨((LinearMap.mul' K K).comp (TensorProduct.map α' β')).toAddMonoidHom.comp φ.hom.toAddMonoidHom,
      fun a b => ?_⟩
    show LinearMap.mul' K K (TensorProduct.map α' β' (φ.hom (i.hom a * j.hom b))) = α a * β b
    rw [map_mul, hφi, hφj, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, TensorProduct.map_tmul,
      LinearMap.mul'_apply]
    rfl
  · letI : Algebra K C := (f ≫ i).hom.toAlgebra
    let iA : A →ₐ[K] C := { i.hom with commutes' := fun _ => rfl }
    let jA : B →ₐ[K] C :=
      { j.hom with commutes' := fun c => (congrArg (fun m => m.hom c) po.w).symm }
    let ψ := Algebra.TensorProduct.productMap iA jA
    have hψ : φ ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 C := by
      apply po.hom_ext
      · ext a
        show ψ (φ.hom (i.hom a)) = i.hom a
        rw [hφi, Algebra.TensorProduct.productMap_apply_tmul]
        show i.hom a * j.hom 1 = i.hom a
        rw [map_one, _root_.mul_one]
      · ext b
        show ψ (φ.hom (j.hom b)) = j.hom b
        rw [hφj, Algebra.TensorProduct.productMap_apply_tmul]
        show i.hom 1 * j.hom b = j.hom b
        rw [map_one, _root_.one_mul]
    have hw' : ψ (φ.hom w) = w := congrArg (fun m => m.hom w) hψ
    rw [← hw']
    generalize φ.hom w = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      exact hG a b
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
end GlobalTheory.KS.Kunneth
