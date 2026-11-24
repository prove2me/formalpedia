-- Prove2me | solution 1 for GlobalTheory.TorusUnit.torusPoint_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:46.487681+00:00
-- url     : https://prove2.me/submissions/f8d34abf-046a-4439-860f-0c251718892c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_torusPoint_fst
import Theorems.Thm_GlobalTheory_TorusUnit_torus_hom_ext
import Theorems.Thm_GlobalTheory_TorusUnit_pullback_map_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.TorusUnit
theorem _root_.solution {R : CommRingCat.{0}} (φ φ' ψ : torusRing ZU X ⟶ R) (s : Spec R ⟶ S)
    (h : ∀ x : X, ψ.hom (single x 1) = φ.hom (single x 1) * φ'.hom (single x 1)) :
    torusPoint φ s * torusPoint φ' s = torusPoint ψ s := by
  letI : Algebra ZU.{0} R := ULift.algebra' ℤ R
  apply torus_hom_ext
  let a : torusRing ZU X →ₐ[ZU.{0}] R :=
    { φ.hom with commutes' := fun r => RingHom.congr_fun (ringHom_uliftInt_ext (φ.hom.comp (algebraMap ZU.{0} (torusRing ZU X))) (algebraMap ZU.{0} R)) r }
  let a' : torusRing ZU X →ₐ[ZU.{0}] R :=
    { φ'.hom with commutes' := fun r => RingHom.congr_fun (ringHom_uliftInt_ext (φ'.hom.comp (algebraMap ZU.{0} (torusRing ZU X))) (algebraMap ZU.{0} R)) r }
  let m : torusRing ZU X ⊗[ZU.{0}] torusRing ZU X →ₐ[ZU.{0}] R :=
    Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
  have e1 : (lift (torusPoint φ s) (torusPoint φ' s) ≫
      Functor.LaxMonoidal.μ (Over.pullback (toZ S)) (splitTorusAff ZU X) (splitTorusAff ZU X)).left ≫
      pullback.fst (splitTorusAff ZU X ⊗ splitTorusAff ZU X).hom (toZ S) =
      Spec.map (CommRingCat.ofHom m.toRingHom) ≫
        (pullbackSpecIso ZU.{0} (torusRing ZU X) (torusRing ZU X)).inv := by
    apply pullback.hom_ext
    · have := pullback_map_fst (S := S) (fst (splitTorusAff ZU X) (splitTorusAff ZU X))
      rw [Category.assoc]
      erw [← this]
      rw [← Category.assoc, ← Over.comp_left, Category.assoc, Functor.Monoidal.μ_fst]
      erw [lift_fst, torusPoint_fst, Category.assoc, pullbackSpecIso_inv_fst]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x => ?_
      simp [m, a]
    · have := pullback_map_fst (S := S) (snd (splitTorusAff ZU X) (splitTorusAff ZU X))
      rw [Category.assoc]
      erw [← this]
      rw [← Category.assoc, ← Over.comp_left, Category.assoc, Functor.Monoidal.μ_snd]
      erw [lift_snd, torusPoint_fst, Category.assoc, pullbackSpecIso_inv_snd]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x => ?_
      simp [m, a']
  have e2 : μ[splitTorus S X] = Functor.LaxMonoidal.μ (Over.pullback (toZ S)) (splitTorusAff ZU X) (splitTorusAff ZU X) ≫ (Over.pullback (toZ S)).map μ[splitTorusAff ZU X] := rfl
  rw [Hom.mul_def, e2, ← Category.assoc, Over.comp_left, Category.assoc, torusPoint_fst]
  erw [pullback_map_fst]
  rw [← Category.assoc]
  erw [e1]
  rw [mul_spec_asOver_spec_left, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply ringHom_ext_ZU
  intro x
  rw [h]
  change m (Coalgebra.comul (R := ZU.{0}) (single x (1 : ZU.{0}) : AddMonoidAlgebra ZU.{0} X)) = _
  rw [AddMonoidAlgebra.comul_single]
  simp [m, a, a']
end GlobalTheory.TorusUnit
