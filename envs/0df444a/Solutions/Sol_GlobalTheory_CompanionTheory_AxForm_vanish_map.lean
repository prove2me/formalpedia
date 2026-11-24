-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.vanish_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:30.531664+00:00
-- url     : https://prove2.me/submissions/a41fec54-4f15-4a25-adb7-338c02b2b14d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_exists_factor
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_factor_over
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_mem_of_closedPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_core
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution (A : Over (Sp R)) [GrpObj A] (hPar : Par (OAff (A ⊗ A).hom)) (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (B : Type) [CommRing B] [Algebra R B] [IsLocalRing B] (M : Type) [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] (g : GlobForm (A ⊗ A).hom →ₗ[R] M) : g c = 0 := by
  let x : TT (algebraMap R B) ⟶ A ⊗ A := lift (x0 A B) (x0 A B)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x.left (IsLocalRing.closedPoint B))
    (U := ⊤) trivial
  let U : (A ⊗ A).left.affineOpens := ⟨V, hV⟩
  obtain ⟨ε, hε⟩ := exists_factor (A ⊗ A).hom U x.left (mem_of_closedPoint x.left V hzV)
  have he : ε.comp (algebraMap R _) = algebraMap R B :=
    factor_over _ U ε _ (by rw [hε]; exact Over.w x)
  have hb := hPar (op U)
  letI : Module Bᵐᵒᵖ M := Module.compHom M ((RingHom.id B).fromOpposite fun x y ↦ Commute.all x y)
  haveI : IsCentralScalar B M := ⟨fun _ _ ↦ rfl⟩
  letI : Module (Sec (A ⊗ A).hom U.1) M := Module.compHom M ε
  haveI : IsScalarTower R (Sec (A ⊗ A).hom U.1) M := ⟨fun r a m ↦ by
    change ε (r • a) • m = r • (ε a • m)
    have e : ε (algebraMap R _ r) = algebraMap R B r := congrArg (fun q ↦ q r) he
    rw [Algebra.smul_def, map_mul, e, mul_smul, algebraMap_smul]⟩
  let l := hb.lift g
  have k := core A c h1 h2 U ε hε l.toAddMonoidHom (fun a ω ↦ l.map_smul a ω)
  exact (hb.lift_eq g c).symm.trans k
end GlobalTheory.CompanionTheory.AxForm
