-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.tzo_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:30.070313+00:00
-- url     : https://prove2.me/submissions/0fd20cc6-7cc2-4347-ba11-3635f4494a93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (α : B →+* B') (hα : α.comp (algebraMap R B) = algebraMap R B') (f : M →ₗ[R] M')
    (hf : ∀ b m, (f : M →+ M') (b • m) = α b • (f : M →+ M') m)
    (h : (tmap α (f : M →+ M') hf).comp (sz (R := R) B M) = sz B' M') (u : W →ₗ[R] M) :
    spo (tmap α (f : M →+ M') hf) h ≫ tzo hy u = tzo (B := B') hy (f ∘ₗ u) := by
  have e : (tmap α (f : M →+ M') hf).comp (tsz u) = tsz (B := B') (f ∘ₗ u) := RingHom.ext fun c ↦ by
    ext
    · simp [tsz, ← hα]
    · simp [tsz]
  refine Over.OverMorphism.ext ?_
  change spMap (tmap α (f : M →+ M') hf) ≫ spMap (tsz u) ≫ y₀ = spMap (tsz (B := B') (f ∘ₗ u)) ≫ y₀
  rw [← Category.assoc, ← spMap_comp, e]
end GlobalTheory.CompanionTheory.AbForms
