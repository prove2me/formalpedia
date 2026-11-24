-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.uOf_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:21.852234+00:00
-- url     : https://prove2.me/submissions/ee2cb8ab-5023-4859-859a-a022ff4095f5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_exists_lin
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_lin_unique

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
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
variable [IsOpenImmersion x]
omit [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [AddCommGroup M] [Module B M]
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution : IsBaseChange B (uOf hy x hx) := by
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ?_
  letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
  letI : Module Bᵐᵒᵖ Q := Module.compHom Q ((RingHom.id B).fromOpposite fun _ _ ↦ mul_comm _ _)
  haveI : IsCentralScalar B Q := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨f, hf⟩ := exists_lin hy x hx (M := Q) g
  exact ⟨f, hf, fun f' hf' ↦ lin_unique hy x hx f' f (hf'.trans hf.symm)⟩
end GlobalTheory.CompanionTheory.AbForms
