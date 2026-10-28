-- Prove2me | solution 1 for OAI.Lech.ReesRoot.scalarHomology_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:38:58.772777+00:00
-- url     : https://prove2.me/submissions/24ec4ce0-315f-4a6d-95e1-07f53ec1c200

import Mathlib
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L029
import Theorems.Thm_OAI_Lech_FilteredCech_positive_homology_powerTorsion
import Theorems.Thm_OAI_Lech_SourceGraded_exists_uniform_geometric_stableImage
import Theorems.Thm_OAI_Lech_SourceGraded_finiteThickening_homology_zeroClass
import Theorems.Thm_OAI_Lech_ordinaryPower_stableImage_isoMod

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.FiniteComplex

section

variable {C : Type*} [Category C] [Abelian C]
variable (F : CochainComplex C ℤ) (n : ℤ)
  (hn : ∀ i, n < i → IsZero (F.X i))


theorem homology_devissage (P : ObjectProperty C) [P.IsSerreClass]
    (T : CochainComplex C ℤ ⥤ CochainComplex C ℤ) [T.Additive]
    (hT : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (ComplexShape.up ℤ) j)).Splitting) →
      ∀ j, ((S.map T).map (eval C (ComplexShape.up ℤ) j)).Splitting)
    (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j))
    (hg : ∀ j, P ((T.obj ((single C (ComplexShape.up ℤ) j).obj
      (F.X j))).homology i)) : P ((T.obj F).homology i) := by
  let Q := P.inverseImage (T ⋙ homologyFunctor C (ComplexShape.up ℤ) i)
  apply devissage Q ?_ m N F hb hg
  intro S hs h₁ h₃
  have hS : (S.map T).ShortExact :=
    shortExact_of_degreewise_shortExact _ (fun j => (hT S hs j).shortExact)
  exact P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
end Lech.FiniteComplex


open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section


universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


lemma imageMap_isoModSerre (P : ObjectProperty C) [P.IsSerreClass]
    {f g : Arrow C} (φ : f ⟶ g)
    (h₁ : P.isoModSerre φ.left) (h₂ : P.isoModSerre φ.right) :
    P.isoModSerre (image.map φ) := by
  constructor
  · have h := P.monoModSerre.comp_mem (image.ι f.hom) φ.right
      (P.monoModSerre_of_mono _) h₂.1
    rw [← image.map_ι φ] at h
    exact P.prop_of_mono
      (kernel.map (image.map φ) (image.map φ ≫ image.ι g.hom)
        (𝟙 _) (image.ι g.hom) (by simp)) h
  · have h := P.epiModSerre.comp_mem φ.left (factorThruImage g.hom)
      h₁.2 (P.epiModSerre_of_epi _)
    rw [← image.factor_map φ] at h
    exact P.prop_of_epi
      (cokernel.map (factorThruImage f.hom ≫ image.map φ) (image.map φ)
        (factorThruImage f.hom) (𝟙 _) (by simp)) h

variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma eq_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N) : ℓ.value M = ℓ.value N :=
  le_antisymm (ℓ.le_of_mono e.hom hN) (ℓ.le_of_mono e.inv hM)

lemma eq_of_isoModSerre {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N)
    (hf : ℓ.zeroClass.isoModSerre f) : ℓ.value M = ℓ.value N := by
  have h₁ : (ShortComplex.kernelSequence (Abelian.factorThruImage f)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      epi_g := (inferInstance : Epi (Abelian.factorThruImage f)) }
  have h₂ : (ShortComplex.cokernelSequence (Abelian.image.ι f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := (inferInstance : Mono (Abelian.image.ι f)) }
  have e₁ := ℓ.additive h₁ hM
  have e₂ := ℓ.additive h₂ hN
  have hker := hf.1.isoModSerre_factorThruImage.1.2
  have hcoker := hf.2.isoModSerre_image_ι.2.2
  dsimp only [ShortComplex.kernelSequence, ShortComplex.cokernelSequence] at e₁ e₂
  rw [hker, zero_add] at e₁
  rw [hcoker, add_zero] at e₂
  exact e₁.trans e₂.symm

lemma image_value_eq {f g : Arrow (ModuleCat.{u} R)} (φ : f ⟶ g)
    (h₁ : ℓ.zeroClass.isoModSerre φ.left) (h₂ : ℓ.zeroClass.isoModSerre φ.right)
    (hMf : powerTorsion I f.right) (hMg : powerTorsion I g.right) :
    ℓ.value (image f.hom) = ℓ.value (image g.hom) :=
  ℓ.eq_of_isoModSerre (image.map φ)
    (powerTorsion_mono I (image.ι f.hom) hMf)
    (powerTorsion_mono I (image.ι g.hom) hMg)
    (imageMap_isoModSerre ℓ.zeroClass φ h₁ h₂)

end TorsionLength
end


universe u
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech
universe u v
variable {R : Type u} [CommRing R] {C : Type v} [Category C] [Abelian C]

 

lemma prop_additive_free (P : ObjectProperty C) [P.IsSerreClass]
    (T : ModuleCat.{u} R ⥤ C) [T.Additive]
    (hR : P (T.obj (ModuleCat.of R R))) (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] [Nontrivial R] : P (T.obj M) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts T
  have hfin : ∀ n : ℕ, P (T.obj (ModuleCat.of R (Fin n → R))) := by
    intro n
    induction n with
    | zero =>
      apply P.prop_of_isZero
      apply T.map_isZero
      rw [ModuleCat.isZero_iff_subsingleton]
      infer_instance
    | succ n ih =>
      let X := ModuleCat.of R R
      let Y := ModuleCat.of R (Fin n → R)
      let e : X ⊞ Y ≅ ModuleCat.of R (Fin (n + 1) → R) :=
        ModuleCat.biprodIsoProd X Y ≪≫
          LinearEquiv.toModuleIso (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R))
      apply P.prop_of_iso (T.mapIso e)
      apply P.prop_of_iso (T.mapBiprod X Y).symm
      exact P.prop_biprod hR ih
  exact P.prop_of_iso (T.mapIso (LinearEquiv.toModuleIso
    (Module.finBasis R M).equivFun).symm) (hfin _)

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
lemma connecting_isoModSerre (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (i j : ι) (hij : c.Rel i j)
    (hi : P (S.X₂.homology i)) (hj : P (S.X₂.homology j)) :
    P.isoModSerre (hS.δ i j hij) := by
  constructor
  · have : Epi (kernel.lift (hS.δ i j hij) (homologyMap S.g i)
        (hS.comp_δ i j hij)) := (hS.homology_exact₃ i j hij).epi_kernelLift
    exact P.prop_of_epi (kernel.lift (hS.δ i j hij) (homologyMap S.g i) (hS.comp_δ i j hij)) hi
  · have : Mono (cokernel.desc (hS.δ i j hij) (homologyMap S.f j)
        (hS.δ_comp i j hij)) := (hS.homology_exact₁ i j hij).mono_cokernelDesc
    exact P.prop_of_mono (cokernel.desc (hS.δ i j hij) (homologyMap S.f j) (hS.δ_comp i j hij)) hj
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

 

lemma homology_property_of_bounded_free
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hK : ∀ i, P (K.homology i))
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j, Module.Free R (F.X j)) (hfinite : ∀ j, Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (i : ℤ) :
    P (((functor K).obj F).homology i) := by
  apply FiniteComplex.homology_devissage P (functor K) (splitting K) m N F i hb
  intro j
  let T := single (ModuleCat.{u} R) (.up ℤ) j ⋙ functor K ⋙
    homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  let := hfree j
  let := hfinite j
  exact prop_additive_free P T
    (P.prop_of_iso (singleRingHomologyIso K j i).symm (hK (i-j))) (F.X j)

end Lech.TensorTotal


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {C : Type u} [Category C] [Abelian C]

 

lemma homology_property_extendUpNat
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (K : CochainComplex C ℕ) (hK : ∀ n, P (K.homology n)) (i : ℤ) :
    P ((K.extend ComplexShape.embeddingUpNat).homology i) := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact P.prop_of_iso (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm (hK n)
  · apply P.prop_of_isZero
    apply (exactAt_iff_isZero_homology _ _).mp
    apply K.extend_exactAt
    intro n hn
    change (n : ℤ)=i at hn
    omega
end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]
  (F K : CochainComplex (ModuleCat.{u} R) ℤ)
  (hK : ∀ j, j < 0 → IsZero (K.X j))

lemma bottomComparison_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (h : ∀ i, P (((Right.functor F).obj K).homology i)) (i : ℤ) :
    P.isoModSerre (bottomComparison F K hK i) :=
  connecting_isoModSerre P (bottomSequence_shortExact F K hK) i (i+1) rfl (h i) (h (i+1))

end Lech.TensorTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmentationRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.moduleQuotient_linear _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

private lemma extended_square {C : Type*} [Category C]
    {X X' Y Y' Z W : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X' ⟶ Y') (a : X' ⟶ Z) (b : Y' ⟶ W) (g : Z ⟶ W)
    (h : f ≫ b = a ≫ g) :
    (eX.hom ≫ f ≫ eY.inv) ≫ (eY.hom ≫ b) = (eX.hom ≫ a) ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (eX.hom ≫ ·) h

private lemma inverse_square_comp {C : Type*} [Category C]
    {X X' Y Y' Z W : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ Z) (b : Y ⟶ W) (k : Z ⟶ W)
    (h : f ≫ eY.hom = eX.hom ≫ g) (h' : f ≫ b = a ≫ k) :
    g ≫ (eY.inv ≫ b) = (eX.inv ≫ a) ≫ k := by
  apply (cancel_epi eX.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc eX.hom g, ← h]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

private lemma map_square_comp {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {X X' Y Y' : C}
    {V V' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (qX : T.obj X' ≅ V) (qY : T.obj Y' ≅ V')
    (f : X ⟶ Y) (g : X' ⟶ Y') (k : V ⟶ V')
    (h : f ≫ eY.hom = eX.hom ≫ g) (h' : T.map g ≫ qY.hom = qX.hom ≫ k) :
    T.map f ≫ (T.map eY.hom ≫ qY.hom) = (T.map eX.hom ≫ qX.hom) ≫ k := by
  rw [← Category.assoc, ← T.map_comp, h, T.map_comp, Category.assoc, h', Category.assoc]


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)



lemma finiteThickeningZeroIso_transition {M N : ℕ} (hMN : M ≤ N) :
    (finiteThickeningTransition I z hz 0 hMN).f 0 ≫ (finiteThickeningZeroIso I z hz M).hom =
      (finiteThickeningZeroIso I z hz N).hom ≫
        ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hMN)) := by
  let f := FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 N)
  have he : cokernel.π f ≫ finiteThickeningTransition I z hz 0 hMN =
      cokernel.π (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M)) := by
    exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  have he' := congrArg (fun k => k.f 0) he
  have hM := finiteThickeningZeroIso_π I z hz M
  have hN := finiteThickeningZeroIso_π I z hz N
  apply (cancel_epi ((cokernel.π f).f 0)).mp
  calc
    _ = ((cokernel.π f).f 0 ≫ (finiteThickeningTransition I z hz 0 hMN).f 0) ≫
        (finiteThickeningZeroIso I z hz M).hom := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ (finiteThickeningZeroIso I z hz M).hom) he'
    _ = _ := hM
    _ = ((cokernel.π f).f 0 ≫ (finiteThickeningZeroIso I z hz N).hom) ≫
        ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hMN)) := by
      rw [hN,Category.assoc]
      congr 1
    _ = _ := Category.assoc _ _ _

end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

lemma augmentedThickeningZeroIso_transition {M N : ℕ} (hMN : M ≤ N) :
    (augmentedThickeningTransition I z hz hMN).f 0 ≫ (augmentedThickeningZeroIso I z hz M).hom =
      (augmentedThickeningZeroIso I z hz N).hom ≫
        ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hMN)) := by
  simp only [augmentedThickeningTransition]
  refine (congrArg (· ≫ (augmentedThickeningZeroIso I z hz M).hom)
    (extendMap_f (finiteThickeningTransition I z hz 0 hMN)
      ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl))).trans ?_
  exact extended_square _ _ _ _ _ _ (finiteThickeningZeroIso_transition I z hz hMN)

end Lech.SourceGraded


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

@[reassoc] lemma tensorSingleQuotientIso_naturality {I J : Ideal R} (hIJ : I ≤ J)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    mapBifunctorMap (𝟙 F) ((single (ModuleCat.{u} R) (.up ℤ) 0).map
      (ModuleCat.ofHom (Submodule.factor hIJ))) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) ≫
        (tensorSingleQuotientIso J F).hom =
    (tensorSingleQuotientIso I F).hom ≫ (complexQuotientMap hIJ (.up ℤ)).app F := by
  refine inverse_square_comp (tensorSingleIso F (ModuleCat.of R (R ⧸ I)))
    (tensorSingleIso F (ModuleCat.of R (R ⧸ J))) _ _ _ _ _
      (tensorSingleIso_naturality F _ (ModuleCat.ofHom (Submodule.factor hIJ))) ?_
  apply Hom.ext
  funext i
  exact termTensorQuotientIso_naturality hIJ (F.X i)

end Lech.TensorTotal


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

@[reassoc] lemma thickeningTensorBottomIso_transition {M N : ℕ} (hMN : M ≤ N) :
    (TensorTotal.Right.functor F).map ((single (ModuleCat.{u} R) (.up ℤ) 0).map
      ((augmentedThickeningTransition I z hz hMN).f 0)) ≫ (thickeningTensorBottomIso I z hz F M).hom =
    (thickeningTensorBottomIso I z hz F N).hom ≫
      (complexQuotientMap (Ideal.pow_le_pow_right hMN) (.up ℤ)).app F := by
  exact map_square_comp ((single (ModuleCat.{u} R) (.up ℤ) 0) ⋙ TensorTotal.Right.functor F)
    (augmentedThickeningZeroIso I z hz N) (augmentedThickeningZeroIso I z hz M)
    (TensorTotal.tensorSingleQuotientIso (I^N) F) (TensorTotal.tensorSingleQuotientIso (I^M) F)
    _ _ _ (augmentedThickeningZeroIso_transition I z hz hMN)
    (TensorTotal.tensorSingleQuotientIso_naturality (Ideal.pow_le_pow_right hMN) F)

 

@[reassoc] lemma thickeningComparison_transition {M N : ℕ} (hMN : M ≤ N) (i : ℤ) :
    homologyMap ((complexQuotientMap (Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i ≫
      thickeningComparison I z hz F M i =
    thickeningComparison I z hz F N i ≫
      homologyMap ((TensorTotal.Right.functor F).map (thickeningCechTransition I z hz hMN)) (i+1) := by
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  let eN := H.mapIso (thickeningTensorBottomIso I z hz F N)
  let eM := H.mapIso (thickeningTensorBottomIso I z hz F M)
  let f := (TensorTotal.Right.functor F).map ((single (ModuleCat.{u} R) (.up ℤ) 0).map
    ((augmentedThickeningTransition I z hz hMN).f 0))
  have hh : H.map f ≫ eM.hom = eN.hom ≫
      homologyMap ((complexQuotientMap (Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i := by
    dsimp only [H,eM,eN,f,Functor.mapIso,homologyFunctor]
    simpa only [homologyMap_comp] using
      (congrArg (fun g => homologyMap g i) (thickeningTensorBottomIso_transition I z hz F hMN))
  exact inverse_square_comp eN eM _ _ _ _ _ hh
    (TensorTotal.bottomComparison_naturality F (augmentedThickening I z hz N)
    (augmentedThickening_boundedBelow I z hz N) (augmentedThickening I z hz M)
    (augmentedThickening_boundedBelow I z hz M) (augmentedThickeningTransition I z hz hMN) i).symm
end Lech.SourceGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace Lech
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]


variable {R S}
lemma baseChangeHom_isBaseChange (M N : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] :
    IsBaseChange S (LinearMap.baseChangeHom R S M N) := by
  have h := (TensorProduct.isBaseChange R M S).linearMapLeftRight
    (TensorProduct.isBaseChange R N S)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply LinearMap.ext
  intro f
  apply (TensorProduct.isBaseChange R M S).algHom_ext
  intro m
  exact (IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R M S) (TensorProduct.mk R S N 1) f m).symm

instance baseChangeFunctor_map_localized (U : Submonoid R) [IsLocalization U S]
    (M N : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    IsLocalizedModule U ((baseChangeFunctor R S).mapLinearMap R (X := M) (Y := N)) := by
  have : IsLocalizedModule U (LinearMap.baseChangeHom R S M N) :=
    (isLocalizedModule_iff_isBaseChange U S _).mpr (baseChangeHom_isBaseChange M N)
  change IsLocalizedModule U ((baseChangeHomEquiv R S M N).toLinearMap ∘ₗ
    LinearMap.baseChangeHom R S M N ∘ₗ
      (ModuleCat.homLinearEquiv (M := M) (N := N) (S := R)).toLinearMap)
  infer_instance

end Lech

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra


namespace Lech
open scoped TensorProduct
section Retract
variable {R : Type*} [CommRing R] (S : Submonoid R)
  {M N M' N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (f : M →ₗ[R] M') (g : N →ₗ[R] N')
  (i : M →ₗ[R] N) (p : N →ₗ[R] M)
  (i' : M' →ₗ[R] N') (p' : N' →ₗ[R] M')
  (hpi : p.comp i = LinearMap.id) (hp'i' : p'.comp i' = LinearMap.id)
  (hgi : g.comp i = i'.comp f) (hfp : f.comp p = p'.comp g)
  [IsLocalizedModule S g]

include hpi hp'i' hgi hfp in
 
lemma localizedModule_retract : IsLocalizedModule S f where
  map_units s := by
    apply (Module.End.isUnit_iff _).mpr
    have hs := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)
    have hi := LinearMap.injective_of_comp_eq_id i' p' hp'i'
    constructor
    · intro x y h
      apply hi
      apply hs.1
      simpa only [Module.algebraMap_end_apply,←map_smul] using congrArg i' h
    · intro x
      obtain ⟨n,hn⟩ := hs.2 (i' x)
      refine ⟨p' n,?_⟩
      change (s : R) • p' n = x
      have hh := congrArg p' hn
      simp only [Module.algebraMap_end_apply, map_smul] at hh
      exact hh.trans (LinearMap.congr_fun hp'i' x)
  surj x := by
    obtain ⟨⟨n,s⟩,hn⟩ := IsLocalizedModule.surj S g (i' x)
    refine ⟨⟨p n,s⟩,?_⟩
    have hh := congrArg p' hn
    simpa only [Submonoid.smul_def,map_smul,←LinearMap.comp_apply,hp'i',
      LinearMap.id_apply,←hfp] using hh
  exists_of_eq {x y} h := by
    have hh : g (i x) = g (i y) := by
      change (g.comp i) x = (g.comp i) y
      rw [hgi]
      exact congrArg i' h
    obtain ⟨s,hs⟩ := IsLocalizedModule.exists_of_eq (S := S) hh
    refine ⟨s,?_⟩
    have he := congrArg p hs
    simpa only [Submonoid.smul_def,map_smul,←LinearMap.comp_apply,hpi,
      LinearMap.id_apply] using he
end Retract

open CategoryTheory
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (M : Type*) [AddCommGroup M] [Module R M]
  [Module.Projective R M] [Module.Finite R M]

lemma projective_baseChange : Module.Projective A (A ⊗[R] M) := by
  obtain ⟨n,p,i,_,_,hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact Module.Projective.of_split (i.baseChange A) (p.baseChange A)
    (by rw [←LinearMap.baseChange_comp,hpi,LinearMap.baseChange_id])

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

lemma baseChangeHom_localized_projective (U : Submonoid R) [IsLocalization U A]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Finite R M] :
    IsLocalizedModule U (LinearMap.baseChangeHom R A M N) := by
  obtain ⟨n,p,i,_,_,hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hfree : IsLocalizedModule U (LinearMap.baseChangeHom R A (Fin n → R) N) :=
    (isLocalizedModule_iff_isBaseChange U A _).mpr
      (baseChangeHom_isBaseChange (ModuleCat.of R (Fin n → R)) (ModuleCat.of R N))
  apply localizedModule_retract U (LinearMap.baseChangeHom R A M N)
    (LinearMap.baseChangeHom R A (Fin n → R) N)
    (precompLinear p) (precompLinear i)
    ((precompLinear (p.baseChange A)).restrictScalars R)
    ((precompLinear (i.baseChange A)).restrictScalars R)
  · ext f x
    change f (p (i x)) = f x
    exact congrArg f (LinearMap.congr_fun hpi x)
  · apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change f ((p.baseChange A) ((i.baseChange A) x)) = f x
    have h : (p.baseChange A).comp (i.baseChange A) = LinearMap.id := by
      rw [←LinearMap.baseChange_comp,hpi,LinearMap.baseChange_id]
    exact congrArg f (LinearMap.congr_fun h x)
  · apply LinearMap.ext
    intro f
    change (f.comp p).baseChange A = (f.baseChange A).comp (p.baseChange A)
    exact LinearMap.baseChange_comp p f
  · apply LinearMap.ext
    intro f
    change (f.comp i).baseChange A = (f.baseChange A).comp (i.baseChange A)
    exact LinearMap.baseChange_comp i f

lemma baseChangeFunctor_map_localized_projective (U : Submonoid R) [IsLocalization U A]
    (M N : ModuleCat.{u} R) [Module.Projective R M] [Module.Finite R M] :
    IsLocalizedModule U ((baseChangeFunctor R A).mapLinearMap R (X := M) (Y := N)) := by
  have := baseChangeHom_localized_projective (A := A) U M N
  change IsLocalizedModule U ((baseChangeHomEquiv R A M N).toLinearMap ∘ₗ
    LinearMap.baseChangeHom R A M N ∘ₗ
      (ModuleCat.homLinearEquiv (M := M) (N := N) (S := R)).toLinearMap)
  infer_instance

 

lemma baseChange_projective_contractible (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, b < j → IsZero (F.X j))
    (ha : ((baseChangeFunctor R A).mapHomologicalComplex _ |>.obj F).Acyclic) :
    Nonempty (Homotopy (𝟙 ((baseChangeFunctor R A).mapHomologicalComplex _ |>.obj F)) 0) := by
  let T := baseChangeFunctor R A
  let L : CochainComplex (ModuleCat.{u} A) ℤ := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have : L.IsStrictlyLE b := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact T.map_isZero (hb i hi)
  have (i : ℤ) : Projective (L.X i) := by
    have := hp i
    have := hfin i
    have := projective_baseChange (R := R) (A := A) (F.X i)
    change Projective (ModuleCat.of A (A ⊗[R] F.X i))
    infer_instance
  have : L.IsKProjective := isKProjective_of_projective L b
  exact IsKProjective.nonempty_homotopy_zero (𝟙 L) ha
end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechMapCochain
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace Lech
variable {R : Type*} [CommRing R]
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable (T : C ⥤ D) [T.Additive] [T.Linear R]
variable (F G : CochainComplex C ℤ)

lemma map_cochain_smul {n : ℤ} (a : R) (f : Cochain F G n) :
    (a • f).map T = a • f.map T := by
  ext p q hpq
  simp only [Cochain.smul_v, Cochain.map_v, Functor.map_smul]

lemma cochain_surj_away (a : R) (s : Finset ℤ)
    (hb : ∀ p, p ∉ s → IsZero (F.X p))
    (hloc : ∀ p q, IsLocalizedModule.Away a (T.mapLinearMap R (X := F.X p) (Y := G.X q)))
    (n : ℤ) (g : Cochain ((T.mapHomologicalComplex _).obj F)
      ((T.mapHomologicalComplex _).obj G) n) :
    ∃ (N : ℕ) (f : Cochain F G n), a ^ N • g = f.map T := by
  classical
  have h (p : s) := @IsLocalizedModule.Away.surj R _ _ _ _ _ _ _
    (T.mapLinearMap R (X := F.X p) (Y := G.X (p + n))) a
    (hloc p (p + n)) (g.v p (p + n) rfl)
  choose e f hf using h
  let N := s.attach.sup e
  have he (p : s) : e p ≤ N := Finset.le_sup (f := e) (Finset.mem_attach s p)
  refine ⟨N, Cochain.mk (fun p q hpq => ?_), ?_⟩
  · subst q
    exact if hp : p ∈ s then a ^ (N - e ⟨p, hp⟩) • f ⟨p, hp⟩ else 0
  · ext p q hpq
    subst q
    simp only [Cochain.smul_v, Cochain.map_v, Cochain.mk_v]
    by_cases hp : p ∈ s
    · have hf' : a ^ e ⟨p, hp⟩ • g.v p (p + n) rfl = T.map (f ⟨p, hp⟩) := hf ⟨p, hp⟩
      rw [dite_eq_left hp, Functor.map_smul, ← hf', smul_smul,
        ← pow_add, Nat.sub_add_cancel (he ⟨p, hp⟩)]
    · exact (T.map_isZero (hb p hp)).eq_of_src _ _

lemma cochain_eq_zero_away (a : R) (s : Finset ℤ)
    (hb : ∀ p, p ∉ s → IsZero (F.X p))
    (hloc : ∀ p q, IsLocalizedModule.Away a (T.mapLinearMap R (X := F.X p) (Y := G.X q)))
    (n : ℤ) (f : Cochain F G n) (h : f.map T = 0) :
    ∃ N : ℕ, a ^ N • f = 0 := by
  classical
  have hx (p : s) : ∃ N : ℕ, a ^ N • f.v p (p + n) rfl = 0 := by
    have := hloc p (p + n)
    have heq : T.mapLinearMap R (f.v p (p + n) rfl) = T.mapLinearMap R 0 := by
      have h' := Cochain.congr_v h p (p + n) rfl
      simpa only [Functor.coe_mapLinearMap, Cochain.map_v, Cochain.zero_v,
        Functor.map_zero] using h'
    simpa only [smul_zero] using IsLocalizedModule.Away.exists_of_eq a heq
  choose e he using hx
  let N := s.attach.sup e
  have heN (p : s) : e p ≤ N := Finset.le_sup (f := e) (Finset.mem_attach s p)
  refine ⟨N, ?_⟩
  ext p q hpq
  subst q
  simp only [Cochain.smul_v, Cochain.zero_v]
  by_cases hp : p ∈ s
  · rw [← Nat.sub_add_cancel (heN ⟨p, hp⟩), pow_add, mul_smul, he ⟨p, hp⟩, smul_zero]
  · exact (hb p hp).eq_of_src _ _

lemma ofHom_smul {F G : CochainComplex C ℤ} (f : F ⟶ G) (a : R) :
    Cochain.ofHom (a • f) = a • Cochain.ofHom f := by
  ext p
  simp

lemma nullhomotopy_away (a : R) (s : Finset ℤ)
    (hb : ∀ p, p ∉ s → IsZero (F.X p))
    (hloc : ∀ p q, IsLocalizedModule.Away a (T.mapLinearMap R (X := F.X p) (Y := F.X q)))
    (h : Homotopy (𝟙 ((T.mapHomologicalComplex _).obj F)) 0) :
    ∃ N : ℕ, Nonempty (Homotopy (a ^ N • 𝟙 F) 0) := by
  obtain ⟨N, f, hf⟩ := cochain_surj_away T F F a s hb hloc (-1) (Cochain.ofHomotopy h)
  have he : (δ (-1) 0 f - a ^ N • Cochain.ofHom (𝟙 F)).map T = 0 := by
    rw [Cochain.map_sub, ← δ_map, ← hf, δ_smul, δ_ofHomotopy, Cochain.ofHom_zero, sub_zero,
      map_cochain_smul, Cochain.map_ofHom, CategoryTheory.Functor.map_id, sub_self]
  obtain ⟨M, hM⟩ := cochain_eq_zero_away T F F a s hb hloc 0 _ he
  refine ⟨M + N, ⟨(Cochain.equivHomotopy _ _).symm ⟨a ^ M • f, ?_⟩⟩⟩
  rw [smul_sub, sub_eq_zero] at hM
  rw [ofHom_smul, δ_smul, hM, smul_smul, ← pow_add, Cochain.ofHom_zero, add_zero]

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u
variable {R : Type u} [CommRing R]
 

lemma nullhomotopy_of_projective_acyclic_away (a : R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < l ∨ b < j → IsZero (F.X j))
    (ha : ((baseChangeFunctor R (Localization.Away a)).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ N : ℕ, Nonempty (Homotopy (a ^ N • 𝟙 F) 0) := by
  obtain ⟨h⟩ := baseChange_projective_contractible (A := Localization.Away a) F b hp hfin
    (fun j hj => hb j (Or.inr hj)) ha
  apply nullhomotopy_away (baseChangeFunctor R (Localization.Away a)) F a (Finset.Icc l b)
    (fun j hj => hb j (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hj)) _ h
  intro p q
  have := hp p
  have := hfin p
  exact baseChangeFunctor_map_localized_projective (A := Localization.Away a)
    (Submonoid.powers a) (F.X p) (F.X q)
end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 

lemma uniform_nullhomotopy_of_projective_acyclic_away {h : ℕ} (z : Fin h → R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < l ∨ b < j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ m : ℕ, ∀ i, Nonempty (Homotopy (z i ^ m • 𝟙 F) 0) := by
  classical
  have hh (i : Fin h) := nullhomotopy_of_projective_acyclic_away (z i) F l b hp hfin hb (ha i)
  choose N H using hh
  refine ⟨∑ i, N i, ?_⟩
  intro i
  have hi : N i ≤ ∑ j, N j := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  have HH := (H i).some.smul (z i ^ ((∑ j, N j) - N i))
  rw [smul_smul,←pow_add,Nat.sub_add_cancel hi,smul_zero] at HH
  exact ⟨HH⟩
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

lemma tensor_homology_torsion (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    powerTorsion (entryIdeal zs) ((tensor zs F).homology i) :=
  ⟨1, by simpa using tensor_homology_annihilator zs F i⟩

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex

open scoped BigOperators


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u
variable {R : Type u} [CommRing R]

lemma entryIdeal_ofFn {h : ℕ} (z : Fin h → R) :
    entryIdeal (List.ofFn z) = Ideal.span (Set.range z) := by
  unfold entryIdeal
  congr 1
  ext x
  exact List.mem_ofFn

end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomologyProp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]



omit [Nontrivial R] in
 

lemma powerTorsion_of_le_radical {I J : Ideal R} (hI : I.FG) (hIJ : I ≤ J.radical)
    {M : ModuleCat.{u} R} (hM : powerTorsion J M) : powerTorsion I M := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hI
  obtain ⟨m, hm⟩ := hM
  exact ⟨n * m, by rw [pow_mul]; exact (pow_le_pow_left' hn m).trans hm⟩



end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionThickening
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
  (hds : ell.DirectSumZero) (hh : 0<h)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
      a^h • ell.value (ModuleCat.of R (R ⧸ I)))
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap
  TwistedLocalization.gradedMap ImageCech.mapTerm IdealGraded.polynomialMap

variable [Nontrivial R]
include hds hh hmu ha in
lemma finiteThickening_totalTensor_zeroClass (t M : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j,Module.Free R (F.X j)) (hfinite : ∀ j,Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (i : ℤ) :
    ell.zeroClass (((TensorTotal.functor
      ((finiteThickening I z hz t M).extend ComplexShape.embeddingUpNat)).obj F).homology i) := by
  have hK := homology_property_extendUpNat ell.zeroClass (finiteThickening I z hz t M)
    (finiteThickening_homology_zeroClass I z hz ell hds hh hmu ha t M)
  exact TensorTotal.homology_property_of_bounded_free _ ell.zeroClass hK F hfree hfinite m N hb i

include hds hh hmu ha in
lemma thickeningComparison_isoModSerre_torsion
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j,Module.Free R (F.X j)) (hfinite : ∀ j,Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (M : ℕ) (i : ℤ) :
    ell.zeroClass.isoModSerre (thickeningComparison I z hz F M i) := by
  apply ell.zeroClass.isoModSerre.comp_mem
  · exact ell.zeroClass.isoModSerre_of_isIso
      ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
        (thickeningTensorBottomIso I z hz F M)).inv
  · apply TensorTotal.bottomComparison_isoModSerre
    intro j
    exact finiteThickening_totalTensor_zeroClass I z hz ell hds hh hmu ha 0 M F hfree hfinite m N hb j
end Lech.SourceGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionScalarComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ)
theorem cech_homology_value_torsion
    (hds : ell.DirectSumZero)
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (n : ℤ) (d : ℕ) (hb : ∀ j, j<n ∨ n+d≤j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (i : ℤ) :
    ell.value (F.homology i)=ell.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology (i+1)) := by
  classical
  subst I
  let : ∀ j, Module.Free R (F.X j) := hf
  let : ∀ j, Module.Finite R (F.X j) := hfin
  have hp : ∀ j, Module.Projective R (F.X j) := fun j => by have := hf j; infer_instance
  have hbound : ∀ j, j<n ∨ n+d-1<j → IsZero (F.X j) := by
    intro j hj
    apply hb
    omega
  obtain ⟨m,hm⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F n (n+d-1) hp hfin hbound hacyc
  let t := m+1
  have ht : 1≤t := by dsimp [t]; omega
  have H : ∀ j, Homotopy (z j^t • 𝟙 F) 0 := fun j =>
    Koszul.scalarPowerHomotopy F (z j) m t (by dsimp [t]; omega) (hm j).some
  let ℓ := ell
  let P := ℓ.zeroClass
  have hfg : (Ideal.span (Set.range z)).FG := ⟨Finset.univ.image z,by simp⟩
  have hrad (a : ℕ) : Ideal.span (Set.range z) ≤
      (Koszul.entryIdeal (List.ofFn (fun j => z j^a))).radical := by
    rw [entryIdeal_ofFn]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨a,Ideal.subset_span ⟨j,rfl⟩⟩
  have hTF : powerTorsion (Ideal.span (Set.range z)) (F.homology i) := by
    apply powerTorsion_of_le_radical hfg (hrad t)
    refine ⟨1,?_⟩
    rw [pow_one,entryIdeal_ofFn]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Koszul.scalar_annihilates_homology F (z j^t) (H j) i
  have hKos : ∀ a : ℕ, 1≤a → ∀ k : ℤ, k<0 → P ((Koszul.unit (List.ofFn fun j => z j^a)).homology k) := by
    intro a ha k hk
    exact ⟨powerTorsion_of_le_radical hfg (hrad a)
      (Koszul.tensor_homology_torsion _ _ k),hK a ha k hk⟩
  obtain ⟨M₀,hM₀⟩ := ordinaryPower_stableImage_isoMod P F n d hb h z t ht H hKos
  obtain ⟨MD,hMD⟩ := exists_uniform_geometric_stableImage (Ideal.span (Set.range z)) z rfl F
    n (n+d-1) hp hfin hbound hacyc
  let M := max M₀ MD
  obtain ⟨N₀,hMN₀,hN₀⟩ := hM₀ M (le_max_left _ _)
  let N := max N₀ (M+MD)
  have hNN : N₀≤N := le_max_left _ _
  have hMN : M≤N := hMN₀.trans hNN
  have hgap : MD≤N-M := by have := le_max_right N₀ (M+MD); dsimp [N]; omega
  let f := homologyMap ((complexQuotientMap (show Ideal.span (Set.range z)^N ≤ Ideal.span (Set.range z)^M from Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i
  let g := homologyMap ((TensorTotal.Right.functor F).map
    (thickeningCechTransition (Ideal.span (Set.range z)) z rfl hMN)) (i+1)
  let s : Arrow.mk f ⟶ Arrow.mk g := Arrow.homMk
    (thickeningComparison (Ideal.span (Set.range z)) z rfl F N i)
    (thickeningComparison (Ideal.span (Set.range z)) z rfl F M i)
    (thickeningComparison_transition (Ideal.span (Set.range z)) z rfl F hMN i).symm
  have hs₁ : P.isoModSerre s.left :=
    thickeningComparison_isoModSerre_torsion (Ideal.span (Set.range z)) z rfl ell hds hh hmu ha F hf hfin n d hb N i
  have hs₂ : P.isoModSerre s.right :=
    thickeningComparison_isoModSerre_torsion (Ideal.span (Set.range z)) z rfl ell hds hh hmu ha F hf hfin n d hb M i
  have hTQ (c : ℕ) : powerTorsion (Ideal.span (Set.range z))
      (((complexQuotient (Ideal.span (Set.range z)^c) (.up ℤ)).obj F).homology i) := by
    refine ⟨c,?_⟩
    intro r hr
    exact Koszul.scalar_annihilates_homology _ r
      (Homotopy.ofEq (complexQuotient_annihilated _ r hr F)) i
  have hTG : powerTorsion (Ideal.span (Set.range z)) (Arrow.mk g).right := by
    apply (powerTorsion (Ideal.span (Set.range z))).prop_X₂_of_exact
      ((ShortComplex.mk _ _ (cokernel.condition s.right)).exact_of_g_is_cokernel
        (cokernelIsCokernel s.right)) (hTQ M) hs₂.2.1
  have hTFimage := powerTorsion_mono (Ideal.span (Set.range z)) (Limits.image.ι f) (hTQ M)
  have hTGimage := powerTorsion_mono (Ideal.span (Set.range z)) (Limits.image.ι g) hTG
  have hab : ℓ.value (F.homology i)=ℓ.value (Limits.image f) :=
    ℓ.eq_of_isoModSerre _ hTF hTFimage (hN₀ N hNN i)
  have hbc : ℓ.value (Limits.image f)=ℓ.value (Limits.image g) :=
    ℓ.image_value_eq s hs₁ hs₂ (hTQ M) hTG
  have hg := hMD M N hMN (le_max_right _ _) hgap (i+1)
  have hdc : ℓ.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive (Ideal.span (Set.range z)) z (coordinate_mem _ z rfl) 0)).homology (i+1))=
      ℓ.value (Limits.image g) :=
    ℓ.eq_of_iso (asIso (homologyMap (geometricStructureMap (Ideal.span (Set.range z)) z rfl F N) (i+1) ≫
      factorThruImage g))
      (FilteredCech.positive_homology_powerTorsion (Ideal.span (Set.range z)) z
        (coordinate_mem _ z rfl) F n (n+d-1) hp hfin hbound hacyc 0 (i+1)) hTGimage
  exact hab.trans (hbc.trans hdc.symm)
end Lech.SourceGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)


variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

variable [Nontrivial R] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha hK hf hfin hb hac in
theorem scalarHomology_value_oai (i : ℤ) :
    ell.value ((tensorCech F (scalarCechDiagram I z hz)).homology i)=ell.value (F.homology i) := by
  have hp : ∀ p,Module.Projective R (F.X p) := fun p => by have := hf p; infer_instance
  have ht : powerTorsion I (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive I z hz 0)).homology (i+1)) :=
    FilteredCech.positive_homology_powerTorsion I z hz F (-(n+1:ℤ)) 0 hp hfin hb hac 0 (i+1)
  have he := ell.eq_of_iso (scalarHomologyIso I z hz F i)
    ((powerTorsion I).prop_of_iso (scalarHomologyIso I z hz F i).symm ht) ht
  refine he.trans ?_
  symm
  exact SourceGraded.cech_homology_value_torsion I z hgen ell F hds (by omega) hmu ha hK hf hfin
    (-(n+1:ℤ)) (n+2) (by intro p hp; apply hb; omega) hac i

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.scalarHomology_value_oai.{u} := @OAI.Lech.ReesRoot.scalarHomology_value_oai.{u}
