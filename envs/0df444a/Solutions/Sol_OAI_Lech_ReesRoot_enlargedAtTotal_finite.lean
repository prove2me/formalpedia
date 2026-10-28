-- Prove2me | solution 1 for OAI.Lech.ReesRoot.enlargedAtTotal_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:45:41.653512+00:00
-- url     : https://prove2.me/submissions/bf658b9f-ed61-4b3f-b293-8b7459e39e3c

import Mathlib
import Definitions.Def_OAIQ032L039
import Theorems.Thm_OAI_Lech_ReesRoot_layerAtTotal_finite
import Theorems.Thm_OAI_Lech_ReesRoot_uniform_unit_nilpotence

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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

 

lemma cokernel_comp_shortExact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (kernelCokernelCompSequence.snakeInput f g).L₃.ShortExact where
  exact := (kernelCokernelCompSequence.snakeInput f g).L₃_exact
  mono_f := (kernelCokernelCompSequence.snakeInput f g).L₂'_exact.mono_g
    ((isZero_kernel_of_mono g).eq_of_src _ _)
  epi_g := by
    change Epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
    infer_instance



lemma cokernel_homology_property_of_shortExact {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i : ι)
    (h : P (S.X₃.homology i)) : P ((cokernel S.f).homology i) :=
  P.prop_of_iso ((homologyFunctor C c i).mapIso (cokernelIsoOfShortExact hS)).symm h

 

lemma homology_middle_property {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i : ι)
    (h₁ : P (S.X₁.homology i)) (h₃ : P (S.X₃.homology i)) : P (S.X₂.homology i) :=
  P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃

 

lemma cokernel_comp_homology_property {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L M : HomologicalComplex C c} (f : K ⟶ L) (g : L ⟶ M) [Mono g]
    (i : ι) (hf : P ((cokernel f).homology i)) (hg : P ((cokernel g).homology i)) :
    P ((cokernel (f ≫ g)).homology i) :=
  homology_middle_property P (cokernel_comp_shortExact f g) i hf hg
end Lech


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


namespace Lech.TotalGhost
open CategoryTheory
universe u v w u' v' w'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma towerPath_map {X : ℕ → C} (f : ∀ n, X (n+1) ⟶ X n) (G : C ⥤ D) (n : ℕ) :
    towerPath (X := fun n => G.obj (X n)) (fun n => G.map (f n)) n=G.map (towerPath f n) := by
  induction n with
  | zero => exact (G.map_id _).symm
  | succ n ih => simpa only [towerPath,Functor.map_comp] using congrArg (fun g => G.map (f n) ≫ g) ih
end Lech.TotalGhost


open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalExact
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]

lemma diagonal_colim_map (k : ℤ) {K L : Double (R:=R)} (f : K ⟶ L) :
    ((diagonal (R:=R) k ⋙ colim).map f) = ((functor (R:=R)).map f).f k := by
  apply total.hom_ext
  intro p q hpq
  change colimit.ι ((diagonal (R:=R) k).obj K) ⟨⟨(p,q),hpq⟩⟩ ≫
    colim.map ((diagonal (R:=R) k).map f) = _
  rw [colimit.ι_map]
  change (f.f p).f q ≫ ιTotal L (.up ℤ) p q k hpq = _
  exact (ιTotal_map K L f (.up ℤ) p q k hpq).symm


lemma total_shortExact (S : ShortComplex (Double (R:=R))) (hS : S.ShortExact) :
    (S.map (functor (R:=R))).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro k
  have h := (hS.map_of_exact (diagonal k)).map_of_exact colim
  apply ShortComplex.shortExact_of_iso (S₁:=((S.map (diagonal k)).map colim)) _ h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom]
    exact diagonal_colim_map k S.f
  · simp only [Iso.refl_hom]
    exact diagonal_colim_map k S.g
end Lech.BicomplexTotal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CartierTowerDevissage
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

lemma mono_cokernel_shortExact {C : Type*} [Category C] [Abelian C]
    {K L : C} (f : K ⟶ L) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

lemma homology_target_property_of_zero (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [Mono f] (i : ℤ)
    (hzero : homologyMap f i=0) (hquot : P ((cokernel f).homology i)) : P (L.homology i) := by
  have hs := mono_cokernel_shortExact f
  have : Mono (homologyMap (cokernel.π f) i) := (hs.homology_exact₂ i).mono_g hzero
  exact P.prop_of_mono (homologyMap (cokernel.π f) i) hquot

namespace TotalGhost
variable {X : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (f : ∀ n,X (n+1) ⟶ X n)
  (hf : ∀ n,Mono (f n))
include hf in
lemma towerPath_mono (N : ℕ) : Mono (towerPath f N) := by
  induction N with
  | zero => exact inferInstanceAs (Mono (𝟙 _))
  | succ N ih =>
      have := hf N
      have := ih
      exact inferInstanceAs (Mono (f N ≫ towerPath f N))

include hf in
lemma towerPath_cokernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (N : ℕ) (i : ℤ) (hl : ∀ n,n<N → P ((cokernel (f n)).homology i)) :
    P ((cokernel (towerPath f N)).homology i) := by
  induction N with
  | zero =>
      exact P.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).map_isZero
        (isZero_cokernel_of_epi (𝟙 (X 0))))
  | succ N ih =>
      have := towerPath_mono f hf N
      exact cokernel_comp_homology_property P (f N) (towerPath f N) i (hl N (by omega))
        (ih (fun n hn => hl n (by omega)))
end TotalGhost
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierZRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (J : Ideal R)
  {M N M' N' : ModuleCat.{u} R} (f : M ⟶ N) (g : M' ⟶ N')
  (e : M' ≅ M) (e' : N' ≅ N)

lemma injective_of_square (hsq : g ≫ e'.hom=e.hom ≫ f)
    (hf : Function.Injective f.hom) : Function.Injective g.hom := by
  intro x y hxy
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  apply hf
  have hx := congrArg (fun a : M' ⟶ N => a.hom x) hsq
  have hy := congrArg (fun a : M' ⟶ N => a.hom y) hsq
  change e'.hom.hom (g.hom x)=f.hom (e.hom.hom x) at hx
  change e'.hom.hom (g.hom y)=f.hom (e.hom.hom y) at hy
  rw [←hx,←hy,hxy]
end Lech.TensorIdeal

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

lemma cechInclusionZ_injective (a : ℕ) (q : ℤ) :
    Function.Injective ((cechInclusionZ I z hz m a).f q).hom := by
  cases q with
  | ofNat q =>
      exact TensorIdeal.injective_of_square _ _ _ _ (cechInclusionZ_square I z hz m a q)
        (cechInclusionIter_injective I z hz m a q)
  | negSucc q =>
      have hzq := cechZ_negative I z hz (raise m a) (Int.negSucc q) (by omega)
      have : Subsingleton ((cechZ I z hz (raise m a)).X (Int.negSucc q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hzq
      exact Function.injective_of_subsingleton _
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredLayers
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {M N : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (J K : Ideal R) (f : M →ₗ[R] N)


lemma restrictIdeal_injective (hf : Function.Injective f) :
    Function.Injective (restrictIdeal K f) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)
end Lech.TensorIdeal

namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) {M N : ModuleCat.{u} R} (f : M ⟶ N)

lemma rowMap_injective [Module.Flat R (F.X p)] (hf : Function.Injective f.hom) :
    Function.Injective ((rowFunctor I F h s hd p).map f).hom := by
  rw [rowMap_eq]
  exact TensorIdeal.restrictIdeal_injective _ _
    (Module.Flat.lTensor_preserves_injective_linearMap f.hom hf)

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootGLayer
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)


variable (hgen : Ideal.span (Set.range z)=I)

lemma enlarged_first_injective (p q : ℤ) [Module.Flat R (F.X p)] :
    Function.Injective (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1)).f p).f q).hom :=
  IdealFiltered.rowMap_injective I F h s hd p _ (cechInclusionZ_injective I z hz m 1 q)

lemma enlargedLayerShortComplex_exact (hflat : ∀ p,Module.Flat R (F.X p)) :
    (enlargedLayerShortComplex I z hz F h s hd m hgen).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro p
  apply shortExact_of_degreewise_shortExact
  intro q
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    change (((layerAtProjection I z hz F h s hd m).f p).f q).hom y=0 at hy
    rw [layerAtProjection_f] at hy
    change Submodule.Quotient.mk y=0 at hy
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hy
    rw [←enlarged_first_range I z hz F h s hd m hgen p q] at hm
    exact hm
  · apply (ModuleCat.mono_iff_injective _).mpr
    let := hflat p
    exact enlarged_first_injective I z hz F h s hd m p q
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (((layerAtProjection I z hz F h s hd m).f p).f q).hom
    rw [layerAtProjection_f]
    exact Submodule.mkQ_surjective _


end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPositivity
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)
  (hflat : ∀ p,Module.Flat R (F.X p))

include hgen hflat in
lemma enlargedStep_total_mono (t : ℕ) :
    Mono (total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ)) :=
  (BicomplexTotal.total_shortExact _
    (enlargedLayerShortComplex_exact I z hz F h s hd (twistSequence m 1 t) hgen hflat)).mono_f

include hgen hflat in
lemma enlargedStep_cokernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (t : ℕ) (i : ℤ)
    (hl : P (((layerAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ)).homology i)) :
    P ((cokernel (total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ))).homology i) :=
  cokernel_homology_property_of_shortExact P
    (BicomplexTotal.total_shortExact _
      (enlargedLayerShortComplex_exact I z hz F h s hd (twistSequence m 1 t) hgen hflat)) i hl

include hgen hflat in
lemma enlargedPath_total_mono (M : ℕ) :
    Mono (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) := by
  have hh := TotalGhost.towerPath_mono
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ))
    (enlargedStep_total_mono I z hz F h s hd m hgen hflat) M
  have he := TotalGhost.towerPath_map
    (X:=fun t => enlargedAt I z hz F h s hd (twistSequence m 1 t))
    (enlargedStep I z hz F h s hd m 1) (BicomplexTotal.functor (R:=R)) M
  change TotalGhost.towerPath
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ)) M =
      total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ) at he
  rwa [he] at hh

include hgen hflat in
lemma enlargedPath_cokernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (M : ℕ) (i : ℤ)
    (hl : ∀ t,t<M → P (((layerAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ)).homology i)) :
    P ((cokernel (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ))).homology i) := by
  have hh := TotalGhost.towerPath_cokernel_property
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ))
    (enlargedStep_total_mono I z hz F h s hd m hgen hflat) P M i
    (fun t ht => enlargedStep_cokernel_property I z hz F h s hd m hgen hflat P t i (hl t ht))
  have he := TotalGhost.towerPath_map
    (X:=fun t => enlargedAt I z hz F h s hd (twistSequence m 1 t))
    (enlargedStep I z hz F h s hd m 1) (BicomplexTotal.functor (R:=R)) M
  change TotalGhost.towerPath
    (X:=fun t => (enlargedAt I z hz F h s hd (twistSequence m 1 t)).total (.up ℤ))
    (fun t => total.map (enlargedStep I z hz F h s hd m 1 t) (.up ℤ)) M =
      total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ) at he
  rwa [he] at hh

variable [LinearOrder (Chart n)] (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hflat hds hmu ha B hp hfin hb hac in
 
theorem enlargedAtTotal_finite_oai (i : ℤ) :
    ell.finiteClass (((enlargedAt I z hz F h s hd m).total (.up ℤ)).homology i) := by
  obtain ⟨M,hM,hzero⟩ := uniform_unit_nilpotence I z hz F h s hd hgen hp hfin hflat hb hac
  have := enlargedPath_total_mono I z hz F h s hd m hgen hflat M
  apply homology_target_property_of_zero ell.finiteClass
    (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) i (hzero m i)
  apply enlargedPath_cokernel_property I z hz F h s hd m hgen hflat
  intro t ht
  exact layerAtTotal_finite I z hz _ hgen ell hds hmu ha F h s hd b B hflat hb i


end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.enlargedAtTotal_finite_oai.{u} := @OAI.Lech.ReesRoot.enlargedAtTotal_finite_oai.{u}
