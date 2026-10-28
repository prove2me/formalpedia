-- Prove2me | solution 1 for OAI.Lech.ordinaryPower_stableImage_isoMod
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:19:01.991974+00:00
-- url     : https://prove2.me/submissions/7e6c2767-c443-40f5-a39e-f3f152378a50

import Mathlib
import Definitions.Def_OAIQ032L011
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

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

end


universe u
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ActualCechTranspose
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech

section

section
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


lemma quasiIso_middle {S T : ShortComplex (CochainComplex C ℤ)}
    (f : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    [QuasiIso f.τ₁] [QuasiIso f.τ₃] : QuasiIso f.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hprev : (ComplexShape.up ℤ).Rel (i-1) i := by change i - 1 + 1 = i; omega
  have hnext : (ComplexShape.up ℤ).Rel i (i+1) := rfl
  have hm : Mono (homologyMap f.τ₂ i) :=
    mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ f hS hT (i-1) i hprev))
      (composableArrows₅_exact hS (i-1) i hprev).δ₀.δ₀
      (composableArrows₅_exact hT (i-1) i hprev).δ₀.δ₀
      (inferInstanceAs (Epi (homologyMap f.τ₃ (i-1))))
      (inferInstanceAs (Mono (homologyMap f.τ₁ i)))
      (inferInstanceAs (Mono (homologyMap f.τ₃ i)))
  have he : Epi (homologyMap f.τ₂ i) :=
    epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ f hS hT i (i+1) hnext))
      (composableArrows₅_exact hS i (i+1) hnext).δlast.δlast
      (composableArrows₅_exact hT i (i+1) hnext).δlast.δlast
      (inferInstanceAs (Epi (homologyMap f.τ₁ i)))
      (inferInstanceAs (Epi (homologyMap f.τ₃ i)))
      (inferInstanceAs (Mono (homologyMap f.τ₁ (i+1))))
  exact isIso_of_mono_of_epi _

end


open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma quasiIsoAt_localization_iff {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) :
    let Q := P.isoModSerre.Q
    let := ObjectProperty.SerreClassLocalization.abelian Q P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
    QuasiIsoAt ((Q.mapHomologicalComplex c).map f) i ↔
      P.isoModSerre (HomologicalComplex.homologyMap f i) := by
  dsimp only
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  let S := K.sc i
  let T := L.sc i
  let g := (HomologicalComplex.shortComplexFunctor C c i).map f
  rw [quasiIsoAt_iff]
  change ShortComplex.QuasiIso (Q.mapShortComplex.map g) ↔ _
  rw [ShortComplex.quasiIso_iff]
  rw [← ObjectProperty.SerreClassLocalization.isIso_map_iff Q P]
  let h0 : (S.map Q).homology ⟶ (T.map Q).homology := ShortComplex.homologyMap (Q.mapShortComplex.map g)
  change IsIso h0 ↔ IsIso (Q.map (ShortComplex.homologyMap g))
  have he : h0 ≫ (T.mapHomologyIso Q).hom = (S.mapHomologyIso Q).hom ≫ Q.map (ShortComplex.homologyMap g) :=
    ShortComplex.mapHomologyIso_hom_naturality g Q
  have hfact : Q.map (ShortComplex.homologyMap g) =
      (S.mapHomologyIso Q).inv ≫ h0 ≫ (T.mapHomologyIso Q).hom := by
    rw [he, Iso.inv_hom_id_assoc]
  rw [hfact, isIso_comp_left_iff, isIso_comp_right_iff]


lemma homology_middle_isoModSerre (P : ObjectProperty C) [P.IsSerreClass]
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁ : ∀ i, P.isoModSerre (HomologicalComplex.homologyMap f.τ₁ i))
    (h₃ : ∀ i, P.isoModSerre (HomologicalComplex.homologyMap f.τ₃ i)) (i : ℤ) :
    P.isoModSerre (HomologicalComplex.homologyMap f.τ₂ i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  let F := Q.mapHomologicalComplex (ComplexShape.up ℤ)
  have : QuasiIso (F.map f.τ₁) := by
    rw [quasiIso_iff]
    intro j
    exact (quasiIsoAt_localization_iff P f.τ₁ j).mpr (h₁ j)
  have : QuasiIso (F.map f.τ₃) := by
    rw [quasiIso_iff]
    intro j
    exact (quasiIsoAt_localization_iff P f.τ₃ j).mpr (h₃ j)
  have heS : (S.map F).ShortExact := hS.map_of_exact F
  have heT : (T.map F).ShortExact := hT.map_of_exact F
  have : QuasiIso (F.mapShortComplex.map f).τ₁ :=
    inferInstanceAs (QuasiIso (F.map f.τ₁))
  have : QuasiIso (F.mapShortComplex.map f).τ₃ :=
    inferInstanceAs (QuasiIso (F.map f.τ₃))
  have : QuasiIso (F.map f.τ₂) :=
    quasiIso_middle (F.mapShortComplex.map f) heS heT
  exact (quasiIsoAt_localization_iff P f.τ₂ i).mp (inferInstanceAs (QuasiIsoAt (F.map f.τ₂) i))

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmentationRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.moduleQuotient_linear _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [CommRing R]



lemma complexQuotient_shortExact (I : Ideal R) {ι : Type*} {c : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c))
    (σ : ∀ i, (S.map (HomologicalComplex.eval (ModuleCat.{v} R) c i)).Splitting) :
    (S.map (complexQuotient I c)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ((σ i).map (moduleQuotient I)).shortExact

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedThickeningNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v
variable {R : Type*} [CommRing R]
 

lemma stableImage_isIso {A B C : ModuleCat.{v} R} (u : A ⟶ B) (v : A ⟶ C)
    (f : B ⟶ C) (h : u ≫ f = v) (hv : Function.Injective v)
    (hr : LinearMap.range f.hom = LinearMap.range v.hom) :
    IsIso (u ≫ factorThruImage f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have he : u ≫ factorThruImage f ≫ Limits.image.ι f = v := by rw [Limits.image.fac, h]
  constructor
  · intro x y hxy
    apply hv
    have hx := congrArg (fun g => g x) he
    have hy := congrArg (fun g => g y) he
    exact hx.symm.trans ((congrArg (Limits.image.ι f) hxy).trans hy)
  · intro y
    have hy : (Limits.image.ι f) y ∈ LinearMap.range v.hom := by
      rw [← hr]
      have he' := congrArg (fun g => g y) (ModuleCat.imageIsoRange_hom_subtype f)
      exact he' ▸ ((ModuleCat.imageIsoRange f).hom y).property
    obtain ⟨x,hx⟩ := hy
    refine ⟨x, ?_⟩
    apply (ModuleCat.mono_iff_injective (Limits.image.ι f)).mp inferInstance
    have hx' := congrArg (fun g => g x) he
    exact hx'.trans hx

end Lech


open CochainComplex CochainComplex.HomComplex
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
universe u v
variable {R : Type u} [CommRing R]


lemma inclusion_homology_injective
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (H : ∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) (i : ℤ) :
    Function.Injective (HomologicalComplex.homologyMap (inclusion F zs) i) := by
  have he := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (inclusion_retraction F zs H)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at he
  intro x y hxy
  have hx := congrArg (fun f => f x) he
  have hy := congrArg (fun f => f y) he
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
  rw [← hx, ← hy, hxy]


lemma powerMap_comp (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (zs : List R) :
    powerMap F a c (hab.trans hbc) zs =
      powerMap F b c hbc zs ≫ powerMap F a b hab zs := by
  induction zs with
  | nil => exact (Category.id_comp _).symm
  | cons r zs ih =>
    have hc := mappingCone.map_comp
      (r^c • 𝟙 (tensor (zs.map (· ^ c)) F))
      (r^b • 𝟙 (tensor (zs.map (· ^ b)) F))
      (r^a • 𝟙 (tensor (zs.map (· ^ a)) F))
      (r^(c-b) • powerMap F b c hbc zs) (powerMap F b c hbc zs)
      (by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
            Category.comp_id, smul_smul]
          rw [← pow_add, Nat.add_sub_of_le hbc])
      (r^(b-a) • powerMap F a b hab zs) (powerMap F a b hab zs)
      (by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
            Category.comp_id, smul_smul]
          rw [← pow_add, Nat.add_sub_of_le hab])
    refine Eq.trans ?_ hc
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul,
      ← pow_add, show b-a+(c-b) = c-a by omega, ← ih]
    rfl




lemma homology_middle_range_le {ι : Type*} {c : ComplexShape ι} {S T : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)}
    (f : S ⟶ T) (hT : T.ShortExact) (i : ι)
    (hzero : HomologicalComplex.homologyMap f.τ₃ i = 0) :
    LinearMap.range (HomologicalComplex.homologyMap f.τ₂ i).hom ≤
      LinearMap.range (HomologicalComplex.homologyMap T.f i).hom := by
  rw [(hT.homology_exact₂ i).moduleCat_range_eq_ker]
  rintro _ ⟨x,rfl⟩
  have he : HomologicalComplex.homologyMap f.τ₂ i ≫
      HomologicalComplex.homologyMap T.g i = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, f.comm₂₃,
      HomologicalComplex.homologyMap_comp, hzero, comp_zero]
  exact congrArg (fun a => a x) he



lemma powerMap_range_le_inr
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (r : R) (zs : List R)
    (a b t : ℕ) (hab : a ≤ b) (ht : t ≤ b-a)
    (H : Homotopy (r^t • 𝟙 F) 0) (i : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap (powerMap F a b hab (r::zs)) i).hom ≤
      LinearMap.range (HomologicalComplex.homologyMap
        (mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F)) ) i).hom := by
  let f := powerMap F a b hab zs
  let H' := tensorScalarHomotopy (r^t) (zs.map (· ^ b)) H
  let H'' := (scalarPowerHomotopy _ r t (b-a) ht H').compRight f
  let φ := coneShortComplexMap (r^b • 𝟙 _) (r^a • 𝟙 _)
    (r^(b-a) • f) f (by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        Category.comp_id, smul_smul]
      rw [← pow_add, Nat.add_sub_of_le hab])
  have hz : HomologicalComplex.homologyMap φ.τ₃ i = 0 := by
    have HH : Homotopy (r^(b-a) • f) 0 := by
      simpa only [Linear.smul_comp, Category.id_comp, zero_comp] using H''
    have he := (HH.shift (1 : ℤ)).homologyMap_eq i
    simp only [φ, coneShortComplexMap]
    change HomologicalComplex.homologyMap
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (1 : ℤ)).map
        (r^(b-a) • f)) i = 0
    simpa only [Functor.map_zero, HomologicalComplex.homologyMap_zero] using he
  apply homology_middle_range_le φ (coneShortComplex_shortExact _) i hz

 

lemma powerMap_range_eq
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) (t : ℕ)
    (H : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0)
    (a b : ℕ) (hab : a ≤ b) (hgap : zs.length * t ≤ b-a) (i : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap (powerMap F a b hab zs) i).hom =
      LinearMap.range (HomologicalComplex.homologyMap
        (inclusion F (zs.map (· ^ a))) i).hom := by
  induction zs generalizing a b with
  | nil => rfl
  | cons r zs ih =>
    let m := a + zs.length * t
    have ham : a ≤ m := by omega
    have hmb : m ≤ b := by simp only [List.length_cons, Nat.add_mul, one_mul] at hgap; dsimp [m]; omega
    have htm : t ≤ b-m := by simp only [List.length_cons, Nat.add_mul, one_mul] at hgap; dsimp [m]; omega
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      have hx := powerMap_range_le_inr F r zs m b t hmb htm (H r (by simp)) i
        (show _ ∈ LinearMap.range
          (HomologicalComplex.homologyMap (powerMap F m b hmb (r::zs)) i).hom from ⟨x,rfl⟩)
      obtain ⟨y,hy⟩ := hx
      have hinner := ih (fun s hs => H s (by simp [hs])) a m ham (by dsimp [m]; omega)
      have hy' := hinner ▸ (show _ ∈ LinearMap.range
          (HomologicalComplex.homologyMap (powerMap F a m ham zs) i).hom from ⟨y,rfl⟩)
      obtain ⟨z,hz⟩ := hy'
      refine ⟨z, ?_⟩
      have hc := congrArg (fun f => HomologicalComplex.homologyMap f i)
        (powerMap_comp F a m b ham hmb (r::zs))
      have hn : mappingCone.inr (r^m • 𝟙 (tensor (zs.map (· ^ m)) F)) ≫
          powerMap F a m ham (r::zs) =
          powerMap F a m ham zs ≫ mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F)) := by
        change mappingCone.inr _ ≫ mappingCone.map _ _ _ _ _ = _
        simp [mappingCone.map]
      have hn' := congrArg (fun f => HomologicalComplex.homologyMap f i) hn
      simp only [HomologicalComplex.homologyMap_comp] at hc
      change (HomologicalComplex.homologyMap
        (inclusion F (zs.map (· ^ a)) ≫ mappingCone.inr _) i).hom z = _
      rw [HomologicalComplex.homologyMap_comp]
      change (HomologicalComplex.homologyMap
        (mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F))) i).hom
        ((HomologicalComplex.homologyMap (inclusion F (zs.map (· ^ a))) i).hom z) = _
      rw [hz, hc]
      change _ = (HomologicalComplex.homologyMap (powerMap F a m ham (r::zs)) i)
        ((HomologicalComplex.homologyMap (powerMap F m b hmb (r::zs)) i) x)
      rw [← hy]
      exact (congrArg (fun f => f y) (HomologicalComplex.homologyMap_comp
        (powerMap F a m ham zs)
        (mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F))) i)).symm.trans
          ((congrArg (fun f => f y) hn').symm.trans
            (congrArg (fun f => f y) (HomologicalComplex.homologyMap_comp
              (mappingCone.inr (r^m • 𝟙 (tensor (zs.map (· ^ m)) F)))
              (powerMap F a m ham (r::zs)) i)))
    · rintro _ ⟨x,rfl⟩
      refine ⟨(HomologicalComplex.homologyMap
        (inclusion F ((r::zs).map (· ^ b))) i) x, ?_⟩
      have he := congrArg (fun f => HomologicalComplex.homologyMap f i)
        (powerMap_inclusion F a b hab (r::zs))
      simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply] using
        congrArg (fun f => f x) he




end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechNatTrans
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.instAdditiveCochainComplexIntTensorFunctor_1 _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.Koszul.tensorFunctor_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open scoped ZeroObject
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

lemma natTrans_homology_isoMod_of_iso (P : ObjectProperty D) [P.IsSerreClass]
    {A B : CochainComplex C ℤ ⥤ CochainComplex D ℤ} (α : A ⟶ B)
    {F G : CochainComplex C ℤ} (e : F ≅ G)
    (hF : ∀ i, P.isoModSerre (homologyMap (α.app F) i)) (i : ℤ) :
    P.isoModSerre (homologyMap (α.app G) i) := by
  have he : α.app G = A.map e.inv ≫ α.app F ≫ B.map e.hom := by
    rw [← α.naturality e.hom, ← Category.assoc, ← Functor.map_comp,
      e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [he, homologyMap_comp, homologyMap_comp]
  exact P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _)
    (P.isoModSerre.comp_mem _ _ (hF i) (P.isoModSerre_of_isIso _))

 

lemma bounded_natTrans_homology_isoMod (P : ObjectProperty D) [P.IsSerreClass]
    (A B : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [A.Additive] [B.Additive]
    (α : A ⟶ B)
    (hA : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (.up ℤ) j)).Splitting) → (S.map A).ShortExact)
    (hB : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (.up ℤ) j)).Splitting) → (S.map B).ShortExact)
    (F : CochainComplex C ℤ) (n : ℤ) (h : ℕ)
    (hsupp : ∀ i, i < n ∨ n + h ≤ i → IsZero (F.X i))
    (hterms : ∀ j i, P.isoModSerre (homologyMap
      (α.app ((single C (.up ℤ) j).obj (F.X j))) i)) (i : ℤ) :
    P.isoModSerre (homologyMap (α.app F) i) := by
  let Q : ObjectProperty (CochainComplex C ℤ) := fun F =>
    ∀ i, P.isoModSerre (homologyMap (α.app F) i)
  have : Q.ContainsZero := ⟨0, isZero_zero _, by
    intro i
    have hAz := (homologyFunctor D (.up ℤ) i).map_isZero
      (A.map_isZero (isZero_zero _))
    have hBz := (homologyFunctor D (.up ℤ) i).map_isZero
      (B.map_isZero (isZero_zero _))
    have : IsIso (homologyMap (α.app 0) i) := hAz.isIso hBz _
    exact P.isoModSerre_of_isIso _⟩
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e hF =>
    natTrans_homology_isoMod_of_iso P α e hF⟩
  apply FiniteComplex.devissage Q ?_ n h F hsupp hterms i
  intro S σ h₁ h₃ j
  let φ : S.map A ⟶ S.map B :=
    { τ₁ := α.app S.X₁, τ₂ := α.app S.X₂, τ₃ := α.app S.X₃
      comm₁₂ := (α.naturality S.f).symm
      comm₂₃ := (α.naturality S.g).symm }
  exact homology_middle_isoModSerre P φ (hA S σ) (hB S σ) h₁ h₃ j

end Lech


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]



lemma quotientAugmentation_bounded
    (P : ObjectProperty (ModuleCat.{v} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) (n : ℤ) (h : ℕ)
    (hsupp : ∀ i, i < n ∨ n+h ≤ i → IsZero (F.X i))
    (hterms : ∀ j i, P.isoModSerre (homologyMap (quotientAugmentation
      ((single (ModuleCat.{v} R) (.up ℤ) j).obj (F.X j)) zs) i)) (i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation F zs) i) := by
  apply bounded_natTrans_homology_isoMod P (tensorFunctor zs)
    (complexQuotient (entryIdeal zs) (.up ℤ)) (quotientAugmentationNat zs)
    _ _ F n h hsupp hterms i
  · intro S σ
    exact HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun j => (tensorSplitting zs S σ j).shortExact)
  · exact complexQuotient_shortExact (entryIdeal zs)




end Lech.Koszul


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v w

 

lemma isIso_app_of_finite_retract
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (A B : C ⥤ D) [A.Additive] [B.Additive] (α : A ⟶ B)
    (X Y : C) {ι : Type*} [Fintype ι] (s : ι → (X ⟶ Y)) (r : ι → (Y ⟶ X))
    (hs : ∑ i, s i ≫ r i = 𝟙 X) [IsIso (α.app Y)] : IsIso (α.app X) := by
  classical
  let β : B.obj X ⟶ A.obj X := ∑ i, B.map (s i) ≫ inv (α.app Y) ≫ A.map (r i)
  refine ⟨⟨β, ?_, ?_⟩⟩
  · dsimp [β]
    rw [Preadditive.comp_sum]
    have h : ∀ i, α.app X ≫ (B.map (s i) ≫ inv (α.app Y) ≫ A.map (r i)) =
        A.map (s i ≫ r i) := by
      intro i
      rw [← Category.assoc, ← α.naturality, Category.assoc,
        IsIso.hom_inv_id_assoc, ← Functor.map_comp]
    simp_rw [h]
    rw [← A.map_sum, hs, A.map_id]
  · dsimp [β]
    rw [Preadditive.sum_comp]
    have h : ∀ i, (B.map (s i) ≫ inv (α.app Y) ≫ A.map (r i)) ≫ α.app X =
        B.map (s i ≫ r i) := by
      intro i
      rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc,
        ← Functor.map_comp]
    simp_rw [h]
    rw [← B.map_sum, hs, B.map_id]

 
lemma basis_finite_retract {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] {ι : Type w} [Fintype ι] (b : Module.Basis ι R M) :
    ∑ i, (ModuleCat.ofHom (b.coord i)) ≫
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) =
      𝟙 (ModuleCat.of R M) := by
  classical
  ext x
  simp

 

lemma isIso_app_of_finite_free
    {R : Type u} [CommRing R] {D : Type*} [Category D] [Preadditive D]
    (A B : ModuleCat.{u} R ⥤ D) [A.Additive] [B.Additive] (α : A ⟶ B)
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    [IsIso (α.app (ModuleCat.of R R))] : IsIso (α.app M) := by
  let b := Module.Free.chooseBasis R M
  let := Module.Free.ChooseBasisIndex.fintype R M
  exact isIso_app_of_finite_retract A B α M (ModuleCat.of R R)
    (fun i => ModuleCat.ofHom (b.coord i))
    (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))
    (basis_finite_retract b)

end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.instAdditiveCochainComplexIntTensorFunctor_1 _root_.OAI.Lech.Koszul.moduleQuotient_linear _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.Koszul.tensorFunctor_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 

lemma augmentation_scalar_isoMod (P : ObjectProperty (ModuleCat.{u} R))
    [P.IsSerreClass] (zs : List R)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit zs).homology i)) (j i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation
      ((single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)) zs) i) := by
  let F := (single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)
  have hF : ∀ k, j < k → IsZero (F.X k) := fun k hk =>
    isZero_single_obj_X (.up ℤ) j _ k (by omega)
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hK : P ((tensor zs F).homology i) :=
      (P.prop_iff_of_iso (tensorSingleHomologyIso zs (ModuleCat.of R R) j i)).mpr
        (hKos (i-j) (by omega))
    have hG : IsZero (((complexQuotient (entryIdeal zs) (.up ℤ)).obj F).homology i) :=
      ExactAt.isZero_homology (ExactAt.of_isZero
        ((moduleQuotient (entryIdeal zs)).map_isZero
          (isZero_single_obj_X (.up ℤ) j _ i (by omega))))
    rw [hG.eq_zero_of_tgt (homologyMap (quotientAugmentation F zs) i)]
    exact (P.isoModSerre_zero_iff _ _).mpr ⟨hK, P.prop_of_isZero hG⟩
  · have : IsIso (homologyMap (quotientAugmentation F zs) i) :=
      quotientAugmentation_homology_top F i zs hF rfl
    exact P.isoModSerre_of_isIso _
  · have hK : IsZero ((tensor zs F).homology i) :=
      ExactAt.isZero_homology (ExactAt.of_isZero (tensor_isZero_above F zs j hF i hgt))
    have hG : IsZero (((complexQuotient (entryIdeal zs) (.up ℤ)).obj F).homology i) :=
      ExactAt.isZero_homology (ExactAt.of_isZero
        ((moduleQuotient (entryIdeal zs)).map_isZero (hF i hgt)))
    rw [hG.eq_zero_of_tgt (homologyMap (quotientAugmentation F zs) i)]
    exact (P.isoModSerre_zero_iff _ _).mpr ⟨P.prop_of_isZero hK, P.prop_of_isZero hG⟩

lemma augmentation_free_isoMod (P : ObjectProperty (ModuleCat.{u} R))
    [P.IsSerreClass] (zs : List R)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit zs).homology i))
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] (j i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation
      ((single (ModuleCat.{u} R) (.up ℤ) j).obj M) zs) i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let α := CategoryTheory.Functor.whiskerLeft (single (ModuleCat.{u} R) (.up ℤ) j)
    (CategoryTheory.Functor.whiskerRight (CategoryTheory.Functor.whiskerRight (quotientAugmentationNat zs)
      (homologyFunctor _ (.up ℤ) i)) Q)
  have : IsIso (α.app (ModuleCat.of R R)) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mpr
      (augmentation_scalar_isoMod P zs hKos j i)
  have : IsIso (α.app M) := isIso_app_of_finite_free _ _ α M
  exact (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mp this

 

lemma augmentation_finiteFree_bounded_isoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] (zs : List R)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit zs).homology i))
    (F : CochainComplex (ModuleCat.{u} R) ℤ) [∀ j, Module.Free R (F.X j)]
    [∀ j, Module.Finite R (F.X j)] (n : ℤ) (h : ℕ)
    (hsupp : ∀ i, i < n ∨ n+h ≤ i → IsZero (F.X i)) (i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation F zs) i) := by
  apply quotientAugmentation_bounded P F zs n h hsupp
  intro j k
  exact augmentation_free_isoMod P zs hKos (F.X j) j k

end Lech.Koszul


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma monoModSerre_of_comp (P : ObjectProperty C) [P.IsSerreClass]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : P.monoModSerre (f ≫ g)) : P.monoModSerre f := by
  let k : kernel f ⟶ kernel (f ≫ g) := kernel.lift _ (kernel.ι f) (by simp)
  have hk : k ≫ kernel.ι (f ≫ g) = kernel.ι f := by simp [k]
  let : Mono k := mono_of_mono_fac hk
  exact P.prop_of_mono k h

 
lemma isIso_of_image_factorizations {A B D I : C}
    (u : A ⟶ B) (v : A ⟶ D) [Mono v] (f : B ⟶ D)
    (e : B ⟶ I) [Epi e] (m : I ⟶ D) [Mono m]
    (hfac : e ≫ m = f) (hforward : u ≫ f = v)
    (backward : B ⟶ A) (hbackward : backward ≫ v = f) :
    IsIso (u ≫ e) := by
  have he : (u ≫ e) ≫ m = v := by rw [Category.assoc, hfac, hforward]
  have : Mono (u ≫ e) := mono_of_mono_fac he
  have hb : backward ≫ (u ≫ e) = e := by
    apply (cancel_mono m).mp
    rw [Category.assoc, he, hbackward, hfac]
  have : Epi (u ≫ e) := epi_of_epi_fac hb
  exact isIso_of_mono_of_epi _

 

lemma cofinal_stableImage_isoMod (P : ObjectProperty C) [P.IsSerreClass]
    {A N M Jb Ja : C}
    (iN : A ⟶ N) (iM : A ⟶ M) (ib : A ⟶ Jb) (ia : A ⟶ Ja)
    (f : N ⟶ M) (u : N ⟶ Jb) (v : Jb ⟶ Ja) (w : Ja ⟶ M)
    (hn : iN ≫ f = iM) (hb : ib ≫ v = ia) (ha : ia ≫ w = iM)
    (hfact : u ≫ v ≫ w = f) (hmono : P.monoModSerre iM)
    (hstable : P.isoModSerre (ib ≫ factorThruImage v)) :
    P.isoModSerre (iN ≫ factorThruImage f) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  have : Mono (Q.map iM) :=
    (ObjectProperty.SerreClassLocalization.mono_map_iff Q P _).mpr hmono
  let j := Q.map (ib ≫ factorThruImage v)
  have : IsIso j := (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mpr hstable
  let lift := Q.map (factorThruImage v) ≫ inv j
  have hj : j ≫ Q.map (Limits.image.ι v) = Q.map ia := by
    dsimp only [j]
    rw [← Q.map_comp, Category.assoc, Limits.image.fac, hb]
  have hl : lift ≫ Q.map ia = Q.map v := by
    dsimp only [lift]
    rw [← hj, Category.assoc, IsIso.inv_hom_id_assoc, ← Q.map_comp, Limits.image.fac]
  have hback : (Q.map u ≫ lift) ≫ Q.map iM = Q.map f := by
    rw [← ha, Q.map_comp, Category.assoc, ← Category.assoc lift, hl,
      ← Q.map_comp, ← Q.map_comp]
    simpa only [Category.assoc] using congrArg Q.map hfact
  have hiso : IsIso (Q.map iN ≫ Q.map (factorThruImage f)) :=
    isIso_of_image_factorizations (Q.map iN) (Q.map iM) (Q.map f)
      (Q.map (factorThruImage f)) (Q.map (Limits.image.ι f))
      (by rw [← Q.map_comp, Limits.image.fac]) (by rw [← Q.map_comp, hn])
      (Q.map u ≫ lift) hback
  apply (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mp
  simpa only [Q.map_comp] using hiso

end Lech

open scoped BigOperators
namespace Lech

variable {R : Type*} [CommRing R]

 
lemma sup_pow_add_pred_le (I J : Ideal R) (n m : ℕ) :
    (I ⊔ J) ^ (n + m - 1) ≤ I ^ n ⊔ J ^ m := by
  rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left))
  · refine Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right))
    omega

 
lemma finset_sup_pow_le {ι : Type*} (s : Finset ι) (I : ι → Ideal R)
    (a : ℕ) (ha : 1 ≤ a) :
    s.sup I ^ (s.card * (a - 1) + 1) ≤ s.sup (fun j => I j ^ a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj hs =>
    rw [Finset.sup_insert, Finset.sup_insert, Finset.card_insert_of_notMem hj]
    have he : (s.card + 1) * (a - 1) + 1 = a + (s.card * (a - 1) + 1) - 1 := by
      rw [add_mul, one_mul]
      omega
    rw [he]
    exact (sup_pow_add_pred_le (I j) (s.sup I) a _).trans (sup_le_sup_left hs _)

 

lemma parameter_power_cofinality (h a : ℕ) (ha : 1 ≤ a) (z : Fin h → R) :
    (Ideal.span (Set.range z)) ^ (h * (a - 1) + 1) ≤
      Ideal.span (Set.range fun j => z j ^ a) ∧
    Ideal.span (Set.range fun j => z j ^ a) ≤ (Ideal.span (Set.range z)) ^ a := by
  constructor
  · have H := finset_sup_pow_le Finset.univ (fun j : Fin h => Ideal.span {z j}) a ha
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.sup_univ_eq_iSup,
      Ideal.span_singleton_pow, ← Ideal.span_range_eq_iSup] using H
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) a

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u v
variable {R : Type u} [CommRing R]


lemma quotientAugmentation_power_naturality
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R)
    (a b : ℕ) (hab : a ≤ b) :
    quotientAugmentation F (zs.map (· ^ b)) ≫
        (complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F =
      powerMap F a b hab zs ≫ quotientAugmentation F (zs.map (· ^ a)) := by
  let Ha : ∀ r ∈ zs.map (· ^ a), r • 𝟙 ((complexQuotient
      (entryIdeal (zs.map (· ^ a))) (.up ℤ)).obj F) = 0 := fun r hr =>
    complexQuotient_annihilated _ r (Ideal.subset_span hr) F
  let Hb : ∀ r ∈ zs.map (· ^ b), r • 𝟙 ((complexQuotient
      (entryIdeal (zs.map (· ^ a))) (.up ℤ)).obj F) = 0 := fun r hr =>
    complexQuotient_annihilated _ r
      (entryIdeal_power_antitone zs hab (Ideal.subset_span hr)) F
  simp only [quotientAugmentation]
  let Hbb := fun r hr => complexQuotient_annihilated
    (entryIdeal (zs.map (· ^ b))) r (Ideal.subset_span hr) F
  exact (augmentation_naturality_target
    (complexQuotientπ (entryIdeal (zs.map (· ^ b))) F)
    ((complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F)
    (zs.map (· ^ b)) Hbb Hb).trans
    ((congrArg (fun k => augmentation k (zs.map (· ^ b)) Hb)
      (complexQuotientπ_map (entryIdeal_power_antitone zs hab) F)).trans
      (powerMap_augmentation _ zs a b hab Ha Hb).symm)

 

lemma koszul_stableImage_isIso
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) (t a b : ℕ)
    (H : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0)
    (hta : t ≤ a) (hab : a ≤ b) (hgap : zs.length*t ≤ b-a) (i : ℤ) :
    IsIso (homologyMap (inclusion F (zs.map (· ^ b))) i ≫
      factorThruImage (homologyMap (powerMap F a b hab zs) i)) := by
  classical
  apply stableImage_isIso _ (homologyMap (inclusion F (zs.map (· ^ a))) i)
  · rw [← homologyMap_comp, powerMap_inclusion]
  · apply inclusion_homology_injective
    intro x hx
    let e := List.mem_map.mp hx
    exact e.choose_spec.2 ▸ scalarPowerHomotopy F e.choose t a hta (H _ e.choose_spec.1)
  · exact powerMap_range_eq F zs t H a b hab hgap i

 

lemma parameterPower_stableImage_isoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (h : ℕ) (hsupp : ∀ i, i < n ∨ n+h ≤ i → IsZero (F.X i))
    (zs : List R) (t a b : ℕ)
    (H : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0)
    (hta : t ≤ a) (hab : a ≤ b) (hgap : zs.length*t ≤ b-a)
    (hKos : ∀ c ∈ [a,b], ∀ i : ℤ, i < 0 → P ((unit (zs.map (· ^ c))).homology i)) (i : ℤ) :
    P.isoModSerre (homologyMap
      (complexQuotientπ (entryIdeal (zs.map (· ^ b))) F) i ≫
        factorThruImage (homologyMap
          ((complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F) i)) := by
  let f := homologyMap (powerMap F a b hab zs) i
  let g := homologyMap
    ((complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F) i
  let s : Arrow.mk f ⟶ Arrow.mk g := Arrow.homMk
    (homologyMap (quotientAugmentation F (zs.map (· ^ b))) i)
    (homologyMap (quotientAugmentation F (zs.map (· ^ a))) i) (by
      change _ ≫ g = f ≫ _
      dsimp only [f,g]
      rw [← homologyMap_comp, ← homologyMap_comp]
      exact congrArg (fun f => homologyMap f i)
        (quotientAugmentation_power_naturality F zs a b hab))
  have hs : P.isoModSerre (Limits.image.map s) := imageMap_isoModSerre P s
    (augmentation_finiteFree_bounded_isoMod P _ (hKos b (by simp)) F n h hsupp i)
    (augmentation_finiteFree_bounded_isoMod P _ (hKos a (by simp)) F n h hsupp i)
  have hi := koszul_stableImage_isIso F zs t a b H hta hab hgap i
  have hh : P.isoModSerre
      ((homologyMap (inclusion F (zs.map (· ^ b))) i ≫ factorThruImage f) ≫
        Limits.image.map s) := P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _) hs
  have hm : factorThruImage f ≫ Limits.image.map s = s.left ≫ factorThruImage g :=
    Limits.image.factor_map s
  rw [Category.assoc, hm] at hh
  change P.isoModSerre (homologyMap (inclusion F (zs.map (· ^ b))) i ≫
    homologyMap (quotientAugmentation F (zs.map (· ^ b))) i ≫ factorThruImage g) at hh
  simpa only [← Category.assoc, ← homologyMap_comp, quotientAugmentation_inclusion] using hh

end Lech


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

lemma parameterPower_source_monoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (d : ℕ) (hsupp : ∀ i, i < n ∨ n+d ≤ i → IsZero (F.X i))
    (zs : List R) (a : ℕ) (H : ∀ r ∈ zs, Homotopy (r^a • 𝟙 F) 0)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit (zs.map (· ^ a))).homology i)) (i : ℤ) :
    P.monoModSerre (homologyMap
      (complexQuotientπ (entryIdeal (zs.map (· ^ a))) F) i) := by
  classical
  have : Mono (homologyMap (inclusion F (zs.map (· ^ a))) i) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    apply inclusion_homology_injective
    intro x hx
    let e := List.mem_map.mp hx
    exact e.choose_spec.2 ▸ H e.choose e.choose_spec.1
  have ha := augmentation_finiteFree_bounded_isoMod P _ hKos F n d hsupp i
  rw [← quotientAugmentation_inclusion F (zs.map (· ^ a)), homologyMap_comp]
  exact P.monoModSerre.comp_mem _ _ (P.monoModSerre_of_mono _) ha.1



lemma ordinaryPower_stableImage_isoMod_oai
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (d : ℕ) (hsupp : ∀ i, i < n ∨ n+d ≤ i → IsZero (F.X i))
    (h : ℕ) (z : Fin h → R) (t : ℕ) (ht : 1 ≤ t)
    (H : ∀ j, Homotopy (z j ^ t • 𝟙 F) 0)
    (hKos : ∀ a : ℕ, 1 ≤ a → ∀ i : ℤ, i < 0 → P ((unit (List.ofFn fun j => z j ^ a)).homology i)) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N₀ : ℕ, ∃ hMN₀ : M ≤ N₀,
      ∀ N : ℕ, ∀ hN : N₀ ≤ N, ∀ i : ℤ,
        P.isoModSerre (homologyMap
          (complexQuotientπ (Ideal.span (Set.range z) ^ N) F) i ≫
            factorThruImage (homologyMap
              ((complexQuotientMap (Ideal.pow_le_pow_right
                (hMN₀.trans hN))
                (.up ℤ)).app F) i)) := by
  classical
  let I := Ideal.span (Set.range z)
  let zs := List.ofFn z
  let J := fun a => entryIdeal (zs.map (· ^ a))
  have hJ (a : ℕ) : J a = Ideal.span (Set.range fun j => z j ^ a) := by
    simp only [zs, List.map_ofFn, Function.comp_def, entryIdeal_ofFn, J]
  have H' : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0 := by
    intro r hr
    let e := List.mem_ofFn.mp hr
    exact e.choose_spec ▸ H e.choose
  have hKos' (a : ℕ) (ha : 1 ≤ a) : ∀ i : ℤ, i < 0 → P ((unit (zs.map (· ^ a))).homology i) := by
    simpa only [zs, List.map_ofFn, Function.comp_def] using hKos a ha
  refine ⟨h*(t-1)+1, fun M hM => ?_⟩
  let a := max M t
  let b := a+h*t
  have hMa : M ≤ a := le_max_left _ _
  have hta : t ≤ a := le_max_right _ _
  have hab : a ≤ b := Nat.le_add_right _ _
  have hapos : 1 ≤ a := ht.trans hta
  have hbpos : 1 ≤ b := hapos.trans hab
  let N₀ := max M (h*(b-1)+1)
  have hMN₀ : M ≤ N₀ := le_max_left _ _
  refine ⟨N₀,hMN₀,fun N hN i => ?_⟩
  have hNM : M ≤ N := hMN₀.trans hN
  have hIMJ : I^M ≤ J t := by
    rw [hJ]
    exact (Ideal.pow_le_pow_right hM).trans (parameter_power_cofinality h t ht z).1
  have hINJ : I^N ≤ J b := by
    rw [hJ]
    exact (Ideal.pow_le_pow_right ((le_max_right M _).trans hN)).trans
      (parameter_power_cofinality h b hbpos z).1
  have hJIM : J a ≤ I^M := by
    rw [hJ]
    exact (parameter_power_cofinality h a hapos z).2.trans (Ideal.pow_le_pow_right hMa)
  have hJba : J b ≤ J a := entryIdeal_power_antitone zs hab
  have hmono : P.monoModSerre (homologyMap (complexQuotientπ (I^M) F) i) := by
    apply monoModSerre_of_comp P _
      (homologyMap ((complexQuotientMap hIMJ (.up ℤ)).app F) i)
    rw [← homologyMap_comp, complexQuotientπ_map]
    exact parameterPower_source_monoMod P F n d hsupp zs t H' (hKos' t ht) i
  have hstable : P.isoModSerre (homologyMap (complexQuotientπ (J b) F) i ≫
      factorThruImage (homologyMap ((complexQuotientMap hJba (.up ℤ)).app F) i)) := by
    have hx := parameterPower_stableImage_isoMod P F n d hsupp zs t a b H' hta hab
      (by simp only [zs, List.length_ofFn]; dsimp [b]; omega)
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact hKos' a hapos
        · exact hKos' b hbpos) i
    exact hx
  apply cofinal_stableImage_isoMod P
    (homologyMap (complexQuotientπ (I^N) F) i)
    (homologyMap (complexQuotientπ (I^M) F) i)
    (homologyMap (complexQuotientπ (J b) F) i)
    (homologyMap (complexQuotientπ (J a) F) i)
    (homologyMap ((complexQuotientMap (Ideal.pow_le_pow_right hNM) (.up ℤ)).app F) i)
    (homologyMap ((complexQuotientMap hINJ (.up ℤ)).app F) i)
    (homologyMap ((complexQuotientMap hJba (.up ℤ)).app F) i)
    (homologyMap ((complexQuotientMap hJIM (.up ℤ)).app F) i)
    (by rw [← homologyMap_comp, complexQuotientπ_map])
    (by rw [← homologyMap_comp, complexQuotientπ_map])
    (by rw [← homologyMap_comp, complexQuotientπ_map])
    ?_ hmono hstable
  rw [← homologyMap_comp, ← homologyMap_comp, complexQuotientMap_comp,
    complexQuotientMap_comp]

end Lech
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ordinaryPower_stableImage_isoMod_oai.{u} := @OAI.Lech.ordinaryPower_stableImage_isoMod_oai.{u}
