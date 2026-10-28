-- Prove2me | solution 1 for OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:15:15.960847+00:00
-- url     : https://prove2.me/submissions/8e10624a-9c6e-4daf-9a17-4f5cfb07bbfe

import Mathlib
import Definitions.Def_OAIQ032L012
import Definitions.Def_OAIQ032L017
import Definitions.Def_OAIQ032L018

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma inclusion_refl (t : ℕ) : inclusion I z hz (le_refl t)=𝟙 (complex I z hz t) := by
  ext n x
  rfl

end Lech.FilteredCech

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmented
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma positiveInclusion_refl (t : ℕ) : positiveInclusion I z hz (le_refl t)=𝟙 _ := by
  simp only [positiveInclusion]
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)))).mp
  refine (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t) (augmented_boundedBelow I z hz t)
    (extendMap (inclusion I z hz (le_refl t)) ComplexShape.embeddingUpNat)).trans ?_
  have he : extendMap (inclusion I z hz (le_refl t)) ComplexShape.embeddingUpNat =
      𝟙 (augmented I z hz t) := by
    rw [inclusion_refl, extendMap_id]
    rfl
  exact (congrArg (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)) ≫ ·) he).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

lemma positiveInclusion_comp {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    positiveInclusion I z hz hst ≫ positiveInclusion I z hz hrs =
      positiveInclusion I z hz (hrs.trans hst) := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz r) 0
    (augmented_boundedBelow I z hz r)))).mp
  let ι (j : ℕ) := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz j) 0
    (augmented_boundedBelow I z hz j))
  have hι {a b : ℕ} (hab : a ≤ b) : positiveInclusion I z hz hab ≫ ι a =
      ι b ≫ extendMap (inclusion I z hz hab) ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz b) 0
      (augmented_boundedBelow I z hz b) (augmented_boundedBelow I z hz a) _
  have he : extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat ≫
      extendMap (inclusion I z hz hrs) ComplexShape.embeddingUpNat =
        extendMap (inclusion I z hz (hrs.trans hst)) ComplexShape.embeddingUpNat := by
    rw [← extendMap_comp, inclusion_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (positiveInclusion I z hz hst ≫ ·) (hι hrs)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ extendMap (inclusion I z hz hrs) ComplexShape.embeddingUpNat) (hι hst)).trans
          ((Category.assoc _ _ _).trans ((congrArg (ι t ≫ ·) he).trans (hι _).symm)))))
end Lech.FilteredCech


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L M : Bic (R := R)}



lemma homologyMap_correction {f : K ⟶ L} (h : RowHomotopy f) (i : ℤ) :
    homologyMap (correction h) i = homologyMap (total.map f (ComplexShape.up ℤ)) i := by
  have hh := (Homotopy.nullHomotopy' (homotopyTerm h)).homologyMap_eq i
  simp only [homologyMap_zero] at hh
  simp only [correction,homologyMap_sub,hh,sub_zero]

lemma ι_d (K : Bic (R := R)) (p p' q q' i i' : ℤ) (hpq : p+q=i)
    (hp : p+1=p') (hq : q+1=q') (hi : i+1=i') :
    K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ (K.total (ComplexShape.up ℤ)).d i i' =
      (K.d p p').f q ≫ K.ιTotal (ComplexShape.up ℤ) p' q i' (by change p'+q=i'; omega) +
      ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p,q) •
        ((K.X p).d q q' ≫ K.ιTotal (ComplexShape.up ℤ) p q' i' (by change p+q'=i'; omega)) := by
  change _ ≫ (K.D₁ (ComplexShape.up ℤ) i i' + K.D₂ (ComplexShape.up ℤ) i i') = _
  rw [comp_add,ι_D₁,ι_D₂,
    d₁_eq K (ComplexShape.up ℤ) hp q i' (by change p'+q=i'; omega),
    d₂_eq K (ComplexShape.up ℤ) p hq i' (by change p+q'=i'; omega)]
  change (1 : ℤˣ) • _ + _ = _
  rw [one_smul]

 
lemma correction_lowers {f : K ⟶ L} (h : RowHomotopy f) (p q i : ℤ) (hpq : p+q=i) :
    ∃ a : (K.X p).X q ⟶ (L.X (p-1)).X (q+1),
    K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ (correction h).f i =
      a ≫ L.ιTotal (ComplexShape.up ℤ) (p-1) (q+1) i (by change p-1+(q+1)=i; omega) := by
  let e := ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  refine ⟨-(e (p,q) • ((K.X p).d q (q+1) ≫ h.h p (q+1)) +
    e (p-1,q) • (h.h p q ≫ (L.X (p-1)).d q (q+1))), ?_⟩
  have hm := Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (i-1) i by change i-1+1=i; omega)
    (show (ComplexShape.up ℤ).Rel i (i+1) from rfl) (homotopyTerm h)
  dsimp only [correction,sub_f_apply]
  rw [comp_sub,hm,comp_add,←Category.assoc,ι_d K p (p+1) q (q+1) i (i+1) hpq rfl rfl rfl]
  simp only [add_comp,Category.assoc,ι_homotopyTerm,ι_homotopyTerm_assoc,Linear.units_smul_comp]
  have hLd : L.ιTotal (ComplexShape.up ℤ) (p-1) q (i-1) (by change p-1+q=i-1; omega) ≫
      (L.total (ComplexShape.up ℤ)).d (i-1) i =
      (L.d (p-1) p).f q ≫ L.ιTotal (ComplexShape.up ℤ) p q i hpq +
      e (p-1,q) • ((L.X (p-1)).d q (q+1) ≫
        L.ιTotal (ComplexShape.up ℤ) (p-1) (q+1) i (by change p-1+(q+1)=i; omega)) := by
    exact ι_d L (p-1) p q (q+1) (i-1) i (by omega) (by omega) rfl (by omega)
  rw [hLd]
  simp only [comp_add,Linear.comp_units_smul]
  
  rw [ιTotal_map]
  rw [h.equation p q]
  simp only [add_comp,Category.assoc,XXIsoOfEq_hom_ιTotal]
  simp only [neg_comp,add_comp,Linear.units_smul_comp,Category.assoc]
  abel

end Lech.TotalGhost
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L M : Bic (R := R)}



lemma shifted_identity (K : Bic (R := R)) : Shifted 0 (𝟙 (K.total (ComplexShape.up ℤ))) := by
  intro p q i hpq
  refine ⟨p,q,by simp,by simp,hpq,𝟙 _,?_⟩
  simp

lemma shifted_comp {f : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ)}
    {g : L.total (ComplexShape.up ℤ) ⟶ M.total (ComplexShape.up ℤ)}
    {n m : ℕ} (hf : Shifted n f) (hg : Shifted m g) : Shifted (n+m) (f≫g) := by
  intro p q i hpq
  obtain ⟨p',q',hp',hq',hp'q',a,ha⟩ := hf p q i hpq
  obtain ⟨p'',q'',hp'',hq'',hp''q'',b,hb⟩ := hg p' q' i hp'q'
  refine ⟨p'',q'',by push_cast; omega,by push_cast; omega,hp''q'',a≫b,?_⟩
  rw [comp_f,←Category.assoc,ha,Category.assoc,hb,Category.assoc]

lemma shifted_correction {f : K ⟶ L} (h : RowHomotopy f) : Shifted 1 (correction h) := by
  intro p q i hpq
  obtain ⟨a,ha⟩ := correction_lowers h p q i hpq
  exact ⟨p-1,q+1,by norm_num,by norm_num,by omega,a,ha⟩

 

lemma shifted_eq_zero {f : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ)}
    {n : ℕ} (hf : Shifted n f) (l b : ℤ)
    (hK : ∀ p q, b<p → IsZero ((K.X p).X q))
    (hL : ∀ p q, p<l → IsZero ((L.X p).X q)) (hn : b-l<(n:ℤ)) : f=0 := by
  apply HomologicalComplex.hom_ext
  intro i
  apply total.hom_ext
  intro p q hpq
  change p+q=i at hpq
  by_cases hp : b<p
  · exact (hK p q hp).eq_of_src _ _
  obtain ⟨p',q',hp',_,hp'q',a,ha⟩ := hf p q i hpq
  have hp'l : p'<l := by omega
  rw [ha,(hL p' q' hp'l).eq_of_tgt a 0]
  simp


lemma homologyMap_path {X : ℕ → Bic (R := R)} (f : ∀ n, X (n+1) ⟶ X n)
    (h : ∀ n, RowHomotopy (f n)) (n : ℕ) (i : ℤ) :
    homologyMap (towerPath (X := fun n => (X n).total (ComplexShape.up ℤ)) (fun n => correction (h n)) n) i =
      homologyMap (total.map (towerPath f n) (ComplexShape.up ℤ)) i := by
  induction n with
  | zero => simp [towerPath]
  | succ n ih =>
    simp only [towerPath,homologyMap_comp,homologyMap_correction,ih,total.map_comp]

lemma shifted_path {X : ℕ → Bic (R := R)} (f : ∀ n, X (n+1) ⟶ X n)
    (h : ∀ n, RowHomotopy (f n)) (n : ℕ) :
    Shifted n (towerPath (X := fun n => (X n).total (ComplexShape.up ℤ)) (fun n => correction (h n)) n) := by
  induction n with
  | zero => exact shifted_identity _
  | succ n ih =>
    simpa only [towerPath,Nat.add_comm 1 n] using shifted_comp (shifted_correction (h n)) ih

 

lemma homologyMap_path_eq_zero {X : ℕ → Bic (R := R)} (f : ∀ n, X (n+1) ⟶ X n)
    (h : ∀ n, RowHomotopy (f n)) (n : ℕ) (l b : ℤ)
    (hn : b-l<(n:ℤ))
    (hXn : ∀ p q, b<p → IsZero (((X n).X p).X q))
    (hX0 : ∀ p q, p<l → IsZero (((X 0).X p).X q)) (i : ℤ) :
    homologyMap (total.map (towerPath f n) (ComplexShape.up ℤ)) i=0 := by
  rw [←homologyMap_path f h n i,shifted_eq_zero (shifted_path f h n) l b hXn hX0 hn]
  simp only [homologyMap_zero]
end Lech.TotalGhost


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


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma tensorBic_total_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    HomologicalComplex₂.total.map ((tensorBic F).map f) (.up ℤ)=
      (TensorTotal.Right.functor F).map f := by
  unfold tensorBic
  change _ = HomologicalComplex₂.total.map (_ ≫ _) _
  rw [((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).map_id F]
  rw [NatTrans.id_app,Category.id_comp]

lemma tensorBic_isZero (K : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ)
    (hp : IsZero (F.X p)) : IsZero ((((tensorBic F).obj K).X p).X q) :=
  ((curriedTensor (ModuleCat.{u} R)).flip.obj (K.X q)).map_isZero hp

variable (m : ℕ) (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

lemma twistPath (t N : ℕ) :
    TotalGhost.towerPath (X := fun n => positive I z hz (t+m*n))
      (twistStep I z hz m t) N =
      positiveInclusion I z hz (show t ≤ t+m*N by omega) := by
  induction N with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero,TotalGhost.towerPath,positiveInclusion_refl]
  | succ N ih =>
    rw [TotalGhost.towerPath,ih]
    exact positiveInclusion_comp I z hz _ _

include H in
 

lemma positive_homologyMap_zero (l b : ℤ)
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j)) (N : ℕ) (hN : b-l<(N:ℤ))
    (t : ℕ) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+m*N by omega))) i=0 := by
  let X : ℕ → TotalGhost.Bic (R := R) := fun n => (tensorBic F).obj (positive I z hz (t+m*n))
  let f : ∀ n, X (n+1) ⟶ X n := fun n => (tensorBic F).map (twistStep I z hz m t n)
  have hrow : ∀ n, TotalGhost.RowHomotopy (f n) := by
    intro n
    exact bicRowHomotopyAt I z hz F m H (t+m*n) (t+m*(n+1))
      (by rw [Nat.mul_succ,Nat.add_assoc])
  have hh := TotalGhost.homologyMap_path_eq_zero f hrow N l b hN
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inr hp)))
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inl hp))) i
  dsimp only [f] at hh
  have he := TotalGhost.towerPath_map (X := fun n => positive I z hz (t+m*n))
    (twistStep I z hz m t) (tensorBic F) N
  rw [he,twistPath,tensorBic_total_map] at hh
  exact hh
end Lech.FilteredCech

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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma positive_homologyMap_zero_of_le (m : ℕ) (H : ∀ i, Homotopy (z i^m • 𝟙 F) 0)
    (l b : ℤ) (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (N : ℕ) (hN : b-l<(N:ℤ)) (t M : ℕ) (hM : m*N≤M) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+M by omega))) i=0 := by
  have h1 : t ≤ t+m*N := by omega
  have h2 : t+m*N ≤ t+M := by omega
  rw [←positiveInclusion_comp I z hz h1 h2,Functor.map_comp,homologyMap_comp,
    positive_homologyMap_zero I z hz F m H l b hb N hN t i,comp_zero]

 

lemma exists_uniform_positive_nilpotence (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ t M : ℕ, MD≤M → ∀ i : ℤ,
      homologyMap ((TensorTotal.Right.functor F).map
        (positiveInclusion I z hz (show t≤t+M by omega))) i=0 := by
  classical
  obtain ⟨m,H⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F l b hp hfin hb ha
  let N : ℕ := (b-l).toNat+1
  have hN : b-l<(N:ℤ) := by dsimp [N]; omega
  refine ⟨m*N,?_⟩
  intro t M hM i
  exact positive_homologyMap_zero_of_le I z hz F m (fun i => (H i).some) l b hb N hN t M hM i
end Lech.FilteredCech


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]

variable (S : ShortComplex (CochainComplex C ℤ)) (n : ℤ)
    (h₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (h₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (h₃ : ∀ i, i<n → IsZero (S.X₃.X i))

lemma dropShortComplex_shortExact (hS : S.ShortExact) :
    (dropShortComplex S n h₁ h₂ h₃).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : i=n
  · subst i
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ (dropBottom_X_bottom S.X₂ n h₂)
            mono_f := (dropBottom_X_bottom S.X₁ n h₁).mono _
            epi_g := (dropBottom_X_bottom S.X₃ n h₃).epi _ }
  · apply ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (dropBottomXIso S.X₁ n h₁ i hi) (dropBottomXIso S.X₂ n h₂ i hi)
      (dropBottomXIso S.X₃ n h₃ i hi) ?_ ?_).symm (hS.map_of_exact (eval C (.up ℤ) i))
    · exact congrArg (fun f => f.f i) (dropBottomMap_ι S.X₁ n h₁ h₂ S.f).symm
    · exact congrArg (fun f => f.f i) (dropBottomMap_ι S.X₂ n h₂ h₃ S.g).symm
end Lech.FiniteComplex


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

lemma extend_shortExact (S : ShortComplex (HomologicalComplex C c)) (hS : S.ShortExact)
    (e : c.Embedding c') : (S.map (e.extendFunctor C)).ShortExact := by
  classical
  apply shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i=j
  · obtain ⟨i,hi⟩ := hj
    apply ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (S.X₁.extendXIso e hi) (S.X₂.extendXIso e hi) (S.X₃.extendXIso e hi)
      ?_ ?_).symm (hS.map_of_exact (eval C c i))
    · change _ = (extendMap S.f e).f j ≫ _
      rw [extendMap_f _ _ hi]
      simp
      all_goals rfl
    · change _ = (extendMap S.g e).f j ≫ _
      rw [extendMap_f _ _ hi]
      simp
      all_goals rfl
  · have hnone : ∀ i, e.f i≠j := by simpa using hj
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ (S.X₂.isZero_extend_X e j hnone)
            mono_f := (S.X₁.isZero_extend_X e j hnone).mono _
            epi_g := (S.X₃.isZero_extend_X e j hnone).epi _ }
end Lech


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]

lemma dropBottomMap_id (F : CochainComplex C ℤ) (n : ℤ)
    (hf : ∀ i, i<n → IsZero (F.X i)) :
    dropBottomMap F n hf hf (𝟙 F)=𝟙 _ := by
  apply (cancel_mono (kernel.ι (bottomProjection F n hf))).mp
  exact (dropBottomMap_ι F n hf hf (𝟙 F)).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end Lech.FiniteComplex


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
lemma isIso_dropBottomMap {K L : CochainComplex C ℤ} (n : ℤ)
    (hK : ∀ i, i<n → IsZero (K.X i)) (hL : ∀ i, i<n → IsZero (L.X i))
    (f : K ⟶ L) [IsIso f] : IsIso (dropBottomMap K n hK hL f) := by
  refine ⟨⟨dropBottomMap L n hL hK (inv f), ?_, ?_⟩⟩
  · rw [dropBottomMap_comp,IsIso.hom_inv_id,dropBottomMap_id]
  · rw [dropBottomMap_comp,IsIso.inv_hom_id,dropBottomMap_id]
lemma isIso_dropShortComplexMap_τ₂ {S T : ShortComplex (CochainComplex C ℤ)} (n : ℤ)
    (hS₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (hS₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (hS₃ : ∀ i, i<n → IsZero (S.X₃.X i))
    (hT₁ : ∀ i, i<n → IsZero (T.X₁.X i))
    (hT₂ : ∀ i, i<n → IsZero (T.X₂.X i))
    (hT₃ : ∀ i, i<n → IsZero (T.X₃.X i)) (f : S ⟶ T) [IsIso f.τ₂] :
    IsIso (dropShortComplexMap n hS₁ hS₂ hS₃ hT₁ hT₂ hT₃ f).τ₂ :=
  isIso_dropBottomMap n hS₂ hT₂ f.τ₂
end Lech.FiniteComplex


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category J]

lemma functorCategory_shortExact (S : ShortComplex (J ⥤ C))
    (hS : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have hm : ∀ j, Mono (S.f.app j) := fun j => (hS j).mono_f
  have he : ∀ j, Epi (S.g.app j) := fun j => (hS j).epi_g
  refine {exact := ?_, mono_f := ?_, epi_g := ?_}
  · apply S.exact_of_f_is_kernel
    apply evaluationJointlyReflectsLimits
    intro j
    have := (hS j).mono_f
    exact (KernelFork.isLimitMapConeEquiv _ _).symm ((hS j).exact.fIsKernel)
  · exact NatTrans.mono_of_mono_app S.f
  · exact NatTrans.epi_of_epi_app S.g

variable {ι : Type w}

lemma discreteShortComplex_shortExact (S : ι → ShortComplex C)
    (hS : ∀ i, (S i).ShortExact) : (discreteShortComplex S).ShortExact := by
  apply functorCategory_shortExact
  intro i
  exact hS i.as

variable [HasCoproductsOfShape ι C] [HasExactColimitsOfShape (Discrete ι) C]
lemma coproduct_shortExact (S : ι → ShortComplex C) (hS : ∀ i, (S i).ShortExact) :
    ((discreteShortComplex S).map (colim (J:=Discrete ι) (C:=C))).ShortExact :=
  (discreteShortComplex_shortExact S hS).map_of_exact _
end Lech


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)



lemma shortExact (hK : ∀ p, Module.Flat R (K.X p))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) :
    (S.map (functor K)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  apply ShortComplex.shortExact_of_iso (degreeSequenceIso K S i)
  apply Lech.coproduct_shortExact
  intro pq
  have := hK pq.1.1
  exact (hS.map_of_exact (eval (ModuleCat.{u} R) (.up ℤ) pq.1.2)).map_of_exact
    (tensorLeft (K.X pq.1.1))
end Lech.TensorTotal.Right
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedThickeningNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

lemma thickeningNatSequence_shortExact (M : ℕ) : (thickeningNatSequence I z hz M).ShortExact :=
  { exact := ShortComplex.exact_cokernel _
    mono_f := by
      change Mono (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M))
      infer_instance
    epi_g := by
      change Epi (cokernel.π (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M)))
      infer_instance }

lemma thickeningAugSequence_shortExact (M : ℕ) : (thickeningAugSequence I z hz M).ShortExact :=
  Lech.extend_shortExact _ (thickeningNatSequence_shortExact I z hz M) _



lemma thickeningPositiveSequence_shortExact (M : ℕ) :
    (thickeningPositiveSequence I z hz M).ShortExact :=
  FiniteComplex.dropShortComplex_shortExact _ _ _ _ _ (thickeningAugSequence_shortExact I z hz M)

instance thickeningPositiveSequenceMap_middleIso {M N : ℕ} (hMN : M≤N) :
    IsIso (thickeningPositiveSequenceMap I z hz hMN).τ₂ := by
  have hm : IsIso (thickeningNatSequenceMap I z hz hMN).τ₂ := by
    change IsIso (𝟙 _)
    infer_instance
  have he : IsIso (((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapShortComplex.map
      (thickeningNatSequenceMap I z hz hMN)).τ₂) := by
    change IsIso ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map
      (thickeningNatSequenceMap I z hz hMN).τ₂)
    infer_instance
  exact @FiniteComplex.isIso_dropShortComplexMap_τ₂ _ _ _ _ _ 0 _ _ _ _ _ _ _ he

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma thickeningTensorSequence_shortExact (hF : ∀ j, Module.Flat R (F.X j)) (M : ℕ) :
    (thickeningTensorSequence I z hz F M).ShortExact :=
  TensorTotal.Right.shortExact F hF _ (thickeningPositiveSequence_shortExact I z hz M)

end Lech.SourceGraded


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


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 

lemma shortExactTransition_stableImage_isIso
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) [IsIso φ.τ₂]
    (i : ℤ) (hleft : homologyMap T.f i=0) (htrans : homologyMap φ.τ₁ (i+1)=0) :
    IsIso (inv (homologyMap φ.τ₂ i) ≫ homologyMap S.g i ≫
      factorThruImage (homologyMap φ.τ₃ i)) := by
  let a := inv (homologyMap φ.τ₂ i) ≫ homologyMap S.g i
  let b := homologyMap T.g i
  let f := homologyMap φ.τ₃ i
  have hc : a ≫ f=b := by
    dsimp only [a,b,f]
    rw [Category.assoc,←homologyMap_comp,←φ.comm₂₃,homologyMap_comp,
      IsIso.inv_hom_id_assoc]
  have hb : Mono b := (hT.homology_exact₂ i).mono_g hleft
  have hδ : f ≫ hT.δ i (i+1) rfl=0 := by
    rw [←HomologySequence.δ_naturality φ hS hT i (i+1) rfl,htrans,comp_zero]
  have hr : LinearMap.range f.hom=LinearMap.range b.hom := by
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      have hy : (hT.δ i (i+1) rfl) (f y)=0 := by
        change (f ≫ hT.δ i (i+1) rfl) y=0
        rw [hδ]
        rfl
      exact (ShortComplex.moduleCat_exact_iff _).mp (hT.homology_exact₃ i (i+1) rfl) _ hy
    · rintro x ⟨y,rfl⟩
      exact ⟨a y,congrArg (fun g => g y) hc⟩
  have := stableImage_isIso a b f hc ((ModuleCat.mono_iff_injective b).mp hb) hr
  simpa only [a,Category.assoc] using this
end Lech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

instance thickeningTensorSequenceMap_middleIso {M N : ℕ} (hMN : M≤N) :
    IsIso (thickeningTensorSequenceMap I z hz F hMN).τ₂ := by
  change IsIso ((TensorTotal.Right.functor F).map (thickeningPositiveSequenceMap I z hz hMN).τ₂)
  infer_instance

lemma uniform_step_to_gap (P : ∀ a b : ℕ, a≤b → Prop) (MD : ℕ)
    (hP : ∀ a d : ℕ, MD≤d → P a (a+d) (Nat.le_add_right a d))
    (a b : ℕ) (hab : a≤b) (hgap : MD≤b-a) : P a b hab := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hab
  exact hP a d (by omega)

 

lemma exists_uniform_geometric_stableImage_oai (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ M N : ℕ, ∀ hMN : M≤N, MD≤M → MD≤N-M → ∀ i : ℤ,
      IsIso (homologyMap (geometricStructureMap I z hz F N) i ≫
        factorThruImage (homologyMap ((TensorTotal.Right.functor F).map
          (thickeningCechTransition I z hz hMN)) i)) := by
  obtain ⟨MD,hMD⟩ := FilteredCech.exists_uniform_positive_nilpotence I z (coordinate_mem I z hz)
    F l b hp hfin hb ha
  have hflat : ∀ j, Module.Flat R (F.X j) := fun j => by have := hp j; infer_instance
  refine ⟨MD,fun M N hMN hM hgap i => ?_⟩
  let φ := thickeningTensorSequenceMap I z hz F hMN
  have hi₂ : IsIso φ.τ₂ := thickeningTensorSequenceMap_middleIso I z hz F hMN
  have hleft : homologyMap (thickeningTensorSequence I z hz F M).f i=0 := by
    exact hMD 0 M hM i
  have htrans : homologyMap φ.τ₁ (i+1)=0 := by
    change homologyMap ((TensorTotal.Right.functor F).map
      (FilteredCech.positiveInclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN 0))) (i+1)=0
    exact uniform_step_to_gap
      (fun a b hab => homologyMap ((TensorTotal.Right.functor F).map
        (FilteredCech.positiveInclusion I z (coordinate_mem I z hz) hab)) (i+1)=0)
      MD (fun a d hd => hMD a d hd (i+1)) (0+M) (0+N)
      (Nat.add_le_add_left hMN 0) (by omega)
  have hh := shortExactTransition_stableImage_isIso φ
    (thickeningTensorSequence_shortExact I z hz F hflat N)
    (thickeningTensorSequence_shortExact I z hz F hflat M) i hleft htrans
  exact (isIso_comp_left_iff (inv (homologyMap φ.τ₂ i)) _).mp hh
end Lech.SourceGraded

open CochainComplex CochainComplex.HomComplex
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage_oai.{u} := @OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage_oai.{u}
