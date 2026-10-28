-- Prove2me | solution 1 for OAI.Lech.FilteredCech.positive_homology_powerTorsion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:11:52.894288+00:00
-- url     : https://prove2.me/submissions/7bee9f93-d1cb-488d-9191-ca03d59c4d5f

import Mathlib
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L023

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmented
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedCechHomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SignedCech.inclusion_f_mono _root_.OAI.Lech.extendScalars_additive
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
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

 

lemma piece_nat (w : R) (d t : ℕ) : piece I w d (t:ℤ)=FilteredFraction.piece I w d t := by
  apply iSup_congr
  intro n
  ext x
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,by simpa only [order_nat] using a.property⟩,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,by simpa only [order_nat] using a.property⟩,ha⟩

end Lech.SignedFraction


namespace Lech.SignedCech
section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma inclusion_refl (t : ℤ) : inclusion I z hz (le_refl t)=𝟙 (complex I z hz t) := by
  ext n x
  rfl

lemma inclusion_comp {r s t : ℤ} (hrs : r ≤ s) (hst : s ≤ t) :
    inclusion I z hz hst ≫ inclusion I z hz hrs = inclusion I z hz (hrs.trans hst) := by
  ext n x
  rfl

lemma term_nat (t : ℕ) (s : Finset (Fin h)) : term I z (t:ℤ) s=FilteredCech.term I z t s :=
  SignedFraction.piece_nat I _ _ _
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma positiveInclusion_refl (t : ℤ) : positiveInclusion I z hz (le_refl t)=𝟙 _ := by
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

lemma positiveInclusion_comp {r s t : ℤ} (hrs : r ≤ s) (hst : s ≤ t) :
    positiveInclusion I z hz hst ≫ positiveInclusion I z hz hrs =
      positiveInclusion I z hz (hrs.trans hst) := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz r) 0
    (augmented_boundedBelow I z hz r)))).mp
  let ι (j : ℤ) := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz j) 0
    (augmented_boundedBelow I z hz j))
  have hι {a b : ℤ} (hab : a ≤ b) : positiveInclusion I z hz hab ≫ ι a =
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
end Lech.SignedCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SignedCechBicRow
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.FilteredCech (tensorBic tensorBic_total_map tensorBic_isZero)
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

lemma twistPath (t : ℤ) (N : ℕ) :
    TotalGhost.towerPath (X := fun n => positive I z hz (twistIndex t m n))
      (twistStep I z hz m t) N =
      positiveInclusion I z hz (twistIndex_le t m N) := by
  induction N with
  | zero => simp only [twistIndex,TotalGhost.towerPath,positiveInclusion_refl]
  | succ N ih =>
    rw [TotalGhost.towerPath,ih]
    exact positiveInclusion_comp I z hz _ _

include H in
 

lemma positive_homologyMap_zero (l b : ℤ)
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j)) (N : ℕ) (hN : b-l<(N:ℤ))
    (t : ℤ) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t ≤ t+(m*N:ℕ) by omega))) i=0 := by
  let X : ℕ → TotalGhost.Bic (R := R) := fun n => (tensorBic F).obj (positive I z hz (twistIndex t m n))
  let f : ∀ n, X (n+1) ⟶ X n := fun n => (tensorBic F).map (twistStep I z hz m t n)
  have hrow : ∀ n, TotalGhost.RowHomotopy (f n) :=
    fun n => bicRowHomotopy I z hz F m H (twistIndex t m n)
  have hh := TotalGhost.homologyMap_path_eq_zero f hrow N l b hN
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inr hp)))
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inl hp))) i
  dsimp only [f] at hh
  have he := TotalGhost.towerPath_map (X := fun n => positive I z hz (twistIndex t m n))
    (twistStep I z hz m t) (tensorBic F) N
  rw [he,twistPath] at hh
  have hc := congrArg (fun k => homologyMap k i)
    (tensorBic_total_map F (positiveInclusion I z hz (twistIndex_le t m N)))
  have hh' : ∀ ht : t ≤ twistIndex t m N,
      homologyMap ((TensorTotal.Right.functor F).map (positiveInclusion I z hz ht)) i=0 :=
    fun _ => hc.symm.trans hh
  rw [twistIndex_eq t m N] at hh'
  exact hh' _
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma positive_homologyMap_zero_of_le (m : ℕ) (H : ∀ i, Homotopy (z i^m • 𝟙 F) 0)
    (l b : ℤ) (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (N : ℕ) (hN : b-l<(N:ℤ)) (t : ℤ) (M : ℕ) (hM : m*N≤M) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+(M:ℤ) by omega))) i=0 := by
  have h1 : t ≤ t+(m*N:ℕ) := by omega
  have h2 : t+(m*N:ℕ) ≤ t+(M:ℤ) := by omega
  rw [←positiveInclusion_comp I z hz h1 h2,Functor.map_comp,homologyMap_comp,
    positive_homologyMap_zero I z hz F m H l b hb N hN t i,comp_zero]

 

lemma exists_uniform_positive_nilpotence (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ t : ℤ, ∀ M : ℕ, MD≤M → ∀ i : ℤ,
      homologyMap ((TensorTotal.Right.functor F).map
        (positiveInclusion I z hz (show t≤t+(M:ℤ) by omega))) i=0 := by
  classical
  obtain ⟨m,H⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F l b hp hfin hb ha
  let N : ℕ := (b-l).toNat+1
  have hN : b-l<(N:ℤ) := by dsimp [N]; omega
  refine ⟨m*N,?_⟩
  intro t M hM i
  exact positive_homologyMap_zero_of_le I z hz F m (fun i => (H i).some) l b hb N hN t M hM i
end Lech.SignedCech


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

lemma homologyMap_smul (a : R) (f : K ⟶ L) (i : ι) :
    homologyMap (a • f) i=a • homologyMap f i := by
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{u} R) c i).map (a • f))=
    a • ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{u} R) c i).map f)
  have he : (shortComplexFunctor (ModuleCat.{u} R) c i).map (a • f)=
      a • (shortComplexFunctor (ModuleCat.{u} R) c i).map f := rfl
  rw [he,ShortComplex.homologyMap_smul]
end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} {ι' : Type w}
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

lemma extendMap_smul (r : R) (f : K ⟶ L) (e : c.Embedding c') :
    extendMap (r • f) e=r • extendMap f e := by
  apply Hom.ext
  funext j
  by_cases hj : ∃ i, e.f i=j
  · obtain ⟨i,hi⟩ := hj
    simp only [smul_f_apply,extendMap_f _ e hi,CategoryTheory.Linear.comp_smul,
      CategoryTheory.Linear.smul_comp]
  · exact (K.isZero_extend_X e j (by simpa only [not_exists] using hj)).eq_of_src _ _
end Lech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)

@[reassoc] lemma positiveMultiply_inclusion (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    positiveMultiply I z hz t M a ha ≫ positiveInclusion I z hz (by omega : t ≤ t+(M:ℤ)) =
      a • 𝟙 (positive I z hz t) := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)))).mp
  simp only [positiveMultiply, positiveInclusion]
  let ι (j : ℤ) := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz j) 0
    (augmented_boundedBelow I z hz j))
  have hM : positiveMultiply I z hz t M a ha ≫ ι (t+(M:ℤ)) =
      ι t ≫ extendMap (multiply I z hz t M a ha) ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0
      (augmented_boundedBelow I z hz t) (augmented_boundedBelow I z hz (t+(M:ℤ))) _
  have hI : positiveInclusion I z hz (show t ≤ t+(M:ℤ) by omega) ≫ ι t =
      ι (t+(M:ℤ)) ≫ extendMap (inclusion I z hz (show t ≤ t+(M:ℤ) by omega))
        ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz (t+(M:ℤ))) 0
      (augmented_boundedBelow I z hz (t+(M:ℤ))) (augmented_boundedBelow I z hz t) _
  have he : extendMap (multiply I z hz t M a ha) ComplexShape.embeddingUpNat ≫
      extendMap (inclusion I z hz (show t ≤ t+(M:ℤ) by omega)) ComplexShape.embeddingUpNat =
        a • 𝟙 (augmented I z hz t) := by
    rw [← extendMap_comp, multiply_inclusion, Lech.extendMap_smul, extendMap_id]
    rfl
  refine (Category.assoc _ _ _).trans
    ((congrArg (positiveMultiply I z hz t M a ha ≫ ·) hI).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ extendMap (inclusion I z hz (show t ≤ t+(M:ℤ) by omega))
          ComplexShape.embeddingUpNat) hM).trans
          ((Category.assoc _ _ _).trans ((congrArg (ι t ≫ ·) he).trans ?_)))))
  exact (CategoryTheory.Linear.comp_smul _ _ _ (ι t) a (𝟙 (augmented I z hz t))).trans
    ((congrArg (a • ·) (Category.comp_id (ι t))).trans
      ((congrArg (a • ·) (Category.id_comp (ι t))).symm.trans
        (CategoryTheory.Linear.smul_comp _ _ _ a (𝟙 (positive I z hz t)) (ι t)).symm))

end Lech.SignedCech


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G : CochainComplex (ModuleCat.{u} R) ℤ}

lemma map_smul (a : R) (f : F ⟶ G) : (functor K).map (a • f)=a • (functor K).map f := by
  apply Hom.ext
  funext i
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [map_f, smul_f_apply]
  refine (ι_degreeMap K (fun j => a • f.f j) p q i hpq).trans ?_
  change (K.X p ◁ (a • f.f q)) ≫ ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R))
    (.up ℤ) p q i hpq = _
  rw [MonoidalLinear.whiskerLeft_smul]
  exact (CategoryTheory.Linear.smul_comp _ _ _ a _ _).trans
    ((congrArg (a • ·) (ι_degreeMap K f.f p q i hpq).symm).trans
      (CategoryTheory.Linear.comp_smul _ _ _ _ a _).symm)

end Lech.TensorTotal.Right


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

 

lemma annihilator_of_positive_nilpotence (t : ℤ) (M : ℕ) (i : ℤ)
    (hnil : homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+(M:ℤ) by omega))) i=0) :
    I^M ≤ Module.annihilator R
      (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  intro a ha
  rw [Module.mem_annihilator]
  have hf := congrArg (fun f => homologyMap ((TensorTotal.Right.functor F).map f) i)
    (positiveMultiply_inclusion I z hz t M a ha)
  rw [Functor.map_comp,homologyMap_comp,hnil,comp_zero,
    TensorTotal.Right.map_smul,CategoryTheory.Functor.map_id,Lech.homologyMap_smul,homologyMap_id] at hf
  intro x
  have hx := congrArg (fun f => f x) hf
  exact hx.symm

 

lemma exists_uniform_positive_annihilator (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ t : ℤ, ∀ i : ℤ,
      I^MD ≤ Module.annihilator R
        (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  obtain ⟨MD,hMD⟩ := exists_uniform_positive_nilpotence I z hz F l b hp hfin hb ha
  exact ⟨MD,fun t i => annihilator_of_positive_nilpotence I z hz F t MD i (hMD t MD le_rfl i)⟩

lemma positive_homology_powerTorsion (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (t i : ℤ) :
    powerTorsion I (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  obtain ⟨MD,hMD⟩ := exists_uniform_positive_annihilator I z hz F l b hp hfin hb ha
  exact ⟨MD,hMD t i⟩
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)

lemma complex_nat (t : ℕ) : complex I z hz (t:ℤ)=FilteredCech.complex I z hz t := by
  have hT : term I z (t:ℤ)=FilteredCech.term I z t := funext (term_nat I z t)
  unfold complex FilteredCech.complex
  congr 1

lemma positive_nat (t : ℕ) : positive I z hz (t:ℤ)=FilteredCech.positive I z hz t := by
  unfold positive FilteredCech.positive augmented FilteredCech.augmented
  simp only [complex_nat]
end Lech.SignedCech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma positive_homology_powerTorsion_oai (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (t : ℕ) (i : ℤ) :
    powerTorsion I (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  rw [←SignedCech.positive_nat I z hz t]
  exact SignedCech.positive_homology_powerTorsion I z hz F l b hp hfin hb ha t i
end Lech.FilteredCech


end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.FilteredCech.positive_homology_powerTorsion_oai.{u} := @OAI.Lech.FilteredCech.positive_homology_powerTorsion_oai.{u}
