-- Prove2me | solution 1 for OAI.Lech.ReesRoot.uniform_unit_nilpotence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:39:05.216995+00:00
-- url     : https://prove2.me/submissions/b5b94a29-90ce-4148-9747-662fb1dd5129

import Mathlib
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L039

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmented
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
-- module Solutions.OAIQ032_LECH.Multiplicity_BicomplexImageLift
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {K L M : Bic (R:=R)}
  (f : K ⟶ L) (hf : ∀ p q,Function.Injective ((f.f p).f q).hom) (g : M ⟶ L)
  (hr : ∀ p q,((g.f p).f q).hom.range≤((f.f p).f q).hom.range)
include hf hr in
lemma imageLift_comp : imageLift f hf g hr ≫ f=g := by
  let : ∀ p, Mono (f.f p) := fun p =>
    mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q))
  exact ComplexLift.factor_comp _ _ _ _
include hf hr in
lemma homology_zero_of_range (i : ℤ) (hf0 : homologyMap (total.map f (.up ℤ)) i=0) :
    homologyMap (total.map g (.up ℤ)) i=0 := by
  rw [←imageLift_comp f hf g hr,total.map_comp,homologyMap_comp,hf0,comp_zero]

variable (I : Ideal R) {X : ℕ → Bic (R:=R)} (step : ∀ n,X (n+1) ⟶ X n)
lemma towerPath_injective (hstep : ∀ n p q,Function.Injective (((step n).f p).f q).hom)
    (N : ℕ) (p q : ℤ) : Function.Injective (((towerPath step N).f p).f q).hom := by
  induction N with
  | zero => exact Function.injective_id
  | succ N ih => exact ih.comp (hstep N p q)

lemma towerPath_range (a : ℕ)
    (hstep : ∀ n p q,(((step n).f p).f q).hom.range=I^a • (⊤ : Submodule R (((X n).X p).X q)))
    (N : ℕ) (p q : ℤ) :
    (((towerPath step N).f p).f q).hom.range=I^(a*N) • (⊤ : Submodule R (((X 0).X p).X q)) := by
  induction N with
  | zero => simp [towerPath,LinearMap.range_id]
  | succ N ih =>
      change ((((towerPath step N).f p).f q).hom.comp (((step N).f p).f q).hom).range=_
      rw [LinearMap.range_comp,hstep,Submodule.map_smul'',Submodule.map_top,ih,←Submodule.mul_smul,←pow_add]
      congr 2
      ring
end Lech.TotalGhost

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℕ)
  (H : ∀ k, Homotopy (z k^a • 𝟙 F) 0)

variable (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))



lemma enlargedAt_isZero (m : Fin n → ℤ) (p q : ℤ) (hp : IsZero (F.X p)) :
    IsZero (((enlargedAt I z hz F h s hd m).X p).X q) := by
  let Q := (cechZ I z hz m).X q
  exact @IsZero.of_mono (ModuleCat.{u} R) _ _ _ _
    ((IdealFiltered.ambientInclusion I F h s hd Q).f p)
    (IdealFiltered.ambientInclusion_mono I F h s hd Q p)
    (((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj Q).map_isZero hp)


include H in
 

lemma enlargedPath_homology_zero (m : Fin n → ℤ) (l b : ℤ)
    (hb : ∀ p, p<l ∨ b<p → IsZero (F.X p)) (N : ℕ) (hN : b-l<(N:ℤ)) (i : ℤ) :
    homologyMap (HomologicalComplex₂.total.map
      (TotalGhost.towerPath (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
        (enlargedStep I z hz F h s hd m a) N) (.up ℤ)) i=0 := by
  exact TotalGhost.homologyMap_path_eq_zero
    (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
    (enlargedStep I z hz F h s hd m a)
    (fun N => enlargedRowHomotopy I z hz F a H h s hd (twistSequence m a N)) N l b hN
    (fun p q hp => enlargedAt_isZero I z hz F h s hd _ p q (hb p (Or.inr hp)))
    (fun p q hp => enlargedAt_isZero I z hz F h s hd _ p q (hb p (Or.inl hp))) i

 

theorem uniform_enlarged_nilpotence
    (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (ha : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ a : ℕ, 0<a ∧ ∀ m : Fin n → ℤ, ∀ i : ℤ,
      homologyMap (HomologicalComplex₂.total.map
        (TotalGhost.towerPath (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
          (enlargedStep I z hz F h s hd m a) (h+1)) (.up ℤ)) i=0 := by
  obtain ⟨a,Ha⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F (-(h:ℤ)) 0 hp hfin hb ha
  let H : ∀ k,Homotopy (z k^(a+1) • 𝟙 F) 0 := fun k =>
    Koszul.scalarPowerHomotopy F (z k) a (a+1) (by omega) (Ha k).some
  exact ⟨a+1,by omega,fun m i => enlargedPath_homology_zero I z hz F (a+1) H h s hd
    m (-(h:ℤ)) 0 hb (h+1) (by omega) i⟩

end Lech.ReesRoot

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
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPowerPath
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) {M N : ModuleCat.{u} R} (f : M ⟶ N)
lemma rowMap_power_range (a : ℕ) (hf : f.hom.range=I^a • (⊤ : Submodule R N)) :
    ((rowFunctor I F h s hd p).map f).hom.range =
      I^a • (⊤ : Submodule R ((rowFunctor I F h s hd p).obj N)) := by
  rw [rowMap_eq]
  exact TensorIdeal.restrictIdeal_range _ _ _ (TensorIdeal.range_lTensor I f.hom a hf (F.X p))
end Lech.IdealFiltered

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)

include hgen in
lemma enlarged_power_range (a : ℕ) (p q : ℤ) :
    (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m a)).f p).f q).hom.range =
      I^a • (⊤ : Submodule R (((enlargedAt I z hz F h s hd m).X p).X q)) := by
  exact IdealFiltered.rowMap_power_range I F h s hd p ((cechInclusionZ I z hz m a).f q) a
    (cechInclusionZ_range I z hz m hgen a q)

lemma enlarged_power_injective (a : ℕ) (p q : ℤ) [Module.Flat R (F.X p)] :
    Function.Injective (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m a)).f p).f q).hom :=
  IdealFiltered.rowMap_injective I F h s hd p _ (cechInclusionZ_injective I z hz m a q)

include hgen in
lemma enlargedStep_range (a N : ℕ) (p q : ℤ) :
    (((enlargedStep I z hz F h s hd m a N).f p).f q).hom.range =
      I^a • (⊤ : Submodule R (((enlargedAt I z hz F h s hd (twistSequence m a N)).X p).X q)) :=
  enlarged_power_range I z hz F h s hd (twistSequence m a N) hgen a p q

include hgen in
lemma enlargedPath_range (a N : ℕ) (p q : ℤ) :
    (((enlargedPath I z hz F h s hd m a N).f p).f q).hom.range =
      I^(a*N) • (⊤ : Submodule R (((enlargedAt I z hz F h s hd m).X p).X q)) := by
  exact TotalGhost.towerPath_range I
    (X:=fun j => enlargedAt I z hz F h s hd (twistSequence m a j))
    (enlargedStep I z hz F h s hd m a) a
    (enlargedStep_range I z hz F h s hd m hgen a) N p q

lemma enlargedPath_injective (hflat : ∀ p,Module.Flat R (F.X p)) (a N : ℕ) (p q : ℤ) :
    Function.Injective (((enlargedPath I z hz F h s hd m a N).f p).f q).hom := by
  apply TotalGhost.towerPath_injective
  intro i p q
  let := hflat p
  exact enlarged_power_injective I z hz F h s hd _ a p q

include hgen in
 

theorem uniform_unit_nilpotence_oai
    (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (ha : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ M : ℕ, 0<M ∧ ∀ m : Fin n → ℤ, ∀ i : ℤ,
      homologyMap (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) i=0 := by
  obtain ⟨a,ha0,hzero⟩ := uniform_enlarged_nilpotence I z hz F h s hd hp hfin hb ha
  refine ⟨a*(h+1),Nat.mul_pos ha0 (by omega),?_⟩
  intro m i
  apply TotalGhost.homology_zero_of_range (enlargedPath I z hz F h s hd m a (h+1))
    (enlargedPath_injective I z hz F h s hd m hflat a (h+1)) _ _ i (hzero m i)
  intro p q
  have hleft := enlargedPath_range I z hz F h s hd m hgen 1 (a * (h + 1)) p q
  simp only [one_mul] at hleft
  exact le_of_eq (hleft.trans
    (enlargedPath_range I z hz F h s hd m hgen a (h + 1) p q).symm)
end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.uniform_unit_nilpotence_oai.{u} := @OAI.Lech.ReesRoot.uniform_unit_nilpotence_oai.{u}
