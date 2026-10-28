-- Prove2me | solution 1 for OAI.Lech.SourceGraded.acyclicity_finite_torsion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:14:52.972977+00:00
-- url     : https://prove2.me/submissions/9792c0da-9cc2-4532-ad1a-63a260a54fb9

import Mathlib
import Definitions.Def_OAIQ032L011
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L017
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

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

variable [HasZeroObject C]

 

lemma cone_triangleh_epi {f : F ⟶ G} (h : Homotopy f 0) :
    Epi (mappingCone.triangleh f).mor₃ := by
  apply CategoryTheory.Pretriangulated.Triangle.epi₃ _ (HomotopyCategory.mappingCone_triangleh_distinguished f)
  change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f = 0
  simpa using HomotopyCategory.eq_of_homotopy _ _ h

variable [CategoryWithHomology C]


lemma coneHomologyProjection_epi {f : F ⟶ G} (h : Homotopy f 0) (i : ℤ) :
    Epi (coneHomologyProjection f i) := by
  have := cone_triangleh_epi h
  have := CategoryTheory.isSplitEpi_of_epi (mappingCone.triangleh f).mor₃
  have : Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
      (mappingCone.triangleh f).mor₃) := inferInstance
  have : Epi (((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 i
      (i + 1) (by omega)).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj F)) := inferInstance
  unfold coneHomologyProjection
  exact epi_comp' (inferInstanceAs (Epi
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app (mappingCone f)).inv))
      (epi_comp' (inferInstanceAs (Epi ((HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) i).map (mappingCone.triangleh f).mor₃)))
        (epi_comp' (inferInstanceAs (Epi (((HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftIso 1 i (i+1) (by omega)).hom.app
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj F))))
          (inferInstanceAs (Epi ((HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) (i+1)).app F).hom))))

lemma prop_homology_of_cone (P : ObjectProperty C) [P.IsClosedUnderQuotients]
    {f : F ⟶ G} (h : Homotopy f 0) (i : ℤ)
    (hp : P ((mappingCone f).homology i)) : P (F.homology (i + 1)) := by
  have := coneHomologyProjection_epi h i
  exact P.prop_of_epi (coneHomologyProjection f i) hp

 

lemma prop_homology_of_tensor (P : ObjectProperty C) [P.IsClosedUnderQuotients]
    (zs : List R) (F : CochainComplex C ℤ)
    (hzs : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0)) (i : ℤ)
    (hp : P ((tensor zs F).homology i)) : P (F.homology (i + zs.length)) := by
  induction zs generalizing i with
  | nil => simpa using hp
  | cons a zs ih =>
    obtain ⟨ha⟩ := hzs a (by simp)
    have h := prop_homology_of_cone P (tensorScalarHomotopy a zs ha) i hp
    have h' := ih (fun b hb => hzs b (by simp [hb])) (i + 1) h
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
      add_comm (1 : ℤ)] using h'

end Lech.Koszul
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
universe u
variable {R : Type u} [CommRing R]

lemma tensor_homology_torsion (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    powerTorsion (entryIdeal zs) ((tensor zs F).homology i) :=
  ⟨1, by simpa using tensor_homology_annihilator zs F i⟩

variable {C : Type*} [Category C] [Abelian C] [CategoryTheory.Linear R C]

lemma tensor_bounded (zs : List R) (F : CochainComplex C ℤ) (m n : ℤ)
    (hF : ∀ i, i < m ∨ n < i → IsZero (F.X i)) :
    ∀ i, i < m - zs.length ∨ n < i → IsZero ((tensor zs F).X i) := by
  induction zs with
  | nil => simpa using hF
  | cons a zs ih =>
    intro i hi
    rw [tensor_cons, mappingCone.isZero_X_iff]
    constructor <;> apply ih <;> simp only [List.length_cons, Nat.cast_add,
      Nat.cast_one] at hi <;> omega

lemma unit_bounded (zs : List R) (i : ℤ) (hi : i < -(zs.length : ℤ) ∨ 0 < i) :
    IsZero ((unit zs).X i) := by
  apply tensor_bounded zs ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) 0 0
    (fun j hj => isZero_single_obj_X (ComplexShape.up ℤ) 0 _ j (by omega)) i
  simpa using hi

lemma unit_homology_zero (zs : List R) (i : ℤ)
    (hi : i < -(zs.length : ℤ) ∨ 0 < i) : IsZero ((unit zs).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (unit_bounded zs i hi)

variable {F G : CochainComplex C ℤ}


lemma cone_homology_inr_epi (f : F ⟶ G) (i : ℤ)
    (hF : IsZero (F.homology (i + 1))) : Epi (homologyMap (mappingCone.inr f) i) := by
  let e := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i
  let Q := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  let T := mappingCone.triangleh f
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  let e' : Q.obj (T.obj₁⟦(1 : ℤ)⟧) ≅ F.homology (i + 1) :=
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 i
        (i + 1) (by omega)).app T.obj₁ ≪≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (i + 1)).app F
  have hz : IsZero (Q.obj (T.obj₁⟦(1 : ℤ)⟧)) := hF.of_iso e'
  have hex := Q.map_distinguished_exact T.rotate (CategoryTheory.Pretriangulated.rot_of_distTriang T hT)
  have : Epi (Q.map T.mor₂) := hex.epi_f_iff.mpr (hz.eq_of_tgt _ _)
  have : Epi (e.hom.app G ≫ homologyMap (mappingCone.inr f) i) := by
    change Epi (e.hom.app G ≫ (homologyFunctor C (ComplexShape.up ℤ) i).map
      (mappingCone.inr f))
    rw [← e.hom.naturality (mappingCone.inr f)]
    change Epi (Q.map T.mor₂ ≫ (e.app (mappingCone f)).hom)
    exact epi_comp' (inferInstanceAs (Epi (Q.map T.mor₂)))
      (inferInstanceAs (Epi (e.app (mappingCone f)).hom))
  exact epi_of_epi (e.hom.app G) _



instance unitHomologyGenerator_epi (zs : List R) : Epi (unitHomologyGenerator zs) := by
  induction zs with
  | nil =>
    change Epi (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv
    infer_instance
  | cons a zs ih =>
    have := cone_homology_inr_epi (a • 𝟙 (unit zs)) 0
      (unit_homology_zero zs 1 (Or.inr (by omega)))
    change Epi (unitHomologyGenerator zs ≫ homologyMap
      (mappingCone.inr (a • 𝟙 (unit zs))) 0)
    infer_instance

instance unitHomologyQuotient_epi (zs : List R) : Epi (unitHomologyQuotient zs) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (unitHomologyGenerator zs)).mp
    inferInstance x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_SignedCechBicRow
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators


namespace Lech
open CochainComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

lemma prop_tensor_free_single (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (zs : List R) (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    (j i : ℤ)
    (h : P ((Koszul.tensor zs ((singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R R))).homology (i - j))) :
    P ((Koszul.tensor zs ((singleFunctor (ModuleCat R) j).obj M)).homology i) := by
  apply P.prop_of_iso (Koszul.tensorSingleHomologyIso zs M j i).symm
  simpa only [Functor.comp_obj, Koszul.tensorFunctor_obj, homologyFunctor] using
    prop_additive_free P
    (singleFunctor (ModuleCat R) 0 ⋙ Koszul.tensorFunctor zs ⋙
      homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (i - j))
    (by simpa only [Functor.comp_obj, Koszul.tensorFunctor_obj, homologyFunctor] using h) M

 

theorem acyclicity_of_koszul (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(zs.length : ℤ) ∨ 0 < j → IsZero (F.X j))
    (hz : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0))
    (hK : ∀ i < 0, P ((Koszul.tensor zs
      ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))).homology i))
    (i : ℤ) (hi : i < 0) : P (F.homology i) := by
  have ht : P ((Koszul.tensor zs F).homology (i - zs.length)) := by
    rw [← Koszul.tensorFunctor_obj]
    apply FiniteComplex.homology_devissage P (Koszul.tensorFunctor zs)
      (Koszul.tensorSplitting zs) (-(zs.length : ℤ)) (zs.length + 1) F
      (i - zs.length) (fun j hj => hb j (by omega))
    intro j
    by_cases hj : j < -(zs.length : ℤ) ∨ 0 < j
    · exact P.prop_of_isZero ((homologyFunctor (ModuleCat R) (ComplexShape.up ℤ)
        (i - zs.length)).map_isZero ((Koszul.tensorFunctor zs).map_isZero
          ((single (ModuleCat R) (ComplexShape.up ℤ) j).map_isZero (hb j hj))))
    · have := hf j
      have := hfin j
      rw [Koszul.tensorFunctor_obj]
      apply prop_tensor_free_single P zs (F.X j) j (i - zs.length)
      exact hK _ (by omega)
  simpa using Koszul.prop_homology_of_tensor P zs F hz (i - zs.length) ht

end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomologyProp
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

 

lemma homology_prop_of_koszul (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(zs.length : ℤ) ∨ 0 < j → IsZero (F.X j))
    (hz : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0))
    (hK : ∀ i, P ((Koszul.unit zs).homology i)) (i : ℤ) : P (F.homology i) := by
  have ht : P ((Koszul.tensor zs F).homology (i - zs.length)) := by
    rw [← Koszul.tensorFunctor_obj]
    apply FiniteComplex.homology_devissage P (Koszul.tensorFunctor zs)
      (Koszul.tensorSplitting zs) (-(zs.length : ℤ)) (zs.length + 1) F
      (i - zs.length) (fun j hj => hb j (by omega))
    intro j
    have := hf j
    have := hfin j
    rw [Koszul.tensorFunctor_obj]
    exact prop_tensor_free_single P zs (F.X j) j (i - zs.length) (hK _)
  simpa using Koszul.prop_homology_of_tensor P zs F hz (i - zs.length) ht

omit [Nontrivial R] in
 

lemma powerTorsion_of_le_radical {I J : Ideal R} (hI : I.FG) (hIJ : I ≤ J.radical)
    {M : ModuleCat.{u} R} (hM : powerTorsion J M) : powerTorsion I M := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hI
  obtain ⟨m, hm⟩ := hM
  exact ⟨n * m, by rw [pow_mul]; exact (pow_le_pow_left' hn m).trans hm⟩

 

theorem acyclicity_length (I : Ideal R) (ℓ : TorsionLength I)
    (zs : List R) (hI : I.FG) (hIJ : I ≤ (Koszul.entryIdeal zs).radical)
    (hquot : ℓ.value (ModuleCat.of R (R ⧸ Koszul.entryIdeal zs)) ≠ ⊤)
    (hK : ∀ i < 0, ℓ.value ((Koszul.unit zs).homology i) = 0)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(zs.length : ℤ) ∨ 0 < j → IsZero (F.X j))
    (hz : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0)) :
    (∀ i, powerTorsion I (F.homology i) ∧ ℓ.value (F.homology i) ≠ ⊤) ∧
      (∀ i < 0, ℓ.value (F.homology i) = 0) := by
  have htors (i : ℤ) : powerTorsion I ((Koszul.unit zs).homology i) :=
    powerTorsion_of_le_radical hI hIJ (Koszul.tensor_homology_torsion zs _ i)
  have hzero (i : ℤ) (hi : i < 0) : ℓ.zeroClass ((Koszul.unit zs).homology i) :=
    ⟨htors i, hK i hi⟩
  have hquotT : powerTorsion I (ModuleCat.of R (R ⧸ Koszul.entryIdeal zs)) := by
    apply powerTorsion_of_le_radical hI hIJ
    exact ⟨1, by simp only [pow_one, Ideal.annihilator_quotient, le_refl]⟩
  have hfinite (i : ℤ) : ℓ.finiteClass ((Koszul.unit zs).homology i) := by
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · exact ⟨htors i, by rw [hK i hi]; exact ENNReal.zero_ne_top⟩
    · exact ℓ.finiteClass.prop_of_epi (Koszul.unitHomologyQuotient zs) ⟨hquotT, hquot⟩
    · exact ℓ.finiteClass.prop_of_isZero (Koszul.unit_homology_zero zs i (Or.inr hi))
  exact ⟨homology_prop_of_koszul ℓ.finiteClass zs F hf hfin hb hz hfinite,
    fun i hi => (acyclicity_of_koszul ℓ.zeroClass zs F hf hfin hb hz hzero i hi).2⟩

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionAcyclicity
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
include hz in
 

theorem acyclicity_finite_torsion_oai
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(h:ℤ) ∨ 0<j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    (∀ i, powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
      (∀ i : ℤ, i≠0 → ell.value (F.homology i)=0) := by
  classical
  have hp : ∀ j, Module.Projective R (F.X j) := fun j => by have := hf j; infer_instance
  obtain ⟨m,hm⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F (-(h:ℤ)) 0 hp hfin hb hacyc
  let a := m+1
  have ha0 : 0<a := by dsimp [a]; omega
  have hfg : I.FG := by
    rw [←hz]
    exact ⟨Finset.univ.image z, by simp⟩
  have hrad : I ≤ (Koszul.entryIdeal (List.ofFn (fun j => z j^a))).radical := by
    rw [←hz,entryIdeal_ofFn]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨a,Ideal.subset_span ⟨j,rfl⟩⟩
  have hq : ell.value (ModuleCat.of R
      (R ⧸ Koszul.entryIdeal (List.ofFn (fun j => z j^a))))≠⊤ := by
    rw [entryIdeal_ofFn,ha a ha0,nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hmu
  have HK : ∀ i : ℤ, i<0 → ell.value
      ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0 :=
    hK a (by omega)
  have H := acyclicity_length I ell (List.ofFn (fun j => z j^a))
    hfg hrad hq HK F hf hfin (by simpa only [List.length_ofFn] using hb) (by
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨Koszul.scalarPowerHomotopy F (z j) m a (by dsimp [a];omega) (hm j).some⟩)
  refine ⟨H.1, fun i hi => ?_⟩
  rcases lt_or_gt_of_ne hi with hlt|hgt
  · exact H.2 i hlt
  · exact ell.zero (ExactAt.of_isZero (hb i (Or.inr hgt))).isZero_homology

end Lech.SourceGraded

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SourceGraded.acyclicity_finite_torsion_oai.{u} := @OAI.Lech.SourceGraded.acyclicity_finite_torsion_oai.{u}
