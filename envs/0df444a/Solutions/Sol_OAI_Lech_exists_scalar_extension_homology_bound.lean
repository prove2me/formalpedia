-- Prove2me | solution 1 for OAI.Lech.exists_scalar_extension_homology_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:18:39.127202+00:00
-- url     : https://prove2.me/submissions/79d056e9-64d7-4279-a519-d476de7e9c15

import Mathlib
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L023

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable {A D : Type*} [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma length_eq_of_residue_surjective
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)))
    (M : Type*) [AddCommGroup M] [Module A M] [Module D M] [IsScalarTower A D M] :
    Module.length A M = Module.length D M := by
  rw [IsLocalRing.length_restrictScalars A D M,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField D) hres]
  simp

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AdditiveLength
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma additive_length_pi (T : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [T.Additive]
    {ι : Type} [Fintype ι] (M : ι → ModuleCat.{u} R) :
    Module.length R (T.obj (ModuleCat.of R (∀ i,M i))) =
      ∑ i,Module.length R (T.obj (M i)) := by
  let e := T.mapIso (ModuleCat.biproductIsoPi M).symm ≪≫
    T.mapBiproduct M ≪≫ ModuleCat.biproductIsoPi (fun i : ι => T.obj (M i))
  exact e.toLinearEquiv.length_eq.trans (Module.length_pi_of_fintype _ _)

lemma additive_length_finite_free [Nontrivial R] (T : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [T.Additive]
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    Module.length R (T.obj M) = Module.finrank R M •
      Module.length R (T.obj (ModuleCat.of R R)) := by
  classical
  let b := Module.Free.chooseBasis R M
  let := Module.Free.ChooseBasisIndex.fintype R M
  let e := (b.reindex (Fintype.equivFin _)).equivFun.toModuleIso
  rw [(T.mapIso e).toLinearEquiv.length_eq]
  rw [additive_length_pi T (fun _ : Fin (Fintype.card (Module.Free.ChooseBasisIndex R M)) => ModuleCat.of R R)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  exact (Module.finrank_eq_card_basis b).symm
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFiniteFree
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech

 

theorem finite_free_factorization (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (g : A), g ≠ 0 ∧
      ∃ (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A)),
        u.comp v = g • LinearMap.id ∧ v.comp u = g • LinearMap.id := by
  let := Module.finitePresentation_of_finite A M
  let K := FractionRing A
  let MK := LocalizedModule A⁰ M
  let f : M →ₗ[A] MK := LocalizedModule.mkLinearMap A⁰ M
  let n := Module.finrank K MK
  let e : MK ≃ₗ[A] (Fin n → K) := (Module.finBasis K MK).equivFun.restrictScalars A
  let j : (Fin n → A) →ₗ[A] (Fin n → K) :=
    LinearMap.pi fun i => (Algebra.linearMap A K).comp (LinearMap.proj i)
  have : IsLocalizedModule A⁰ j := by dsimp [j]; infer_instance
  obtain ⟨v,s,hv⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ j
    (e.toLinearMap.comp f)
  obtain ⟨u,t,hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ f
    (e.symm.toLinearMap.comp j)
  have huv : f.comp (u.comp v) = f.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu (v x)
    have hs := LinearMap.congr_fun hv x
    change f (u (v x)) = (t:A) • e.symm (j (v x)) at ht
    change j (v x) = (s:A) • e (f x) at hs
    change f (u (v x)) = f (((t:A)*(s:A)) • x)
    rw [ht,hs,map_smul,e.symm_apply_apply,map_smul,mul_smul]
  have hvu : j.comp (v.comp u) = j.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu x
    have hs := LinearMap.congr_fun hv (u x)
    change f (u x) = (t:A) • e.symm (j x) at ht
    change j (v (u x)) = (s:A) • e (f (u x)) at hs
    change j (v (u x)) = j (((t:A)*(s:A)) • x)
    rw [hs,ht,map_smul,e.apply_symm_apply,map_smul,mul_smul,smul_comm]
  obtain ⟨a,ha⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ f
    (u.comp v) (((t:A)*(s:A)) • LinearMap.id) huv
  obtain ⟨b,hb⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ j
    (v.comp u) (((t:A)*(s:A)) • LinearMap.id) hvu
  refine ⟨n,(a:A)*(b:A)*((t:A)*(s:A)),?_, ((a:A)*(b:A)) • u,v,?_,?_⟩
  · exact mul_ne_zero (mul_ne_zero (nonZeroDivisors.coe_ne_zero a)
      (nonZeroDivisors.coe_ne_zero b))
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero t) (nonZeroDivisors.coe_ne_zero s))
  · rw [LinearMap.smul_comp, mul_comm (a:A) (b:A),mul_smul]
    change (b:A) • ((a:A) • u.comp v) = _
    rw [show (a:A) • u.comp v = (a:A) • (((t:A)*(s:A)) • LinearMap.id) from ha]
    simp only [smul_smul]
    congr 1
    ring
  · rw [LinearMap.comp_smul,mul_smul]
    change (a:A) • ((b:A) • v.comp u) = _
    rw [show (b:A) • v.comp u = (b:A) • (((t:A)*(s:A)) • LinearMap.id) from hb]
    simp only [smul_smul]
    congr 1
    ring

variable {A M N P : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

 

lemma length_kernel_eq_cokernel (f : M →ₗ[A] M) (hM : Module.length A M ≠ ⊤) :
    Module.length A f.ker = Module.length A (M ⧸ f.range) := by
  have h₁ := Module.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hk] at h₁
  have h₂ := Module.length_eq_add_of_exact f.range.subtype f.range.mkQ
    (Submodule.subtype_injective _) f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  have hr : Module.length A f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective f.range.subtype
      (Submodule.subtype_injective _))
  exact WithTop.add_left_cancel hr ((add_comm _ _).trans (h₁.symm.trans h₂))

 

lemma length_torsion_subquotient_le (i : N →ₗ[A] M) (q : N →ₗ[A] P)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (g : A) (hg : ∀ x : P, g • x = 0) (hM : Module.length A M ≠ ⊤) :
    Module.length A P ≤ Module.length A (M ⧸ (LinearMap.lsmul A M g).range) := by
  let fN := LinearMap.lsmul A N g
  let fM := LinearMap.lsmul A M g
  have hqker : fN.range ≤ q.ker := by
    rintro x ⟨y,rfl⟩
    change q (g • y) = 0
    rw [map_smul,hg]
  let q' := fN.range.liftQ q hqker
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨fN.range.mkQ y,rfl⟩
  let i' : fN.ker →ₗ[A] fM.ker :=
    (i.comp fN.ker.subtype).codRestrict fM.ker (by
      intro x
      change g • i x = 0
      rw [← map_smul]
      simpa only [fN, LinearMap.lsmul_apply, map_zero] using congrArg i x.property)
  have hi' : Function.Injective i' := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  have hN : Module.length A N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective i hi)
  calc
    Module.length A P ≤ Module.length A (N ⧸ fN.range) :=
      Module.length_le_of_surjective q' hq'
    _ = Module.length A fN.ker := (length_kernel_eq_cokernel fN hN).symm
    _ ≤ Module.length A fM.ker := Module.length_le_of_injective i' hi'
    _ = _ := length_kernel_eq_cokernel fM hM

end Lech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarHomologyError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped Pointwise
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma scalarHomologyCokernelEmbedding_injective (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    Function.Injective (scalarHomologyCokernelEmbedding g F hg i) := by
  let e := (Submodule.quotEquivOfEq _ _ (scalarHomologyKer g F hg i).symm).trans
    (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom.quotKerEquivRange
  intro x y hxy
  apply e.injective
  apply Subtype.ext
  exact hxy

lemma homology_kernel_killed_of_scalar_retract
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ) :
    ∀ x : (homologyMap u i).hom.ker, g • x = 0 := by
  intro x
  apply Subtype.ext
  have heq := congrArg (fun f => homologyMap f i) h
  rw [homologyMap_comp,Koszul.homologyMap_smul,homologyMap_id] at heq
  have hx := congrArg (fun f => f x) heq
  change homologyMap v i (homologyMap u i x) = g • (x : F.homology i) at hx
  rw [x.property,map_zero] at hx
  exact hx.symm

lemma homology_length_le_of_scalar_retract
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x))
    (hfin : Module.length R (F.homology i) ≠ ⊤) :
    Module.length R (F.homology i) ≤ Module.length R (G.homology i) +
      Module.length R ((((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F).homology i)) := by
  let f := (homologyMap u i).hom
  have hk := length_torsion_subquotient_le f.ker.subtype (LinearMap.id : f.ker →ₗ[R] f.ker)
    f.ker.subtype_injective Function.surjective_id g
    (homology_kernel_killed_of_scalar_retract u v g h i) hfin
  have he := Module.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    f.rangeRestrict.ker.subtype_injective f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk' : f.rangeRestrict.ker = f.ker := by ext; simp
  rw [hk'] at he
  rw [he,add_comm]
  exact add_le_add (Module.length_le_of_injective f.range.subtype f.range.subtype_injective)
    (hk.trans (Module.length_le_of_injective (scalarHomologyCokernelEmbedding g F hg i)
      (scalarHomologyCokernelEmbedding_injective g F hg i)))

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStageQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
lemma restrictScalars_complex_smul (f : R →+* S)
    {F G : CochainComplex (ModuleCat.{u} S) ℤ} (a : R) (v : F ⟶ G) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (f a • v) =
      a • ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map v := rfl
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexTensorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma tensorModuleFunctor_smul (F : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (a : R) (f : M ⟶ N) :
    (tensorModuleFunctor F).map (a • f) = a • (tensorModuleFunctor F).map f := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  change x ⊗ₜ[R] (a • f y) = a • (x ⊗ₜ[R] f y)
  exact TensorProduct.tmul_smul _ _ _

lemma tensorModule_homology_length_free [Nontrivial R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] (i : ℤ) :
    Module.length R (((tensorModuleFunctor F).obj M).homology i) =
      Module.finrank R M • Module.length R (F.homology i) := by
  change Module.length R (((tensorModuleFunctor F) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) i).obj M) = _
  rw [additive_length_finite_free
    ((tensorModuleFunctor F) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) i) M]
  congr 1
  exact ((homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso (tensorModuleUnitIso F)).toLinearEquiv.length_eq

 

theorem exists_tensor_homology_bound [IsDomain R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (r : ℕ) (g : R), g ≠ 0 ∧ ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
      (∀ j,Function.Injective (fun x : ((tensorModuleFunctor F).obj M).X j => g • x)) →
      Module.length R (((tensorModuleFunctor F).obj M).homology i) ≠ ⊤ →
      Module.length R (((tensorModuleFunctor F).obj M).homology i) ≤
        r • Module.length R (F.homology i) +
          Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
            ((tensorModuleFunctor F).obj M)).homology i) := by
  obtain ⟨r,g,hg,u,v,huv,hvu⟩ := finite_free_factorization R M
  refine ⟨r,g,hg,fun F i hgi hfin => ?_⟩
  let U : ModuleCat.of R (Fin r → R) ⟶ M := ModuleCat.ofHom u
  let V : M ⟶ ModuleCat.of R (Fin r → R) := ModuleCat.ofHom v
  have hVU : V ≫ U = g • 𝟙 M := ModuleCat.hom_ext huv
  have he := congrArg (tensorModuleFunctor F).map hVU
  rw [CategoryTheory.Functor.map_comp,tensorModuleFunctor_smul,
    CategoryTheory.Functor.map_id] at he
  have hb := homology_length_le_of_scalar_retract
    ((tensorModuleFunctor F).map V) ((tensorModuleFunctor F).map U) g he i hgi hfin
  rw [tensorModule_homology_length_free F (ModuleCat.of R (Fin r → R)) i] at hb
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hb
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionComplexCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
lemma restriction_homology_length
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    Module.length R
      ((((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) =
      Module.length S (F.homology i) := by
  rw [(restrictionHomologyIso (algebraMap R S) F i).toLinearEquiv.length_eq]
  let M := (ModuleCat.restrictScalars (algebraMap R S)).obj (F.homology i)
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  exact RootTower.length_eq_of_residue_surjective hres M

lemma restriction_scalar_quotient_homology_length
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (g : R) (i : ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => (algebraMap R S g) • x)) :
    Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
      (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj F)).homology i) =
      Module.length S (((complexQuotient (Ideal.span {algebraMap R S g}) (.up ℤ)).obj F).homology i) := by
  let E := (ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)
  let e := scalarQuotientTransport E F (algebraMap R S g) g (by
    rw [restrictScalars_complex_smul,CategoryTheory.Functor.map_id]) hg hg
  rw [← (homologyMapIso e i).toLinearEquiv.length_eq]
  exact restriction_homology_length hres _ i

 
theorem exists_scalar_extension_homology_bound_oai
    [IsDomain R] [IsNoetherianRing R] [Module.Finite R S]
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))) :
    ∃ (r : ℕ) (g : R), g ≠ 0 ∧ ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
      (∀ j,Function.Injective (fun x : (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).X j =>
        (algebraMap R S g) • x)) →
      Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≠ ⊤ →
      Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≤
        r • Module.length R (F.homology i) +
          Module.length S (((complexQuotient (Ideal.span {algebraMap R S g}) (.up ℤ)).obj
            (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F)).homology i) := by
  obtain ⟨r,g,hg,hbound⟩ := exists_tensor_homology_bound (ModuleCat.of R S)
  refine ⟨r,g,hg,fun F i hgi hfin => ?_⟩
  let G := ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj F
  let H := ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj G
  let e := tensorScalarExtensionIso F (S:=S)
  have hlen := (homologyMapIso e i).toLinearEquiv.length_eq.trans (restriction_homology_length hres G i)
  have hT (j : ℤ) : Function.Injective (fun x : ((tensorModuleFunctor F).obj (ModuleCat.of R S)).X j => g • x) := by
    let a := ((eval (ModuleCat R) (.up ℤ) j).mapIso e).toLinearEquiv
    intro x y hxy
    apply a.injective
    apply hgi j
    exact (a.map_smul g x).symm.trans ((congrArg a hxy).trans (a.map_smul g y))
  have hb := hbound F i hT (by rw [hlen]; exact hfin)
  rw [hlen] at hb
  have heq := (homologyMapIso ((complexQuotient (Ideal.span {g}) (.up ℤ)).mapIso e) i).toLinearEquiv.length_eq
  rw [heq,restriction_scalar_quotient_homology_length hres G g i hgi] at hb
  exact hb
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.exists_scalar_extension_homology_bound_oai.{u} := @OAI.Lech.exists_scalar_extension_homology_bound_oai.{u}
