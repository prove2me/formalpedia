-- Prove2me | solution 1 for OAI.Lech.ReesRoot.fibreCech_homology
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:47:41.97624+00:00
-- url     : https://prove2.me/submissions/9ad6ef8e-618e-4bae-8c35-63284ac7e67d

import Mathlib
import Definitions.Def_OAIQ032L036
import Definitions.Def_OAIQ032L038
import Theorems.Thm_OAI_Lech_ReesRoot_coefficientComparisonLinear_kernel_zero
import Theorems.Thm_OAI_Lech_TensorIdeal_fibreMap_kernel_zero

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
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


namespace Lech.Homogeneous

section
open HomogeneousLocalization SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]


variable (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)


lemma kernel_fraction {f : A} {d : ℕ} (hf : f ∈ G d)
    (x : LinearMap.ker (awayMap G H g hg f)) :
    ∃ (n : ℕ) (a : LinearMap.ker (gradedMap G H g hg (n*d))),
      fraction G hf n a = (x : Away G f) := by
  obtain ⟨n,a,ha,hax⟩ := Away.mk_surjective G hf x
  have hz := x.2
  change awayMap G H g hg f x = 0 at hz
  rw [←hax] at hz
  change Away.map g f (Away.mk G hf n a ha) = 0 at hz
  rw [Away.map_mk] at hz
  have hv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk,val_zero,Localization.mk_eq_mk'] at hv
  obtain ⟨⟨s,hs⟩,he⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hv
  obtain ⟨k,rfl⟩ := hs
  have hmem : f^k*a ∈ G ((k+n)*d) := by
    rw [add_mul]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul,Nat.cast_id] using
      (pow_mem_graded k hf)) (by simpa only [nsmul_eq_mul,Nat.cast_id] using ha)
  have hker : gradedMap G H g hg ((k+n)*d) ⟨f^k*a,hmem⟩ = 0 := by
    apply Subtype.ext
    change g (f^k*a) = 0
    simpa only [map_mul,map_pow] using he
  refine ⟨k+n,⟨⟨f^k*a,hmem⟩,hker⟩,?_⟩
  rw [← hax]
  apply val_injective (Submonoid.powers f)
  simp only [fraction,LinearMap.coe_mk,AddHom.coe_mk,Away.val_mk]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

end


open HomogeneousLocalization SetLike Graded
open CategoryTheory CategoryTheory.Limits
universe u

end Lech.Homogeneous


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] Homogeneous.awayAddCommGroup
variable (ell : AllModuleLength R)
attribute [local instance] kernel_addCommGroup kernel_module

include hz in
lemma chart_surjective {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ}
    (hf : f ∈ sourceGrade I h d) : Function.Surjective (chartMapR I z hz f) := by
  unfold chartMapR
  apply Homogeneous.awayMap_surjective (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
      (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) hf
  exact mapR_surjective I z hz
end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ActualCechTranspose
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
namespace Lech

section


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


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
 

lemma homology_isoModSerre_of_termwise {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ i, P.isoModSerre (f.f i)) (i : ι) :
    P.isoModSerre (homologyMap f i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  have (j : ι) : IsIso (((Q.mapHomologicalComplex c).map f).f j) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (f.f j)).mpr (hf j)
  have : IsIso ((Q.mapHomologicalComplex c).map f) := Hom.isIso_of_components _
  exact (quasiIsoAt_localization_iff P f i).mp inferInstance
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionChartKernel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
lemma powerTorsion_submodule {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hT : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R N) := by
  obtain ⟨a,ha⟩ := hT
  exact ⟨a,ha.trans (N.subtype.annihilator_le_of_injective N.injective_subtype)⟩
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

include ha hb hka hkb hsq in
lemma fibreMap_surjective (hg : Function.Surjective g) :
    Function.Surjective (fibreMap I (A:=A) (B:=B) V) := by
  intro x
  obtain ⟨y,hy⟩ := LinearMap.rTensor_surjective V hg (quotientTensorEquiv I b hb hkb V x)
  refine ⟨(quotientUnitTensorEquiv I a ha hka V).symm y,?_⟩
  apply (quotientTensorEquiv I b hb hkb V).injective
  rw [fibre_square I a b g ha hb hka hkb hsq V,LinearEquiv.apply_symm_apply,hy]

end Square
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
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
namespace Lech

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v w u' v'
variable {A : Type u'} [Category.{v'} A] [Abelian A]
lemma pi_isoModSerre (P : ObjectProperty A) [P.IsSerreClass]
    {ι : Type w} [Finite ι] {M N : ι → A} [HasProduct M] [HasProduct N]
    (f : ∀ i, M i ⟶ N i) (hf : ∀ i, P.isoModSerre (f i)) :
    P.isoModSerre (Limits.Pi.map f) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  have (i : ι) : IsIso (Q.map (f i)) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (f i)).mpr (hf i)
  have he : Q.map (Limits.Pi.map f) ≫ piComparison Q N =
      piComparison Q M ≫ Limits.Pi.map (fun i => Q.map (f i)) := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
    rw [← Q.map_comp, Limits.Pi.map_π, Q.map_comp]
    rw [← Category.assoc, piComparison_comp_π]
  have : IsIso (Q.map (Limits.Pi.map f) ≫ piComparison Q N) := by
    rw [he]
    infer_instance
  have : IsIso (Q.map (Limits.Pi.map f)) := IsIso.of_isIso_comp_right _ (piComparison Q N)
  exact (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (Limits.Pi.map f)).mp inferInstance

end


open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Finite ι]
  {M N : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

omit [Finite ι] in
lemma piLinear_factorization :
    ModuleCat.ofHom (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      (ModuleCat.piIsoPi (fun i => ModuleCat.of R (M i))).inv ≫
      Limits.Pi.map (fun i => ModuleCat.ofHom (f i)) ≫
      (ModuleCat.piIsoPi (fun i => ModuleCat.of R (N i))).hom := by
  apply (cancel_mono (ModuleCat.piIsoPi (fun i => ModuleCat.of R (N i))).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc,Limits.Pi.map_π,
    ModuleCat.piIsoPi_inv_kernel_ι]
  rw [← Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι]
  rfl

lemma piLinear_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hf : ∀ i, P.isoModSerre (ModuleCat.ofHom (f i))) :
    P.isoModSerre (ModuleCat.ofHom (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i)))) := by
  rw [piLinear_factorization]
  exact P.isoModSerre.comp_mem _ _
    (P.isoModSerre_of_isIso _)
    (P.isoModSerre.comp_mem _ _ (pi_isoModSerre P _ hf) (P.isoModSerre_of_isIso _))

lemma isoModSerre_of_surjective_kernel
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hsurj : Function.Surjective f) (hk : P (ModuleCat.of R f.ker)) :
    P.isoModSerre (ModuleCat.ofHom f) := by
  have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  rw [P.isoModSerre_iff_of_epi]
  exact (P.prop_iff_of_iso (ModuleCat.kernelIsoKer (ModuleCat.ofHom f))).mpr hk
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.FilteredFraction


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)


lemma quotientGraded_surjective : Function.Surjective (quotientGraded I) :=
  Ideal.Quotient.mk_surjective

attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap quotientGraded
attribute [local instance] TwistedLocalization.kernelAdd TwistedLocalization.kernelModule

lemma quotientTwist_surjective (t : ℕ) : Function.Surjective (quotientTwist I hw t) := by
  unfold quotientTwist
  apply TwistedLocalization.pieceMap_surjective
  exact quotientGraded_surjective I

end Lech.FilteredFraction


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealQuotientFunctor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma quotient_torsion (M : Type u) [AddCommGroup M] [Module R M] :
    powerTorsion I (ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [←Submodule.Quotient.mk_smul,Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

variable {ι : Type} [Fintype ι] (M N : ι → Type u)
  [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)]
  [∀ i,AddCommGroup (N i)] [∀ i,Module R (N i)]
  (f : ∀ i,M i →ₗ[R] N i)

lemma quotientPiMap_square (x : (∀ i,M i) ⧸ (I • (⊤ : Submodule R (∀ i,M i)))) :
    quotientPiEquiv I N
      (idealQuotientMap I (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) x) =
        fun i => idealQuotientMap I (f i) (quotientPiEquiv I M x i) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [idealQuotientMap_mk,quotientPiEquiv_mk,quotientPiEquiv_mk]
    rfl

lemma quotientPiMap_factor :
    (quotientFunctor I).map (ModuleCat.ofHom
      (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i)))) =
    (quotientPiEquiv I M).toModuleIso.hom ≫
      ModuleCat.ofHom (LinearMap.pi (fun i => (idealQuotientMap I (f i)).comp (LinearMap.proj i))) ≫
        (quotientPiEquiv I N).toModuleIso.inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (quotientPiEquiv I N).injective
  change quotientPiEquiv I N (idealQuotientMap I _ x) =
    quotientPiEquiv I N ((quotientPiEquiv I N).symm _)
  rw [LinearEquiv.apply_symm_apply]
  exact quotientPiMap_square I M N f x

lemma quotientPi_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hf : ∀ i,P.isoModSerre (ModuleCat.ofHom (idealQuotientMap I (f i)))) :
    P.isoModSerre ((quotientFunctor I).map (ModuleCat.ofHom
      (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))))) := by
  let e := (quotientPiEquiv I M).toModuleIso
  let e' := (quotientPiEquiv I N).toModuleIso
  have hM : P.isoModSerre e.hom := P.isoModSerre_of_isIso e.hom
  have hN : P.isoModSerre e'.inv := P.isoModSerre_of_isIso e'.inv
  have hp := piLinear_isoModSerre (fun i => idealQuotientMap I (f i)) P hf
  rw [quotientPiMap_factor]
  exact P.isoModSerre.comp_mem _ _ hM (P.isoModSerre.comp_mem _ _ hp hN)

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)

variable (I : Ideal R)

namespace Map
variable {D} {E : Diagram R ι} (φ : Map D E)
variable (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]

omit [LinearOrder ι] in
lemma cochains_isoModSerre (hφ : ∀ s,P.isoModSerre (φ.app s)) (q : ℕ) :
    P.isoModSerre (ModuleCat.ofHom (φ.cochains q)) :=
  piLinear_isoModSerre (fun s : Set.powersetCard ι q => (φ.app s.val).hom) P
    (fun s => hφ s.val)

lemma positiveHomology_isoModSerre (hφ : ∀ s,P.isoModSerre (φ.app s)) (q : ℕ) :
    P.isoModSerre (HomologicalComplex.homologyMap φ.positiveComplex q) :=
  homology_isoModSerre_of_termwise P φ.positiveComplex
    (fun q => φ.cochains_isoModSerre P hφ (q+1)) q
end Map
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_HomogeneousFunctor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech
lemma linearEquiv_mem_ideal_smul_top_iff {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) (x : M) :
    e x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have hmap : Submodule.map e.toLinearMap (I • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  rw [←hmap]
  constructor
  · rintro ⟨y,hy,he⟩
    exact e.injective he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProjectiveReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CoefficientReduction
open MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (h : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup



lemma homogeneous_mem_smul (j : ℕ) (a : grade (R:=R) h j)
    (ha : graded I h a.val=0) : a ∈ I • (⊤ : Submodule R (grade (R:=R) h j)) := by
  classical
  let b (e : (Fin h →₀ ℕ)) : grade (R:=R) h j :=
    if he : e.degree=j then ⟨monomial e 1,isHomogeneous_monomial 1 he⟩ else 0
  have hd (e : Fin h →₀ ℕ) (he : e ∈ a.val.support) : e.degree=j := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using a.property (mem_support_iff.mp he)
  have heq : a = ∑ e ∈ a.val.support, a.val.coeff e • b e := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul]
    conv_lhs => rw [a.val.as_sum]
    apply Finset.sum_congr rfl
    intro e he
    dsimp [b]
    rw [dite_eq_left (hd e he)]
    simp only [smul_monomial,smul_eq_mul,mul_one]
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hh := congrArg (fun polynomial : MvPolynomial (Fin h) (R ⧸ I) => polynomial.coeff e) ha
  change (MvPolynomial.map (Ideal.Quotient.mk I) a.val).coeff e=
    (0 : MvPolynomial (Fin h) (R ⧸ I)).coeff e at hh
  simpa only [coeff_map,MvPolynomial.coeff_zero] using hh

variable {f : MvPolynomial (Fin h) R} {d : ℕ} (hf : f ∈ grade (R:=R) h d)

lemma target_scalar_zero (r : R) (hr : r ∈ I)
    (x : Away (SourceGraded.sourceGrade I h) (graded I h f)) : r • x=0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_smul,HomogeneousLocalization.val_zero]
  rw [←IsScalarTower.algebraMap_smul (R ⧸ I) r x.val]
  change (Ideal.Quotient.mk I r) • x.val=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr,zero_smul]

include hf in
 
lemma chartMap_kernel : (chartMap I h f).ker = I • (⊤ : Submodule R (Away (grade (R:=R) h) f)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨j,a,ha⟩ := Homogeneous.kernel_fraction (grade (R:=R) h)
      (SourceGraded.sourceGrade I h) (graded I h) (graded_smul I h) hf ⟨x,hx⟩
    change Homogeneous.fraction (grade (R:=R) h) hf j a.val=x at ha
    rw [←ha]
    have hm := homogeneous_mem_smul I h (j*d) a.val (congrArg Subtype.val a.property)
    have hp := Submodule.mem_map_of_mem (f:=Homogeneous.fraction (grade (R:=R) h) hf j) hm
    rw [Submodule.map_smul'',Submodule.map_top] at hp
    exact Submodule.smul_mono le_rfl le_top hp
  · apply Submodule.smul_le.mpr
    intro r hr x _
    rw [LinearMap.mem_ker,map_smul]
    exact target_scalar_zero I h r hr _


end Lech.CoefficientReduction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local irreducible] quotientGraded Homogeneous.awayMap TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap

attribute [local instance] OAI.Lech.FilteredFraction.reesChartCommRing
attribute [local instance] OAI.Lech.FilteredFraction.reesChartModule
lemma chartReduction_surjective : Function.Surjective (chartReduction I hw) :=
  (exceptionalChartEquiv I hw).symm.surjective.comp ((quotientTwist_surjective I hw 0).comp
    (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).surjective)

lemma chartReduction_layerMap (x : ReesChart I hw) :
    exceptionalChartEquiv I hw (chartReduction I hw x) =
        layerMap I hw 0 (chartEquiv I hw x) := by
  change _ = quotientTwist I hw 0 ((reesEquiv I hw 0).symm
    ((reesEquiv I hw 0) (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw) x)))
  rw [LinearEquiv.symm_apply_apply]
  unfold chartReduction
  exact LinearEquiv.apply_symm_apply _ _

attribute [local irreducible] TwistedLocalization.ambientMap

lemma chartReduction_eq_zero_iff (x : ReesChart I hw) :
    chartReduction I hw x=0 ↔ chartFraction I hw x ∈ piece I w d 1 := by
  have he : chartReduction I hw x=0 ↔ layerMap I hw 0 (chartEquiv I hw x)=0 := by
    rw [←chartReduction_layerMap]
    exact (LinearEquiv.map_eq_zero_iff _).symm
  rw [he,←LinearMap.mem_ker,layerMap_kernel]
  rfl

include hw in
lemma scalar_mem_next {r : R} (hr : r ∈ I) (x : piece I w d 0) :
    r • x.val ∈ piece I w d 1 := by
  obtain ⟨j,b,hb⟩ := exists_fraction I w d hw 0 x
  have hmem : r*b.val ∈ I^(j*d+1) := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul hr (by simpa only [Nat.add_zero] using b.property)
  have he : r • fraction I w d 0 j b = fraction I w d 1 j ⟨r*b.val,hmem⟩ := by
    change r • Localization.mk b.val (⟨w^j,j,rfl⟩ : Submonoid.powers w) =
      Localization.mk (r*b.val) (⟨w^j,j,rfl⟩ : Submonoid.powers w)
    simpa only [smul_eq_mul] using (Localization.smul_mk r b.val (⟨w^j,j,rfl⟩ : Submonoid.powers w))
  rw [←hb,he]
  exact fraction_mem I w d 1 j _

 

attribute [local instance] OAI.Lech.FilteredFraction.reesChartTower
lemma chartReduction_kernel {z c : R} {k : ℕ} (hz : z∈I) (hc : c∈I^k)
    (hwc : z*c=w) (hdk : k+1=d) :
    (chartReduction I hw).ker=I • (⊤ : Submodule R (ReesChart I hw)) := by
  apply le_antisymm
  · intro x hx
    have hx1 := (chartReduction_eq_zero_iff I hw x).mp (LinearMap.mem_ker.mp hx)
    let y : piece I w d 1 := ⟨chartFraction I hw x,hx1⟩
    let v := divide I hw hc hdk 0 1 y
    have hv : z • v = chartEquiv I hw x := by
      have hh := smul_divide I hw hc hwc hdk 0 1 y
      apply Subtype.ext
      change z • (divide I hw hc hdk 0 1 y).val = chartFraction I hw x
      simpa only [pow_one,Submodule.coe_smul,Submodule.coe_inclusion] using congrArg Subtype.val hh
    have he : z • (chartEquiv I hw).symm v=x := by
      apply (chartEquiv I hw).injective
      rw [map_smul,LinearEquiv.apply_symm_apply]
      exact hv
    rw [←he]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  · apply Submodule.smul_le.mpr
    intro r hr x _
    rw [LinearMap.mem_ker,chartReduction_eq_zero_iff,map_smul]
    exact scalar_mem_next I hw hr (chartEquiv I hw x)



end Lech.FilteredFraction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p2
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p2
lemma reduction_surjective (s : Finset (Fin (n+1))) : Function.Surjective (reduction I z hz s) :=
  (exceptionalRename I z hz s).symm.surjective.comp
    ((FilteredFraction.chartReduction_surjective I (product_mem I z hz s)).comp
      (chartRename I z hz s).surjective)

attribute [local instance] OAI.Lech.ReesRoot.renamedModule
lemma reduction_eq_zero_iff (s : Finset (Fin (n+1))) (x : Ring I z hz s) :
    reduction I z hz s x=0 ↔
      FilteredFraction.chartReduction I (product_mem I z hz s) (chartRename I z hz s x)=0 := by
  change (exceptionalRename I z hz s).symm _=0 ↔ _
  exact map_eq_zero_iff _ (exceptionalRename I z hz s).symm.injective

lemma renamed_reduction_kernel (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    letI := renamedModule I z hz s
    (FilteredFraction.chartReduction I (product_mem I z hz s)).ker =
      I • (⊤ : Submodule R (FilteredFraction.ReesChart I (product_mem I z hz s))) := by
  classical
  let k := hs.choose
  have hk : k∈s := hs.choose_spec
  exact FilteredFraction.chartReduction_kernel I (product_mem I z hz s)
    (hz k) (product_mem I z hz (s.erase k)) (Finset.mul_prod_erase s z hk)
      (Finset.card_erase_add_one hk)

private lemma renamed_reduction_zero_iff (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (x : FilteredFraction.ReesChart I (product_mem I z hz s)) :
    letI := renamedModule I z hz s
    FilteredFraction.chartReduction I (product_mem I z hz s) x = 0 ↔
      x ∈ (I • ⊤ : Submodule R (FilteredFraction.ReesChart I (product_mem I z hz s))) := by
  change x ∈ (FilteredFraction.chartReduction I (product_mem I z hz s)).ker ↔ _
  rw [renamed_reduction_kernel I z hz s hs]

attribute [local instance] OAI.Lech.ReesRoot.baseModule_p1
lemma reduction_kernel (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    (reduction I z hz s).toLinearMap.ker = I • (⊤ : Submodule R (Ring I z hz s)) := by
  let := baseModule_p1 I z hz s
  let := renamedModule I z hz s
  ext x
  change reduction I z hz s x = 0 ↔ x ∈ _
  exact (reduction_eq_zero_iff I z hz s x).trans
    ((renamed_reduction_zero_iff I z hz s hs (chartRename I z hz s x)).trans
      (linearEquiv_mem_ideal_smul_top_iff I (chartRename I z hz s).toLinearEquiv x))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalCoefficientSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

lemma coefficientComparison_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientComparison I z hz hgen s) :=
  (coefficientTargetRename I z hz hgen s).surjective.comp
    (SourceGraded.chart_surjective I z hgen (coefficientDenominator_mem I s))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalFibre
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory IdealGraded HomogeneousLocalization
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.coefRing
attribute [local instance] OAI.Lech.ReesRoot.coefModule
attribute [local instance] OAI.Lech.ReesRoot.coefficientPModule
lemma coefficientReductionLinear_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientReductionLinear I s) := coefficientReduction_surjective I s
attribute [local instance] OAI.Lech.ReesRoot.exRing
attribute [local instance] OAI.Lech.ReesRoot.reesRing_p0
attribute [local instance] OAI.Lech.ReesRoot.exModule
attribute [local instance] OAI.Lech.ReesRoot.reesModule_p0
attribute [local instance] OAI.Lech.ReesRoot.exceptionalPModule
attribute [local instance] OAI.Lech.ReesRoot.reesPModule_p0
lemma reductionLinear_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (reductionLinear I z hz s) := reduction_surjective I z hz s
lemma coefficientComparisonLinear_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientComparisonLinear I z hz hgen s) := coefficientComparison_surjective I z hz hgen s

lemma coefficientReductionLinear_kernel (s : Finset (Fin (n+1))) :
    ((coefficientReductionLinear I s).restrictScalars R).ker =
      I • (⊤ : Submodule R (ProjectiveRoot.Ring R n s)) := by
  change (coefficientReduction I s).ker=_
  exact CoefficientReduction.chartMap_kernel I (n+1) (ProjectiveRoot.product_homogeneous R n s)

lemma reductionLinear_kernel (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    ((reductionLinear I z hz s).restrictScalars R).ker = I • (⊤ : Submodule R (Ring I z hz s)) :=
  reduction_kernel I z hz s hs

lemma coefficient_torsion (s : Finset (Fin (n+1))) :
    powerTorsion I (ModuleCat.of R (CoefficientRing I s)) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  exact CoefficientReduction.target_scalar_zero I (n+1) r hr

attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p0
lemma fibre_unit_square (s : Finset (Fin (n+1))) :
    reductionLinear I z hz s 1 = coefficientComparisonLinear I z hz hgen s
      (coefficientReductionLinear I s 1) := by
  change reduction I z hz s 1 = coefficientComparison I z hz hgen s (coefficientReduction I s 1)
  rw [←local_square]
  simp only [map_one]

attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p1
private local instance reesScalarComm_r0e1c7f_1 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionModule_r0e1c7f_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
include hgen in
lemma rootFibreMap_surjective (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Function.Surjective (rootFibreMap I z hz s hs m) :=
  TensorIdeal.fibreMap_surjective I (coefficientReductionLinear I s) (reductionLinear I z hz s)
    (coefficientComparisonLinear I z hz hgen s) (coefficientReductionLinear_surjective I s)
    (reductionLinear_surjective I z hz s) (coefficientReductionLinear_kernel I s)
    (reductionLinear_kernel I z hz s hs) (fibre_unit_square I z hz hgen s)
    (ProjectiveRoot.Sections R n s hs m) (coefficientComparisonLinear_surjective I z hz hgen s)

include hgen in
lemma rootFibreMap_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    ell.value (ModuleCat.of R (rootFibreMap I z hz s hs m).ker)=0 := by
  apply TensorIdeal.fibreMap_kernel_zero I (coefficientReductionLinear I s)
    (reductionLinear I z hz s) (coefficientComparisonLinear I z hz hgen s)
    (coefficientReductionLinear_surjective I s) (reductionLinear_surjective I z hz s)
    (coefficientReductionLinear_kernel I s) (reductionLinear_kernel I z hz s hs)
    (fibre_unit_square I z hz hgen s) (ProjectiveRoot.Sections R n s hs m) ell hds
  · exact coefficientComparisonLinear_surjective I z hz hgen s
  · exact coefficient_torsion I s
  · exact coefficientComparisonLinear_kernel_zero I z hz hgen ell hds hmu ha s

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootFibreCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

variable (m : Fin n → ℤ)

variable (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

attribute [local instance] OAI.Lech.ReesRoot.reesRing_p2
attribute [local instance] OAI.Lech.ReesRoot.reesModule_p2
attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p2
attribute [local instance] OAI.Lech.ReesRoot.reesPModule_p2
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p12
attribute [local instance] OAI.Lech.ReesRoot.sectionModule_p6
attribute [local instance] OAI.Lech.ReesRoot.indexFinite
attribute [local instance] OAI.Lech.ReesRoot.projectiveSectionModule
include hgen hds hmu ha in
lemma fibreCechMap_isoModSerre (s : Finset (Fin (n+1))) :
    ell.zeroClass.isoModSerre ((fibreCechMap I z hz m).app s) := by
  change ell.zeroClass.isoModSerre ((TensorIdeal.quotientFunctor I).map (unitCech I z hz m s))
  apply TensorIdeal.quotientPi_isoModSerre I
    (fun hs : PLift s.Nonempty => ProjectiveRoot.Sections R n s hs.down m)
    (fun hs : PLift s.Nonempty => Sections I z hz s hs.down m)
    (fun hs => TensorIdeal.unitMap (A:=ProjectiveRoot.Ring R n s) (B:=Ring I z hz s)
      (ProjectiveRoot.Sections R n s hs.down m)) ell.zeroClass
  intro hs
  change ell.zeroClass.isoModSerre (ModuleCat.ofHom (rootFibreMap I z hz s hs.down m))
  apply isoModSerre_of_surjective_kernel ell.zeroClass
  · exact rootFibreMap_surjective I z hz hgen s hs.down m
  · exact ⟨powerTorsion_submodule I _ (TensorIdeal.quotient_torsion I _),
      rootFibreMap_kernel_zero I z hz hgen ell hds hmu ha s hs.down m⟩

include hgen hds hmu ha in
 

theorem fibreCech_homology_oai (q : ℕ) :
    ell.zeroClass.isoModSerre
      (homologyMap (fibreCechMap I z hz m).positiveComplex q) :=
  (fibreCechMap I z hz m).positiveHomology_isoModSerre ell.zeroClass
    (fibreCechMap_isoModSerre I z hz m hgen ell hds hmu ha) q

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.fibreCech_homology_oai.{u} := @OAI.Lech.ReesRoot.fibreCech_homology_oai.{u}
