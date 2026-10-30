-- Prove2me | solution 1 for OAI.Tachikawa.SourceField.sourceCone_closed_boundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T02:55:24.074762+00:00
-- url     : https://prove2.me/submissions/8cf0af03-b47b-41fe-a0ba-e2cb10f2614e

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta016
import Theorems.Thm_OAI_Tachikawa_SourceField_sourceDelta_bijective

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.evaluation_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_bounded _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_isKProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finiteAlg _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_leftProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_rightProjective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instAddCommGroupRightIndType _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindCoker _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindEndo _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindIterate _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgLeftIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightFreeFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteAlgCarrierXNatModuleCatComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgRegular _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgTwistedRegular _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerRightIndType _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType_1 _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instProjectiveMulOppositeObjTwistedRegular _root_.OAI.Tachikawa.Enveloping.instProjectiveMulOppositeObjXNatModuleCatAlgComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instProjectiveObjTwistedRegular _root_.OAI.Tachikawa.Enveloping.instProjectiveObjXNatModuleCatAlgComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.leftFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.Enveloping.rightFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.HomBimodule.instEpiModuleCatAlgPostMap _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable [FiniteDimensional k R] (M : ModuleCat (Alg k R R))
  [FiniteDimensional k (Obj M)] [Module.Projective R (Obj M)]
  [Module.Projective Rᵐᵒᵖ (Obj M)]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))
  (v : N.obj ⟶ (tensorFunctor M).obj N.obj)

lemma tensorCompleteLift_aug : (tensorCompleteLift M N t v).f 0 ≫
    (tensorFunctor M).map (ModuleCat.ofHom N.cover.map) = ModuleCat.ofHom N.cover.map ≫ v :=
  (exists_tensorCompleteLift M N t v).choose_spec

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

variable {k : Type} [Field k] [Algebra k R]

lemma exists_good_component_zero (hp : TotallyAcyclic P)
    (pproj : Module.Projective R (P.X 0))
    (hf : CokerAt.map f 0 ∈ projectiveFactors (k := k)) :
    Nonempty (CompleteNull.State f 0) := by
  obtain ⟨J, hJf, hJp, a, b, hab⟩ := hf
  let := hJf
  let := hJp
  let := pproj
  obtain ⟨a', ha⟩ := hp.extend_at 0 (-1) rfl a
  obtain ⟨b', hb⟩ := Module.projective_lifting_property (CokerAt.π Q 0) b
    (CokerAt.π_surjective Q 0)
  let r := (f.f 0).hom - (b'.comp a').comp (P.d 0 (-1)).hom
  have hr (x : P.X 0) : r x ∈ LinearMap.range (Q.d 1 0).hom := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change CokerAt.π Q 0 (r x) = 0
    have ha' := LinearMap.congr_fun ha (CokerAt.π P 0 x)
    change a' (P.d 0 (-1) x) = a (CokerAt.π P 0 x) at ha'
    have hb' := LinearMap.congr_fun hb (a (CokerAt.π P 0 x))
    change CokerAt.π Q 0 (b' (a (CokerAt.π P 0 x))) = b (a (CokerAt.π P 0 x)) at hb'
    have hab' := LinearMap.congr_fun hab (CokerAt.π P 0 x)
    change b (a (CokerAt.π P 0 x)) = CokerAt.π Q 0 (f.f 0 x) at hab'
    change CokerAt.π Q 0 (f.f 0 x - b' (a' (P.d 0 (-1) x))) = 0
    rw [map_sub, ha', hb', hab', sub_self]
  obtain ⟨c, hc⟩ := Module.projective_lifting_property
    (Q.d 1 0).hom.rangeRestrict (r.codRestrict _ hr)
    (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)
  have hc' : (Q.d 1 0).hom.comp c = r := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hc x)
  refine ⟨⟨c, ?_⟩⟩
  unfold GoodComponent
  change ((f.f 0).hom - (Q.d 1 0).hom.comp c).comp (P.d 1 0).hom = 0
  rw [hc']
  dsimp only [r]
  rw [sub_sub_cancel, LinearMap.comp_assoc]
  have hd : (P.d 0 (-1)).hom.comp (P.d 1 0).hom = 0 :=
    ModuleCat.hom_ext_iff.mp (P.d_comp_d _ _ _)
  rw [hd, LinearMap.comp_zero]

theorem nullhomotopic_of_coker_factors (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (hf : CokerAt.map f 0 ∈ projectiveFactors (k := k)) : Nonempty (Homotopy f 0) := by
  obtain ⟨b₀⟩ := exists_good_component_zero f hp (pproj 0) hf
  exact ⟨CompleteNull.homotopy f hp hq pproj qfin qproj b₀⟩

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableShift
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
  {K L M : HomologicalComplex (ModuleCat k) c}

lemma quotient_eq_zero_iff (i : I) (z : Z K i) :
    quotient K i z = 0 ↔ ∃ x, boundary K i x = z :=
  Submodule.Quotient.mk_eq_zero _

variable {K L M : CochainComplex (ModuleCat k) ℤ}

lemma quotient_zero_iff_predecessor (i : ℤ) (z : Z K i) :
    quotient K i z = 0 ↔ ∃ x : K.X (i-1), K.d (i-1) i x = z.val := by
  rw [quotient_eq_zero_iff]
  simp only [← Subtype.val_inj]
  change (∃ x : K.X ((ComplexShape.up ℤ).prev i),
    K.d ((ComplexShape.up ℤ).prev i) i x = z.val) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (i-1) i by change (i-1)+1=i; omega)]

lemma memZ_iff (i : ℤ) (x : K.X i) : x ∈ Z K i ↔ K.d i (i+1) x = 0 := by
  change K.d i ((ComplexShape.up ℤ).next i) x = 0 ↔ _
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i+1) from rfl)]

end Tachikawa.VectorSplit



namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {K L M : CochainComplex (ModuleCat k) ℤ}
  (i : K ⟶ L) (p : L ⟶ M)
  (hi : ∀ a, Function.Injective (i.f a))
  (he : ∀ a, Function.Exact (i.f a) (p.f a))
  (hp : ∀ a, Function.Surjective (p.f a))

lemma comm_apply {K L : CochainComplex (ModuleCat k) ℤ} (f : K ⟶ L)
    (a b : ℤ) (x : K.X a) : L.d a b (f.f a x) = f.f b (K.d a b x) :=
  congrArg (fun z => z x) (f.comm a b)

include hi he hp in

lemma Hmap_injective_of_prev_surjective (a : ℤ)
    (hs : Function.Surjective (Hmap p (a-1))) : Function.Injective (Hmap i a) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨z,rfl⟩ := quotient_surjective a x
  obtain ⟨v,hv⟩ := (quotient_zero_iff_predecessor a _).mp hx
  have hpv : p.f (a-1) v ∈ Z M (a-1) := by
    rw [memZ_iff,show a-1+1=a by omega,comm_apply p,hv]
    exact (he a _).mpr ⟨z.val,rfl⟩
  obtain ⟨c,hc⟩ := hs (quotient M (a-1) ⟨p.f (a-1) v,hpv⟩)
  obtain ⟨w,rfl⟩ := quotient_surjective (a-1) c
  have hw : quotient M (a-1) (⟨p.f (a-1) v,hpv⟩ - cycleMap p (a-1) w) = 0 := by
    rw [map_sub,← Hmap_quotient,hc,sub_self]
  obtain ⟨b,hb⟩ := (quotient_zero_iff_predecessor (a-1) _).mp hw
  obtain ⟨b',hb'⟩ := hp (a-1-1) b
  have hv' : p.f (a-1) (v-w.val-L.d (a-1-1) (a-1) b') = 0 := by
    rw [map_sub,map_sub,← comm_apply p,hb',hb]
    change p.f (a-1) v - p.f (a-1) w.val - (p.f (a-1) v-p.f (a-1) w.val) = 0
    exact sub_self _
  obtain ⟨u,hu⟩ := (he (a-1) _).mp hv'
  apply (quotient_zero_iff_predecessor a z).mpr
  refine ⟨u,?_⟩
  apply hi a
  rw [← comm_apply i,hu,map_sub,map_sub]
  have hwz := (memZ_iff (a-1) w.val).mp w.property
  rw [show a-1+1=a by omega] at hwz
  have hd := congrArg (fun f => f b') (L.d_comp_d (a-1-1) (a-1) a)
  change L.d (a-1) a (L.d (a-1-1) (a-1) b') = 0 at hd
  rw [hwz,hd,sub_zero,sub_zero]
  exact hv

include hi he hp in
lemma Hmap_injective_of_prev_zero (a : ℤ) (hz : Subsingleton (H M (a-1))) :
    Function.Injective (Hmap i a) := by
  apply Hmap_injective_of_prev_surjective i p hi he hp a
  intro x
  exact ⟨0,by rw [map_zero]; exact hz.elim _ _⟩

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) {M N L : ModuleCat.{0} R}

lemma completeHomMap_injective (i : M ⟶ N) (hi : Function.Injective i) (a : ℤ) :
    Function.Injective ((completeHomMap (k := k) P i).f a) := by
  change Function.Injective (fun f : P.X a ⟶ M => f ≫ i)
  intro f g h
  ext x
  exact hi (congrArg (fun z => z x) h)

lemma completeHomMap_exact (i : M ⟶ N) (p : N ⟶ L)
    (hi : Function.Injective i) (he : Function.Exact i p) (a : ℤ) :
    Function.Exact ((completeHomMap (k := k) P i).f a) ((completeHomMap (k := k) P p).f a) := by
  change Function.Exact (fun f : P.X a ⟶ M => f ≫ i) (fun f : P.X a ⟶ N => f ≫ p)
  intro f
  constructor
  · intro hf
    have hr (x : P.X a) : f x ∈ LinearMap.range i.hom :=
      (he (f x)).mp (congrArg (fun z => z x) hf)
    refine ⟨ModuleCat.ofHom (CokerAt.factorThrough i.hom hi f.hom hr),?_⟩
    exact ModuleCat.hom_ext (CokerAt.factorThrough_spec i.hom hi f.hom hr)
  · rintro ⟨g,rfl⟩
    ext x
    exact (he _).mpr ⟨g x,rfl⟩

lemma completeHomMap_surjective (p : N ⟶ L) (hp : Function.Surjective p)
    (proj : ∀ a, Module.Projective R (P.X a)) (a : ℤ) :
    Function.Surjective ((completeHomMap (k := k) P p).f a) := by
  let := proj a
  change Function.Surjective (fun f : P.X a ⟶ N => f ≫ p)
  intro f
  obtain ⟨g,hg⟩ := Module.projective_lifting_property p.hom f.hom hp
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)

lemma completeHom_projective_zero (hP : TotallyAcyclic P) (N : ModuleCat.{0} R)
    [Module.Finite R N] [Module.Projective R N] (a : ℤ) :
    Subsingleton (VectorSplit.H (completeHom (k := k) P N) a) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  obtain ⟨g,hg⟩ := hP.projective_boundaries a z.val.hom
    (ModuleCat.hom_ext_iff.mp ((completeHom_memZ P N a z.val).mp z.property))
  apply (VectorSplit.quotient_zero_iff_predecessor a z).mpr
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instInjectiveE _root_.OAI.Tachikawa.Construction.instIsScalarTowerEX _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in

lemma inducedRange_hom_zero (n : ℕ) (f : inducedRangeObj q n ⟶ simpleObj q) : f = 0 := by
  have hh : ModuleCat.ofHom (inducedD q n).hom.rangeRestrict ≫ f = 0 :=
    induced_positive_hom_zero q n _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x,y,hy⟩
  subst x
  exact congrArg (fun g : inducedObj q (n+1) ⟶ simpleObj q => g y) hh

omit [CharP k 2] in
lemma inducedRange_ext_zero_zero (n : ℕ) :
    Subsingleton (Ext (inducedRangeObj q n) (simpleObj q) 0) := by
  have : Subsingleton (inducedRangeObj q n ⟶ simpleObj q) :=
    subsingleton_of_forall_eq 0 (inducedRange_hom_zero q n)
  exact Ext.addEquiv₀.injective.subsingleton

omit [CharP k 2] in
lemma simple_ext_one_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 1) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 1) from Ext.subsingleton_of_projective _ _ 0
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (initial_shortExact q hp) (simpleObj q)
    x (Subsingleton.elim _ _) (n₀ := 0) (by omega)
  let : Subsingleton (Ext (initialShortComplex q hp).X₁ (simpleObj q) 0) :=
    inducedRange_ext_zero_zero q 0
  rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
  exact hy.symm

lemma firstRange_ext_one_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (inducedRangeObj q 0) (simpleObj q) 1) := by
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) 0) :=
    induced_positive_ext_zero q 0 0
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) 1) :=
    induced_positive_ext_zero q 0 1
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₁ (simpleObj q) 0) :=
    inducedRange_ext_zero_zero q 1
  exact (extShiftEquiv k (middle_shortExact q hq hp) (simpleObj q) 0).symm.injective.subsingleton

lemma simple_ext_two_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) 2) := by
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 1) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 1) from Ext.subsingleton_of_projective _ _ 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 2) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 2) from Ext.subsingleton_of_projective _ _ 1
  let : Subsingleton (Ext (initialShortComplex q hp).X₁ (simpleObj q) 1) :=
    firstRange_ext_one_zero q hq hp
  exact (extShiftEquiv k (initial_shortExact q hp) (simpleObj q) 1).symm.injective.subsingleton

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma simpleExt_zero_off_multiples (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n % 3 ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact simple_ext_one_zero q hp
    by_cases h2 : n = 2
    · subst n
      exact simple_ext_two_zero q hq hp
    have h3 : 3 ≤ n := by omega
    have hm : (n-3)%3 ≠ 0 := by omega
    have := ih (n-3) (by omega) hm
    have he : n = (n-3)+3 := by omega
    rw [he]
    exact (simpleExtPeriod q hq hp (n-3)).symm.injective.subsingleton

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma XExt_zero_off_multiples (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n % 3 ≠ 0) :
    Subsingleton (Ext (XTensorObj q) (XTensorObj q) n) := by
  have hcomp (t : TotalDualPairing.Diag n) :
      Subsingleton (Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
        Ext (C.simpleObj q) (C.simpleObj q) t.val.2) := by
    by_cases h : t.val.1 % 3 = 0
    · have h' : t.val.2 % 3 ≠ 0 := by
        have ht := t.property
        omega
      let := C.simpleExt_zero_off_multiples q hq hp t.val.2 h'
      infer_instance
    · let := C.simpleExt_zero_off_multiples q hq hp t.val.1 h
      infer_instance
  let := hcomp
  exact (XExtKunneth q n).injective.subsingleton

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

include hq hp in
lemma completeYHomology_zero (a : ℤ) (h3 : a ≠ -3) (h0 : a ≠ 0) :
    Subsingleton (VectorSplit.H
      (completeHom (k := k) (xComplete q) (MissingYProfile.finiteYX q).obj) a) := by
  let := (y_profile q hq hp a).2 h3 h0
  exact (completeYHomologyEquiv q hq hp a).injective.subsingleton

end Tachikawa.Construction



namespace Tachikawa.CompleteHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
  (proj : ∀ j, Module.Projective R (P.X j))

variable {X : ModuleCat.{0} R} (e : CokerAt P 0 ≃ₗ[R] X)

lemma zeroEquiv_natural {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (x : VectorSplit.H (completeHom (k := k) P M) 0) :
    zeroEquiv P hP fin proj e N (completeHmap P f 0 x) =
      stablePostcompose f.hom (zeroEquiv P hP fin proj e M x) := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective 0 x
  change stableClass (k := k) _ = stableClass (k := k) _
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨y,hy⟩ := CokerAt.π_surjective P 0 (e.symm x)
  change ((cokerCycles P N 0).symm
    (VectorSplit.cycleMap (completeHomMap P f) 0 z)) (e.symm x) =
    f (((cokerCycles P M 0).symm z) (e.symm x))
  rw [← hy]
  rfl

end Tachikawa.CompleteHom

namespace Tachikawa
variable {k V W : Type*} [Field k] [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W]
lemma linear_surjective_to_line (f : V →ₗ[k] W) (e : W ≃ₗ[k] k)
    (x : V) (hx : f x ≠ 0) : Function.Surjective f := by
  have hn : e (f x) ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
  intro y
  refine ⟨(e y / e (f x)) • x,?_⟩
  apply e.injective
  rw [map_smul,map_smul,smul_eq_mul,div_mul_cancel₀ _ hn]
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

include hq hp in
lemma positiveSelfHom_zero (n : ℕ) (hn : (n+1)%3 ≠ 0) :
    Subsingleton (VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ)) := by
  let := XExt_zero_off_multiples q hq hp (n+1) hn
  have he := extIso (k := k) (XTensorIso q).symm (XTensorIso q).symm (n+1)
  let : Subsingleton (Ext (xObj q) (xObj q) (n+1)) := he.injective.subsingleton
  exact (positiveSelfHomExt q n).injective.subsingleton

omit [CharP k 2] in
lemma selfHom_zero_of_dual (a : ℤ) (h : Subsingleton (VectorSplit.H (selfHom q) (-a-1))) :
    Subsingleton (VectorSplit.H (selfHom q) a) := by
  let := h
  let : Subsingleton (Module.Dual k (VectorSplit.H (selfHom q) (-a-1))) := by
    constructor
    intro f g
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0,map_zero,map_zero]
  exact (selfHomDual q a).injective.subsingleton

include hq hp in
lemma selfHom_zero_near : Subsingleton (VectorSplit.H (selfHom q) 1) ∧
    Subsingleton (VectorSplit.H (selfHom q) 2) ∧
    Subsingleton (VectorSplit.H (selfHom q) (-2)) ∧
    Subsingleton (VectorSplit.H (selfHom q) (-3)) := by
  have h1 := positiveSelfHom_zero q hq hp 0 (by decide)
  have h2 := positiveSelfHom_zero q hq hp 1 (by decide)
  exact ⟨h1,h2,selfHom_zero_of_dual q (-2) h1,selfHom_zero_of_dual q (-3) h2⟩

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

lemma wZero_ne_zero : wZero q hq hp ≠ 0 := by
  intro h
  have := congrArg (WZeroEquiv q hq hp) h
  simp [wZero] at this

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma concrete_evaluated_surjective : Function.Surjective
    (Enveloping.evalMap (xObj q) (concreteProjection q hq hp H₁ H₂ h₁ h₂)) :=
  Enveloping.evalMap_surjective (xObj q) _ (Enveloping.fiberProjection_surjective _ _ _ _ _)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma concreteVZero_fst : concreteVZero q hq hp H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap (xObj q) (concreteFst q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₁ h₁).inv :=
  (exists_concrete_vZero q hq hp H₁ H₂ h₁ h₂).choose_spec.1

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  {L M N Q : ModuleCat.{0} R} [Module.Finite R Q] [Module.Projective R Q]
  (i₁ : M ⟶ L) (i₂ : N ⟶ L) (i₃ : Q ⟶ L)
  (p₁ : L ⟶ M) (p₂ : L ⟶ N) (p₃ : L ⟶ Q)
  (h11 : i₁ ≫ p₁ = 𝟙 _) (h12 : i₁ ≫ p₂ = 0)
  (h21 : i₂ ≫ p₁ = 0) (h22 : i₂ ≫ p₂ = 𝟙 _)
  (hs : p₁ ≫ i₁ + p₂ ≫ i₂ + p₃ ≫ i₃ = 𝟙 _)

include hP h11 h12 h21 h22 hs in
lemma completeHpair_bijective (a : ℤ) : Function.Bijective
    ((completeHmap (k := k) P p₁ a).prod (completeHmap P p₂ a)) := by
  have pair_id : ((completeHmap (k := k) P i₁ a).comp (completeHmap P p₁ a) +
      (completeHmap P i₂ a).comp (completeHmap P p₂ a)) = LinearMap.id := by
    have hh := congrArg (fun f => completeHmap (k := k) P f a) hs
    simp only [completeHmap_add,completeHmap_comp,completeHmap_id] at hh
    have hz : (completeHmap (k := k) P i₃ a).comp (completeHmap P p₃ a) = 0 := by
      apply LinearMap.ext
      intro x
      let := completeHom_projective_zero (k := k) P hP Q a
      change completeHmap P i₃ a (completeHmap P p₃ a x) = 0
      rw [Subsingleton.elim (completeHmap P p₃ a x) 0,map_zero]
    rwa [hz,add_zero] at hh
  constructor
  · intro x y h
    have hf := congrArg (fun z => completeHmap P i₁ a z.1 + completeHmap P i₂ a z.2) h
    change (completeHmap P i₁ a).comp (completeHmap P p₁ a) x +
        (completeHmap P i₂ a).comp (completeHmap P p₂ a) x =
      (completeHmap P i₁ a).comp (completeHmap P p₁ a) y +
        (completeHmap P i₂ a).comp (completeHmap P p₂ a) y at hf
    simp only [← LinearMap.add_apply,pair_id,LinearMap.id_apply] at hf
    exact hf
  · rintro ⟨x,y⟩
    refine ⟨completeHmap P i₁ a x + completeHmap P i₂ a y,?_⟩
    apply Prod.ext
    · change completeHmap P p₁ a (_+_) = x
      rw [map_add,← LinearMap.comp_apply,← LinearMap.comp_apply,
        ← completeHmap_comp,← completeHmap_comp,h11,h21,completeHmap_id,completeHmap_zero]
      exact add_zero _
    · change completeHmap P p₂ a (_+_) = y
      rw [map_add,← LinearMap.comp_apply,← LinearMap.comp_apply,
        ← completeHmap_comp,← completeHmap_comp,h12,h22,completeHmap_id,completeHmap_zero]
      exact zero_add _
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

lemma fiber_sum_id : fiberFst U V Y ≫ fiberInl U V Y +
    fiberSnd U V Y ≫ fiberInm U V Y + fiberThird U V Y ≫ fiberInr U V Y = 𝟙 _ := by
  ext x
  change (x.1,(0,0)) + (0,(x.2.1,0)) + (0,(0,x.2.2)) = x
  rcases x with ⟨x,y,z⟩
  apply Prod.ext
  · change (x+0)+0=x
    simp
  · apply Prod.ext
    · change (0+y)+0=y
      simp
    · change (0+0)+z=z
      simp
end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma FHom_shortExact :
    (∀ a, Function.Injective ((FHomInclusion q hq hp H₁ H₂ h₁ h₂).f a)) ∧
    (∀ a, Function.Exact ((FHomInclusion q hq hp H₁ H₂ h₁ h₂).f a)
      ((FHomProjection q hq hp H₁ H₂ h₁ h₂).f a)) ∧
    (∀ a, Function.Surjective ((FHomProjection q hq hp H₁ H₂ h₁ h₂).f a)) :=
  ⟨completeHomMap_injective _ _ (concrete_evaluated_injective q hq hp H₁ H₂ h₁ h₂),
    completeHomMap_exact _ _ _ (concrete_evaluated_injective q hq hp H₁ H₂ h₁ h₂)
      (concrete_evaluated_exact q hq hp H₁ H₂ h₁ h₂),
    completeHomMap_surjective _ _ (concrete_evaluated_surjective q hq hp H₁ H₂ h₁ h₂)
      ((finiteX q).complete_projective (formE q))⟩

omit [CharP k 2] in
lemma middleHpair_bijective (a : ℤ) : Function.Bijective (middleHpair q H₁ H₂ h₁ h₂ a) := by
  let L := Enveloping.evaluation (k := k) (S := E q) (xObj q)
  let U := finiteU q H₁ h₁
  let V := finiteU q H₂ h₂
  let : Module.Finite (Enveloping.Alg k (E q) (E q)) (Enveloping.fiberCover (Y q)) := by
    exact inferInstanceAs (Module.Finite (Enveloping.Alg k (E q) (E q))
      (Fin (Y q).cover.rank → Enveloping.Alg k (E q) (E q)))
  let : Module.Projective (Enveloping.Alg k (E q) (E q)) (Enveloping.fiberCover (Y q)) := by
    exact inferInstanceAs (Module.Projective (Enveloping.Alg k (E q) (E q))
      (Fin (Y q).cover.rank → Enveloping.Alg k (E q) (E q)))
  let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (Enveloping.fiberCover (Y q)) :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := Enveloping.Alg k (E q) (E q))
      (M := Enveloping.fiberCover (Y q)) (fun _ _ => rfl)
  let : FiniteDimensional k (Enveloping.fiberCover (Y q)) :=
    Module.Finite.trans (R := k) (A := Enveloping.Alg k (E q) (E q)) _
  let : Module.Finite (E q) (L.obj (Enveloping.fiberCover (Y q))) :=
    Enveloping.eval_finite (xObj q)
  let : CategoryTheory.Projective (Enveloping.fiberCover (Y q)) :=
    ModuleCat.projective_of_categoryTheory_projective _
  let : CategoryTheory.Projective (L.obj (Enveloping.fiberCover (Y q))) :=
    Enveloping.evaluation_projective (xObj q) _
  let : Module.Projective (E q) (L.obj (Enveloping.fiberCover (Y q))) :=
    ModuleCat.projective_of_module_projective _
  change Function.Bijective
    ((completeHmap (k := k) (xComplete q) (L.map (Enveloping.fiberFst U V (Y q))) a).prod
      (completeHmap (xComplete q) (L.map (Enveloping.fiberSnd U V (Y q))) a))
  apply completeHpair_bijective (xComplete q) ((finiteX q).complete_totallyAcyclic (formE q))
    (L.map (Enveloping.fiberInl U V (Y q))) (L.map (Enveloping.fiberInm U V (Y q)))
    (L.map (Enveloping.fiberInr U V (Y q))) _ _ (L.map (Enveloping.fiberThird U V (Y q)))
  · rw [← L.map_comp,Enveloping.fiberInl_fst,L.map_id]
  · rw [← L.map_comp,Enveloping.fiberInl_snd,L.map_zero]
  · rw [← L.map_comp,Enveloping.fiberInm_fst,L.map_zero]
  · rw [← L.map_comp,Enveloping.fiberInm_snd,L.map_id]
  · rw [← L.map_comp,← L.map_comp,← L.map_comp,← L.map_add,← L.map_add,
      Enveloping.fiber_sum_id,L.map_id]

end Tachikawa.Construction



namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {K L M : CochainComplex (ModuleCat k) ℤ}
  (i : K ⟶ L) (p : L ⟶ M)
  (hi : ∀ a, Function.Injective (i.f a))
  (he : ∀ a, Function.Exact (i.f a) (p.f a))
  (hp : ∀ a, Function.Surjective (p.f a))

include hi he hp in
lemma Hmap_exact (a : ℤ) : Function.Exact (Hmap i a) (Hmap p a) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z,rfl⟩ := quotient_surjective a x
    obtain ⟨y,hy⟩ := (quotient_zero_iff_predecessor a _).mp hx
    obtain ⟨v,hv⟩ := hp (a-1) y
    have hz' : p.f a (z.val - L.d (a-1) a v) = 0 := by
      rw [map_sub,← comm_apply p,hv,hy]
      exact sub_self _
    obtain ⟨u,hu⟩ := (he a _).mp hz'
    have huz : u ∈ Z K a := by
      rw [memZ_iff]
      apply hi (a+1)
      rw [map_zero,← comm_apply i,hu,map_sub]
      rw [(memZ_iff a z.val).mp z.property]
      have hd := congrArg (fun f => f v) (L.d_comp_d (a-1) a (a+1))
      change L.d a (a+1) (L.d (a-1) a v) = 0 at hd
      rw [hd,sub_self]
    refine ⟨quotient K a ⟨u,huz⟩,?_⟩
    rw [Hmap_quotient]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (quotient_zero_iff_predecessor a _).mpr
    use -v
    change L.d (a-1) a (-v) = i.f a u - z.val
    rw [map_neg,hu]
    abel
  · rintro ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := quotient_surjective a y
    rw [Hmap_quotient,Hmap_quotient]
    have hz : cycleMap p a (cycleMap i a z) = 0 := by
      apply Subtype.ext
      exact (he a _).mpr ⟨z.val,rfl⟩
    rw [hz,map_zero]
end Tachikawa.VectorSplit



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma FHomProjection_zero_surjective : Function.Surjective
    (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0) := by
  let L := Enveloping.evaluation (k := k) (S := E q) (xObj q)
  let U := finiteU q H₁ h₁
  let V := finiteU q H₂ h₂
  let a := (uXIso q H₁ h₁).inv ≫ L.map (Enveloping.fiberInl U V (Y q))
  let x := (zeroHomEquiv q _).symm (stableClass (k := k) a.hom)
  let ep := zeroHomEquiv q (Enveloping.evalObj (xObj q) (Y q).obj)
  let ew := ep.trans (WZeroEquiv q hq hp)
  apply linear_surjective_to_line _ ew x
  intro hz
  have hn := CompleteHom.zeroEquiv_natural (xComplete q)
    ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    ((finiteX q).cokerEquiv (formE q)) (L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂)) x
  change ep (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0 x) = _ at hn
  have hez : ep (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0 x) = 0 :=
    (congrArg ep hz).trans (map_zero ep.toLinearMap)
  have hx : zeroHomEquiv q _ x = stableClass (k := k) a.hom := LinearEquiv.apply_symm_apply _ _
  rw [hx] at hn
  have ha : a ≫ L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂) =
      (uXIso q H₁ h₁).inv ≫ L.map (normalizedMap q hq hp H₁ h₁) := by
    change ((uXIso q H₁ h₁).inv ≫ L.map (Enveloping.fiberInl U V (Y q))) ≫
      L.map (Enveloping.fiberProjection U V (Y q) _ _) = _
    exact (Category.assoc _ _ _).trans (congrArg (fun morphism =>
      (uXIso q H₁ h₁).inv ≫ morphism) ((L.map_comp _ _).symm.trans
        (congrArg L.map (Enveloping.fiberInl_projection U V (Y q)
          (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)))))
  have hn' : stableClass (k := k) (a ≫ L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂)).hom = 0 := hn.symm.trans hez
  rw [ha] at hn'
  change evaluatedStableMap q H₁ h₁ (normalizedMap q hq hp H₁ h₁) = 0 at hn'
  rw [normalizedMap_class] at hn'
  exact wZero_ne_zero q hq hp hn'

omit [CharP k 2] in
lemma middleHpairX_bijective (a : ℤ) : Function.Bijective (middleHpairX q H₁ H₂ h₁ h₂ a) := by
  dsimp only [middleHpairX, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact Function.Bijective.comp (LinearEquiv.bijective _) (middleHpair_bijective q H₁ H₂ h₁ h₂ a)

lemma FHomInclusion_injective (a : ℤ) (h2 : a ≠ -2) (h1 : a ≠ 1) :
    Function.Injective (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_injective_of_prev_zero _ _ hs.1 hs.2.1 hs.2.2 a
    (completeYHomology_zero q hq hp (a-1) (by omega) (by omega))

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

attribute [local instance] OAI.Tachikawa.Construction.concreteF_left_projective
attribute [local instance] OAI.Tachikawa.Construction.concreteF_right_projective
attribute [local instance] OAI.Tachikawa.Construction.concreteF_finite
lemma VAction_first : VAction q hq hp H₁ H₂ h₁ h₂ ≫ FFirst q hq hp H₁ H₂ h₁ h₂ = 𝟙 _ := by
  rw [← completeHomMap_comp,← Category.assoc,concreteVZero_fst,Iso.inv_hom_id,completeHomMap_id]

end Tachikawa.Construction



namespace Tachikawa
namespace Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma delta_minusTwo_injective : Function.Injective (delta q hq hp H₁ H₂ h₁ h₂ (-2)) := by
  let := (selfHom_zero_near q hq hp).2.2.1
  exact fun _ _ _ => Subsingleton.elim _ _

end Construction

end Tachikawa



namespace Tachikawa
variable {k A B C V : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V]

lemma exact_line_surjective (i : A →ₗ[k] B) (p : B →ₗ[k] C)
    (hi : Function.Injective i) (hp : Function.Surjective p) (he : Function.Exact i p)
    (eB : B ≃ₗ[k] k × k) (eC : C ≃ₗ[k] k) (eV : V ≃ₗ[k] k)
    (v : V →ₗ[k] A) (hv : Function.Injective v) : Function.Surjective v := by
  let : FiniteDimensional k B := eB.symm.finiteDimensional
  let : FiniteDimensional k C := eC.symm.finiteDimensional
  let : FiniteDimensional k V := eV.symm.finiteDimensional
  let : FiniteDimensional k A := Module.Finite.of_injective i hi
  have hB : Module.finrank k B = 2 := by simpa using eB.finrank_eq
  have hC : Module.finrank k C = 1 := by simpa using eC.finrank_eq
  have hV : Module.finrank k V = 1 := by simpa using eV.finrank_eq
  have hr : Module.finrank k p.range = 1 := by rw [LinearMap.range_eq_top.mpr hp]; simpa using hC
  have ha : Module.finrank k A = 1 := by
    have h := p.finrank_range_add_finrank_ker
    rw [he.linearMap_ker_eq,LinearMap.finrank_range_of_inj hi,hr,hB] at h
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV.trans ha.symm)).mp hv

end Tachikawa



namespace Tachikawa
namespace Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma VAction_injective (a : ℤ) : Function.Injective
    (VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a) := by
  have he := VAction_first q hq hp H₁ H₂ h₁ h₂
  have hh := congrArg (fun f => VectorSplit.Hmap f a) he
  rw [VectorSplit.Hmap_comp,VectorSplit.Hmap_id] at hh
  intro x y hxy
  have hx := LinearMap.congr_fun hh x
  have hy := LinearMap.congr_fun hh y
  rw [LinearMap.comp_apply,LinearMap.id_apply] at hx hy
  exact hx.symm.trans ((congrArg (VectorSplit.Hmap (FFirst q hq hp H₁ H₂ h₁ h₂) a) hxy).trans hy)

lemma VAction_zero_surjective : Function.Surjective
    (VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) 0) := by
  let em := (LinearEquiv.ofBijective (middleHpairX q H₁ H₂ h₁ h₂ 0)
    (middleHpairX_bijective q H₁ H₂ h₁ h₂ 0)).trans
      ((selfHomZeroEquiv q hq hp).prodCongr (selfHomZeroEquiv q hq hp))
  let ey := (zeroHomEquiv q (Enveloping.evalObj (xObj q) (Y q).obj)).trans (WZeroEquiv q hq hp)
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact exact_line_surjective
    (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) 0)
    (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0)
    (FHomInclusion_injective q hq hp H₁ H₂ h₁ h₂ 0 (by decide) (by decide))
    (FHomProjection_zero_surjective q hq hp H₁ H₂ h₁ h₂)
    (VectorSplit.Hmap_exact _ _ hs.1 hs.2.1 hs.2.2 0)
    em ey (selfHomZeroEquiv q hq hp) _ (VAction_injective q hq hp H₁ H₂ h₁ h₂ 0)

lemma delta_zero_surjective : Function.Surjective (delta q hq hp H₁ H₂ h₁ h₂ 0) := by
  intro x
  obtain ⟨y,hy⟩ := VAction_zero_surjective q hq hp H₁ H₂ h₁ h₂ x
  refine ⟨(0,y),?_⟩
  change VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) 0 0 +
    VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) 0 y = x
  rw [map_zero,zero_add,hy]

end Construction
namespace SourceField
open Construction

theorem sourceDelta_vanishing_ranges (a : ℤ) (ha : 0 < a ∨ a ≤ -2) :
    Function.Injective (sourceDelta a) ∧ Function.Surjective (sourceDelta (a-1)) := by
  constructor
  · by_cases h2 : a = -2
    · subst a
      exact delta_minusTwo_injective _ _ _ _ _ _ _
    · exact (sourceDelta_bijective a (by omega)).1
  · by_cases h1 : a = 1
    · subst a
      exact delta_zero_surjective _ _ _ _ _ _ _
    · exact (sourceDelta_bijective (a-1) (by omega)).2
end SourceField
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Triangular
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R))

variable {F} {L L' : ModuleCat R}

lemma cross₀₁_zero (f : D₀Obj F L ⟶ D₁Obj F L') : f = 0 := by
  apply ModuleCat.hom_ext
  apply triple_hom_ext
  · exact Subsingleton.elim _ _
  · have hc := hom_compatible f.hom
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun hc x
    exact he

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))

lemma diagonal₀_pre {L M N : ModuleCat.{0} R} (d : L ⟶ M)
    (f : D₀Obj F M ⟶ D₀Obj F N) :
    diagonal₀ (D₀Map F d ≫ f) = d ≫ diagonal₀ f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f.hom (d x, BalancedTensor.mapRight d.hom 0)).1 = _
  rw [map_zero]
  rfl
lemma diagonal₁_pre {L M N : ModuleCat.{0} R} (d : L ⟶ M)
    (f : D₁Obj F M ⟶ D₁Obj F N) :
    diagonal₁ (D₁Map F d ≫ f) = d ≫ diagonal₁ f := rfl

end Tachikawa.Triangular

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DownHom
attribute [-instance] _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace CompleteTranslate

lemma exact (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    (hP : ComplexExact P) : ComplexExact (complex P a) := by
  intro j
  change Function.Exact (P.d (j+1+a) (j+a)) (P.d (j+a) (j-1+a))
  rw [show j+1+a=j+a+1 by omega, show j-1+a=j+a-1 by omega]
  exact hP (j+a)
lemma totallyAcyclic (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    (hP : TotallyAcyclic P) : TotallyAcyclic (complex P a) := by
  refine ⟨exact P a hP.1,?_⟩
  intro j f hf
  change f.comp (P.d (j+1+a) (j+a)).hom = 0 at hf
  change ∃ g : P.X (j-1+a) →ₗ[R] R, g.comp (P.d (j+a) (j-1+a)).hom = f
  rw [show j+1+a=j+a+1 by omega] at hf
  rw [show j-1+a=j+a-1 by omega]
  exact hP.2 (j+a) f hf

end CompleteTranslate
end Tachikawa



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P Q : ChainComplex (ModuleCat.{0} R) ℤ)

variable {P Q}

lemma transport_left {a i i' j : ℤ} (f : Cochain P Q a) (h : i=i') (he : i'=j+a) :
    (P.XIsoOfEq h).hom ≫ f i' j he = f i j (h.trans he) := by
  subst i'; simp

lemma d_pre_eq {a : ℤ} (f : Cochain P Q a) (p i i' j : ℤ)
    (he : i=i') (hi : i=j+a) (hi' : i'=j+a) :
    P.d p i ≫ f i j hi = P.d p i' ≫ f i' j hi' := by
  subst i'; rfl
lemma d_post_eq {a : ℤ} (f : Cochain P Q a) (i j j' q : ℤ)
    (he : j=j') (hi : i=j+a) (hi' : i=j'+a) :
    f i j hi ≫ Q.d j q = f i j' hi' ≫ Q.d j' q := by
  subst j'; rfl

lemma ofChain_closed {a : ℤ} (f : CompleteTranslate.complex P a ⟶ Q) :
    Closed (ofChain P Q f) := by
  intro i j l m hij hlm
  subst i; subst l
  change (P.XIsoOfEq rfl).hom ≫ f.f j ≫ Q.d j m =
    P.d (j+a) (m+a) ≫ (P.XIsoOfEq rfl).hom ≫ f.f m
  simpa only [XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp] using f.comm j m

@[simp] lemma to_ofChain {a : ℤ} (f : CompleteTranslate.complex P a ⟶ Q) :
    toChain (ofChain P Q f) (ofChain_closed f) = f := by
  ext j; simp [toChain,ofChain]

lemma ofHomotopy_boundary {a : ℤ} {f : CompleteTranslate.complex P a ⟶ Q}
    (h : Homotopy f 0) : Boundary (ofChain P Q f) := by
  let c : Cochain P Q (a-1) := fun i j he =>
    (P.XIsoOfEq (show i=(j-1)+a by omega)).hom ≫ h.hom (j-1) j
  refine ⟨c,?_⟩
  intro i j he
  subst i
  simp only [ofChain,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp]
  have hh := h.comm j
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)] at hh
  simp only [zero_f,add_zero] at hh
  dsimp only [CompleteTranslate.complex] at hh
  change f.f j = P.d (j+a) (j-1+a) ≫ h.hom (j-1) j + h.hom j (j+1) ≫ Q.d (j+1) j at hh
  have ht (p p' q : ℤ) (he : p=p') :
      (P.XIsoOfEq (congrArg (fun t => t+a) he)).hom ≫ h.hom p' q = h.hom p q := by
    subst p'; simp
  dsimp only [c]
  rw [← Category.assoc,HomologicalComplex.d_comp_XIsoOfEq_hom]
  rw [ht j (j+1-1) (j+1) (by omega)]
  exact hh

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℤ}

lemma twice {V : Type*} [AddCommGroup V] [Module k V] (v : V) : v+v=0 := by
  rw [← two_smul k]
  have hz : (2:k)=0 := CharP.cast_eq_zero k 2
  rw [hz,zero_smul]
lemma negative {V : Type*} [AddCommGroup V] [Module k V] (v : V) : -v=v :=
  (neg_eq_iff_add_eq_zero).mpr (twice (k := k) v)

lemma closed_of_adjacent {a : ℤ} (f : Cochain P Q a)
    (hf : ∀ i j (h : i=j+a), f i j h ≫ Q.d j (j-1) = P.d i (i-1) ≫ f (i-1) (j-1) (by omega)) :
    Closed f := by
  intro i j l m hij hlm
  by_cases he : m+1=j
  · have hl : l=i-1 := by omega
    subst l
    have hm : m=j-1 := by omega
    subst m
    exact (hf i j hij).trans (d_pre_eq f i (i-1) (j-1+a) (j-1) (by omega) _ _)
  · rw [Q.shape _ _ he,P.shape _ _ (by change ¬ l+1=i; omega),comp_zero,zero_comp]

lemma diff_closed {a : ℤ} (f : Cochain P Q (a-1)) : Closed (diff f) := by
  apply closed_of_adjacent
  intro i j he
  dsimp only [diff]
  rw [add_comp,comp_add,Category.assoc,Category.assoc,Q.d_comp_d,comp_zero,
    ← Category.assoc (P.d i (i-1)) (P.d (i-1) (i-1-1)),P.d_comp_d,zero_comp,add_zero,zero_add]
  exact congrArg (fun t => P.d i (i-1) ≫ t)
    (d_post_eq f (i-1) j (j-1+1) (j-1) (by omega) _ _)

lemma boundary_diff {a : ℤ} (f : Cochain P Q (a-1)) : Boundary (diff f) := by
  refine ⟨fun i j he => f i j (by omega),?_⟩
  intros; rfl
lemma boundary_add {a : ℤ} {f g : Cochain P Q a} (hf : Boundary f) (hg : Boundary g) :
    Boundary (f+g) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  refine ⟨s+t,?_⟩
  intro i j he
  change f i j he+g i j he = _ ≫ (s _ _ _+t _ _ _) + (s _ _ _+t _ _ _) ≫ _
  rw [hs,ht,comp_add,add_comp]
  abel

lemma boundary_iff_diff {a : ℤ} (f : Cochain P Q a) :
    Boundary f ↔ ∃ h : Cochain P Q (a-1), f = diff h := by
  constructor
  · rintro ⟨h,hh⟩
    exact ⟨h,funext fun i => funext fun j => funext fun he => hh i j he⟩
  · rintro ⟨h,rfl⟩; exact boundary_diff h

include k in
lemma closed_iff_diff_zero {a : ℤ} (f : Cochain P Q (a-1)) :
    Closed f ↔ diff f = 0 := by
  constructor
  · intro hf
    funext i j he
    change P.d i (i-1) ≫ f (i-1) j _ + f i (j+1) _ ≫ Q.d (j+1) j = 0
    rw [hf i (j+1) (i-1) j (by omega) (by omega)]
    exact twice (k := k) _
  · intro hf
    apply closed_of_adjacent
    intro i j he
    have hh := congrFun (congrFun (congrFun hf i) (j-1)) (by omega)
    change P.d i (i-1) ≫ f (i-1) (j-1) _ + f i (j-1+1) _ ≫ Q.d (j-1+1) (j-1) = 0 at hh
    rw [d_post_eq f i (j-1+1) j (j-1) (by omega) _ he] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (negative (k := k) _)

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {P' Q' : ChainComplex (ModuleCat.{0} S) ℤ}
variable (e : ∀ i j, (P.X i ⟶ Q.X j) ≃ₗ[k] (P'.X i ⟶ Q'.X j))

variable (hpre : ∀ i l j (f : P.X l ⟶ Q.X j),
    e i j (P.d i l ≫ f) = P'.d i l ≫ e l j f)
  (hpost : ∀ i j m (f : P.X i ⟶ Q.X j),
    e i m (f ≫ Q.d j m) = e i j f ≫ Q'.d j m)
include hpre hpost
lemma cochainEquiv_closed_iff {a : ℤ} (f : Cochain P Q a) :
    Closed (cochainEquiv e a f) ↔ Closed f := by
  constructor
  · intro hf i j l m hij hlm
    apply (e i m).injective
    rw [hpre,hpost]
    exact hf i j l m hij hlm
  · intro hf i j l m hij hlm
    change e i j (f i j hij) ≫ Q'.d j m = P'.d i l ≫ e l m (f l m hlm)
    rw [← hpre,← hpost,hf]

lemma cochainEquiv_diff {a : ℤ} (f : Cochain P Q (a-1)) :
    cochainEquiv e a (diff f) = diff (cochainEquiv e (a-1) f) := by
  funext i j h
  change e i j (_+_) = _+_
  rw [map_add,hpre,hpost]
  rfl

lemma cochainEquiv_boundary_iff {a : ℤ} (f : Cochain P Q a) :
    Boundary (cochainEquiv e a f) ↔ Boundary f := by
  rw [boundary_iff_diff,boundary_iff_diff]
  constructor
  · rintro ⟨h,hh⟩
    refine ⟨(cochainEquiv e (a-1)).symm h,?_⟩
    apply (cochainEquiv e a).injective
    rw [cochainEquiv_diff e hpre hpost,LinearEquiv.apply_symm_apply,hh]
  · rintro ⟨h,rfl⟩
    exact ⟨cochainEquiv e (a-1) h,cochainEquiv_diff e hpre hpost h⟩
end Tachikawa.DownHom



namespace Tachikawa
open CategoryTheory
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (hp : TotallyAcyclic P) (hq : ComplexExact Q)
  (pproj : ∀ j, Module.Projective R (P.X j))
  (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
  {N : ModuleCat.{0} R} (ε : Q.X 0 ⟶ N)
  (he : Function.Exact (Q.d 1 0) ε) (hs : Function.Surjective ε)
include hp hq pproj qfin qproj he hs
lemma exists_augmented_complete_lift (g : P.X 0 ⟶ N) (hg : P.d 1 0 ≫ g = 0) :
    ∃ f : P ⟶ Q, f.f 0 ≫ ε = g := by
  let e := CokerAt.augmentationEquiv Q N 0 ε.hom he hs
  let u := e.symm.toLinearMap.comp (CokerAt.descend P 0 g.hom (ModuleCat.hom_ext_iff.mp hg))
  obtain ⟨f,hf⟩ := exists_complete_lift P Q hp hq pproj qfin qproj u
  refine ⟨f,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hy := congrArg e (LinearMap.congr_fun hf (CokerAt.π P 0 y))
  change ε (f.f 0 y) = e (e.symm (g y)) at hy
  change ε (f.f 0 y) = g y
  simpa only [LinearEquiv.apply_symm_apply] using hy
end Tachikawa



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)

lemma eval_boundary {a : ℤ} (f : Cochain P Q a) (hf : Closed f) (hb : Boundary f) :
    evalClass (k := k) ε hε f hf = 0 := by
  obtain ⟨h,hh⟩ := hb
  apply (VectorSplit.quotient_zero_iff_predecessor a _).mpr
  refine ⟨h (a-1) 0 (by omega) ≫ ε,?_⟩
  change P.d a (a-1) ≫ h (a-1) 0 _ ≫ ε = f a 0 _ ≫ ε
  rw [hh a 0,add_comp,Category.assoc,Category.assoc,show Q.d (0+1) 0 ≫ ε = 0 from hε,Limits.comp_zero,add_zero]

variable (hP : TotallyAcyclic P) (hQ : ComplexExact Q)
  (pP : ∀ j, Module.Projective R (P.X j))
  (fP : ∀ j, Module.Finite R (P.X j))
  (fQ : ∀ j, Module.Finite R (Q.X j)) (pQ : ∀ j, Module.Projective R (Q.X j))
  (he : Function.Exact (Q.d 1 0) ε) (hs : Function.Surjective ε)

include hP hQ pP fP fQ pQ he hs in
lemma boundary_of_eval_zero {a : ℤ} (f : Cochain P Q a) (hf : Closed f)
    (hz : evalClass (k := k) ε hε f hf = 0) : Boundary f := by
  obtain ⟨g,hg⟩ := (VectorSplit.quotient_zero_iff_predecessor a _).mp hz
  change P.X (a-1) ⟶ N at g
  change P.d a (a-1) ≫ g = f a 0 _ ≫ ε at hg
  let P' := CompleteTranslate.complex P a
  let e := CokerAt.augmentationEquiv Q N 0 ε.hom he hs
  let g' : P'.X (-1) →ₗ[R] N :=
    g.hom.comp (P.XIsoOfEq (show -1+a=a-1 by omega)).hom.hom
  have hfac : CokerAt.map (toChain f hf) 0 ∈ projectiveFactors (k := k) := by
    refine ⟨P'.X (-1), ?_, ?_, CokerAt.δ P' 0 (-1), e.symm.toLinearMap.comp g', ?_⟩
    · exact fP (-1+a)
    · exact pP (-1+a)
    · apply LinearMap.ext
      intro x
      obtain ⟨y,rfl⟩ := CokerAt.π_surjective P' 0 x
      apply e.injective
      change e (e.symm (g' (P'.d 0 (-1) y))) = e (CokerAt.π Q 0 (f (0+a) 0 rfl y))
      rw [LinearEquiv.apply_symm_apply]
      change g ((P.XIsoOfEq (show -1+a=a-1 by omega)).hom (P.d (0+a) (-1+a) y)) =
        ε (f (0+a) 0 rfl y)
      have hm : P.d (0+a) (-1+a) ≫ (P.XIsoOfEq (show -1+a=a-1 by omega)).hom ≫ g =
          f (0+a) 0 rfl ≫ ε := by
        rw [← Category.assoc,P.d_comp_XIsoOfEq_hom]
        have hx := congrArg (fun z => (P.XIsoOfEq (show 0+a=a by omega)).hom ≫ z) hg
        rw [← Category.assoc,P.XIsoOfEq_hom_comp_d,← Category.assoc,transport_left] at hx
        exact hx
      exact congrArg (fun z => z y) hm
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (k := k) (toChain f hf)
    (CompleteTranslate.totallyAcyclic P a hP) hQ (fun j => pP (j+a)) fQ pQ hfac
  simpa only [of_toChain] using ofHomotopy_boundary h

include hP hQ pP fQ pQ he hs in
lemma eval_surjective (a : ℤ) (x : VectorSplit.H (completeHom (k := k) P N) a) :
    ∃ (f : Cochain P Q a) (hf : Closed f), evalClass (k := k) ε hε f hf = x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  let g : (CompleteTranslate.complex P a).X 0 ⟶ N :=
    (P.XIsoOfEq (show 0+a=a by omega)).hom ≫ z.val
  have hg : (CompleteTranslate.complex P a).d 1 0 ≫ g = 0 := by
    dsimp only [g,CompleteTranslate.complex]
    erw [← Category.assoc,P.d_comp_XIsoOfEq_hom]
    have hz := (completeHom_memZ P N a z.val).mp z.property
    have hx := congrArg (fun t => (P.XIsoOfEq (show 1+a=a+1 by omega)).hom ≫ t) hz
    erw [← Category.assoc,P.XIsoOfEq_hom_comp_d,Limits.comp_zero] at hx
    exact hx
  obtain ⟨f,hf⟩ := exists_augmented_complete_lift
    (CompleteTranslate.totallyAcyclic P a hP) hQ (fun j => pP (j+a)) fQ pQ ε he hs g hg
  refine ⟨ofChain P Q f, ofChain_closed f, ?_⟩
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (P.XIsoOfEq (show a=0+a by omega)).hom ≫ f.f 0 ≫ ε = z.val
  rw [hf]
  dsimp only [g]
  erw [← Category.assoc]
  simp
  exact Category.id_comp (z.val : P.X a ⟶ N)

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R]  [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)
lemma eval_add {a : ℤ} (f g : Cochain P Q a) (hf : Closed f) (hg : Closed g) :
    evalClass (k := k) ε hε (f+g) (closed_add hf hg) =
      evalClass ε hε f hf + evalClass ε hε g hg := by
  change VectorSplit.quotient _ a _ = VectorSplit.quotient _ a _ + VectorSplit.quotient _ a _
  rw [← map_add]
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (f a 0 (by omega)+g a 0 (by omega)) ≫ ε = _
  rw [add_comp]
  rfl

variable (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive]

variable [F.Linear k] (X : ModuleCat.{0} R) (εP : P.X 0 ⟶ X)
  (hεP : P.d 1 0 ≫ εP = 0) (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map εP = εP ≫ u₀)

set_option backward.isDefEq.respectTransparency false in
include hu in
lemma eval_actionDelta {a : ℤ} (f g : Cochain P P a) (hf : Closed f) (hg : Closed g) :
    evalClass (k := k) (F.map εP) (map_augmentation_zero F X εP hεP)
      (actionDelta F u f g) (actionDelta_closed F u hf hg) =
    homologyDelta F X u u₀ a (evalClass εP hεP f hf,evalClass εP hεP g hg) := by
  dsimp only [actionDelta]
  rw [eval_add _ _ _ _ (pre_closed u (map_closed F hf)) (post_closed hg u)]
  change _ = VectorSplit.Hmap (completeFunctorHom F P P X u) a
    (VectorSplit.quotient _ a (evalCycle εP hεP f hf)) +
    VectorSplit.Hmap (completeHomMap (k := k) P u₀) a
    (VectorSplit.quotient _ a (evalCycle εP hεP g hg))
  rw [VectorSplit.Hmap_quotient,VectorSplit.Hmap_quotient]
  congr 1
  · apply congrArg (VectorSplit.quotient _ a)
    apply Subtype.ext
    change (u.f a ≫ F.map (f a 0 _)) ≫ F.map εP = u.f a ≫ F.map (f a 0 _ ≫ εP)
    rw [F.map_comp,Category.assoc]
  · apply congrArg (VectorSplit.quotient _ a)
    apply Subtype.ext
    change (g a 0 _ ≫ u.f 0) ≫ F.map εP = (g a 0 _ ≫ εP) ≫ u₀
    rw [Category.assoc,hu,Category.assoc]

end Tachikawa.DownHom



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
open DownHom
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
lemma diagonal₀_comp {L M N : ModuleCat.{0} R}
    (f : D₀Obj F L ⟶ D₀Obj F M) (g : D₀Obj F M ⟶ D₀Obj F N) :
    diagonal₀ (f ≫ g) = diagonal₀ f ≫ diagonal₀ g := by
  have hf : D₀Map F (diagonal₀ f) = f := diagonal₀.symm_apply_apply f
  rw [← hf,diagonal₀_pre]
  rfl
lemma diagonal₁_comp {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₁Obj F M) (g : D₁Obj F M ⟶ D₁Obj F N) :
    diagonal₁ (f ≫ g) = diagonal₁ f ≫ diagonal₁ g := by
  have hf : D₁Map F (diagonal₁ f) = f := diagonal₁.symm_apply_apply f
  rw [← hf,diagonal₁_pre]
  rfl
lemma diagonal₀_post {L M N : ModuleCat.{0} R}
    (f : D₀Obj F L ⟶ D₀Obj F M) (g : M ⟶ N) :
    diagonal₀ (f ≫ D₀Map F g) = diagonal₀ f ≫ g := diagonal₀_comp F f (D₀Map F g)
lemma diagonal₁_post {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₁Obj F M) (g : M ⟶ N) :
    diagonal₁ (f ≫ D₁Map F g) = diagonal₁ f ≫ g := diagonal₁_comp F f (D₁Map F g)
lemma cross₁₀_comp_right {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₀Obj F M) (g : D₀Obj F M ⟶ D₀Obj F N) :
    cross₁₀ (f ≫ g) = cross₁₀ f ≫ (Enveloping.tensorFunctor F).map (diagonal₀ g) := by
  have hg : D₀Map F (diagonal₀ g) = g := diagonal₀.symm_apply_apply g
  rw [← hg,cross₁₀_post]
  rfl
lemma cross₁₀_comp_left {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₁Obj F M) (g : D₁Obj F M ⟶ D₀Obj F N) :
    cross₁₀ (f ≫ g) = diagonal₁ f ≫ cross₁₀ g := by
  have hf : D₁Map F (diagonal₁ f) = f := diagonal₁.symm_apply_apply f
  rw [← hf,cross₁₀_pre]
  rfl

variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

lemma down₀_closed {a : ℤ} (f : Cochain (D₀Complex F P) (D₀Complex F Q) a) :
    Closed (down₀ F a f) ↔ Closed f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
lemma down₁_closed {a : ℤ} (f : Cochain (D₁Complex F P) (D₁Complex F Q) a) :
    Closed (down₁ F a f) ↔ Closed f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => diagonal₁_pre F _ _)
    (fun _ _ _ _ => diagonal₁_post F _ _) f
lemma downCross_closed {a : ℤ} (f : Cochain (D₁Complex F P) (D₀Complex F Q) a) :
    Closed (downCross F a f) ↔ Closed f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => cross₁₀_pre F _ _)
    (fun _ _ _ _ => cross₁₀_post F _ _) f
lemma down₀_boundary {a : ℤ} (f : Cochain (D₀Complex F P) (D₀Complex F Q) a) :
    Boundary (down₀ F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
lemma down₁_boundary {a : ℤ} (f : Cochain (D₁Complex F P) (D₁Complex F Q) a) :
    Boundary (down₁ F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => diagonal₁_pre F _ _)
    (fun _ _ _ _ => diagonal₁_post F _ _) f
lemma downCross_boundary {a : ℤ} (f : Cochain (D₁Complex F P) (D₀Complex F Q) a) :
    Boundary (downCross F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => cross₁₀_pre F _ _)
    (fun _ _ _ _ => cross₁₀_post F _ _) f

lemma downCross_delta (u : P ⟶ Enveloping.tensorComplex F P) {a : ℤ}
    (f : Cochain (D₀Complex F P) (D₀Complex F P) a)
    (g : Cochain (D₁Complex F P) (D₁Complex F P) a) :
    downCross F a (pre (crossMap F u) f+post g (crossMap F u)) =
      actionDelta (Enveloping.tensorFunctor F) u (down₀ F a f) (down₁ F a g) := by
  funext i j h
  change cross₁₀ ((crossMap F u).f i ≫ f i j h + g i j h ≫ (crossMap F u).f j) = _
  erw [map_add,cross₁₀_comp_right,cross₁₀_comp_left]
  change cross₁₀ (cross₁₀.symm (u.f i)) ≫ _ + _ ≫ cross₁₀ (cross₁₀.symm (u.f j)) = _
  erw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rfl
end Tachikawa.Triangular

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Cone
attribute [-instance] _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
variable {R : Type} [Ring R]
namespace CompleteCone
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
lemma inRight_d (i j : ℤ) : inRight v i ≫ (complex v).d i j = A.d i j ≫ inRight v j :=
  HomologicalComplex.homotopyCofiber.inrX_d v i j

end CompleteCone
end Tachikawa



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

lemma inl_fst_apply {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain B D a) (p p' t j : ℤ)
    (hp : (ComplexShape.down ℤ).Rel t p) (hp' : (ComplexShape.down ℤ).Rel t p')
    (he : p=j+a) (he' : p'=j+a) :
    homotopyCofiber.inlX v p t hp ≫ homotopyCofiber.fstX v t p' hp' ≫ f p' j he' = f p j he := by
  have hh : p'=p := by change p+1=t at hp; change p'+1=t at hp'; omega
  cases hh
  simp only [homotopyCofiber.inlX_fstX_assoc]
lemma apply_inl_fst {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain D B a) (i p p' t : ℤ)
    (hp : (ComplexShape.down ℤ).Rel t p) (hp' : (ComplexShape.down ℤ).Rel t p')
    (he : i=p+a) (he' : i=p'+a) :
    f i p' he' ≫ homotopyCofiber.inlX v p' t hp' ≫ homotopyCofiber.fstX v t p hp = f i p he := by
  have hh : p'=p := by change p+1=t at hp; change p'+1=t at hp'; omega
  cases hh
  simp only [homotopyCofiber.inlX_fstX,Category.comp_id]
lemma block_transport {a : ℤ} (f : Cochain (C v) (C v) a)
    (p q i j i' j' : ℤ) (hi : (ComplexShape.down ℤ).Rel i p)
    (hi' : (ComplexShape.down ℤ).Rel i' p) (hj : (ComplexShape.down ℤ).Rel j q)
    (hj' : (ComplexShape.down ℤ).Rel j' q) (he : i=j+a) (he' : i'=j'+a) :
    homotopyCofiber.inlX v p i hi ≫ f i j he ≫ homotopyCofiber.fstX v j q hj =
    homotopyCofiber.inlX v p i' hi' ≫ f i' j' he' ≫ homotopyCofiber.fstX v j' q hj' := by
  have H : i'=i := by change p+1=i at hi; change p+1=i' at hi'; omega
  cases H
  have H : j'=j := by change q+1=j at hj; change q+1=j' at hj'; omega
  cases H; rfl
lemma cross_transport {a : ℤ} (f : Cochain (C v) (C v) a)
    (p i i' j : ℤ) (hi : (ComplexShape.down ℤ).Rel i p)
    (hi' : (ComplexShape.down ℤ).Rel i' p) (he : i=j+a) (he' : i'=j+a) :
    homotopyCofiber.inlX v p i hi ≫ f i j he ≫ right v j =
    homotopyCofiber.inlX v p i' hi' ≫ f i' j he' ≫ right v j := by
  have H : i'=i := by change p+1=i at hi; change p+1=i' at hi'; omega
  cases H; rfl

lemma low_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    low v (assemble v f g c) = f := by
  funext i j h
  simp only [assemble,low,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inrX_fstX_assoc,
      homotopyCofiber.inrX_sndX_assoc,homotopyCofiber.inlX_sndX,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,comp_zero,add_zero]
lemma high_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    high v (assemble v f g c) = g := by
  funext i j h
  simp only [assemble,high,iL,pL,left,right,inLeft,inRight,add_comp,
      Category.assoc,homotopyCofiber.inrX_fstX,comp_zero,add_zero,zero_add]
  rw [apply_inl_fst v g _ j _ _ _ _ (by omega) _,inl_fst_apply v g _ _ _ _ _ _ h _]
lemma cross_assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a) (c : Cochain B A (a-1)) :
    cross v (assemble v f g c) = c := by
  funext i j h
  simp only [assemble,cross,iL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_sndX_assoc,homotopyCofiber.inlX_sndX,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,comp_zero,add_zero,zero_add]

  exact inl_fst_apply v c _ _ _ _ _ _ h _
variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
lemma assemble_blocks {a : ℤ} (f : Cochain (C v) (C v) a) :
    assemble v (low v f) (high v f) (cross v f) = f := by
  funext i j h
  apply homotopyCofiber.ext_from_X v (i-1) i (by change i-1+1=i; omega)
  · apply homotopyCofiber.ext_to_X v j (j-1) (by change j-1+1=j; omega)
    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,
      homotopyCofiber.inlX_fstX,homotopyCofiber.inrX_fstX,
      Category.comp_id,zero_comp,comp_zero,add_zero,zero_add]
      exact block_transport v f _ _ _ _ _ _ _ _ _ _ _ _

    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,
      homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_sndX,
      Category.comp_id,zero_comp,comp_zero,zero_add]
      exact cross_transport v f _ _ _ _ _ _ _ _

  · apply homotopyCofiber.ext_to_X v j (j-1) (by change j-1+1=j; omega)
    · simpa only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,add_comp,
      Category.assoc,sub_add_cancel,add_sub_cancel_right,homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,homotopyCofiber.inrX_fstX_assoc,
      homotopyCofiber.inrX_sndX_assoc,homotopyCofiber.inlX_fstX,
      homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_fstX,
      homotopyCofiber.inrX_sndX,Category.id_comp,Category.comp_id,zero_comp,comp_zero,add_zero,zero_add] using (hAB i (j-1) (inRight v i ≫ f i j h ≫ left v j)).symm
    · simp only [assemble,low,high,cross,iL,pL,left,right,inLeft,inRight,comp_add,
      Category.assoc,homotopyCofiber.inrX_fstX_assoc,homotopyCofiber.inrX_sndX_assoc,
      homotopyCofiber.inrX_sndX,Category.comp_id,zero_comp,add_zero]

end Tachikawa.DownCone



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

include k in
@[reassoc] lemma d_left (i : ℤ) : (C v).d i (i-1) ≫ left v (i-1) =
    left v i ≫ B.d (i-1) (i-1-1) := by
  have h := homotopyCofiber.d_fstX v i (i-1) (i-1-1)
    (by change i-1+1=i; omega) (by change i-1-1+1=i-1; omega)
  change (C v).d i (i-1) ≫ left v (i-1) = -(left v i) ≫ B.d (i-1) (i-1-1) at h
  rw [negative (k := k)] at h
  exact h
@[reassoc] lemma inRight_dcat (i j : ℤ) : inRight v i ≫ (C v).d i j =
    A.d i j ≫ inRight v j := inRight_d v i j
include k in
lemma apply_inl_d {D : ChainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (f : Cochain D B a) (i s t j : ℤ)
    (hs : (ComplexShape.down ℤ).Rel t s) (hj : (ComplexShape.down ℤ).Rel t j)
    (he : i=s+a) (he' : i=j+a) :
    f i s he ≫ homotopyCofiber.inlX v s t hs ≫ (C v).d t j =
    f i j he' ≫ B.d j (j-1) ≫ inLeft v j + f i j he' ≫ v.f j ≫ inRight v j := by
  have H : s=j := by change s+1=t at hs; change j+1=t at hj; omega
  cases H
  change f i s he ≫ homotopyCofiber.inlX v s t hs ≫ homotopyCofiber.d v t s = _
  rw [homotopyCofiber.inlX_d v t s (s-1) hs (by change s-1+1=s; omega)]
  rw [comp_add,negative (k := k)]

include k in
lemma diff_assemble {a : ℤ} (f : Cochain A A (a-1)) (g : Cochain B B (a-1))
    (c : Cochain B A (a-1-1)) :
    diff (assemble v f g c) =
      assemble v (diff f) (diff g) (diff c + pre v f + post g v) := by
  funext i j h
  simp only [diff,assemble,DownHom.add_apply,pre,post,comp_add,add_comp,Category.assoc,
    d_left_assoc (k := k),d_right_assoc,inRight_dcat]
  rw [apply_inl_d (k := k) v g (i-1) (j+1-1) (j+1) j
    (by change j+1-1+1=j+1; omega) (by rfl) _ (by omega)]
  simp only [comp_add]
  rw [← Category.assoc (g (i-1) (j-1+1) _) (B.d (j-1+1) (j-1)) (inLeft v j),
    d_post_eq g (i-1) (j-1+1) j (j-1) (by omega) _ (by omega),Category.assoc]
  abel

variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB k

lemma low_diff {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    low v (diff f) = diff (low v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble (k := k),low_assemble]
lemma high_diff {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    high v (diff f) = diff (high v f) := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble (k := k),high_assemble]
lemma cross_diff {a : ℤ} (f : Cochain (C v) (C v) (a-1)) :
    cross v (diff f) = diff (cross v f) + pre v (low v f) + post (high v f) v := by
  conv_lhs => rw [← assemble_blocks v hAB f,diff_assemble (k := k),cross_assemble]

end Tachikawa.DownCone



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

variable (hAB : ∀ i j (f : A.X i ⟶ B.X j), f=0)
include hAB in
lemma blocks_ext {a : ℤ} {f g : Cochain (C v) (C v) a}
    (hl : low v f = low v g) (hh : high v f = high v g) (hc : cross v f = cross v g) : f=g := by
  rw [← assemble_blocks v hAB f,← assemble_blocks v hAB g,hl,hh,hc]

include hAB k in
lemma closed_blocks_aux {a : ℤ} : ∀ (f : Cochain (C v) (C v) (a-1)), Closed f →
    Closed (low v f) ∧ Closed (high v f) ∧
      pre v (low v f)+post (high v f) v = diff (cross v f) := by
  intro f hf
  have hz := (closed_iff_diff_zero (k := k) f).mp hf
  refine ⟨(closed_iff_diff_zero (k := k) _).mpr ?_,
    (closed_iff_diff_zero (k := k) _).mpr ?_,?_⟩
  · rw [← low_diff (k := k) v hAB,hz,low_zero]
  · rw [← high_diff (k := k) v hAB,hz,high_zero]
  · have hh := congrArg (cross v) hz
    rw [cross_diff (k := k) v hAB,cross_zero,add_assoc] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (negative (k := k) _)

include hAB k in
lemma closed_blocks {a : ℤ} (f : Cochain (C v) (C v) a) (hf : Closed f) :
    Closed (low v f) ∧ Closed (high v f) ∧
      pre v (low v f)+post (high v f) v = diff (cross v f) := by
  have hh := closed_blocks_aux (k := k) v hAB (a := a+1)
  rw [show a+1-1=a by omega] at hh
  exact hh f hf

include k hAB in

theorem boundary_of_delta (a : ℤ)
    (hI : ∀ (f : Cochain A A a) (g : Cochain B B a),
      Closed f → Closed g → Boundary (pre v f+post g v) → Boundary f ∧ Boundary g)
    (hS : ∀ (c : Cochain B A (a-1)), Closed c →
      ∃ (f : Cochain A A (a-1)) (g : Cochain B B (a-1)),
        Closed f ∧ Closed g ∧ Boundary (c+pre v f+post g v))
    (z : Cochain (C v) (C v) a) (hz : Closed z) : Boundary z := by
  obtain ⟨hf,hg,he⟩ := closed_blocks (k := k) v hAB z hz
  have hb : Boundary (pre v (low v z)+post (high v z) v) := he ▸ boundary_diff (cross v z)
  obtain ⟨hbf,hbg⟩ := hI _ _ hf hg hb
  obtain ⟨s,hs⟩ := (boundary_iff_diff _).mp hbf
  obtain ⟨t,ht⟩ := (boundary_iff_diff _).mp hbg
  let b := diff (assemble v s t 0)
  let zz := z+b
  have hzz : Closed zz := closed_add hz (diff_closed _)
  have hl : low v zz = 0 := by
    dsimp only [zz,b]
    rw [low_add,low_diff (k := k) v hAB,low_assemble,hs]
    exact twice (k := k) _
  have hh : high v zz = 0 := by
    dsimp only [zz,b]
    rw [high_add,high_diff (k := k) v hAB,high_assemble,ht]
    exact twice (k := k) _
  have hc : Closed (cross v zz) := by
    apply (closed_iff_diff_zero (k := k) _).mpr
    have he := (closed_blocks (k := k) v hAB zz hzz).2.2
    rw [hl,hh] at he
    have h0 : pre v (0 : Cochain A A a)+post (0 : Cochain B B a) v = 0 := by
      funext i j he; simp [pre,post]
    exact he.symm.trans h0
  obtain ⟨f,g,hf,hg,hc⟩ := hS (cross v zz) hc
  obtain ⟨c,hc⟩ := (boundary_iff_diff _).mp hc
  have hf0 : diff f = (0 : Cochain A A a) := (closed_iff_diff_zero (k := k) f).mp hf
  have hg0 : diff g = (0 : Cochain B B a) := (closed_iff_diff_zero (k := k) g).mp hg
  have hd : diff (assemble v f g c) = zz := by
    apply blocks_ext v hAB
    · rw [low_diff (k := k) v hAB,low_assemble,hf0,hl]
    · rw [high_diff (k := k) v hAB,high_assemble,hg0,hh]
    · rw [cross_diff (k := k) v hAB,cross_assemble,low_assemble,high_assemble,← hc]
      have htw := twice (k := k) (pre v f+post g v)
      calc
        _ = cross v zz + ((pre v f+post g v)+(pre v f+post g v)) := by abel
        _ = _ := by rw [htw,add_zero]
  have hzB : Boundary zz := hd ▸ boundary_diff (assemble v f g c)
  have hbB : Boundary b := boundary_diff _
  have hsum : zz+b=z := by
    dsimp only [zz]
    rw [add_assoc,twice (k := k) b,add_zero]
  exact hsum ▸ boundary_add hzB hbB
end Tachikawa.DownCone



namespace Tachikawa.Triangular
open CategoryTheory
open DownHom
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ}
  (u : P ⟶ Enveloping.tensorComplex F P)

include k in
lemma cone_closed_boundary (a : ℤ)
    (hI : ∀ (f g : Cochain P P a), Closed f → Closed g →
      Boundary (actionDelta (Enveloping.tensorFunctor F) u f g) → Boundary f ∧ Boundary g)
    (hS : ∀ (c : Cochain P (Enveloping.tensorComplex F P) (a-1)), Closed c →
      ∃ (f g : Cochain P P (a-1)), Closed f ∧ Closed g ∧
        Boundary (c+actionDelta (Enveloping.tensorFunctor F) u f g))
    (z : Cochain (cone F u) (cone F u) a) (hz : Closed z) : Boundary z := by
  apply DownCone.boundary_of_delta (k := k) (crossMap F u) (fun _ _ f => cross₀₁_zero f) a ?_ ?_ z hz
  · intro f g hf hg hb
    have hh := (downCross_boundary F _).mpr hb
    rw [downCross_delta] at hh
    obtain ⟨h0,h1⟩ := hI (down₀ F a f) (down₁ F a g)
      ((down₀_closed F f).mpr hf) ((down₁_closed F g).mpr hg) hh
    exact ⟨(down₀_boundary F f).mp h0,(down₁_boundary F g).mp h1⟩
  · intro c hc
    obtain ⟨f,g,hf,hg,hb⟩ := hS (downCross F (a-1) c) ((downCross_closed F c).mpr hc)
    let f' := (down₀ F (a-1)).symm f
    let g' := (down₁ F (a-1)).symm g
    have h0 : down₀ F (a-1) f'=f := LinearEquiv.apply_symm_apply _ _
    have h1 : down₁ F (a-1) g'=g := LinearEquiv.apply_symm_apply _ _
    refine ⟨f',g',(down₀_closed F f').mp (h0.symm ▸ hf),
      (down₁_closed F g').mp (h1.symm ▸ hg),?_⟩
    apply (downCross_boundary F _).mp
    rw [add_assoc,map_add,downCross_delta,h0,h1]
    exact hb
end Tachikawa.Triangular



namespace Tachikawa.DownHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (X : ModuleCat.{0} R)
  (ε : P.X 0 ⟶ X) (hε : P.d 1 0 ≫ ε = 0)
  (hP : TotallyAcyclic P) (pP : ∀ j, Module.Projective R (P.X j))
  (fP : ∀ j, Module.Finite R (P.X j))
  (heP : Function.Exact (P.d 1 0) ε) (hsP : Function.Surjective ε)
  (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive] [F.Linear k]
  (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map ε = ε ≫ u₀)
include hε hP pP fP heP hsP hu in
omit [CharP k 2] in
lemma actionDelta_injective (a : ℤ) (hI : Function.Injective (homologyDelta (k := k) F X u u₀ a))
    (f g : Cochain P P a) (hf : Closed f) (hg : Closed g)
    (hb : Boundary (actionDelta F u f g)) : Boundary f ∧ Boundary g := by
  have hz := eval_boundary (k := k) (F.map ε) (map_augmentation_zero F X ε hε)
    (actionDelta F u f g) (actionDelta_closed F u hf hg) hb
  rw [eval_actionDelta F X ε hε u u₀ hu f g hf hg] at hz
  have he : (evalClass (k := k) ε hε f hf,evalClass (k := k) ε hε g hg) = 0 :=
    hI (hz.trans (map_zero _).symm)
  constructor
  · exact boundary_of_eval_zero ε hε hP hP.1 pP fP fP pP heP hsP f hf
      (congrArg Prod.fst he)
  · exact boundary_of_eval_zero ε hε hP hP.1 pP fP fP pP heP hsP g hg
      (congrArg Prod.snd he)

variable (hQ : ComplexExact (mapComplex F P))
  (fQ : ∀ j, Module.Finite R ((mapComplex F P).X j))
  (pQ : ∀ j, Module.Projective R ((mapComplex F P).X j))
  (heQ : Function.Exact ((mapComplex F P).d 1 0) (F.map ε))
  (hsQ : Function.Surjective (F.map ε))
set_option backward.isDefEq.respectTransparency false in
include hε hP pP fP heP hsP hQ fQ pQ heQ hsQ hu in
lemma actionDelta_surjective (a : ℤ)
    (hS : Function.Surjective (homologyDelta (k := k) F X u u₀ a))
    (c : Cochain P (mapComplex F P) a) (hc : Closed c) :
    ∃ (f g : Cochain P P a), Closed f ∧ Closed g ∧ Boundary (c+actionDelta F u f g) := by
  let hεQ := map_augmentation_zero F X ε hε
  obtain ⟨⟨x,y⟩,hxy⟩ := hS (evalClass (k := k) (F.map ε) hεQ c hc)
  obtain ⟨f,hf,heF⟩ := eval_surjective ε hε hP hP.1 pP fP pP heP hsP a x
  obtain ⟨g,hg,heG⟩ := eval_surjective ε hε hP hP.1 pP fP pP heP hsP a y
  refine ⟨f,g,hf,hg,?_⟩
  apply boundary_of_eval_zero (k := k) (F.map ε) hεQ hP hQ pP fP fQ pQ heQ hsQ
    (c+actionDelta F u f g) (closed_add hc (actionDelta_closed F u hf hg))
  rw [eval_add _ _ _ _ hc (actionDelta_closed F u hf hg),
    eval_actionDelta F X ε hε u u₀ hu f g hf hg,heF,heG,hxy]
  exact twice (k := k) _
end Tachikawa.DownHom

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Counterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra
local instance sourceF_left : Module.Projective (E q) (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).1
local instance sourceF_right : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).2
local instance sourceF_finite : FiniteDimensional K (Enveloping.Obj sourceF.obj) :=
  inferInstanceAs (FiniteDimensional K sourceF)
lemma sourceAug_exact : Function.Exact (sourceP.d 1 0) sourceAug := by
  change Function.Exact ((sourceX.complete (formE q)).d (0+1) 0) sourceX.cover.map
  rw [sourceX.complete_d]
  exact sourceX.pos_augmentation_exact

lemma sourceAug_zero : sourceP.d 1 0 ≫ sourceAug = 0 := by
  ext x
  exact sourceAug_exact.apply_apply_eq_zero x

lemma sourceCone_closed_boundary_oai (a : ℤ) (ha : 0<a ∨ a≤ -2)
    (f : DownHom.Cochain sourceCone sourceCone a) (hf : DownHom.Closed f) : DownHom.Boundary f := by
  have hd := sourceDelta_vanishing_ranges a ha
  apply Triangular.cone_closed_boundary sourceF.obj sourceU a ?_ ?_ f hf
  · exact DownHom.actionDelta_injective sourceP sourceX.obj sourceAug sourceAug_zero
      (sourceX.complete_totallyAcyclic (formE q)) (sourceX.complete_projective (formE q))
      (sourceX.complete_finite (formE q)) sourceAug_exact sourceX.cover.surjective
      (Enveloping.tensorFunctor sourceF.obj) sourceU sourceUZero
      (Enveloping.tensorCompleteLift_aug sourceF.obj sourceX (formE q) sourceUZero) a hd.1
  · exact DownHom.actionDelta_surjective sourceP sourceX.obj sourceAug sourceAug_zero
      (sourceX.complete_totallyAcyclic (formE q)) (sourceX.complete_projective (formE q))
      (sourceX.complete_finite (formE q)) sourceAug_exact sourceX.cover.surjective
      (Enveloping.tensorFunctor sourceF.obj) sourceU sourceUZero
      (Enveloping.tensorCompleteLift_aug sourceF.obj sourceX (formE q) sourceUZero)
      (Enveloping.tensorComplex_exact sourceF.obj sourceP (sourceX.complete_exact (formE q)))
      (Enveloping.tensorComplex_finite sourceF.obj sourceP (sourceX.complete_finite (formE q)))
      (Enveloping.tensorComplex_projective sourceF.obj sourceP (sourceX.complete_finite (formE q))
        (sourceX.complete_projective (formE q)))
      (Enveloping.tensor_augmentation_exact sourceF.obj sourceX (formE q))
      (Enveloping.tensor_map_surjective sourceF.obj sourceAug sourceX.cover.surjective) (a-1) hd.2

end Tachikawa.SourceField



end

end OAI
end

theorem solution : type_of% @OAI.Tachikawa.SourceField.sourceCone_closed_boundary_oai := @OAI.Tachikawa.SourceField.sourceCone_closed_boundary_oai
