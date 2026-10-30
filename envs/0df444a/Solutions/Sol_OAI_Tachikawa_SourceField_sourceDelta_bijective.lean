-- Prove2me | solution 1 for OAI.Tachikawa.SourceField.sourceDelta_bijective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:03:55.798866+00:00
-- url     : https://prove2.me/submissions/8bfe3299-2a4d-41d6-9fdd-23f4a86a9b83

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta013
import Definitions.Def_OAIQ116Ta016
import Theorems.Thm_OAI_Tachikawa_Construction_XInverseTwist_weight
import Theorems.Thm_OAI_Tachikawa_Construction_xTwistHom_positive

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R)) [FiniteDimensional k R]
variable (ι : Type) [Fintype ι] [DecidableEq ι]

lemma freeHomDual_cyclic (g : N →ₗ[R] (ι → R))
    (f : (ι → R) →ₗ[R] N) (a : (ι → R) →ₗ[R] (ι → R)) :
    t.freeHomDual ι g (f.comp a) = t.freeHomDual ι (a.comp g) f := by
  have expand (h : (ι → R) →ₗ[R] N) (x : ι → R) :
      h x = ∑ i, x i • h (Pi.single i 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (ι → R) →ₗ[R] N => z x)
        ((LinearEquiv.piRing R N ι k).symm_apply_apply h)).symm
  have expand' (x : ι → R) : a x = ∑ i, x i • a (Pi.single i 1) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using
      (congrArg (fun z : (ι → R) →ₗ[R] (ι → R) => z x)
        ((LinearEquiv.piRing R (ι → R) ι k).symm_apply_apply a)).symm
  simp only [freeHomDual_apply, LinearMap.comp_apply]
  conv_lhs => arg 2; ext j; rw [expand f (a (Pi.single j 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => arg 2; ext j; rw [expand' (g (f (Pi.single j 1)))]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact t.comm _ _

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.evaluation_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_bounded _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_isKProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finiteAlg _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_leftProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_rightProjective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instAddCommGroupRightIndType _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindCoker _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindEndo _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindIterate _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgLeftIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightFreeFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteAlgCarrierXNatModuleCatComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgRegular _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgTwistedRegular _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerRightIndType _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType_1 _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instProjectiveMulOppositeObjTwistedRegular _root_.OAI.Tachikawa.Enveloping.instProjectiveMulOppositeObjXNatModuleCatAlgComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instProjectiveObjTwistedRegular _root_.OAI.Tachikawa.Enveloping.instProjectiveObjXNatModuleCatAlgComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.leftFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.Enveloping.rightFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.HomBimodule.instEpiModuleCatAlgPostMap _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instSMulCommClassMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdOff _root_.OAI.Tachikawa.downIntTensorSigns
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



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

include k in
lemma complete_homotopy_of_augmentation (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    {N : ModuleCat.{0} R} (a : Q.X 0 →ₗ[R] N)
    (he : Function.Exact (Q.d 1 0) a) (hs : Function.Surjective a)
    (f g : P ⟶ Q) (hfg : a.comp (f.f 0).hom = a.comp (g.f 0).hom) :
    Nonempty (Homotopy f g) := by
  have hz : CokerAt.map (f-g) 0 = 0 := by
    ext x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P 0 x
    apply (CokerAt.augmentationEquiv Q N 0 a he hs).injective
    change a (f.f 0 y-g.f 0 y) = _
    have hy : a (f.f 0 y) = a (g.f 0 y) := LinearMap.congr_fun hfg y
    rw [map_sub,hy,sub_self]
    exact (map_zero _).symm
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (k := k) (f-g) hp hq pproj qfin qproj
    (by rw [hz]; exact (projectiveFactors (k := k)).zero_mem)
  exact ⟨Homotopy.equivSubZero.symm h⟩

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

lemma Hmap_surjective_of_right_zero (a : ℤ) (hM : Subsingleton (H M a)) :
    Function.Surjective (Hmap i a) := by
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective a x
  have hpz : quotient M a (cycleMap p a z) = 0 := hM.elim _ _
  obtain ⟨y,hy⟩ := (quotient_zero_iff_predecessor a _).mp hpz
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

include hi he hp in
lemma Hmap_bijective_of_zeros (a : ℤ) (hprev : Subsingleton (H M (a-1)))
    (hnow : Subsingleton (H M a)) : Function.Bijective (Hmap i a) :=
  ⟨Hmap_injective_of_prev_zero i p hi he hp a hprev,
    Hmap_surjective_of_right_zero i p hi he hp a hnow⟩

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



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] [F.Linear k]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (Q : ChainComplex (ModuleCat.{0} S) ℤ)
  (X : ModuleCat.{0} R)
  (l : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P)

lemma completeFunctorHom_homotopic
    {l' : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P}
    (h : Homotopy l l') (a : ℤ) :
    VectorSplit.Hmap (completeFunctorHom (k := k) F P Q X l) a =
      VectorSplit.Hmap (completeFunctorHom (k := k) F P Q X l') a := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  rw [VectorSplit.Hmap_quotient,VectorSplit.Hmap_quotient]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (VectorSplit.quotient_zero_iff_predecessor a _).mpr
  refine ⟨h.hom (a-1) a ≫ F.map z.val,?_⟩
  change Q.d a (a-1) ≫ h.hom (a-1) a ≫ F.map z.val =
    l.f a ≫ F.map z.val - l'.f a ≫ F.map z.val
  have hc := h.comm a
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel a (a-1) by change a-1+1=a; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (a+1) a from rfl)] at hc
  have hz := (completeHom_memZ P X a z.val).mp z.property
  erw [hc,Preadditive.add_comp,Preadditive.add_comp,Category.assoc]
  let cycle : P.X a ⟶ X := z.val
  change P.d (a+1) a ≫ cycle = 0 at hz
  change Q.d a (a-1) ≫ h.hom (a-1) a ≫ F.map cycle =
    Q.d a (a-1) ≫ h.hom (a-1) a ≫ F.map cycle +
      (h.hom a (a+1) ≫ F.map (P.d (a+1) a) ≫ F.map cycle) +
      l'.f a ≫ F.map cycle - l'.f a ≫ F.map cycle
  erw [← F.map_comp,hz,F.map_zero,Limits.comp_zero,add_zero,add_sub_cancel_right]

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (F G : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] [G.Additive]
  [F.Linear k] [G.Linear k]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (Q : ChainComplex (ModuleCat.{0} S) ℤ)
  (X : ModuleCat.{0} R)
  (l : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P)
  (α : F ⟶ G)

lemma completeFunctorHom_natural :
    completeFunctorHom (k := k) F P Q X l ≫ completeHomMap Q (α.app X) =
      completeFunctorHom G P Q X (l ≫ (α.mapHomologicalComplex (.down ℤ)).app P) := by
  ext a g
  change P.X a ⟶ X at g
  change (l.f a ≫ F.map g) ≫ α.app X = (l.f a ≫ α.app (P.X a)) ≫ G.map g
  erw [Category.assoc,α.naturality,Category.assoc]
  rfl

end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SymmetrizingForm.twist_isEquivalence _root_.OAI.Tachikawa.SymmetrizingForm.twist_preserves_injective _root_.OAI.Tachikawa.SymmetrizingForm.twist_preserves_projective _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R)

variable (ι : Type) [Fintype ι] [DecidableEq ι] (N : ModuleCat R)

omit [FiniteDimensional k R] [Fintype ι] in
lemma twistFromFree_single (f : (ι → R) →ₗ[R] N) (i : ι) :
    twistFromFree σ ι N f (Pi.single i 1) = f (Pi.single i 1) := by
  change f (fun j => σ.symm ((Pi.single i (1:R) : ι → R) j)) = _
  congr 1
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

lemma freeHomDual_twist (c : k) (hc : ∀ r, t.linear (σ r) = c * t.linear r)
    (g : N →ₗ[R] (ι → R)) (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι (twistToFree σ ι N g) (twistFromFree σ ι N f) =
      c * t.freeHomDual ι g f := by
  simp only [freeHomDual_apply,twistFromFree_single]
  change (∑ i, t.linear (σ (g (f (Pi.single i 1)) i))) = _
  simp only [hc,Finset.mul_sum]

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteColimitsModuleCatRes _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteLimitsModuleCatRes _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
  {Y : C} (P : InjectiveResolution Y)

lemma mappedCoresolutionCochainIso_ι :
    (mappedCoresolution F P).ι' ≫ (mappedCoresolutionCochainIso F P).hom =
      (F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
        (F.mapHomologicalComplex (.up ℤ)).map P.ι' := by
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : j = 0
  · subst j
    dsimp only [mappedCoresolution]
    simp only [HomologicalComplex.comp_f,Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, mappedCoresolutionCochainIso,
      mappedCoresolutionCochainXIso_nonneg F P 0 0 rfl,
      InjectiveResolution.ι'_f_zero, Functor.map_comp]
    simp [mappedCoresolution,Functor.mapCochainComplexSingleFunctor,
      singleMapHomologicalComplex]
    simp only [singleObjXSelf,singleObjXIsoOfEq,eqToIso.hom]
    erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.id_comp,
      F.map_id, Category.id_comp]
    try rfl
  · exact (isZero_single_obj_X (.up ℤ) 0 (F.obj Y) j hj).eq_of_src _ _

open CochainComplex CochainComplex.HomComplex
omit [F.PreservesInjectiveObjects] [F.PreservesHomology] in
lemma map_fromSingle_shifted {K : CochainComplex C ℤ} {X : C}
    {p n : ℤ} (f : X ⟶ K.X p) (h : 0+n=p) (p' : ℤ) (hp' : p+1=p')
    (hf : f ≫ K.d p p' = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f h p' hp' hf))
        (F.mapHomologicalComplex (.up ℤ)) =
      Cocycle.equivHomShift.symm (Cocycle.fromSingleMk (F.map f) h p' hp'
        (by simp only [Functor.mapHomologicalComplex_obj_d,← F.map_comp,hf,F.map_zero])) := by
  ext j
  simp [ShiftedHom.map,Cocycle.equivHomShift_symm_apply,
    Cocycle.fromSingleMk,Cocycle.homOf,Cocycle.rightShift,
    Cochain.rightShift_v, Cochain.fromSingleMk,
    Functor.mapCochainComplexSingleFunctor,singleMapHomologicalComplex]
  by_cases hj : j = 0
  · subst j
    simp [Cochain.single,h,HomologicalComplex.XIsoOfEq,
      singleObjXSelf,singleObjXIsoOfEq,eqToHom_map]
    erw [Category.id_comp]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hj]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : InjectiveResolution Y)

lemma injective_extMk_hom_roof [HasDerivedCategory C] [HasExt C]
    {n : ℕ} (f : X ⟶ P.cocomplex.X n) (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    (P.extMk f (n+1) rfl hf).hom =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (P.cochainComplexXIso n n rfl).inv)
          (zero_add _) ((n+1 : ℕ) : ℤ) (by omega)
          (by
            rw [InjectiveResolution.cochainComplex_d _ _ _ n (n+1) rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc]
            rw [← Category.assoc,hf,zero_comp])))
        DerivedCategory.Q ≫ (inv (DerivedCategory.Q.map P.ι'))⟦(n : ℤ)⟧' := by
  rw [InjectiveResolution.extMk_hom]
  simp [DerivedCategory.singleFunctorIsoCompQ,ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀]
  erw [CategoryTheory.Functor.map_id,Category.id_comp,IsIso.inv_hom_id,Category.comp_id]

lemma mappedCoresolutionCochain_cocycle {n : ℕ} (f : X ⟶ P.cocomplex.X n)
    (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (P.cochainComplexXIso n n rfl).inv)
          (zero_add _) ((n+1 : ℕ) : ℤ) (by omega)
          (by
            rw [InjectiveResolution.cochainComplex_d _ _ _ n (n+1) rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc]
            rw [← Category.assoc,hf,zero_comp])))
        (F.mapHomologicalComplex (.up ℤ)) ≫
      ((mappedCoresolutionCochainIso F P).inv)⟦(n : ℤ)⟧' =
    Cocycle.equivHomShift.symm (Cocycle.fromSingleMk
      (F.map f ≫ ((mappedCoresolution F P).cochainComplexXIso n n rfl).inv)
      (zero_add _) ((n+1 : ℕ) : ℤ) (by omega) (by
        rw [InjectiveResolution.cochainComplex_d _ _ _ n (n+1) rfl rfl]
        dsimp only [mappedCoresolution]
        simp only [Category.assoc,Iso.inv_hom_id_assoc]
        change F.map f ≫ F.map (P.cocomplex.d n (n+1)) ≫ _ = 0
        rw [← F.map_comp_assoc,hf,F.map_zero,zero_comp])) := by
  rw [← Category.assoc,map_fromSingle_shifted]
  erw [← Cocycle.equivHomShift_symm_postcomp,← Cocycle.fromSingleMk_postcomp]
  congr 2
  change F.map (f ≫ (P.cochainComplexXIso n n rfl).inv) ≫
    (mappedCoresolutionCochainXIso F P n).inv = _
  rw [mappedCoresolutionCochainXIso_nonneg F P n n rfl]
  dsimp only [mappedCoresolution]
  simp only [Iso.trans_inv,Iso.symm_inv,Functor.mapIso_hom,Functor.map_comp,
    Category.assoc,← F.map_comp_assoc,Iso.inv_hom_id,F.map_id,Category.id_comp]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex

section Shift
variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] {X Y Z : C} {n : ℤ}
lemma shifted_map_precomp (a : X ⟶ Y) (b : Y ⟶ Z⟦n⟧) :
    ShiftedHom.map (a ≫ b) F = F.map a ≫ ShiftedHom.map b F := by
  simp only [ShiftedHom.map,Functor.map_comp,Category.assoc]
lemma shifted_map_postcomp (a : X ⟶ Y⟦n⟧) (b : Y ⟶ Z) :
    ShiftedHom.map (a ≫ b⟦n⟧') F = ShiftedHom.map a F ≫ (F.map b)⟦n⟧' := by
  simp only [ShiftedHom.map,Functor.map_comp,Category.assoc,
    Functor.commShiftIso_hom_naturality]
end Shift

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {K : CochainComplex C ℤ}

lemma derived_roof_map_dual {n : ℤ} (p : (singleFunctor C 0).obj Y ⟶ K) [QuasiIso p]
    (f : (singleFunctor C 0).obj X ⟶ K⟦n⟧) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q ≫ (inv (DerivedCategory.Q.map p))⟦n⟧')
        F.mapDerivedCategory ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧' =
    ShiftedHom.map ((F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
      (inv (DerivedCategory.Q.map
        ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
          (F.mapHomologicalComplex (.up ℤ)).map p)))⟦n⟧' := by
  let A := F.mapDerivedCategoryFactors
  have hf : ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q) F.mapDerivedCategory =
      A.hom.app ((singleFunctor C 0).obj X) ≫ ShiftedHom.map
        (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
          (A.inv.app K)⟦n⟧' := by
    have h := ShiftedHom.map_naturality_2 f A
    simpa only [ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.comp_map] using h.symm
  have hp : A.inv.app K ≫ F.mapDerivedCategory.map (inv (DerivedCategory.Q.map p)) =
      inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p)) ≫
        A.inv.app ((singleFunctor C 0).obj Y) := by
    apply (cancel_epi (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map p))).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc]
    erw [A.inv.naturality p]
    simp only [Functor.comp_map,Category.assoc,← F.mapDerivedCategory.map_comp,IsIso.hom_inv_id,
      F.mapDerivedCategory.map_id]
    erw [Category.comp_id]
  rw [shifted_map_postcomp,hf]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,hp]
  simp only [Functor.map_comp,Category.assoc]
  have hy : F.mapDerivedCategoryFactors.inv.app ((singleFunctor C 0).obj Y) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app Y =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) :=
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y
  have hx : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj X) =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) :=
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  rw [← Functor.map_comp]
  erw [hy]
  rw [← Category.assoc ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
    (A.hom.app ((singleFunctor C 0).obj X))]
  erw [hx]
  have hc : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) =
      inv (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app Y)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [← DerivedCategory.Q.map_comp,Iso.inv_hom_id_app,DerivedCategory.Q.map_id]
  simp only [Functor.map_comp,IsIso.inv_comp,shifted_map_precomp,Category.assoc]
  rw [hc]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
  {X Y : C} (P : InjectiveResolution Y)

lemma mapExactFunctor_injective_extMk {n : ℕ} (f : X ⟶ P.cocomplex.X n)
    (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    (P.extMk f (n+1) rfl hf).mapExactFunctor F =
      (mappedCoresolution F P).extMk (F.map f) (n+1) rfl
        (by change F.map _ ≫ F.map _ = 0; rw [← F.map_comp,hf,F.map_zero]) := by
  apply Ext.ext
  rw [Ext.mapExactFunctor_hom,injective_extMk_hom_roof,derived_roof_map_dual]
  conv_rhs => erw [injective_extMk_hom_roof (mappedCoresolution F P)]
  have hι := mappedCoresolutionCochainIso_ι F P
  have hc := mappedCoresolutionCochain_cocycle F P f hf
  have hq := congrArg (fun z => DerivedCategory.Q.map z) hι
  simp only [Functor.map_comp] at hq
  have hr : DerivedCategory.Q.map (mappedCoresolutionCochainIso F P).inv ≫
      inv (DerivedCategory.Q.map (mappedCoresolution F P).ι') =
      inv (DerivedCategory.Q.map
        ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
          (F.mapHomologicalComplex (.up ℤ)).map P.ι')) := by
    apply (cancel_epi (DerivedCategory.Q.map
      ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
        (F.mapHomologicalComplex (.up ℤ)).map P.ι'))).1
    rw [IsIso.hom_inv_id]
    simp only [Functor.map_comp]
    rw [← hq]
    simp only [Category.assoc,← DerivedCategory.Q.map_comp_assoc,Iso.hom_inv_id,
      DerivedCategory.Q.map_id,Category.id_comp,IsIso.hom_inv_id]
  rw [← Category.assoc] at hc
  dsimp only [mappedCoresolution] at hc ⊢
  rw [← hc]
  erw [shifted_map_postcomp]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  erw [hr]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesInjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : InjectiveResolution X) (e : F.obj X ≅ X)

lemma coresolutionTwistHom_extMk
    (l : InjectiveResolution.Hom (mappedCoresolution F P) P e.hom)
    {n : ℕ} (f : X ⟶ P.cocomplex.X n) (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    extIso (k := k) e e n ((P.extMk f (n+1) rfl hf).mapExactFunctor F) =
      P.extMk ((coresolutionTwistHom (k := k) F P e l.hom).f n f) (n+1) rfl
        (by change (e.inv ≫ F.map f ≫ l.hom.f n) ≫ P.cocomplex.d n (n+1) = 0
            dsimp only [mappedCoresolution] at l ⊢
            rw [Category.assoc,Category.assoc,l.hom.comm]
            change e.inv ≫ F.map f ≫ F.map (P.cocomplex.d n (n+1)) ≫ l.hom.f (n+1) = 0
            rw [← F.map_comp_assoc,hf,F.map_zero,zero_comp,comp_zero]) := by
  let := HasDerivedCategory.standard (ModuleCat R)
  change (Ext.mk₀ e.inv).comp
    (((P.extMk f (n+1) rfl hf).mapExactFunctor F).comp (Ext.mk₀ e.hom) (add_zero n))
      (zero_add n) = _
  rw [mapExactFunctor_injective_extMk]
  have hcomp := InjectiveResolution.extMk_comp_mk₀ (R := mappedCoresolution F P)
    (show F.obj X ⟶ (mappedCoresolution F P).cocomplex.X n from F.map f)
    (n+1) rfl (by change F.map f ≫ F.map _ = 0; rw [← F.map_comp,hf,F.map_zero]) l
  erw [hcomp, P.mk₀_comp_extMk]
  rfl



lemma coresolutionTwist_diff_boundary
    (l : InjectiveResolution.Hom (mappedCoresolution F P) P e.hom) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X (n+1), extIso (k := k) e e (n+1) (x.mapExactFunctor F) = r • x)
    (g : X ⟶ P.cocomplex.X (n+1)) (hg : g ≫ P.cocomplex.d (n+1) (n+2) = 0) :
    ∃ a : X ⟶ P.cocomplex.X n, a ≫ P.cocomplex.d n (n+1) =
      (show X ⟶ P.cocomplex.X (n+1) from
        (coresolutionTwistHom (k := k) F P e l.hom).f (n+1) g) - r • g := by
  let K := coresolutionHom k R P.cocomplex X
  let S := coresolutionTwistHom (k := k) F P e l.hom
  have hgS : S.f (n+1) g ≫ P.cocomplex.d (n+1) (n+2) = 0 := by
    have he := congrArg (fun f => f g) (S.comm (n+1) (n+2))
    change S.f (n+1) g ≫ P.cocomplex.d (n+1) (n+2) =
      S.f (n+2) (g ≫ P.cocomplex.d (n+1) (n+2)) at he
    rw [he,hg]
    exact (S.f (n+2)).hom.map_zero
  let z : VectorSplit.Z K (n+1) := ⟨g,(coresolutionHom_memZ _ _ _ _ _ _).mpr hg⟩
  let zS : VectorSplit.Z K (n+1) := ⟨S.f (n+1) g,(coresolutionHom_memZ _ _ _ _ _ _).mpr hgS⟩
  have he : coresolutionCyclesToExt X P (n+1) (zS-r•z) = 0 := by
    rw [map_sub,map_smul]
    have ha := coresolutionTwistHom_extMk (k := k) F P e l g hg
    change extIso (k := k) e e (n+1)
      ((coresolutionCyclesToExt X P (n+1) z).mapExactFunctor F) =
      coresolutionCyclesToExt X P (n+1) zS at ha
    rw [← ha,h,sub_self]
  have hz : ((show X ⟶ P.cocomplex.X (n+1) from S.f (n+1) g) - r • g) ≫
      P.cocomplex.d (n+1) (n+2) = 0 := by
    rw [Preadditive.sub_comp, Linear.smul_comp, hgS, hg, smul_zero, sub_self]
  exact (P.extMk_eq_zero_iff _ (n+2) rfl hz n rfl).mp he
end Tachikawa



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (ι : Type) [Fintype ι] [DecidableEq ι] (N : ModuleCat R)

lemma freeHomDual_semilinear_adjoint
    (c : k) (hc : ∀ r, t.linear (σ r) = c * t.linear r)
    (l : ModuleCat.of R (ι → R) ⟶ (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    (e : (twistFunctor σ).obj N ⟶ N) (he : ∀ x, e x = x)
    (g g' : N →ₗ[R] (ι → R)) (hg : ∀ x, g' x = l (g x))
    (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι g ((l ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e).hom) =
      c * t.freeHomDual ι g' f := by
  let L := (l ≫ (freeTwistIso σ ι).hom).hom
  have h0 : (l ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e).hom =
      e.hom.comp ((twistFromFree σ ι N f).comp L) := by
    apply LinearMap.ext
    intro x
    change e (f (l x)) = e (f (fun i => σ.symm (σ (l x i))))
    simp only [AlgEquiv.symm_apply_apply]
  rw [h0,← t.freeHomDual_natural]
  rw [t.freeHomDual_cyclic]
  have h1 : L.comp (g.comp e.hom) = twistToFree σ ι N g' := by
    ext x i
    change σ (l (g (e x)) i) = σ (g' x i)
    rw [he]
    exact congrArg σ (congrFun (hg (show N from x)) i).symm
  rw [h1,t.freeHomDual_twist σ ι N c hc]
end Tachikawa.SymmetrizingForm



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (t : SymmetrizingForm (k := k) (R := R))
  {ι κ τ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype τ] [DecidableEq τ]
  {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

lemma free_boundary_iff_pair_cycles (d : (ι → R) →ₗ[R] (κ → R)) (f : (ι → R) →ₗ[R] N) :
    (∃ h : (κ → R) →ₗ[R] N, h.comp d = f) ↔
      ∀ g : N →ₗ[R] (ι → R), d.comp g = 0 → t.freeHomDual ι g f = 0 := by
  constructor
  · rintro ⟨h,rfl⟩ g hg
    rw [t.freeHomDual_cyclic_rect, hg, map_zero,LinearMap.zero_apply]
  · intro h
    change f ∈ LinearMap.range (homPrecompose (k := k) (N := N) d)
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ f).mp
    intro φ hφ
    obtain ⟨g,rfl⟩ := (t.freeHomDual ι (N := N)).surjective φ
    apply h
    apply (t.freeHomDual κ).injective
    ext a
    rw [map_zero,LinearMap.zero_apply,← t.freeHomDual_cyclic_rect]
    exact (Submodule.mem_dualAnnihilator _).mp hφ _ ⟨a,rfl⟩

lemma free_boundary_of_adjoint_scalar
    (d : (ι → R) →ₗ[R] (κ → R)) (b : (τ → R) →ₗ[R] (ι → R))
    (f f' : (ι → R) →ₗ[R] N) (hf : f.comp b = 0) (c r : k)
    (T : (N →ₗ[R] (ι → R)) → (N →ₗ[R] (ι → R)))
    (hpair : ∀ g, t.freeHomDual ι g f' = c * t.freeHomDual ι (T g) f)
    (hT : ∀ g, d.comp g = 0 →
      ∃ a : N →ₗ[R] (τ → R), b.comp a = T g - r • g) :
    ∃ a : (κ → R) →ₗ[R] N, a.comp d = f' - (c*r) • f := by
  apply (t.free_boundary_iff_pair_cycles d _).mpr
  intro g hg
  obtain ⟨a,ha⟩ := hT g hg
  have hb : t.freeHomDual ι (b.comp a) f = 0 := by
    rw [← t.freeHomDual_cyclic_rect,hf,map_zero]
  rw [ha,map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply] at hb
  have he : t.freeHomDual ι (T g) f = r * t.freeHomDual ι g f := sub_eq_zero.mp hb
  rw [map_sub,map_smul,hpair,he]
  change c * (r * _) - (c*r) * _ = 0
  ring
end Tachikawa.SymmetrizingForm



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (e : (twistFunctor σ).obj M.obj ≅ M.obj) (he : ∀ x, e.hom x = x)
  (e' : (twistFunctor σ.symm).obj M.obj ≅ M.obj) (he' : ∀ x, e'.hom x = x)

include he he' in

lemma negativeTwist_diff_boundary
    (l : InjectiveResolution.Hom (M.coresolution t)
      (mappedCoresolution (twistFunctor σ) (M.coresolution t)) e.inv)
    (n : ℕ) (c r : k) (hc : ∀ a, t.linear (σ a) = c * t.linear a)
    (hr : ∀ x : Ext M.obj M.obj (n+1),
      extIso (k := k) e' e' (n+1) (x.mapExactFunctor (twistFunctor σ.symm)) = r • x)
    (f : M.negTerm t (n+1) →ₗ[R] M)
    (hf : f.comp (M.negDifferential t n) = 0) :
    ∃ a : M.negTerm t (n+2) →ₗ[R] M,
      a.comp (M.negDifferential t (n+1)) =
        (show M.negTerm t (n+1) →ₗ[R] M from
          (l.hom.f (n+1) ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e.hom).hom) -
          (c*r) • f := by
  let li := inverseCoresolutionHom σ (M.coresolution t) e he e' he' l
  let S := coresolutionTwistHom (k := k) (twistFunctor σ.symm) (M.coresolution t) e' li.hom
  let T : (M →ₗ[R] M.negTerm t (n+1)) → (M →ₗ[R] M.negTerm t (n+1)) := fun g =>
    (show M.obj ⟶ ModuleCat.of R (M.negTerm t (n+1)) from S.f (n+1) (ModuleCat.ofHom g)).hom
  apply t.free_boundary_of_adjoint_scalar (M.negDifferential t (n+1))
    (M.negDifferential t n) f _ hf c r T
  · intro g
    apply t.freeHomDual_semilinear_adjoint σ _ M.obj c hc (l.hom.f (n+1)) e.hom he g (T g) _ f
    intro x
    change l.hom.f (n+1) (g (e'.inv x)) = l.hom.f (n+1) (g x)
    rw [twistIso_inv_apply σ.symm e' he']
  · intro g hg
    obtain ⟨a,ha⟩ := coresolutionTwist_diff_boundary (k := k) (twistFunctor σ.symm)
      (M.coresolution t) e' li n r hr (ModuleCat.ofHom g) (by
        rw [M.coresolution_d]
        exact ModuleCat.hom_ext hg)
    refine ⟨a.hom,?_⟩
    rw [M.coresolution_d] at ha
    apply LinearMap.ext
    intro x
    have h := congrArg (fun u => u x) ha
    change M.negDifferential t n (a x) = T g x -
      (algebraMap k R r) • g x at h
    rw [IsScalarTower.algebraMap_smul R r (g x)] at h
    exact h

end Tachikawa.FiniteModule

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteColimitsModuleCatRes _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteLimitsModuleCatRes _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.evaluation_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_bounded _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_isKProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finiteAlg _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_leftProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_projective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_rightProjective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instAddCommGroupRightIndType _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindCoker _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindEndo _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgCoindIterate _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgLeftIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightFreeFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierDualLeftObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerRightIndType _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType_1 _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.leftFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.Enveloping.rightFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.HomBimodule.instEpiModuleCatAlgPostMap _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.C_finite _root_.OAI.Tachikawa.LeftCoinduced.J_finite _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.LeftCoinduced.iterate_finite _root_.OAI.Tachikawa.OuterTensor.algebraTwist_preserves_projective _root_.OAI.Tachikawa.OuterTensor.inductionDoubleComparison_isIso _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instSMulCommClassMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdOff _root_.OAI.Tachikawa.downIntTensorSigns _root_.OAI.Tachikawa.freeEndo_finite _root_.OAI.Tachikawa.freeKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (e : (twistFunctor σ).obj M.obj ≅ M.obj)

lemma completeTwistHom_negative (he : ∀ x, e.hom x = x)
    (e' : (twistFunctor σ.symm).obj M.obj ≅ M.obj) (he' : ∀ x, e'.hom x = x)
    (n : ℕ) (c r : k) (hc : ∀ a, t.linear (σ a) = c * t.linear a)
    (hr : ∀ x : Ext M.obj M.obj (n+1),
      extIso (k := k) e' e' (n+1) (x.mapExactFunctor (twistFunctor σ.symm)) = r • x)
    (x : VectorSplit.H (completeHom (k := k) (M.complete t) M.obj) (Int.negSucc (n+1))) :
    VectorSplit.Hmap (M.completeTwistHom t σ e) _ x = (c*r) • x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective _ x
  rw [VectorSplit.Hmap_quotient,← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (VectorSplit.quotient_zero_iff_predecessor _ _).mpr
  have hz := (completeHom_memZ (M.complete t) M.obj (Int.negSucc (n+1)) z.val).mp z.property
  have hz' : z.val.hom.comp (M.negDifferential t n) = 0 := by
    rw [M.complete_d] at hz
    exact ModuleCat.hom_ext_iff.mp hz
  obtain ⟨a,ha⟩ := M.negativeTwist_diff_boundary t σ e he e' he'
    (M.negativeTwistLift t σ e) n c r hc hr z.val.hom hz'
  rw [show Int.negSucc (n+1)-1 = Int.negSucc (n+2) by omega]
  refine ⟨ModuleCat.ofHom a,?_⟩
  change (M.complete t).d (Int.negSucc (n+2)+1) (Int.negSucc (n+2)) ≫ ModuleCat.ofHom a = _
  rw [M.complete_d]
  apply ModuleCat.hom_ext
  exact ha

end Tachikawa.FiniteModule



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R) (e : (twistFunctor σ).obj N.obj ≅ N.obj)

lemma tensorTwistLift_aug : (tensorTwistLift N t σ e).f 0 ≫
    (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) =
      ModuleCat.ofHom N.cover.map ≫ e.inv ≫ (twistedTensorIso σ N.obj).inv := by
  have hc := (N.positiveTwistLift σ e).hom_f_zero_comp_π_f_zero
  change (N.positiveTwistLift σ e).hom.f 0 ≫ (twistFunctor σ).map
    (ModuleCat.ofHom N.cover.map) = ModuleCat.ofHom N.cover.map ≫ e.inv at hc
  change ((N.positiveTwistLift σ e).hom.f 0 ≫ (twistedTensorNatIso σ).inv.app _) ≫ _ = _
  have hn := (twistedTensorNatIso σ).inv.naturality
    (show N.projectiveResolution.complex.X 0 ⟶ N.obj from ModuleCat.ofHom N.cover.map)
  change (twistFunctor σ).map (ModuleCat.ofHom N.cover.map) ≫ (twistedTensorIso σ N.obj).inv =
    (twistedTensorNatIso σ).inv.app (N.projectiveResolution.complex.X 0) ≫
      (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) at hn
  erw [Category.assoc,← hn,← Category.assoc,hc,Category.assoc]

lemma tensorTwistLift_action :
    completeFunctorHom (k := k) (tensorFunctor (twistedRegular σ))
        (N.complete t) (N.complete t) N.obj (tensorTwistLift N t σ e) ≫
      completeHomMap (N.complete t) ((twistedTensorIso σ N.obj).hom ≫ e.hom) =
      N.completeTwistHom t σ e := by
  have hn := completeFunctorHom_natural (k := k) (twistFunctor σ)
    (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj
    (N.completeTwistLift t σ e) (twistedTensorNatIso σ).inv
  change completeFunctorHom (k := k) (twistFunctor σ) (N.complete t) (N.complete t) N.obj
    (N.completeTwistLift t σ e) ≫ completeHomMap _ (twistedTensorIso σ N.obj).inv =
    completeFunctorHom (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj
      (tensorTwistLift N t σ e) at hn
  rw [← hn,Category.assoc,← completeHomMap_comp,(twistedTensorIso σ N.obj).inv_hom_id_assoc]
  rfl

variable {M : ModuleCat (Alg k R R)} (v : N.obj ⟶ (tensorFunctor M).obj N.obj)
  (l : N.complete t ⟶ tensorComplex M (N.complete t))
  (hl : l.f 0 ≫ (tensorFunctor M).map (ModuleCat.ofHom N.cover.map) = ModuleCat.ofHom N.cover.map ≫ v)
  (p : M ⟶ twistedRegular σ)
  (hv : v ≫ evalMap N.obj p = e.inv ≫ (twistedTensorIso σ N.obj).inv)

include hl hv in
lemma tensor_projected_action (a : ℤ) :
    VectorSplit.Hmap
      (completeFunctorHom (k := k) (tensorFunctor M) (N.complete t) (N.complete t) N.obj l ≫
        completeHomMap (N.complete t) (evalMap N.obj p ≫ (twistedTensorIso σ N.obj).hom ≫ e.hom)) a =
      VectorSplit.Hmap (N.completeTwistHom t σ e) a := by
  let lp := l ≫ ((tensorNatTrans p).mapHomologicalComplex (.down ℤ)).app (N.complete t)
  have hpaug : lp.f 0 ≫ (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) =
      (tensorTwistLift N t σ e).f 0 ≫ (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) := by
    change (l.f 0 ≫ (tensorNatTrans p).app _) ≫ _ = _
    erw [Category.assoc,← (tensorNatTrans p).naturality,← Category.assoc,hl, Category.assoc]
    change ModuleCat.ofHom N.cover.map ≫ (v ≫ evalMap N.obj p) = _
    rw [hv,tensorTwistLift_aug]
    try rfl
  obtain ⟨h⟩ := complete_homotopy_of_augmentation (k := k) (N.complete_totallyAcyclic t)
    (tensorComplex_exact (twistedRegular σ) _ (N.complete_exact t)) (N.complete_projective t)
    (tensorComplex_finite (twistedRegular σ) _ (N.complete_finite t))
    (tensorComplex_projective (twistedRegular σ) _ (N.complete_finite t) (N.complete_projective t))
    ((tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map)).hom
    (tensor_augmentation_exact (twistedRegular σ) N t)
    (tensor_map_surjective (twistedRegular σ) (X := (N.complete t).X 0) (Y := N.obj)
      (ModuleCat.ofHom N.cover.map) N.cover.surjective) lp (tensorTwistLift N t σ e)
    (ModuleCat.hom_ext_iff.mp hpaug)
  have hn := completeFunctorHom_natural (k := k) (tensorFunctor M)
    (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj l (tensorNatTrans p)
  change completeFunctorHom (k := k) (tensorFunctor M) (N.complete t) (N.complete t) N.obj l ≫
    completeHomMap _ (evalMap N.obj p) =
    completeFunctorHom (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj lp at hn
  erw [completeHomMap_comp,← Category.assoc,hn]
  have he := congrArg (fun morphism =>
    (VectorSplit.Hmap (completeHomMap (N.complete t)
      ((twistedTensorIso σ N.obj).hom ≫ e.hom)) a).comp morphism)
    (completeFunctorHom_homotopic (k := k) _ _ _ _ _ h a)
  exact (VectorSplit.Hmap_comp _ _ a).trans (he.trans
    ((VectorSplit.Hmap_comp _ _ a).symm.trans
      (congrArg (fun morphism => VectorSplit.Hmap morphism a)
        (tensorTwistLift_action N t σ e))))

end Tachikawa.Enveloping

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
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open scoped TensorProduct
namespace Construction
variable {k : Type*} [Field k] (q : k)

lemma formE_sigma (H : k) (hH : H ≠ 0) (a : E q) :
    (formE q).linear (sigma q H hH a) = H^2 * (formE q).linear a := by
  induction a using OAI.tensorInductionOn with
  | tmul a b =>
    change (H * a.snd 1) * (H * b.snd 1) = H^2 * (a.snd 1 * b.snd 1)
    ring
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]

end Construction
end Tachikawa



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



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

omit [CharP k 2] in
lemma XTwistIso_hom : (XTwistIso q H hH).hom = XTwistComparison q H hH := by
  apply (cancel_epi ((eTwist q H hH).map (XTensorIso q).hom)).1
  simp only [XTwistIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
    ← Functor.map_comp_assoc,Iso.hom_inv_id]
  rw [(eTwist q H hH).map_id,Category.id_comp]
  apply (cancel_epi (OuterTensor.twistObjIso
    (TrivialExtension.scaleDual (R := C k q) H hH)
    (TrivialExtension.scaleDual (R := C k q) H hH)
    (C.simpleObj q) (C.simpleObj q)).hom).1
  change _ ≫ ((_ ≫ _) ≫ _) = _
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

variable [CharP k 2]

omit [CharP k 2] in
lemma XInverseTwistIso_hom_apply (x) : (XInverseTwistIso q H hH).hom x = x := rfl

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.SourceField

lemma distinct_parameter_powers {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ parameter j ^ n := by
  intro h
  have he : (MvPolynomial.X i : Base)^n = (MvPolynomial.X j)^n := by
    apply IsFractionRing.injective Base K
    simpa only [parameter, map_pow] using h
  let v : Fin 3 → ZMod 2 := fun t => if t = i then 0 else 1
  have hv := congrArg (MvPolynomial.eval v) he
  have hji : j ≠ i := Ne.symm hij
  simp [v, hji, Nat.ne_of_gt hn] at hv

lemma H_powers_distinct (n : ℕ) (hn : 0 < n) : H₁^n ≠ H₂^n :=
  distinct_parameter_powers (by decide) n hn

lemma H_inverse_powers_distinct (n : ℕ) (hn : 0 < n) : (H₁^n)⁻¹ ≠ (H₂^n)⁻¹ := by
  intro h
  exact H_powers_distinct n hn (inv_injective h)

end Tachikawa.SourceField



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



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

include hq hp in
lemma xTwistHom_negative (n : ℕ) (x : VectorSplit.H (selfHom q) (Int.negSucc (n+1))) :
    VectorSplit.Hmap (xTwistHom q H hH) _ x = (H^2*H^((n+1)/3)) • x := by
  apply (finiteX q).completeTwistHom_negative (formE q) (sigma q H hH) (XTwistIso q H hH)
    (fun x => by rw [XTwistIso_hom]; rfl) (XInverseTwistIso q H hH)
    (XInverseTwistIso_hom_apply q H hH) n (H^2) (H^((n+1)/3))
  · exact formE_sigma q H hH
  · exact XInverseTwist_weight q H hH hq hp (n+1)

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdOff
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
lemma concreteVZero_snd : concreteVZero q hq hp H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap (xObj q) (concreteSnd q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₂ h₂).inv :=
  (exists_concrete_vZero q hq hp H₁ H₂ h₁ h₂).choose_spec.2

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

include hq hp in
lemma FHomInclusion_bijective (a : ℤ) (h3 : a ≠ -3) (h2 : a ≠ -2)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Function.Bijective (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_bijective_of_zeros _ _ hs.1 hs.2.1 hs.2.2 a
    (completeYHomology_zero q hq hp (a-1) (by omega) (by omega))
    (completeYHomology_zero q hq hp a h3 h0)
end Tachikawa.Construction



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

lemma FHomInclusion_one_bijective : Function.Bijective
    (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) 1) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact ⟨VectorSplit.Hmap_injective_of_prev_surjective _ _ hs.1 hs.2.1 hs.2.2 1
    (FHomProjection_zero_surjective q hq hp H₁ H₂ h₁ h₂),
    VectorSplit.Hmap_surjective_of_right_zero _ _ hs.1 hs.2.1 hs.2.2 1
      (completeYHomology_zero q hq hp 1 (by decide) (by decide))⟩

omit [CharP k 2] in
lemma middleHpairX_bijective (a : ℤ) : Function.Bijective (middleHpairX q H₁ H₂ h₁ h₂ a) := by
  dsimp only [middleHpairX, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact Function.Bijective.comp (LinearEquiv.bijective _) (middleHpair_bijective q H₁ H₂ h₁ h₂ a)

omit [CharP k 2] in
lemma middleHom_zero (a : ℤ) (hz : Subsingleton (VectorSplit.H (selfHom q) a)) :
    Subsingleton (VectorSplit.H (middleHom q H₁ H₂ h₁ h₂) a) := by
  let := hz
  exact (middleHpairX_bijective q H₁ H₂ h₁ h₂ a).1.subsingleton

lemma FHomInclusion_injective (a : ℤ) (h2 : a ≠ -2) (h1 : a ≠ 1) :
    Function.Injective (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_injective_of_prev_zero _ _ hs.1 hs.2.1 hs.2.2 a
    (completeYHomology_zero q hq hp (a-1) (by omega) (by omega))

lemma FHom_minusThree_zero : Subsingleton
    (VectorSplit.H (FHom q hq hp H₁ H₂ h₁ h₂) (-3)) := by
  have hi := FHomInclusion_injective q hq hp H₁ H₂ h₁ h₂ (-3) (by decide) (by decide)
  let := middleHom_zero q H₁ H₂ h₁ h₂ (-3) (selfHom_zero_near q hq hp).2.2.2
  exact hi.subsingleton

lemma FHomPair_bijective (a : ℤ) (ha : 0 < a ∨ a ≤ -3) :
    Function.Bijective (FHomPair q hq hp H₁ H₂ h₁ h₂ a) := by
  by_cases h3 : a = -3
  · subst a
    have hF := FHom_minusThree_zero q hq hp H₁ H₂ h₁ h₂
    have hX := (selfHom_zero_near q hq hp).2.2.2
    exact ⟨fun _ _ _ => hF.elim _ _,fun x => ⟨0,Prod.ext (hX.elim _ _) (hX.elim _ _)⟩⟩
  · apply (middleHpairX_bijective q H₁ H₂ h₁ h₂ a).comp
    by_cases h1 : a = 1
    · subst a
      exact FHomInclusion_one_bijective q hq hp H₁ H₂ h₁ h₂
    · exact FHomInclusion_bijective q hq hp H₁ H₂ h₁ h₂ a h3 (by omega) (by omega) h1

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
lemma evalMap_comp (X : ModuleCat R) {U V W : ModuleCat (Alg k R R)} (f : U ⟶ V) (g : V ⟶ W) :
    evalMap X (f ≫ g) = evalMap X f ≫ evalMap X g := (evaluation X).map_comp f g

lemma completeHmap_eval_comp (P : ChainComplex (ModuleCat R) ℤ) (X N : ModuleCat R)
    {U V W : ModuleCat (Alg k R R)} (f : U ⟶ V) (g : V ⟶ W)
    (h : evalObj X W ⟶ N) (a : ℤ) :
    completeHmap (k := k) P (evalMap X (f ≫ g) ≫ h) a =
      (completeHmap P h a).comp
        ((completeHmap P (evalMap X g) a).comp (completeHmap P (evalMap X f) a)) := by
  rw [evalMap_comp,completeHmap_comp,completeHmap_comp]
end Tachikawa.Enveloping

namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

omit [CharP k 2] in
lemma uXIso_hom_twist (H : k) (hH : H ≠ 0) :
    (uXIso q H hH).hom = (Enveloping.twistedTensorIso (sigma q H hH) (xObj q)).hom ≫
      (XTwistIso q H hH).hom := by
  rw [XTwistIso_hom]
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  change (show E q from m) • x = (sigma q H hH).symm (show E q from m) • x
  have h := sigma_fixed_x q H hH ((sigma q H hH).symm (show E q from m)) x
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

omit [CharP k 2] in
lemma uXIso_inv_twist (H : k) (hH : H ≠ 0) :
    (uXIso q H hH).inv = (XTwistIso q H hH).inv ≫
      (Enveloping.twistedTensorIso (sigma q H hH) (xObj q)).inv := by
  apply (cancel_mono (uXIso q H hH).hom).1
  rw [(uXIso q H hH).inv_hom_id,uXIso_hom_twist]
  erw [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id]

attribute [local instance] OAI.Tachikawa.Construction.concreteF_left_projective
attribute [local instance] OAI.Tachikawa.Construction.concreteF_right_projective
attribute [local instance] OAI.Tachikawa.Construction.concreteF_finite
lemma FHomPair_eq (a : ℤ) : FHomPair q hq hp H₁ H₂ h₁ h₂ a =
    (VectorSplit.Hmap (FFirst q hq hp H₁ H₂ h₁ h₂) a).prod
      (VectorSplit.Hmap (FSecond q hq hp H₁ H₂ h₁ h₂) a) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change completeHmap _ (uXIso q H₁ h₁).hom a
      (completeHmap _ (Enveloping.evalMap _ (Enveloping.fiberFst _ _ _)) a
      (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a x)) =
      completeHmap _ (Enveloping.evalMap (xObj q)
        (concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
          Enveloping.fiberFst (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)) ≫
        (uXIso q H₁ h₁).hom) a x
    exact (LinearMap.congr_fun (Enveloping.completeHmap_eval_comp
      (xComplete q) (xObj q) (xObj q) _ _ (uXIso q H₁ h₁).hom a) x).symm
  · change completeHmap _ (uXIso q H₂ h₂).hom a
      (completeHmap _ (Enveloping.evalMap _ (Enveloping.fiberSnd _ _ _)) a
      (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a x)) =
      completeHmap _ (Enveloping.evalMap (xObj q)
        (concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
          Enveloping.fiberSnd (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)) ≫
        (uXIso q H₂ h₂).hom) a x
    exact (LinearMap.congr_fun (Enveloping.completeHmap_eval_comp
      (xComplete q) (xObj q) (xObj q) _ _ (uXIso q H₂ h₂).hom a) x).symm

lemma FAction_first (a : ℤ) : VectorSplit.Hmap
    (FAction q hq hp H₁ H₂ h₁ h₂ ≫ FFirst q hq hp H₁ H₂ h₁ h₂) a =
    VectorSplit.Hmap (xTwistHom q H₁ h₁) a := by
  dsimp only [FFirst]
  rw [uXIso_hom_twist]
  exact Enveloping.tensor_projected_action (finiteX q) (formE q) (sigma q H₁ h₁)
    (XTwistIso q H₁ h₁) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
    (concreteLift q hq hp H₁ H₂ h₁ h₂)
    (Enveloping.tensorCompleteLift_aug _ _ _ _)
    (concreteFst q hq hp H₁ H₂ h₁ h₂)
    ((concreteVZero_fst q hq hp H₁ H₂ h₁ h₂).trans (uXIso_inv_twist q H₁ h₁)) a

lemma FAction_second (a : ℤ) : VectorSplit.Hmap
    (FAction q hq hp H₁ H₂ h₁ h₂ ≫ FSecond q hq hp H₁ H₂ h₁ h₂) a =
    VectorSplit.Hmap (xTwistHom q H₂ h₂) a := by
  dsimp only [FSecond]
  rw [uXIso_hom_twist]
  exact Enveloping.tensor_projected_action (finiteX q) (formE q) (sigma q H₂ h₂)
    (XTwistIso q H₂ h₂) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
    (concreteLift q hq hp H₁ H₂ h₁ h₂)
    (Enveloping.tensorCompleteLift_aug _ _ _ _)
    (concreteSnd q hq hp H₁ H₂ h₁ h₂)
    ((concreteVZero_snd q hq hp H₁ H₂ h₁ h₂).trans (uXIso_inv_twist q H₂ h₂)) a

lemma VAction_first : VAction q hq hp H₁ H₂ h₁ h₂ ≫ FFirst q hq hp H₁ H₂ h₁ h₂ = 𝟙 _ := by
  rw [← completeHomMap_comp,← Category.assoc,concreteVZero_fst,Iso.inv_hom_id,completeHomMap_id]
lemma VAction_second : VAction q hq hp H₁ H₂ h₁ h₂ ≫ FSecond q hq hp H₁ H₂ h₁ h₂ = 𝟙 _ := by
  rw [← completeHomMap_comp,← Category.assoc,concreteVZero_snd,Iso.inv_hom_id,completeHomMap_id]

end Tachikawa.Construction



namespace Tachikawa
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

lemma scalarPair_bijective (r s : k) (hrs : r ≠ s) :
    Function.Bijective (scalarPair (V := V) r s) := by
  have hn : r-s ≠ 0 := sub_ne_zero.mpr hrs
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨g,h⟩ hz
    have h1 : r • g + h = 0 := congrArg Prod.fst hz
    have h2 : s • g + h = 0 := congrArg Prod.snd hz
    have hg : (r-s) • g = 0 := by rw [sub_smul]; exact (add_left_inj h).mp (h1.trans h2.symm) |> sub_eq_zero.mpr
    have hg0 : g = 0 := (smul_eq_zero.mp hg).resolve_left hn
    simp only [hg0,smul_zero,zero_add] at h1
    exact Prod.ext hg0 h1
  · rintro ⟨x,y⟩
    let g := (r-s)⁻¹ • (x-y)
    refine ⟨(g,x-r•g),?_⟩
    apply Prod.ext
    · change r•g+(x-r•g)=x
      abel
    · change s•g+(x-r•g)=y
      have he : (r-s) • g = x-y := by
        dsimp [g]
        rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
      rw [sub_smul] at he
      calc
        s•g+(x-r•g) = x-(r•g-s•g) := by abel
        _ = y := by rw [he]; abel

end Tachikawa



namespace Tachikawa
namespace Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma delta_pair (a : ℤ) (x y : VectorSplit.H (selfHom q) a) :
    FHomPair q hq hp H₁ H₂ h₁ h₂ a (delta q hq hp H₁ H₂ h₁ h₂ a (x,y)) =
      (VectorSplit.Hmap (xTwistHom q H₁ h₁) a x + y,
        VectorSplit.Hmap (xTwistHom q H₂ h₂) a x + y) := by
  rw [FHomPair_eq]
  change (VectorSplit.Hmap (FFirst q hq hp H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) a x +
        VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a y),
    VectorSplit.Hmap (FSecond q hq hp H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) a x +
        VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a y)) = _
  simp only [map_add, ← LinearMap.comp_apply,← VectorSplit.Hmap_comp,
    FAction_first,FAction_second,VAction_first,VAction_second,VectorSplit.Hmap_id,
    LinearMap.id_apply]

lemma delta_bijective_weights (a : ℤ) (ha : 0 < a ∨ a ≤ -3) (r s : k) (hrs : r ≠ s)
    (hr : ∀ x, VectorSplit.Hmap (xTwistHom q H₁ h₁) a x = r • x)
    (hs : ∀ x, VectorSplit.Hmap (xTwistHom q H₂ h₂) a x = s • x) :
    Function.Bijective (delta q hq hp H₁ H₂ h₁ h₂ a) := by
  have he : (FHomPair q hq hp H₁ H₂ h₁ h₂ a).comp (delta q hq hp H₁ H₂ h₁ h₂ a) =
      scalarPair r s := by
    apply LinearMap.ext
    rintro ⟨x,y⟩
    exact (delta_pair q hq hp H₁ H₂ h₁ h₂ a x y).trans (by rw [hr,hs]; rfl)
  have hb := scalarPair_bijective (V := VectorSplit.H (selfHom q) a) r s hrs
  rw [← he] at hb
  exact ⟨fun _ _ h => hb.1 (congrArg (FHomPair q hq hp H₁ H₂ h₁ h₂ a) h),fun z => by
    obtain ⟨x,hx⟩ := hb.2 (FHomPair q hq hp H₁ H₂ h₁ h₂ a z)
    exact ⟨x,(FHomPair_bijective q hq hp H₁ H₂ h₁ h₂ a ha).1 hx⟩⟩

lemma delta_bijective_of_zero (a : ℤ) (ha : 0 < a ∨ a ≤ -3)
    (hz : Subsingleton (VectorSplit.H (selfHom q) a)) :
    Function.Bijective (delta q hq hp H₁ H₂ h₁ h₂ a) := by
  let := hz
  let : Subsingleton (VectorSplit.H (FHom q hq hp H₁ H₂ h₁ h₂) a) :=
    (FHomPair_bijective q hq hp H₁ H₂ h₁ h₂ a ha).1.subsingleton
  exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun x => ⟨0,Subsingleton.elim _ _⟩⟩

end Construction

namespace SourceField
open Construction

lemma sourceDelta_positive (n : ℕ) : Function.Bijective (sourceDelta ((n+1:ℕ):ℤ)) := by
  by_cases hlow : n+1 < 3
  · apply delta_bijective_of_zero _ _ _ _ _ _ _ _ (Or.inl (by omega))
    exact positiveSelfHom_zero q (parameter_ne_zero 0) one_add_q_pow_ne_zero n (by omega)
  · apply delta_bijective_weights _ _ _ _ _ _ _ _ (Or.inl (by omega))
      ((H₁⁻¹)^((n+1)/3)) ((H₂⁻¹)^((n+1)/3))
    · simpa only [inv_pow] using H_inverse_powers_distinct ((n+1)/3) (by omega)
    · exact xTwistHom_positive q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero n
    · exact xTwistHom_positive q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero n

lemma sourceDelta_negative (n : ℕ) : Function.Bijective (sourceDelta (Int.negSucc (n+2))) := by
  apply delta_bijective_weights _ _ _ _ _ _ _ _ (Or.inr (by omega))
    (H₁^2*H₁^((n+2)/3)) (H₂^2*H₂^((n+2)/3))
  · simpa only [← pow_add] using H_powers_distinct (2+(n+2)/3) (by omega)
  · exact xTwistHom_negative q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero (n+1)
  · exact xTwistHom_negative q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero (n+1)

lemma sourceDelta_bijective_oai (a : ℤ) (ha : 0 < a ∨ a ≤ -3) :
    Function.Bijective (sourceDelta a) := by
  rcases ha with ha | ha
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, a = ((n+1:ℕ):ℤ) := ⟨(a-1).toNat,by omega⟩
    exact sourceDelta_positive n
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, a = Int.negSucc (n+2) := ⟨(-a-3).toNat,by omega⟩
    exact sourceDelta_negative n

end SourceField
end Tachikawa



end

end OAI
end

theorem solution : type_of% @OAI.Tachikawa.SourceField.sourceDelta_bijective_oai := @OAI.Tachikawa.SourceField.sourceDelta_bijective_oai
