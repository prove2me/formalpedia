-- Prove2me | solution 1 for OAI.Tachikawa.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:01:09.81502+00:00
-- url     : https://prove2.me/submissions/7632630b-fe48-4df0-9993-6f6792205d26

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta016
import Theorems.Thm_OAI_Tachikawa_SourceField_sourceCone_closed_boundary

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instInjectiveE _root_.OAI.Tachikawa.Construction.instIsScalarTowerEX _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.TrivialInduction.inducedProjective _root_.OAI.Tachikawa.TrivialInduction.instAdditiveModuleCatTrivialExtensionFunctor _root_.OAI.Tachikawa.TrivialInduction.instIsScalarTowerTrivialExtensionObj _root_.OAI.Tachikawa.TrivialInduction.instModuleTrivialExtensionObj _root_.OAI.Tachikawa.TrivialInduction.instProjectiveTrivialExtensionObjForallFin _root_.OAI.Tachikawa.TrivialInflation.instIsScalarTowerTrivialExtension _root_.OAI.Tachikawa.TrivialInflation.instModuleTrivialExtension _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa
variable {K A : Type} [Field K] [Ring A] [Algebra K A]
lemma SymmetrizingForm.symmetricOver (t : SymmetrizingForm (k := K) (R := A))
    [FiniteDimensional K A] : SymmetricOver K A := by
  refine ⟨t.dualEquiv.restrictScalars K, ?_, ?_⟩
  · intro a b c
    change t.linear (c * (a*b)) = t.linear ((c*a)*b)
    rw [mul_assoc]
  · intro a b c
    change t.linear (c * (a*b)) = t.linear ((b*c)*a)
    calc
      t.linear (c * (a*b)) = t.linear ((c*a)*b) := by rw [mul_assoc]
      _ = t.linear (b*(c*a)) := t.comm _ _
      _ = t.linear ((b*c)*a) := by rw [mul_assoc]
lemma TrivialExtension.symmetricOver [FiniteDimensional K A] :
    SymmetricOver K (TrivialExtension K A) :=
  (TrivialExtension.symmetrizingForm (k := K) (R := A)).symmetricOver
end Tachikawa



namespace Tachikawa
lemma counterexampleOf (A M : Type) [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite k A] [Module.Finite k M]
    (sym : SymmetricOver k A) (nonproj : ¬ Module.Projective A M)
    (van : ∀ n : ℕ, Subsingleton (CategoryTheory.Abelian.Ext
      (ModuleCat.of A M) (ModuleCat.of A M) (n+1))) : Counterexample := by
  refine ⟨A, inferInstance, inferInstance, inferInstance, sym, M, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, nonproj, ?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact van m
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteResolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]

variable (P Q : ChainComplex (ModuleCat R) ℤ)

namespace CokerAt
variable {P Q}

lemma map_id (j : ℤ) : map (𝟙 P) j = LinearMap.id := by
  ext x
  obtain ⟨y, rfl⟩ := π_surjective P j x
  rfl
end CokerAt

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



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

lemma coker_factors_of_nullhomotopic (h : Homotopy f 0)
    (pfin : Module.Finite R (P.X (-1))) (pproj : Module.Projective R (P.X (-1))) :
    CokerAt.map f 0 ∈ projectiveFactors (k := k) := by
  refine ⟨P.X (-1), pfin, pproj, CokerAt.δ P 0 (-1),
    (CokerAt.π Q 0).comp (h.hom (-1) 0).hom, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective P 0 x
  have hc := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel 0 (-1) by decide),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel 1 0 by decide)] at hc
  have hc' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) y
  change f.f 0 y = h.hom (-1) 0 (P.d 0 (-1) y) +
    Q.d 1 0 (h.hom 0 1 y) + 0 at hc'
  change CokerAt.π Q 0 (h.hom (-1) 0 (P.d 0 (-1) y)) = CokerAt.π Q 0 (f.f 0 y)
  have hz : CokerAt.π Q 0 (Q.d 1 0 (h.hom 0 1 y)) = 0 :=
    LinearMap.congr_fun (CokerAt.π_d Q 0) (h.hom 0 1 y)
  rw [hc', add_zero, map_add, hz, add_zero]

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

end Tachikawa.VectorSplit



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [Ring R]

theorem ext_subsingleton_of_coboundaries {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (I : InjectiveResolution Y) (n : ℕ)
    (h : ∀ f : X ⟶ I.cocomplex.X (n+1),
      f ≫ I.cocomplex.d (n+1) (n+2) = 0 →
      ∃ g : X ⟶ I.cocomplex.X n, g ≫ I.cocomplex.d n (n+1) = f) :
    Subsingleton (Abelian.Ext X Y (n+1)) := by
  have hzero (α : Abelian.Ext X Y (n+1)) : α = 0 := by
    obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n+2) rfl
    exact (I.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mpr (h f hf)
  exact ⟨fun α β => (hzero α).trans (hzero β).symm⟩
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instInjectiveE _root_.OAI.Tachikawa.Construction.instIsScalarTowerEX _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.TrivialInduction.instAdditiveModuleCatTrivialExtensionFunctor _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]
  [Module k Z] [IsScalarTower k R Z]

namespace Nakayama
lemma coevaluation_natural_left (f : P →ₗ[R] Q) (ψ : Module.Dual k (P →ₗ[R] Z)) :
    (map f).comp (coevaluation ψ) = coevaluation (ψ.comp (homPrecomp f)) := by
  ext z a
  rfl

lemma homDualEquiv_natural_left [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (g : Z →ₗ[R] Nakayama k R P) :
    homDualEquiv ((map f).comp g) = (homDualEquiv g).comp (homPrecomp f) := by
  apply coevaluation_bijective.injective
  rw [coevaluation_homDualEquiv, ← coevaluation_natural_left, coevaluation_homDualEquiv]

end Nakayama
end Tachikawa



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]

variable [FiniteDimensional k R] [FiniteDimensional k M]

lemma hom_ext {f g : Obj k R M →ₗ[TrivialExtension k R] Obj k R N}
    (h : ∀ m, f (unit m) = g (unit m)) : f = g := by
  let lower : Nakayama k R M →ₗ[R] Obj k R M := LinearMap.inr R M (Nakayama k R M)
  have ht : ∀ ψ : Nakayama k R M, f (lower ψ) = g (lower ψ) := by
    intro ψ
    obtain ⟨z, rfl⟩ := Nakayama.evaluation_surjective (k := k) (R := R) (M := M) ψ
    induction z using BalancedTensor.induction_on with
    | h0 => rw [_root_.map_zero, _root_.map_zero, _root_.map_zero, _root_.map_zero]
    | ht φ m =>
      have he : lower (Nakayama.evaluation (BalancedTensor.mk φ m)) =
          (TrivSqZeroExt.inr φ : TrivialExtension k R) • unit m := by
        apply Prod.ext
        · change (0:M) = (0:R) • m
          exact (zero_smul R m).symm
        · change Nakayama.evaluationBilinear φ m = Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M)
          rw [zero_smul, add_zero]
      rw [he, map_smul, map_smul, h]
    | ha z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  apply LinearMap.ext
  intro x
  have hx : x = unit (k := k) (R := R) x.1 + lower x.2 := by
    apply Prod.ext
    · change x.1 = x.1+0
      rw [add_zero]
    · change x.2 = 0+x.2
      rw [zero_add]
  rw [hx, map_add, map_add, h, ht]

@[simp] lemma lift_restrict (f : Obj k R M →ₗ[TrivialExtension k R] Obj k R N) :
    lift (restrict f) = f := hom_ext (fun m => lift_unit (restrict f) m)

lemma restrict_injective : Function.Injective (restrict (k := k) (R := R) (M := M) (N := N)) := by
  intro f g h
  apply hom_ext
  intro m
  exact LinearMap.congr_fun h m

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma restrict_comp (f : Obj k R N →ₗ[TrivialExtension k R] Obj k R P) (a : M →ₗ[R] N) :
    restrict (f.comp (map a)) = (restrict f).comp a := by
  apply LinearMap.ext
  intro m
  change f (map a (unit m)) = f (unit (a m))
  rw [map_unit]

end Tachikawa.TrivialInduction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama
variable {P Q T Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T]
  [AddCommGroup Z] [Module R Z] [Module k Z] [IsScalarTower k R Z]
  [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]
  [Module.Finite R T] [Module.Projective R T]

lemma hom_map_exact (f : P →ₗ[R] Q) (g : Q →ₗ[R] T)
    (h : Function.Exact (homPrecomp (k := k) (Z := Z) g) (homPrecomp (k := k) f)) :
    Function.Exact (LinearMap.compRight k (map (k := k) f) :
        (Z →ₗ[R] Nakayama k R P) →ₗ[k] (Z →ₗ[R] Nakayama k R Q))
      (LinearMap.compRight k (map (k := k) g)) := by
  have he := exact_dual _ _ h
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := homDualEquiv (k := k) (P := P) (Z := Z))
    (e₂ := homDualEquiv (k := k) (P := Q) (Z := Z))
    (e₃ := homDualEquiv (k := k) (P := T) (Z := Z))
    (g₁₂ := (homPrecomp (k := k) f).dualMap) (g₂₃ := (homPrecomp (k := k) g).dualMap) ?_ ?_).mp he
  · apply LinearMap.ext
    intro a
    exact (homDualEquiv_natural_left f a).symm
  · apply LinearMap.ext
    intro a
    exact (homDualEquiv_natural_left g a).symm

variable (C : ChainComplex (ModuleCat R) ℤ)

lemma injectiveTail_d (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j))
    (proj : ∀ j, Module.Projective R (C.X j)) (n : ℕ) :
    (injectiveTail (k := k) C hC fin proj).cocomplex.d n (n+1) =
      (complex (k := k) C).d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1) := by
  dsimp only [injectiveTail, coresolutionOfExact]
  exact CochainComplex.of_d _ _ n

lemma ext_negative (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j))
    (proj : ∀ j, Module.Projective R (C.X j))
    (Z : ModuleCat R) (n : ℕ)
    (h : Function.Exact
      (homPrecomp (k := k) (Z := Z) (C.d (-((n+1 : ℕ) : ℤ)-1) (-((n+2 : ℕ) : ℤ)-1)).hom)
      (homPrecomp (k := k) (C.d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1)).hom)) :
    Subsingleton (Abelian.Ext Z (ModuleCat.of R (CokerAt (complex (k := k) C) 0)) (n+1)) := by
  let I := injectiveTail (k := k) C hC fin proj
  apply ext_subsingleton_of_coboundaries I n
  intro f hf
  rw [injectiveTail_d] at hf
  let := fin (-(n : ℤ)-1)
  let := fin (-((n+1 : ℕ) : ℤ)-1)
  let := fin (-((n+2 : ℕ) : ℤ)-1)
  let := proj (-(n : ℤ)-1)
  let := proj (-((n+1 : ℕ) : ℤ)-1)
  let := proj (-((n+2 : ℕ) : ℤ)-1)
  have he := hom_map_exact (Z := Z) _ _ h
  obtain ⟨g, hg⟩ := (he f.hom).mp (ModuleCat.hom_ext_iff.mp hf)
  refine ⟨ModuleCat.ofHom g, ?_⟩
  rw [injectiveTail_d]
  exact ModuleCat.hom_ext hg

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory

lemma ext_subsingleton_target_iso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (e : Y ≅ Z) (n : ℕ) [Subsingleton (Abelian.Ext X Y n)] :
    Subsingleton (Abelian.Ext X Z n) := by
  let h := (Abelian.extFunctorObj X n).mapIso e
  let e' : Abelian.Ext X Y n ≃+ Abelian.Ext X Z n := h.addCommGroupIsoToAddEquiv
  exact e'.symm.injective.subsingleton

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace TrivialInduction
variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

lemma projective_of_inducedProjective [Module.Finite R M]
    [Module.Projective (TrivialExtension k R) (Obj k R M)] : Module.Projective R M := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.projective_lifting_property (map (k := k) c.map)
    (LinearMap.id (R := TrivialExtension k R) (M := Obj k R M)) (map_surjective c.map c.surjective)
  apply Module.Projective.of_split (first.comp (restrict s)) c.map
  apply LinearMap.ext
  intro m
  exact congrArg Prod.fst (LinearMap.congr_fun hs (unit m))

variable (C : ChainComplex (ModuleCat R) ℤ)

lemma inducedResolution_d (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j)) (n : ℕ) :
    (inducedResolution (k := k) C hC fin proj).complex.d (n+1) n =
      ModuleCat.ofHom (map (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom) := by
  dsimp only [inducedResolution, resolutionOfExact]
  exact ChainComplex.of_d _ _ n

theorem transfer [FiniteDimensional k R] (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
    (pos : ∀ n : ℕ, Function.Exact
      (homPrecomp (k := k) (Z := CokerAt C 0) (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom)
      (homPrecomp (k := k) (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom))
    (neg : ∀ n : ℕ, Function.Exact
      (homPrecomp (k := k) (Z := CokerAt C 0) (C.d (-((n+1 : ℕ) : ℤ)-1) (-((n+2 : ℕ) : ℤ)-1)).hom)
      (homPrecomp (k := k) (C.d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1)).hom))
    (n : ℕ) :
    Subsingleton (Abelian.Ext
      (ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0)))
      (ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0))) (n+1)) := by
  let Q := completeResolutionTail C hC.1 proj
  let Z := CokerAt C 0
  let := Nakayama.ext_negative (k := k) C hC fin proj (ModuleCat.of R Z) n (neg n)
  let : Subsingleton (Abelian.Ext (ModuleCat.of R Z) (ModuleCat.of R (Nakayama k R Z)) (n+1)) :=
    ext_subsingleton_target_iso (Nakayama.cokerEquiv (k := k) C).toModuleIso (n+1)
  apply ext_subsingleton_of_boundaries (inducedResolution (k := k) C hC fin proj) n
  intro f hf
  rw [inducedResolution_d] at hf
  let f₀ : Obj k R (C.X ((n+1 : ℕ) : ℤ)) →ₗ[TrivialExtension k R] Obj k R Z := f.hom
  have hf₀ : f₀.comp (map (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom) = 0 :=
    congrArg ModuleCat.Hom.hom hf
  have hf' := congrArg (restrict (k := k) (R := R)) hf₀
  rw [restrict_comp] at hf'
  have hzero : restrict (0 : Obj k R (C.X ((n+2 : ℕ) : ℤ)) →ₗ[TrivialExtension k R] Obj k R Z) = 0 := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hzero] at hf'
  have hf₁ : (first.comp (restrict f₀)).comp (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0 := by
    rw [LinearMap.comp_assoc, hf', LinearMap.comp_zero]
  obtain ⟨g₁,hg₁⟩ := (pos n (first.comp (restrict f₀))).mp hf₁
  have hf₂ : (Q.complex.d (n+2) (n+1)) ≫ ModuleCat.ofHom (second.comp (restrict f₀)) = 0 := by
    rw [completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (second.comp (restrict f₀)).comp (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    rw [LinearMap.comp_assoc, hf', LinearMap.comp_zero]
  obtain ⟨g₂,hg₂⟩ := boundaries_of_ext_subsingleton Q n (ModuleCat.ofHom (second.comp (restrict f₀))) hf₂
  rw [completeResolutionTail_d] at hg₂
  let g : C.X (n : ℤ) →ₗ[R] Obj k R Z := g₁.prod g₂.hom
  refine ⟨ModuleCat.ofHom (lift g), ?_⟩
  rw [inducedResolution_d]
  apply ModuleCat.hom_ext
  change (lift g).comp (map (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom) = f₀
  let := fin ((n+1 : ℕ) : ℤ)
  let : FiniteDimensional k (C.X ((n+1 : ℕ) : ℤ)) := Module.Finite.trans R _
  apply restrict_injective
  rw [restrict_comp, restrict_lift]
  apply LinearMap.ext
  intro x
  exact Prod.ext (LinearMap.congr_fun hg₁ x) (congrArg (fun h => h x) hg₂)

end TrivialInduction



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
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R))
  [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]

lemma D₀Map_exact {L N P : ModuleCat R} (f : L ⟶ N) (g : N ⟶ P)
    (he : Function.Exact f g) : Function.Exact (D₀Map F f) (D₀Map F g) := by
  have ht := BalancedTensor.mapRight_exact (k := k) (R := R) (S := R) (M := Enveloping.Obj F) f.hom g.hom he
  intro x
  constructor
  · intro hx
    have h₀ : g x.1 = 0 := congrArg Prod.fst hx
    have h₁ : BalancedTensor.mapRight (M := Enveloping.Obj F) g.hom x.2 = 0 := congrArg Prod.snd hx
    obtain ⟨y,hy⟩ := (he x.1).mp h₀
    obtain ⟨z,hz⟩ := (ht x.2).mp h₁
    exact ⟨(y,z),Prod.ext hy hz⟩
  · rintro ⟨y,rfl⟩
    apply Prod.ext
    · exact (he _).mpr ⟨y.1,rfl⟩
    · exact (ht _).mpr ⟨y.2,rfl⟩

omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma D₁Map_exact {L N P : ModuleCat R} (f : L ⟶ N) (g : N ⟶ P)
    (he : Function.Exact f g) : Function.Exact (D₁Map F f) (D₁Map F g) := by
  intro x
  constructor
  · intro hx
    have h₁ : g x.2 = 0 := congrArg Prod.snd hx
    obtain ⟨z,hz⟩ := (he x.2).mp h₁
    exact ⟨(0,z),Prod.ext (Subsingleton.elim _ _) hz⟩
  · rintro ⟨y,rfl⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact (he _).mpr ⟨y.2,rfl⟩

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (ι : Type) [Fintype ι]

lemma D₀Free_retract : (D₀FreeProjection F ι).comp (D₀FreeInclusion F ι) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact freeTensorInv_eval F ι x.2

omit [Fintype ι] in
lemma D₁Free_retract : (D₁FreeProjection F ι).comp (D₁FreeInclusion F ι) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

lemma D₀Free_projective : Module.Projective (Alg F) (D₀Obj F (freeObj (R := R) ι)) :=
  Module.Projective.of_split (D₀FreeInclusion F ι) (D₀FreeProjection F ι) (D₀Free_retract F ι)
lemma D₁Free_projective : Module.Projective (Alg F) (D₁Obj F (freeObj (R := R) ι)) :=
  Module.Projective.of_split (D₁FreeInclusion F ι) (D₁FreeProjection F ι) (D₁Free_retract F ι)

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (L : ModuleCat R)

lemma D₀_projective [Module.Finite R L] [Module.Projective R L] :
    Module.Projective (Alg F) (D₀Obj F L) := by
  let c := finiteFreeCover (R := R) (M := L)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let : Module.Projective (Alg F) (D₀Obj F (freeObj (R := R) (Fin c.rank))) :=
    D₀Free_projective F (Fin c.rank)
  let inclusion : L ⟶ freeObj (R := R) (Fin c.rank) := ModuleCat.ofHom i
  let projection : freeObj (R := R) (Fin c.rank) ⟶ L := ModuleCat.ofHom c.map
  refine Module.Projective.of_split (D₀Map F inclusion).hom (D₀Map F projection).hom ?_
  have h : inclusion ≫ projection = 𝟙 L := ModuleCat.hom_ext hi
  have he := (D₀ F).map_comp inclusion projection
  rw [h,(D₀ F).map_id] at he
  exact (congrArg ModuleCat.Hom.hom he).symm

lemma D₁_projective [Module.Finite R L] [Module.Projective R L] :
    Module.Projective (Alg F) (D₁Obj F L) := by
  let c := finiteFreeCover (R := R) (M := L)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let : Module.Projective (Alg F) (D₁Obj F (freeObj (R := R) (Fin c.rank))) :=
    D₁Free_projective F (Fin c.rank)
  let inclusion : L ⟶ freeObj (R := R) (Fin c.rank) := ModuleCat.ofHom i
  let projection : freeObj (R := R) (Fin c.rank) ⟶ L := ModuleCat.ofHom c.map
  refine Module.Projective.of_split (D₁Map F inclusion).hom (D₁Map F projection).hom ?_
  have h : inclusion ≫ projection = 𝟙 L := ModuleCat.hom_ext hi
  have he := (D₁ F).map_comp inclusion projection
  rw [h,(D₁ F).map_id] at he
  exact (congrArg ModuleCat.Hom.hom he).symm

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

variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  (N : ModuleCat.{0} R)
include hP
lemma D₀_boundaries [Module.Finite R N] [Module.Projective R N]
    (j : ℤ) (f : D₀Obj F (P.X j) ⟶ D₀Obj F N)
    (hf : D₀Map F (P.d (j+1) j) ≫ f = 0) :
    ∃ g : D₀Obj F (P.X (j-1)) ⟶ D₀Obj F N, D₀Map F (P.d j (j-1)) ≫ g = f := by
  have h := congrArg (diagonal₀ (F := F)) hf
  rw [diagonal₀_pre,map_zero] at h
  obtain ⟨g,hg⟩ := hP.projective_boundaries j (diagonal₀ f).hom (ModuleCat.hom_ext_iff.mp h)
  refine ⟨diagonal₀.symm (ModuleCat.ofHom g),?_⟩
  apply diagonal₀.injective
  rw [diagonal₀_pre,LinearEquiv.apply_symm_apply]
  exact ModuleCat.hom_ext hg
lemma D₁_boundaries [Module.Finite R N] [Module.Projective R N]
    (j : ℤ) (f : D₁Obj F (P.X j) ⟶ D₁Obj F N)
    (hf : D₁Map F (P.d (j+1) j) ≫ f = 0) :
    ∃ g : D₁Obj F (P.X (j-1)) ⟶ D₁Obj F N, D₁Map F (P.d j (j-1)) ≫ g = f := by
  have h := congrArg (diagonal₁ (F := F)) hf
  rw [diagonal₁_pre,map_zero] at h
  obtain ⟨g,hg⟩ := hP.projective_boundaries j (diagonal₁ f).hom (ModuleCat.hom_ext_iff.mp h)
  refine ⟨diagonal₁.symm (ModuleCat.ofHom g),?_⟩
  apply diagonal₁.injective
  rw [diagonal₁_pre,LinearEquiv.apply_symm_apply]
  exact ModuleCat.hom_ext hg
lemma cross_boundaries [Module.Finite R (tensorObj F N)] [Module.Projective R (tensorObj F N)]
    (j : ℤ) (f : D₁Obj F (P.X j) ⟶ D₀Obj F N)
    (hf : D₁Map F (P.d (j+1) j) ≫ f = 0) :
    ∃ g : D₁Obj F (P.X (j-1)) ⟶ D₀Obj F N, D₁Map F (P.d j (j-1)) ≫ g = f := by
  have h := congrArg (cross₁₀ (F := F)) hf
  rw [cross₁₀_pre,map_zero] at h
  obtain ⟨g,hg⟩ := hP.projective_boundaries j (cross₁₀ f).hom (ModuleCat.hom_ext_iff.mp h)
  refine ⟨cross₁₀.symm (ModuleCat.ofHom g),?_⟩
  apply cross₁₀.injective
  rw [cross₁₀_pre,LinearEquiv.apply_symm_apply]
  exact ModuleCat.hom_ext hg

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

lemma boundary_diff {a : ℤ} (f : Cochain P Q (a-1)) : Boundary (diff f) := by
  refine ⟨fun i j he => f i j (by omega),?_⟩
  intros; rfl

lemma boundary_iff_diff {a : ℤ} (f : Cochain P Q a) :
    Boundary f ↔ ∃ h : Cochain P Q (a-1), f = diff h := by
  constructor
  · rintro ⟨h,hh⟩
    exact ⟨h,funext fun i => funext fun j => funext fun he => hh i j he⟩
  · rintro ⟨h,rfl⟩; exact boundary_diff h

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
lemma diagonal₀_post {L M N : ModuleCat.{0} R}
    (f : D₀Obj F L ⟶ D₀Obj F M) (g : M ⟶ N) :
    diagonal₀ (f ≫ D₀Map F g) = diagonal₀ f ≫ g := diagonal₀_comp F f (D₀Map F g)

variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
lemma down₀_boundary {a : ℤ} (f : Cochain (D₀Complex F P) (D₀Complex F Q) a) :
    Boundary (down₀ F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
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
lemma total (j : ℤ) : left v j ≫ inLeft v j + right v j ≫ inRight v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X v j (j-1) (rel j) <;>
    simp only [add_comp,Category.assoc,inLeft_left,inLeft_right,inRight_left,
      inRight_right,Category.comp_id,comp_zero,zero_add,add_zero,Category.id_comp]

lemma ext_element (j : ℤ) {x y : (complex v).X j}
    (hl : left v j x = left v j y) (hr : right v j x = right v j y) : x = y := by
  have hx := congrArg (fun f => f x) (total v j)
  have hy := congrArg (fun f => f y) (total v j)
  change inLeft v j (left v j x) + inRight v j (right v j x) = x at hx
  change inLeft v j (left v j y) + inRight v j (right v j y) = y at hy
  rw [hl,hr,hy] at hx
  exact hx.symm

lemma left_d (j : ℤ) (x : (complex v).X j) :
    left v (j-1) ((complex v).d j (j-1) x) = - B.d (j-1) (j-1-1) (left v j x) := by
  exact congrArg (fun f => f x)
    (HomologicalComplex.homotopyCofiber.d_fstX v j (j-1) (j-1-1) (rel j) (rel (j-1)))
lemma right_d (j : ℤ) (x : (complex v).X j) :
    right v (j-1) ((complex v).d j (j-1) x) =
      v.f (j-1) (left v j x) + A.d j (j-1) (right v j x) := by
  exact congrArg (fun f => f x)
    (HomologicalComplex.homotopyCofiber.d_sndX v j (j-1) (rel j))
lemma inRight_d (i j : ℤ) : inRight v i ≫ (complex v).d i j = A.d i j ≫ inRight v j :=
  HomologicalComplex.homotopyCofiber.inrX_d v i j

lemma exact (hA : ComplexExact A) (hB : ComplexExact B) : ComplexExact (complex v) := by
  intro j x
  constructor
  · intro hx
    have hl : B.d (j-1) (j-1-1) (left v j x) = 0 := by
      have he := left_d v j x
      rw [hx,map_zero] at he
      exact neg_eq_zero.mp he.symm
    have hex := hB (j-1)
    rw [show j-1+1=j by omega] at hex
    obtain ⟨b,hb⟩ := (hex _).mp hl
    let y : (complex v).X (j+1) :=
      HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) (-b)
    have hyl : left v j ((complex v).d (j+1) j y) = left v j x := by
      have he : HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) ≫
          (complex v).d (j+1) j ≫ left v j = -B.d j (j-1) := by
        calc
          _ = (-B.d j (j-1) ≫ inLeft v j + v.f j ≫ inRight v j) ≫ left v j :=
            (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ left v j)
              (HomologicalComplex.homotopyCofiber.inlX_d v (j+1) j (j-1) (by rfl) (rel j)))
          _ = _ := by simp only [add_comp,neg_comp,Category.assoc,inLeft_left,inRight_left,
            Category.comp_id,comp_zero,add_zero]
      have he' := congrArg (fun f => f (-b)) he
      change left v j ((complex v).d (j+1) j y) = -(B.d j (j-1) (-b)) at he'
      rw [map_neg,neg_neg] at he'
      exact he'.trans hb
    let z := x - (complex v).d (j+1) j y
    have hzl : left v j z = 0 := by simp only [z,map_sub,hyl,sub_self]
    have hzd : (complex v).d j (j-1) z = 0 := by
      rw [map_sub,hx]
      have hd := congrArg (fun f => f y) ((complex v).d_comp_d (j+1) j (j-1))
      change (complex v).d j (j-1) ((complex v).d (j+1) j y) = 0 at hd
      rw [hd,sub_self]
    have hzr : A.d j (j-1) (right v j z) = 0 := by
      have he := right_d v j z
      rw [hzd,map_zero,hzl,map_zero,zero_add] at he
      exact he.symm
    obtain ⟨a,ha⟩ := (hA j _).mp hzr
    refine ⟨y + inRight v (j+1) a,?_⟩
    rw [map_add]
    have hd := congrArg (fun f => f a) (inRight_d v (j+1) j)
    change (complex v).d (j+1) j (inRight v (j+1) a) = inRight v j (A.d (j+1) j a) at hd
    rw [hd,ha]
    have hz : inRight v j (right v j z) = z := by
      apply ext_element v j
      · exact (congrArg (fun f => f (right v j z)) (inRight_left v j)).trans hzl.symm
      · exact congrArg (fun f => f (right v j z)) (inRight_right v j)
    rw [hz]
    dsimp only [z]
    rw [add_comm,sub_add_cancel]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) ((complex v).d_comp_d (j+1) j (j-1))

private lemma boundaries {P : ChainComplex (ModuleCat.{0} R) ℤ} (hP : TotallyAcyclic P)
    (j : ℤ) (f : P.X j ⟶ ModuleCat.of R R) (hf : P.d (j+1) j ≫ f = 0) :
    ∃ g : P.X (j-1) ⟶ ModuleCat.of R R, P.d j (j-1) ≫ g = f := by
  obtain ⟨g,hg⟩ := hP.2 j f.hom (ModuleCat.hom_ext_iff.mp hf)
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩

lemma totallyAcyclic (hA : TotallyAcyclic A) (hB : TotallyAcyclic B) :
    TotallyAcyclic (complex v) := by
  refine ⟨exact v hA.1 hB.1,?_⟩
  intro j fl hfl
  let f : (complex v).X j ⟶ ModuleCat.of R R := ModuleCat.ofHom fl
  have hf : (complex v).d (j+1) j ≫ f = 0 := ModuleCat.hom_ext hfl
  have hfa : A.d (j+1) j ≫ (inRight v j ≫ f) = 0 := by
    rw [← Category.assoc,← inRight_d,Category.assoc,hf,comp_zero]
  obtain ⟨a,ha⟩ := boundaries hA j (inRight v j ≫ f) hfa
  let t := f - (complex v).d j (j-1) ≫ right v (j-1) ≫ a
  have htr : inRight v j ≫ t = 0 := by
    dsimp only [t]
    rw [comp_sub,← Category.assoc,← Category.assoc,inRight_d]
    simp only [Category.assoc]
    rw [← Category.assoc (inRight v (j-1)) (right v (j-1)) a,
      inRight_right,Category.id_comp,ha,sub_self]
  have htcy : (complex v).d (j+1) j ≫ t = 0 := by
    dsimp only [t]
    rw [comp_sub,hf,← Category.assoc,← Category.assoc,
      (complex v).d_comp_d,zero_comp,zero_comp,sub_self]
  let b := inLeft v j ≫ t
  have htb : t = left v j ≫ b := by
    calc
      t = (left v j ≫ inLeft v j + right v j ≫ inRight v j) ≫ t := by rw [total,Category.id_comp]
      _ = _ := by rw [add_comp,Category.assoc,Category.assoc,htr,comp_zero,add_zero]
  have hbcy : B.d j (j-1) ≫ b = 0 := by
    have he := congrArg (fun h => h ≫ t)
      (HomologicalComplex.homotopyCofiber.inlX_d v (j+1) j (j-1) (by rfl) (rel j))
    change (HomologicalComplex.homotopyCofiber.inlX v j (j+1) (by rfl) ≫
      (complex v).d (j+1) j) ≫ t =
      (-B.d j (j-1) ≫ inLeft v j + v.f j ≫ inRight v j) ≫ t at he
    simp only [Category.assoc,htcy,comp_zero,add_comp,neg_comp,htr,add_zero] at he
    exact neg_eq_zero.mp he.symm
  have hbound := boundaries hB (j-1)
  rw [show j-1+1=j by omega] at hbound
  obtain ⟨b',hb'⟩ := hbound b hbcy
  let g := right v (j-1) ≫ a - left v (j-1) ≫ b'
  have hg : (complex v).d j (j-1) ≫ g = f := by
    dsimp only [g]
    rw [comp_sub]
    have hd : (complex v).d j (j-1) ≫ left v (j-1) = -left v j ≫ B.d (j-1) (j-1-1) :=
      HomologicalComplex.homotopyCofiber.d_fstX v j (j-1) (j-1-1) (rel j) (rel (j-1))
    rw [← Category.assoc ( (complex v).d j (j-1)) (left v (j-1)) b',hd,
      neg_comp,Category.assoc,hb',← htb,sub_neg_eq_add]
    dsimp only [t]
    rw [add_comm,sub_add_cancel]
  exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩

lemma finite (af : ∀ j, Module.Finite R (A.X j)) (bf : ∀ j, Module.Finite R (B.X j))
    (j : ℤ) : Module.Finite R ((complex v).X j) := by
  let := af j
  let := bf (j-1)
  exact Module.Finite.equiv (termEquiv v j).symm
lemma projective (ap : ∀ j, Module.Projective R (A.X j))
    (bp : ∀ j, Module.Projective R (B.X j)) (j : ℤ) :
    Module.Projective R ((complex v).X j) := by
  let := ap j
  let := bp (j-1)
  exact Module.Projective.of_equiv (termEquiv v j).symm

end CompleteCone
end Tachikawa



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
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

end Tachikawa.DownCone



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
lemma reg_split : (regIn₀ F).comp (regOut₀ F) + (regIn₁ F).comp (regOut₁ F) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply TrivSqZeroExt.ext
  · apply Prod.ext
    · change upper F a + 0 = a.fst.1
      exact add_zero _
    · change 0 + lower F a = a.fst.2
      exact zero_add _
  · change freeTensorEval F PUnit (freeTensorInv F PUnit (fun _ => off F a)) PUnit.unit + 0 = a.snd
    rw [freeTensorEval_inv,add_zero]
    rfl

variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]
include hP in
lemma D₀_totallyAcyclic : TotallyAcyclic (D₀Complex F P) := by
  refine ⟨fun j => D₀Map_exact F _ _ (hP.1 j),?_⟩
  intro j f hf
  let f₀ : D₀Obj F (P.X j) ⟶ D₀Obj F (oneFree (R := R)) := ModuleCat.ofHom ((regOut₀ F).comp f)
  have hf₀ : D₀Map F (P.d (j+1) j) ≫ f₀ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₀ F).comp f).comp ((D₀Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  obtain ⟨g₀,hg₀⟩ := D₀_boundaries F P hP (oneFree (R := R)) j f₀ hf₀
  have hf₁ : (regOut₁ F).comp f = 0 :=
    ModuleCat.hom_ext_iff.mp (cross₀₁_zero (ModuleCat.ofHom ((regOut₁ F).comp f)))
  refine ⟨(regIn₀ F).comp g₀.hom,?_⟩
  have hg := ModuleCat.hom_ext_iff.mp hg₀
  change g₀.hom.comp ((D₀Complex F P).d j (j-1)).hom = (regOut₀ F).comp f at hg
  erw [LinearMap.comp_assoc,hg]
  have hs := congrArg (fun p : Alg F →ₗ[Alg F] Alg F => p.comp f) (reg_split F)
  rw [LinearMap.add_comp,LinearMap.comp_assoc,LinearMap.comp_assoc,hf₁,
    LinearMap.comp_zero,add_zero,LinearMap.id_comp] at hs
  exact hs

variable [FiniteDimensional k (Enveloping.Obj F)] [Module.Projective R (Enveloping.Obj F)]
include hP in
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma D₁_totallyAcyclic : TotallyAcyclic (D₁Complex F P) := by
  let N := oneFree (R := R)
  let : Module.Finite R N := inferInstanceAs (Module.Finite R (PUnit → R))
  let : Module.Projective R N := inferInstanceAs (Module.Projective R (PUnit → R))
  let : Module.Finite R (tensorObj F N) := by
    let : Module.Finite R (Enveloping.Obj F) := Module.Finite.of_restrictScalars_finite k _ _
    exact Module.Finite.equiv (freeTensorEquiv F PUnit).symm
  let : Module.Projective R (tensorObj F N) :=
    BalancedTensor.map_projective (k := k) (R := R) (S := R) (M := Enveloping.Obj F) (N := N)
  refine ⟨fun j => D₁Map_exact F _ _ (hP.1 j),?_⟩
  intro j f hf
  let f₀ : D₁Obj F (P.X j) ⟶ D₀Obj F N := ModuleCat.ofHom ((regOut₀ F).comp f)
  let f₁ : D₁Obj F (P.X j) ⟶ D₁Obj F N := ModuleCat.ofHom ((regOut₁ F).comp f)
  have hf₀ : D₁Map F (P.d (j+1) j) ≫ f₀ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₀ F).comp f).comp ((D₁Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  have hf₁ : D₁Map F (P.d (j+1) j) ≫ f₁ = 0 := by
    apply ModuleCat.hom_ext
    change ((regOut₁ F).comp f).comp ((D₁Complex F P).d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,hf,LinearMap.comp_zero]
  obtain ⟨g₀,hg₀⟩ := cross_boundaries F P hP N j f₀ hf₀
  obtain ⟨g₁,hg₁⟩ := D₁_boundaries F P hP N j f₁ hf₁
  refine ⟨(regIn₀ F).comp g₀.hom + (regIn₁ F).comp g₁.hom,?_⟩
  have hg₀ := ModuleCat.hom_ext_iff.mp hg₀
  have hg₁ := ModuleCat.hom_ext_iff.mp hg₁
  change g₀.hom.comp ((D₁Complex F P).d j (j-1)).hom = (regOut₀ F).comp f at hg₀
  change g₁.hom.comp ((D₁Complex F P).d j (j-1)).hom = (regOut₁ F).comp f at hg₁
  change (regIn₀ F).comp (g₀.hom.comp ((D₁Complex F P).d j (j-1)).hom) +
    (regIn₁ F).comp (g₁.hom.comp ((D₁Complex F P).d j (j-1)).hom) = f
  rw [hg₀,hg₁]
  exact congrArg (fun p : Alg F →ₗ[Alg F] Alg F => p.comp f) (reg_split F)

end Tachikawa.Triangular



namespace Tachikawa.DownHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  (pP : ∀ j, Module.Projective R (P.X j)) (fP : ∀ j, Module.Finite R (P.X j))
include hP pP fP in
lemma homology_subsingleton (a : ℤ)
    (hb : ∀ (f : Cochain P P a), Closed f → Boundary f) :
    Subsingleton (VectorSplit.H (completeHom (k := k) P (ModuleCat.of R (CokerAt P 0))) a) := by
  let ε : P.X 0 ⟶ ModuleCat.of R (CokerAt P 0) := ModuleCat.ofHom (CokerAt.π P 0)
  have hε : P.d 1 0 ≫ ε = 0 := by
    apply ModuleCat.hom_ext
    exact CokerAt.π_d P 0
  have he : Function.Exact (P.d 1 0) ε := fun x => Submodule.Quotient.mk_eq_zero _
  have hs : Function.Surjective ε := CokerAt.π_surjective P 0
  have hz : ∀ x : VectorSplit.H (completeHom (k := k) P (ModuleCat.of R (CokerAt P 0))) a, x=0 := by
    intro x
    obtain ⟨f,hf,hx⟩ := eval_surjective ε hε hP hP.1 pP fP pP he hs a x
    rw [← hx]
    exact eval_boundary ε hε f hf (hb f hf)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩
end Tachikawa.DownHom



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  [FiniteDimensional k R] [FiniteDimensional k F]
  [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)
  (hP : TotallyAcyclic P) (fP : ∀ j, Module.Finite R (P.X j))
  (pP : ∀ j, Module.Projective R (P.X j))
include hP in
omit [FiniteDimensional k R] in
lemma cone_totallyAcyclic : TotallyAcyclic (cone F u) := by
  let : FiniteDimensional k (Enveloping.Obj F) := inferInstanceAs (FiniteDimensional k F)
  let : Module.Finite Rᵐᵒᵖ (Enveloping.Obj F) := Module.Finite.of_restrictScalars_finite k _ _
  exact CompleteCone.totallyAcyclic _ (D₀_totallyAcyclic F P hP) (D₁_totallyAcyclic F P hP)
include fP in
omit [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma cone_finite (j : ℤ) : Module.Finite (Alg F) ((cone F u).X j) := by
  apply CompleteCone.finite
  · intro i
    let := fP i
    let : FiniteDimensional k (P.X i) := Module.Finite.trans R _
    change Module.Finite (Alg F) (D₀Obj F (P.X i))
    exact Module.Finite.of_restrictScalars_finite k _ _
  · intro i
    let := fP i
    let : FiniteDimensional k (P.X i) := Module.Finite.trans R _
    change Module.Finite (Alg F) (D₁Obj F (P.X i))
    exact Module.Finite.of_restrictScalars_finite k _ _
include fP pP in
omit [FiniteDimensional k R] [FiniteDimensional k F]
  [Module.Projective R (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma cone_projective (j : ℤ) : Module.Projective (Alg F) ((cone F u).X j) := by
  apply CompleteCone.projective
  · intro i
    let := fP i
    let := pP i
    exact D₀_projective F (P.X i)
  · intro i
    let := fP i
    let := pP i
    exact D₁_projective F (P.X i)
end Tachikawa.Triangular



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
local instance sourceF_finite_rff5ce5_1 : FiniteDimensional K (Enveloping.Obj sourceF.obj) :=
  inferInstanceAs (FiniteDimensional K sourceF)
lemma sourceCone_totallyAcyclic : TotallyAcyclic sourceCone :=
  Triangular.cone_totallyAcyclic sourceF.obj sourceU (sourceX.complete_totallyAcyclic (formE q))
lemma sourceCone_finite (j : ℤ) : Module.Finite sourceTriangle (sourceCone.X j) :=
  Triangular.cone_finite sourceF.obj sourceU (sourceX.complete_finite (formE q)) j
lemma sourceCone_projective (j : ℤ) : Module.Projective sourceTriangle (sourceCone.X j) :=
  Triangular.cone_projective sourceF.obj sourceU (sourceX.complete_finite (formE q))
    (sourceX.complete_projective (formE q)) j

lemma sourceCone_homology_zero (a : ℤ) (ha : 0<a ∨ a≤ -2) :
    Subsingleton (VectorSplit.H (completeHom (k := K) sourceCone
      (ModuleCat.of sourceTriangle (CokerAt sourceCone 0))) a) :=
  DownHom.homology_subsingleton sourceCone sourceCone_totallyAcyclic
    sourceCone_projective sourceCone_finite a (sourceCone_closed_boundary a ha)
end Tachikawa.SourceField



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
lemma ofMap_boundary {f : P ⟶ Q} (h : Homotopy f 0) : Boundary (ofMap f) := by
  let c : Cochain P Q (0-1) := fun i j _ => h.hom i j
  refine ⟨c,?_⟩
  intro i j hij
  have hi : i=j := by omega
  cases hi
  have hh := h.comm i
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i-1) by change i-1+1=i; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (i+1) i from rfl)] at hh
  simpa only [ofMap,add_zero,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp,zero_f,c] using hh
lemma ofMap_nullhomotopic (f : P ⟶ Q) (hb : Boundary (ofMap f)) : Nonempty (Homotopy f 0) := by
  obtain ⟨c,hc⟩ := hb
  classical
  let h : ∀ p q, P.X p ⟶ Q.X q :=
    fun p q => if he : q=p+1 then c p q (by omega) else 0
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    change ¬ p+1=q at hpq
    simp only [h,dite_eq_right (Ne.symm hpq)]
  · intro j
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)]
    simp only [zero_f,add_zero,h,dite_eq_left (show j=j-1+1 by omega),dite_eq_left rfl]
    have hr := hc j j (by omega)
    simpa only [ofMap,add_zero,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp] using hr
end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (hP : TotallyAcyclic P) (fP : ∀ j, Module.Finite R (P.X j))
  (pP : ∀ j, Module.Projective R (P.X j))
include fP in
lemma coker_finite : Module.Finite R (CokerAt P 0) := by
  let := fP 0
  exact Module.Finite.of_surjective (CokerAt.π P 0) (CokerAt.π_surjective P 0)
include hP fP pP k in
lemma id_boundary_of_projective (hp : Module.Projective R (CokerAt P 0)) : Boundary (ofMap (𝟙 P)) := by
  let := coker_finite P fP
  have hf : CokerAt.map (𝟙 P) 0 ∈ projectiveFactors (k := k) := by
    rw [CokerAt.map_id]
    exact id_mem_projectiveFactors_iff.mpr hp
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (𝟙 P) hP hP.1 pP fP pP hf
  exact ofMap_boundary h
include fP pP k in
lemma projective_of_id_boundary (hb : Boundary (ofMap (𝟙 P))) : Module.Projective R (CokerAt P 0) := by
  let := coker_finite P fP
  obtain ⟨h⟩ := ofMap_nullhomotopic (𝟙 P) hb
  have hf := coker_factors_of_nullhomotopic (k := k) (𝟙 P) h (fP (-1)) (pP (-1))
  rw [CokerAt.map_id] at hf
  exact id_mem_projectiveFactors_iff.mp hf
end Tachikawa.DownHom



namespace Tachikawa.Triangular
open CategoryTheory HomologicalComplex
open DownHom DownCone CompleteCone
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)
omit [CharP k 2] in
lemma low_identity : low (crossMap F u) (ofMap (𝟙 (cone F u))) = ofMap (𝟙 (D₀Complex F P)) := by
  funext i j h
  have hh : i=j := by omega
  cases hh
  simp [low,ofMap]
omit [CharP k 2] in
lemma down_identity : down₀ F 0 (ofMap (𝟙 (D₀Complex F P))) = ofMap (𝟙 P) := by
  funext i j h
  have hh : i=j := by omega
  cases hh
  change diagonal₀ (ofMap (𝟙 (D₀Complex F P)) i i _) = ofMap (𝟙 P) i i _
  simp only [ofMap,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp,id_f]
  rfl

include k in
lemma cone_id_boundary (hb : Boundary (ofMap (𝟙 (cone F u)))) : Boundary (ofMap (𝟙 P)) := by
  obtain ⟨h,hh⟩ := (boundary_iff_diff _).mp hb
  have he := congrArg (low (crossMap F u)) hh
  rw [low_diff (k := k) _ (fun _ _ f => cross₀₁_zero f),low_identity] at he
  have hB : Boundary (ofMap (𝟙 (D₀Complex F P))) := (boundary_iff_diff _).mpr ⟨_,he⟩
  have hC := (down₀_boundary F _).mpr hB
  rw [down_identity] at hC
  exact hC
end Tachikawa.Triangular



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (N : ModuleCat.{0} R)
lemma completeHom_exact_of_zero (a : ℤ)
    [Subsingleton (VectorSplit.H (completeHom (k := k) P N) a)] :
    Function.Exact (homPrecomp (k := k) (Z := N) (P.d a (a-1)).hom)
      (homPrecomp (k := k) (P.d (a+1) a).hom) := by
  intro f
  constructor
  · intro hf
    let z : VectorSplit.Z (completeHom (k := k) P N) a :=
      ⟨ModuleCat.ofHom f,(completeHom_memZ P N a _).mpr (ModuleCat.hom_ext hf)⟩
    have hz : VectorSplit.quotient _ a z = 0 := Subsingleton.elim _ _
    obtain ⟨g,hg⟩ := (VectorSplit.quotient_zero_iff_predecessor a z).mp hz
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,rfl⟩
    change (g.comp (P.d a (a-1)).hom).comp (P.d (a+1) a).hom = 0
    rw [LinearMap.comp_assoc]
    have hd : (P.d a (a-1)).hom.comp (P.d (a+1) a).hom = 0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d (a+1) a (a-1))
    rw [hd,LinearMap.comp_zero]
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (C : ChainComplex (ModuleCat.{0} R) ℤ)
lemma transfer_of_completeHom_vanishing [FiniteDimensional k R]
    (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
    (van : ∀ a : ℤ, 0<a ∨ a≤ -2 →
      Subsingleton (VectorSplit.H (completeHom (k := k) C (ModuleCat.of R (CokerAt C 0))) a))
    (n : ℕ) :
    Subsingleton (Abelian.Ext
      (ModuleCat.of (TrivialExtension k R) (TrivialInduction.Obj k R (CokerAt C 0)))
      (ModuleCat.of (TrivialExtension k R) (TrivialInduction.Obj k R (CokerAt C 0))) (n+1)) := by
  apply TrivialInduction.transfer (k := k) C hC fin proj
  · intro m
    let := van ((m+1:ℕ):ℤ) (Or.inl (by omega))
    have hx := completeHom_exact_of_zero (k := k) C
      (ModuleCat.of R (CokerAt C 0)) ((m+1:ℕ):ℤ)
    have h1 : ((m+1:ℕ):ℤ)-1 = (m:ℤ) := by omega
    have h2 : ((m+1:ℕ):ℤ)+1 = ((m+2:ℕ):ℤ) := by omega
    rw [h1,h2] at hx
    exact hx
  · intro m
    let := van (-((m+1:ℕ):ℤ)-1) (Or.inr (by omega))
    have hx := completeHom_exact_of_zero (k := k) C
      (ModuleCat.of R (CokerAt C 0)) (-((m+1:ℕ):ℤ)-1)
    have h1 : (-((m+1:ℕ):ℤ)-1)-1 = -((m+2:ℕ):ℤ)-1 := by omega
    have h2 : (-((m+1:ℕ):ℤ)-1)+1 = -(m:ℤ)-1 := by omega
    rw [h1,h2] at hx
    exact hx
end Tachikawa



namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra
instance sourceConeModule_finite : Module.Finite sourceTriangle sourceConeModule :=
  DownHom.coker_finite sourceCone sourceCone_finite
instance sourceConeModule_finiteK : FiniteDimensional K sourceConeModule :=
  Module.Finite.trans sourceTriangle _
lemma sourceConeModule_nonprojective : ¬ Module.Projective sourceTriangle sourceConeModule := by
  intro hp
  have hb := DownHom.id_boundary_of_projective (k := K) sourceCone sourceCone_totallyAcyclic
    sourceCone_finite sourceCone_projective hp
  have hX := Triangular.cone_id_boundary sourceF.obj sourceU hb
  let := DownHom.projective_of_id_boundary (k := K) sourceP
    (sourceX.complete_finite (formE q)) (sourceX.complete_projective (formE q)) hX
  have h := Module.Projective.of_equiv (sourceX.cokerEquiv (formE q))
  exact X_nonprojective q (parameter_ne_zero 0) one_add_q_pow_ne_zero h

instance sourceModule_finite : FiniteDimensional K sourceModule := inferInstanceAs
  (FiniteDimensional K (TrivialInduction.Obj K sourceTriangle sourceConeModule))
lemma sourceModule_nonprojective : ¬ Module.Projective sourceAlgebra sourceModule := by
  intro hp
  let := hp
  exact sourceConeModule_nonprojective
    (TrivialInduction.projective_of_inducedProjective (k := K) (R := sourceTriangle) (M := sourceConeModule))

lemma sourceModule_ext (n : ℕ) :
    Subsingleton (Abelian.Ext (ModuleCat.of sourceAlgebra sourceModule)
      (ModuleCat.of sourceAlgebra sourceModule) (n+1)) :=
  transfer_of_completeHom_vanishing (k := K) sourceCone sourceCone_totallyAcyclic
    sourceCone_finite sourceCone_projective sourceCone_homology_zero n
end Tachikawa.SourceField



namespace Tachikawa.SourceField
lemma sourceAlgebra_symmetric : SymmetricOver K sourceAlgebra :=
  TrivialExtension.symmetricOver
end Tachikawa.SourceField



namespace Tachikawa

theorem main_theorem_oai : Counterexample :=
  counterexampleOf SourceField.sourceAlgebra SourceField.sourceModule
    SourceField.sourceAlgebra_symmetric SourceField.sourceModule_nonprojective
    SourceField.sourceModule_ext
end Tachikawa

end

end OAI
end

theorem solution : type_of% @OAI.Tachikawa.main_theorem_oai := @OAI.Tachikawa.main_theorem_oai
