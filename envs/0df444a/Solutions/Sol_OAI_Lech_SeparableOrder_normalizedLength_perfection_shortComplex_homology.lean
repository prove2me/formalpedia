-- Prove2me | solution 1 for OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:32:22.073619+00:00
-- url     : https://prove2.me/submissions/aa555b83-b434-4488-be31-89b419ecbf2a

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_SeparableOrder_normalizedLength_coordinate_power_koszul
import Theorems.Thm_OAI_Lech_shortComplex_nullScalar_radical

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedThickeningNat
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
-- module Solutions.OAIQ032_LECH.Multiplicity_SignedCechBicRow
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.instAdditiveCochainComplexIntTensorFunctor_1 _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.Koszul.tensorFunctor_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable {A B C : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
  [CommRing C] [IsReduced C] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]

omit [IsReduced A] [IsReduced B] in
lemma perfectMap_of (f : A →+* B) (a : A) :
    perfectMap p f (PerfectClosure.of A p a) = PerfectClosure.of B p (f a) :=
  PerfectRing.lift_comp_apply _ _ _ _

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct

lemma finite_extendScalars {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance


instance finite_frobeniusModule (D : Type*) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (n : ℕ) (M : ModuleCat D) [Module.Finite D M] :
    Module.Finite D (FrobeniusModule D p n M) :=
  finite_extendScalars (iterateFrobenius D p n) M
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
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


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]



lemma shortComplex_uniform_nullhomotopy [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    ∃ a : ℕ, 0 < a ∧ (IsLocalRing.maximalIdeal R)^a ≤ Koszul.nullScalarIdeal F := by
  obtain ⟨a,ha⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (shortComplex_nullScalar_radical F hF)
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  exact ⟨a+1,by omega,(Ideal.pow_le_pow_right (Nat.le_succ a)).trans ha⟩

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.Free S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free S (S ⊗[R] M)
  infer_instance

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectionAcyclicity
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

include K L in
lemma normalizedLength_perfection_shortComplex_homology_oai
    (hdim : dimension D = h) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
        (PerfectClosure D p))).obj
        ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj F).homology i)) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let E := (ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex (.up ℤ)
  let G := E.obj F
  let T := regularTower (Fin h) k p
  let ell : Lech.TorsionLength (⊥ : Ideal C) := T.torsionLength (algebraMap P C) ⊥
  obtain ⟨a,ha,hn⟩ := shortComplex_uniform_nullhomotopy F hF
  let zsA : List A := List.ofFn fun j : Fin h => (MvPowerSeries.X j : A)^a
  let zsP : List P := (zsA.map (PerfectClosure.of A p)).reverse
  let zsC : List C := zsP.map (algebraMap P C)
  have hzlen : zsC.length = h := by simp [zsC,zsP,zsA]
  have hK (j : ℤ) (hj : j < 0) : ell.zeroClass ((unit zsC).homology j) := by
    refine ⟨⟨1,by simp⟩,?_⟩
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((tensor (zsP.map (algebraMap P C)) ((single (ModuleCat C) (.up ℤ) 0).obj
        (ModuleCat.of C C))).homology j)) = 0
    rw [T.length_eq_of_equiv
      (restrictScalarsSingleTensorHomologyIso (algebraMap P C) zsP (ModuleCat.of C C) j).toLinearEquiv]
    exact normalizedLength_coordinate_power_koszul h k D p K L a (Nat.ne_of_gt ha) j hj
  have hnull (b : C) (hb : b ∈ zsC) : Nonempty (Homotopy (b • 𝟙 G) 0) := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    have hw' : w ∈ zsA.map (PerfectClosure.of A p) := by simpa only [zsP,List.mem_reverse] using hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw'
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    have hm : algebraMap A D (MvPowerSeries.X j) ∈ IsLocalRing.maximalIdeal D :=
      IsLocalRing.map_maximalIdeal_le (algebraMap A D) (Ideal.mem_map_of_mem _ (by
        rw [Lech.PowerSeries.maximalIdeal_eq_variables]
        exact Ideal.subset_span ⟨j,rfl⟩))
    have hnx := hn (Ideal.pow_mem_pow hm a)
    have he : algebraMap P C (PerfectClosure.of A p ((MvPowerSeries.X j : A)^a)) =
        PerfectClosure.of D p ((algebraMap A D (MvPowerSeries.X j))^a) := by
      change perfectMap p (algebraMap A D) (PerfectClosure.of A p _) = _
      rw [perfectMap_of,map_pow]
    rw [he]
    exact ⟨extendScalars_nullhomotopy (PerfectClosure.of D p) F _ hnx.some⟩
  have hh := acyclicity_of_koszul ell.zeroClass zsC G
    (fun j => by have := hF.term_free j; exact free_extendScalars (PerfectClosure.of D p) (F.X j))
    (fun j => by have := hF.term_finite j; exact finite_extendScalars (PerfectClosure.of D p) (F.X j))
    (fun j hj => (ModuleCat.extendScalars (PerfectClosure.of D p)).map_isZero
      (hF.bounded j (by simpa only [hzlen,hdim] using hj))) hnull hK i hi
  exact hh.2
end Lech.SeparableOrder

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology_oai.{u} := @OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology_oai.{u}
