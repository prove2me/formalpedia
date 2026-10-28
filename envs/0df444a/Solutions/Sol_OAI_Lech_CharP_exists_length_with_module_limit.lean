-- Prove2me | solution 1 for OAI.Lech.CharP.exists_length_with_module_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:19:25.126395+00:00
-- url     : https://prove2.me/submissions/eb273c67-a08b-48a6-8e67-7775e5cf7c64

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_Normalization_parameter_frobenius_multiplicity_enn
import Theorems.Thm_OAI_Lech_Normalization_parameter_multiplicity_pos
import Theorems.Thm_OAI_Lech_SeparableOrder_exists_normalization_frobenius_module_limit
import Theorems.Thm_OAI_Lech_SeparableOrder_normalizedLength_coordinate_power_koszul

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
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
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
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

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


namespace Lech.Normalization
variable {R S : Type*} [CommRing R] [CommRing S]

 
lemma dimension_le_of_integral (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro p q hpq
  exact Ideal.IsIntegral.comap_lt_comap hpq

 
lemma injective_of_integral_dimension [IsDomain R] (f : R →+* S) (hf : f.IsIntegral)
    {h : ℕ} (hS : (h : WithBot ℕ∞) ≤ ringKrullDim S) (hR : ringKrullDim R ≤ h) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro r hr
  by_contra hn
  have hd := dimension_le_of_integral f.kerLift hf.kerLift
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hh : (h : WithBot ℕ∞) + 1 ≤ h :=
    (add_le_add (hS.trans hd) le_rfl).trans (hdrop.trans hR)
  norm_cast at hh
  omega

end Lech.Normalization


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))

 

theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top


end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
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


namespace Lech
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

end Lech

open scoped BigOperators
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

lemma tensor_terms_free (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : ∀ i, Module.Free R (F.X i)) : ∀ i, Module.Free R ((tensor zs F).X i) := by
  induction zs with
  | nil => exact hF
  | cons a zs ih =>
    intro i
    let := ih (i+1)
    let := ih i
    exact Module.Free.of_equiv (coneTermEquiv (tensor zs F) a i).symm

lemma tensor_terms_finite (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : ∀ i, Module.Finite R (F.X i)) : ∀ i, Module.Finite R ((tensor zs F).X i) := by
  induction zs with
  | nil => exact hF
  | cons a zs ih =>
    intro i
    let := ih (i+1)
    let := ih i
    exact Module.Finite.equiv (coneTermEquiv (tensor zs F) a i).symm

lemma unit_terms_free (zs : List R) (i : ℤ) : Module.Free R ((unit zs).X i) := by
  apply tensor_terms_free
  intro j
  by_cases hj : j = 0
  · subst j
    exact Module.Free.of_equiv
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).symm.toLinearEquiv)
  · let : Subsingleton (((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).X j) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj)
    infer_instance

lemma unit_terms_finite (zs : List R) (i : ℤ) : Module.Finite R ((unit zs).X i) := by
  apply tensor_terms_finite
  intro j
  by_cases hj : j = 0
  · subst j
    exact Module.Finite.equiv
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).symm.toLinearEquiv)
  · let : Subsingleton (((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).X j) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj)
    infer_instance


lemma entryIdeal_le_nullScalarIdeal (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : entryIdeal zs ≤ nullScalarIdeal (tensor zs F) := by
  apply Ideal.span_le.mpr
  exact fun a ha => tensor_entry_nullhomotopic zs F a ha

lemma unit_nullhomotopic_of_mem (zs : List R) (a : R) (ha : a ∈ entryIdeal zs) :
    Nonempty (Homotopy (a • 𝟙 (unit zs)) 0) :=
  entryIdeal_le_nullScalarIdeal zs _ ha
end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SeparableOrderNormalizedLength
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.SeparableOrder
open Lech.PerfectDomainStages Lech.RootTower Lech.Koszul CategoryTheory CategoryTheory.Limits CochainComplex
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
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
 

theorem normalizedLength_parameter_koszul (ys : List D) (hlen : ys.length = h)
    (hys : (entryIdeal ys).radical = IsLocalRing.maximalIdeal D) (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
        (PerfectClosure D p))).obj ((unit (ys.map (PerfectClosure.of D p))).homology i)) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let f := algebraMap A D
  let Q := entryIdeal ys
  let I := (IsLocalRing.maximalIdeal A).map f
  have hIQ : I ≤ Q.radical := by
    rw [hys]
    exact IsLocalRing.map_maximalIdeal_le f
  obtain ⟨t,ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIQ
    (Ideal.FG.map (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)) f)
  let a := t+1
  have ha : a ≠ 0 := Nat.succ_ne_zero t
  have hp : I^a ≤ Q := (Ideal.pow_le_pow_right (Nat.le_add_right t 1)).trans ht
  let zsA : List A := List.ofFn fun j : Fin h => (MvPowerSeries.X j : A)^a
  let zsP : List P := (zsA.map (PerfectClosure.of A p)).reverse
  let zsC : List C := zsP.map (algebraMap P C)
  let F := unit (ys.map (PerfectClosure.of D p))
  let T := regularTower (Fin h) k p
  let ell : Lech.TorsionLength (⊥ : Ideal C) := T.torsionLength (algebraMap P C) ⊥
  have hzlen : zsC.length = h := by simp [zsC,zsP,zsA]
  have hK (j : ℤ) (hj : j < 0) : ell.zeroClass ((unit zsC).homology j) := by
    refine ⟨⟨1, by simp⟩,?_⟩
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((unit zsC).homology j)) = 0
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((tensor (zsP.map (algebraMap P C)) ((single (ModuleCat C) (.up ℤ) 0).obj
        (ModuleCat.of C C))).homology j)) = 0
    rw [T.length_eq_of_equiv
      (restrictScalarsSingleTensorHomologyIso (algebraMap P C) zsP (ModuleCat.of C C) j).toLinearEquiv]
    exact normalizedLength_coordinate_power_koszul h k D p K L a ha j hj
  have hnull (b : C) (hb : b ∈ zsC) : Nonempty (Homotopy (b • 𝟙 F) 0) := by
    apply unit_nullhomotopic_of_mem
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    change w ∈ (zsA.map (PerfectClosure.of A p)).reverse at hw
    have hw' : w ∈ zsA.map (PerfectClosure.of A p) := by simpa only [List.mem_reverse] using hw
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp hw'
    subst w
    change v ∈ List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a) at hv
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hv
    subst v
    have hm : (MvPowerSeries.X j : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [Lech.PowerSeries.maximalIdeal_eq_variables]
      exact Ideal.subset_span ⟨j,rfl⟩
    have hq : f (MvPowerSeries.X j)^a ∈ Q := hp
      (Ideal.pow_mem_pow (Ideal.mem_map_of_mem f hm) a)
    have hmap : algebraMap P C (PerfectClosure.of A p ((MvPowerSeries.X j : A)^a)) =
        PerfectClosure.of D p (f (MvPowerSeries.X j)^a) := by
      change perfectMap p f (PerfectClosure.of A p _) = _
      rw [perfectMap_of,map_pow]
    rw [hmap]
    have hspan : Q.map (PerfectClosure.of D p) = entryIdeal (ys.map (PerfectClosure.of D p)) := by
      dsimp only [Q]
      rw [entryIdeal,Ideal.map_span]
      congr 1
      ext z
      simp only [Set.mem_image,Set.mem_ofPred_eq,List.mem_map]
    rw [← hspan]
    exact Ideal.mem_map_of_mem _ hq
  have hh := Lech.acyclicity_of_koszul ell.zeroClass zsC F
    (unit_terms_free _) (unit_terms_finite _) (fun j hj => ?_) hnull hK i hi
  · exact hh.2
  · apply unit_bounded
    simpa only [F,List.length_map,hlen,hzlen] using hj
end Lech.SeparableOrder


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_maximal_pow_le (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, (IsLocalRing.maximalIdeal R) ^ a ≤ I := by
  simpa only [hI] using I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing

lemma length_ne_top (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (a * N)) hle

end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech.Normalization
open IsLocalRing
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [Algebra k D]

lemma finite_primary_quotient (I : Ideal D) (hI : I.radical = maximalIdeal D)
    (hres : Function.Surjective (algebraMap k (ResidueField D))) : Module.Finite k (D ⧸ I) := by
  let : IsArtinianRing (D ⧸ I) := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I
    rw [← Ideal.radical_minimalPrimes,hI,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  let : IsArtinian D (D ⧸ I) := isArtinian_of_surjective_algebraMap (R := D ⧸ I) (M := D ⧸ I)
    (S := D) Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (algebraMap (ResidueField k) (ResidueField D)) := by
    intro y
    obtain ⟨x,hx⟩ := hres y
    exact ⟨residue k x,hx⟩
  have hl : Module.length k (D ⧸ I) = Module.length D (D ⧸ I) := by
    rw [IsLocalRing.length_restrictScalars k D (D ⧸ I),Module.length_eq_of_surjective hs]
    simp
  have hfin : IsFiniteLength k (D ⧸ I) := Module.length_ne_top_iff.mp (by
    rw [hl]; exact Module.length_ne_top)
  let : IsNoetherian k (D ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  infer_instance

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
 

theorem finite_parameter_algebra
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    let : Algebra (MvPowerSeries σ k) D :=
      (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).toAlgebra
    Module.Finite (MvPowerSeries σ k) D := by
  let A := MvPowerSeries σ k
  let I := Lech.PowerSeries.variablesIdeal σ k
  let J : Ideal D := Ideal.span (Set.range z)
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra k D := φ.toAlgebra
  let : Algebra A D := ψ.toAlgebra
  let : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Lech.PowerSeries.eval_C φ (maximalIdeal D) z hz a).symm)
  have hmap : I.map (algebraMap A D) = J := by
    change (Ideal.span (Set.range (X : σ → A))).map (algebraMap A D) = J
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    exact congrArg Set.range (funext (fun i => Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i))
  have hJ : J ≤ maximalIdeal D := Ideal.span_le.mpr (Set.range_subset_iff.mpr hz)
  let : IsHausdorff I D := IsHausdorff.of_map (I := I) (J := maximalIdeal D) (by rw [hmap]; exact hJ)
  let : IsPrecomplete I A := (Lech.PowerSeries.complete_variables σ k).toIsPrecomplete
  let : Module.Finite k (D ⧸ J) := finite_primary_quotient J hprim hφ
  let : Module.Finite A (D ⧸ J) := Module.Finite.of_restrictScalars_finite k A (D ⧸ J)
  have hsub : I • (⊤ : Submodule A D) = J.restrictScalars A := by
    rw [← hmap]
    symm
    simpa only [smul_eq_mul,Ideal.mul_top,Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule D D)
  let e := (Submodule.quotEquivOfEq _ _ hsub).trans (Submodule.Quotient.restrictScalarsEquiv A J)
  let : Module.Finite A (D ⧸ (I • (⊤ : Submodule A D))) := Module.Finite.equiv e.symm
  exact Lech.AdicNakayama.finite_of_quotient I

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

 
lemma exists_parameters : ∃ (n : ℕ) (z : Fin n → R),
    (∀ i, z i ∈ maximalIdeal R) ∧
    (Ideal.span (Set.range z)).radical = maximalIdeal R ∧
    ringKrullDim R = n := by
  classical
  obtain ⟨s,hs,hcard⟩ := (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing
  let e := s.equivFin
  let z : Fin s.card → R := fun i => (e.symm i : R)
  have hrange : Set.range z = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i,rfl⟩
      exact (e.symm i).2
    · intro hr
      exact ⟨e ⟨r,hr⟩,by simp [z]⟩
  refine ⟨s.card,z,?_,?_,?_⟩
  · intro i
    exact hs.le (Ideal.subset_span (by rw [← hrange]; exact Set.mem_range_self i))
  · rw [hrange,← Ideal.sInf_minimalPrimes]
    apply le_antisymm (sInf_le hs)
    apply le_sInf
    intro Q hQ
    let : Q.IsPrime := hQ.isPrime
    exact hs.2 hQ.1 (le_maximalIdeal_of_isPrime Q)
  · rw [← maximalIdeal_height_eq_ringKrullDim,← hcard]
    rfl
end Lech.Normalization


namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p]


variable [IsAdicComplete I R]



lemma sectionMap_mod (n : ℕ) (x : R ⧸ I) :
    Ideal.Quotient.mk (I^(p^n)) (sectionMap R I p x) = stage R I p n x :=
  IsAdicComplete.StrictMono.mk_liftRingHom _ _ _ _ x

 
theorem sectionMap_rightInverse : Function.RightInverse (sectionMap R I p) (Ideal.Quotient.mk I) := by
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := sectionMap_mod R I p 0 (Ideal.Quotient.mk I a)
  have h0 := stage_pow_mk R I p 0 a
  apply Ideal.Quotient.eq.mpr
  have hh := Ideal.Quotient.eq.mp (h.trans (by simpa only [pow_zero,pow_one] using h0))
  simpa only [pow_zero,pow_one] using hh

end Lech.CoefficientField
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CoefficientFieldLocalSection
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]
  [PerfectRing (IsLocalRing.ResidueField R) p]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]



lemma localSection_rightInverse :
    Function.RightInverse (localSection R p) (IsLocalRing.residue R) := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk _) p (Nat.Prime.ne_zero Fact.out)
  let : PerfectRing (R ⧸ IsLocalRing.maximalIdeal R) p :=
    inferInstanceAs (PerfectRing (IsLocalRing.ResidueField R) p)
  exact sectionMap_rightInverse R (IsLocalRing.maximalIdeal R) p

end Lech.CoefficientField


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
lemma parameter_eval_finite (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).Finite :=
  finite_parameter_algebra φ hφ z hz hprim

include hφ in
lemma parameter_eval_injective (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (hdim : (Fintype.card σ : WithBot ℕ∞) ≤ ringKrullDim D) :
    Function.Injective (Lech.PowerSeries.eval φ (maximalIdeal D) z hz) := by
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra (MvPowerSeries σ k) D := ψ.toAlgebra
  let : Module.Finite (MvPowerSeries σ k) D := finite_parameter_algebra φ hφ z hz hprim
  exact injective_of_integral_dimension ψ (Algebra.IsIntegral.isIntegral)
    hdim (Lech.PowerSeries.dimension_le_variables σ k)

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable (D : Type*) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

include p in
 

theorem exists_finite_powerSeries_normalization :
    ∃ (n : ℕ) (ψ : MvPowerSeries (Fin n) (ResidueField D) →+* D),
      Function.Injective ψ ∧ ψ.Finite ∧ IsLocalHom ψ ∧
      Function.Surjective ((residue D).comp ψ) ∧ ringKrullDim D = n := by
  obtain ⟨n,z,hz,hprim,hdim⟩ := exists_parameters D
  let φ := Lech.CoefficientField.localSection D p
  have hφ : Function.Surjective ((residue D).comp φ) :=
    fun a => ⟨a,Lech.CoefficientField.localSection_rightInverse D p a⟩
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  have hfin : ψ.Finite := parameter_eval_finite φ hφ z hz hprim
  have hinj : Function.Injective ψ := parameter_eval_injective φ hφ z hz hprim (by
    simpa only [Fintype.card_fin,hdim] using (le_refl (n : WithBot ℕ∞)))
  have hint : ψ.IsIntegral := by
    let : Algebra (MvPowerSeries (Fin n) (ResidueField D)) D := ψ.toAlgebra
    let : Module.Finite (MvPowerSeries (Fin n) (ResidueField D)) D := hfin
    exact Algebra.IsIntegral.isIntegral
  refine ⟨n,ψ,hinj,hfin,hint.isLocalHom hinj,?_,hdim⟩
  intro a
  refine ⟨C a,?_⟩
  change residue D (Lech.PowerSeries.eval φ (maximalIdeal D) z hz (C a)) = a
  rw [Lech.PowerSeries.eval_C]
  exact Lech.CoefficientField.localSection_rightInverse D p a

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing Filter
open scoped Topology ENNReal
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

omit [Field k] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] in
lemma radical_span_powers {ι : Type*} (z : ι → D) (q : ℕ) (hq : q ≠ 0) :
    (Ideal.span (Set.range fun i => z i^q)).radical =
      (Ideal.span (Set.range z)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) q (Nat.pos_of_ne_zero hq)
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨q,Ideal.subset_span ⟨i,rfl⟩⟩

end Lech.Normalization


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_QuotientExtension
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace Lech
universe u
variable {D C : Type u} [CommRing D] [CommRing C]

lemma finiteLength_primary_quotient [IsNoetherianRing D] [IsLocalRing D]
    (I : Ideal D) (hI : I.radical = IsLocalRing.maximalIdeal D) : IsFiniteLength D (D ⧸ I) := by
  apply Module.length_ne_top_iff.mp
  have h := Lech.Primary.length_ne_top I hI 1
  rw [pow_one] at h
  exact h
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CharPModuleLength
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Lech.CharP
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

theorem exists_length_with_module_limit_oai (hh : 0 < Lech.dimension D) :
    ∃ ell : Lech.AllModuleLength (PerfectClosure D p),
      (∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
          atTop (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M)))) ∧
      (∀ (H : Ideal D), H.radical = maximalIdeal D →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
          atTop (𝓝 (ell.value (ModuleCat.of (PerfectClosure D p)
            ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))))) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
        ∀ a : ℕ, 0 < a →
          ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
            (parameterIdeal D z a).map (PerfectClosure.of D p))) =
              (a : ℝ≥0∞)^(Lech.dimension D) *
                ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) ∧
      (∀ (ys : List D), ys.length = Lech.dimension D →
        (entryIdeal ys).radical = maximalIdeal D → ∀ i : ℤ, i < 0 →
          ell.value ((unit (ys.map (PerfectClosure.of D p))).homology i) = 0) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
          0 < Lech.Primary.multiplicity (Ideal.span (Set.range z))) := by
  obtain ⟨h,ψ,hψ,hfin,hloc,hres,hd⟩ :=
    Lech.Normalization.exists_finite_powerSeries_normalization D p
  have hdim : Lech.dimension D = h := by
    have hd' := Lech.dimension_cast D
    rw [hd] at hd'
    exact_mod_cast hd'
  let k := ResidueField D
  let : CharP k p := CharP.of_ringHom_of_ne_zero (residue D) p
    (Nat.Prime.ne_zero Fact.out)
  let A := MvPowerSeries (Fin h) k
  let C := PerfectClosure D p
  let P := PerfectClosure A p
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := hfin
  let : IsLocalHom (algebraMap A D) := hloc
  have hf : Function.Injective (algebraMap A D) := hψ
  have hres' : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hres b
    refine ⟨residue A a,?_⟩
    rw [ResidueField.algebraMap_residue]
    exact ha
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hf
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := Module.Finite.of_isLocalization A D A⁰
  obtain ⟨r,hr,hlimmod⟩ :=
    Lech.SeparableOrder.exists_normalization_frobenius_module_limit h k D p K L hf hres'
  have hlim (H : Ideal D) (hH : H.radical = maximalIdeal D) :
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
          ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
    have ht := hlimmod (ModuleCat.of D (D ⧸ H)) (Lech.finiteLength_primary_quotient H hH)
    have heq := (regularTower (Fin h) k p).length_eq_of_equiv
      ((ModuleCat.restrictScalars (algebraMap P C)).mapIso
        (Lech.quotientExtensionEquiv (PerfectClosure.of D p) H).toModuleIso).toLinearEquiv
    change normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] (D ⧸ H)) =
      normalizedLength (Fin h) k p ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)) at heq
    rw [heq] at ht
    apply ht.congr
    intro n
    congr 1
    exact congrArg ENat.toENNReal (Lech.quotientExtensionEquiv (iterateFrobenius D p n) H).length_eq
  let ell := (regularTower (Fin h) k p).allModuleLength (algebraMap P C) r
    (by exact_mod_cast (Nat.ne_of_gt hr))
  let φ := Lech.CoefficientField.localSection D p
  have hφ : Function.Surjective ((residue D).comp φ) :=
    fun a => ⟨a,Lech.CoefficientField.localSection_rightInverse D p a⟩
  refine ⟨ell,?_,?_,?_,?_,?_⟩
  · intro M hM
    rw [hdim]
    exact hlimmod M hM
  · intro H hH
    rw [hdim]
    exact hlim H hH
  · intro z hz a ha
    have hprim : (parameterIdeal D z a).radical = maximalIdeal D :=
      (Lech.Normalization.radical_span_powers z a (Nat.ne_of_gt ha)).trans hz
    have ht := hlim (parameterIdeal D z a) hprim
    have hp := Lech.Normalization.parameter_frobenius_multiplicity_enn
      (Lech.dimension D) hh rfl φ hφ z hz a ha p
    have hp' : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (D ⧸ (parameterIdeal D z a).map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 ((a : ℝ≥0∞)^(Lech.dimension D) *
          ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      ext n
      apply congrArg (fun b : ℝ≥0∞ => b *
        (Module.length D (D ⧸ (parameterIdeal D z a).map (iterateFrobenius D p n))).toENNReal)
      rw [hdim]
    exact tendsto_nhds_unique ht hp'
  · intro ys hlen hys i hi
    have hz := Lech.SeparableOrder.normalizedLength_parameter_koszul
      h k D p K L ys (hlen.trans hdim) hys i hi
    change (r : ℝ≥0∞) * _ = 0
    change (regularTower (Fin h) k p).length _ = 0 at hz
    rw [hz,mul_zero]
  · intro z hz
    exact Lech.Normalization.parameter_multiplicity_pos
      (Lech.dimension D) hh rfl φ hφ z hz
end Lech.CharP

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.CharP.exists_length_with_module_limit_oai.{u} := @OAI.Lech.CharP.exists_length_with_module_limit_oai.{u}
