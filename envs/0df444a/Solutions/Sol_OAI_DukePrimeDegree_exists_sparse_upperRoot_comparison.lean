-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:56.882975+00:00
-- url     : https://prove2.me/submissions/bba06534-c1eb-4eb5-a026-156d416a4b82

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_DukePrimeDegree_exists_lastActiveObservation_entropy_budget

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CountableOrbitSection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable section from a countable separated cover

The finite-neighbor relation in the application consists of the first
few forward and backward iterates. Removing earlier neighbors leaves a
separated section meeting every orbit in the cover. This construction
requires no ergodicity of the selected diagonal map.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

/-- The elementary marker construction, with orbit equivalence separated
from the finite-neighbor relation. -/
theorem exists_measurable_orbit_section
    {Y : Type*} [MeasurableSpace Y] (E : Setoid Y)
    (R : Y → Y → Prop) (hRsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hRE : ∀ x y, R x y → E.r x y)
    (C : ℕ → Set Y) (hC : ∀ n, MeasurableSet (C n))
    (hRC : ∀ n, MeasurableSet {x | ∃ y ∈ C n, R x y})
    (hsep : ∀ n, ∀ x ∈ C n, ∀ y ∈ C n, R x y → x=y) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ ⋃ n, C n ∧
      (∀ x ∈ S, ∀ y ∈ S, R x y → x=y) ∧
      ∀ x ∈ ⋃ n, C n, ∃ y ∈ S, E.r x y := by
  classical
  let B (n : ℕ) : Set Y := C n \ ⋃ i : Fin n, {x | ∃ y ∈ C i.val, R x y}
  let S := ⋃ n, B n
  have hB (n : ℕ) : MeasurableSet (B n) :=
    (hC n).diff (MeasurableSet.iUnion fun i => hRC i.val)
  have hSC : S ⊆ ⋃ n, C n := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n,hn.1⟩
  refine ⟨S,MeasurableSet.iUnion hB,hSC,?_,?_⟩
  · intro x hx y hy hxy
    obtain ⟨n,hxn,hxearly⟩ := mem_iUnion.mp hx
    obtain ⟨m,hym,hyearly⟩ := mem_iUnion.mp hy
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · exact (hyearly (mem_iUnion.mpr ⟨⟨n,hnm⟩,x,hxn,hRsymm hxy⟩)).elim
    · exact hsep n x hxn y hym hxy
    · exact (hxearly (mem_iUnion.mpr ⟨⟨m,hmn⟩,y,hym,hxy⟩)).elim
  · have hmeet : ∀ n, ∀ x ∈ C n, ∃ y ∈ S, E.r x y := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro x hx
        by_cases hxb : x ∈ B n
        · exact ⟨x,mem_iUnion.mpr ⟨n,hxb⟩,E.refl x⟩
        · have hnear : x ∈ ⋃ i : Fin n, {x | ∃ y ∈ C i.val, R x y} := by
            by_contra hn
            exact hxb ⟨hx,hn⟩
          obtain ⟨i,y,hy,hxy⟩ := mem_iUnion.mp hnear
          obtain ⟨z,hz,hyz⟩ := ih i.val i.isLt y hy
          exact ⟨z,hz,E.trans (hRE x y hxy) hyz⟩
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact hmeet n x hn

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SeparatedOrbitCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable separated covers for the diagonal-map section construction -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

section Topology
variable {Y : Type*} [TopologicalSpace Y]

lemma finiteOrbitNeighbor_symm (e : Y ≃ₜ Y) (N : ℕ) :
    ∀ ⦃x y⦄, finiteOrbitNeighbor e N x y → finiteOrbitNeighbor e N y x := by
  intro x y h
  rcases h with h | ⟨k,h | h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨k,Or.inr h⟩
  · exact Or.inr ⟨k,Or.inl h⟩

lemma finiteOrbitNeighbor_orbit (e : Y ≃ₜ Y) (N : ℕ) (x y : Y)
    (h : finiteOrbitNeighbor e N x y) : (homeomorphOrbitSetoid e).r x y := by
  rcases h with rfl | ⟨k,h | h⟩
  · exact (homeomorphOrbitSetoid e).refl x
  · exact ⟨(k.val+1:ℕ),by simpa only [zpow_natCast] using h⟩
  · apply (homeomorphOrbitSetoid e).symm
    exact ⟨(k.val+1:ℕ),by simpa only [zpow_natCast] using h⟩

lemma exists_open_finite_orbit_separated [T2Space Y] (e : Y ≃ₜ Y) (N : ℕ) (x : Y)
    (hfree : ∀ k : Fin N, (e^(k.val+1)) x ≠ x) :
    ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, finiteOrbitNeighbor e N y z → y=z := by
  classical
  have hchoice (k : Fin N) := t2_separation (hfree k).symm
  choose U V hU hV hxU hxV hdis using hchoice
  let W := ⋂ k : Fin N, U k ∩ (e^(k.val+1)) ⁻¹' V k
  refine ⟨W,isOpen_iInter_of_finite (fun k =>
    (hU k).inter ((hV k).preimage (e^(k.val+1)).continuous)),?_,?_⟩
  · exact mem_iInter.mpr fun k => ⟨hxU k,hxV k⟩
  · intro y hy z hz h
    rcases h with h | ⟨k,h | h⟩
    · exact h
    · have hyk := mem_iInter.mp hy k
      have hzk := mem_iInter.mp hz k
      exact (Set.disjoint_left.mp (hdis k) hzk.1 (h ▸ hyk.2)).elim
    · have hyk := mem_iInter.mp hy k
      have hzk := mem_iInter.mp hz k
      exact (Set.disjoint_left.mp (hdis k) hyk.1 (h ▸ hzk.2)).elim

end Topology

section Measurable
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] in
lemma measurableSet_finiteOrbitNeighbor (e : Y ≃ₜ Y) (N : ℕ)
    {C : Set Y} (hC : MeasurableSet C) :
    MeasurableSet {x | ∃ y ∈ C, finiteOrbitNeighbor e N x y} := by
  have he : {x | ∃ y ∈ C, finiteOrbitNeighbor e N x y} =
      C ∪ ⋃ k : Fin N, ((e^(k.val+1)) ⁻¹' C ∪ (e^(k.val+1)) '' C) := by
    ext x
    constructor
    · rintro ⟨y,hy,h | ⟨k,h | h⟩⟩
      · exact Or.inl (h.symm ▸ hy)
      · exact Or.inr (mem_iUnion.mpr ⟨k,Or.inl (show (e^(k.val+1)) x ∈ C from h.symm ▸ hy)⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨k,Or.inr ⟨y,hy,h⟩⟩)
    · rintro (hx | hx)
      · exact ⟨x,hx,Or.inl rfl⟩
      · obtain ⟨k,hk | hk⟩ := mem_iUnion.mp hx
        · exact ⟨(e^(k.val+1)) x,hk,Or.inr ⟨k,Or.inl rfl⟩⟩
        · obtain ⟨y,hy,he⟩ := hk
          exact ⟨y,hy,Or.inr ⟨k,Or.inr he⟩⟩
  rw [he]
  exact hC.union (MeasurableSet.iUnion fun k =>
    (hC.preimage (e^(k.val+1)).measurable).union
      ((e^(k.val+1)).measurableEmbedding.measurableSet_image.mpr hC))

/-- A countable separated cover exists inside any measurable set with
no short periodic points. The set need not be invariant or ergodic. -/
theorem exists_countable_finite_orbit_cover (e : Y ≃ₜ Y) (N : ℕ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ k : Fin N, (e^(k.val+1)) x ≠ x) :
    ∃ C : ℕ → Set Y, (∀ n, MeasurableSet (C n)) ∧ (⋃ n, C n)=A ∧
      ∀ n, ∀ x ∈ C n, ∀ y ∈ C n, finiteOrbitNeighbor e N x y → x=y := by
  classical
  by_cases hne : A.Nonempty
  · have : Nonempty A := hne.to_subtype
    choose U hU hxU hsep using fun x : A =>
      exists_open_finite_orbit_separated e N x.val (hfree x.val x.property)
    obtain ⟨f,hf⟩ := (HereditarilyLindelofSpace.isLindelof A).indexed_countable_subcover
      U hU (by
        intro x hx
        exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩)
    refine ⟨fun n => A ∩ U (f n),fun n => hA.inter (hU _).measurableSet,?_,?_⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨n,hn⟩ := mem_iUnion.mp hx
        exact hn.1
      · intro hx
        obtain ⟨n,hn⟩ := mem_iUnion.mp (hf hx)
        exact mem_iUnion.mpr ⟨n,hx,hn⟩
    · intro n x hx y hy hxy
      exact hsep (f n) x hx.2 y hy.2 hxy
  · have hzero : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst A
    exact ⟨fun _ => ∅,fun _ => MeasurableSet.empty,by simp,
      fun _ _ hx => hx.elim⟩

/-- A measurable separated section meets every orbit represented in A. -/
theorem exists_finite_orbit_section (e : Y ≃ₜ Y) (N : ℕ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ k : Fin N, (e^(k.val+1)) x ≠ x) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧
      (∀ x ∈ S, ∀ y ∈ S, finiteOrbitNeighbor e N x y → x=y) ∧
      ∀ x ∈ A, ∃ y ∈ S, (homeomorphOrbitSetoid e).r x y := by
  obtain ⟨C,hC,hcover,hsep⟩ := exists_countable_finite_orbit_cover e N hA hfree
  obtain ⟨S,hS,hSA,hind,hmeet⟩ := exists_measurable_orbit_section
    (homeomorphOrbitSetoid e) (finiteOrbitNeighbor e N) (finiteOrbitNeighbor_symm e N)
    (finiteOrbitNeighbor_orbit e N) C hC
    (fun n => measurableSet_finiteOrbitNeighbor e N (hC n)) hsep
  exact ⟨S,hS,by rwa [hcover] at hSA,hind,by rwa [hcover] at hmeet⟩

end Measurable
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallOrbitSection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small complete sections without a map-ergodicity hypothesis -/

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] [BorelSpace Y] in
lemma measurePreserving_homeomorph_pow (μ : Measure Y) (e : Y ≃ₜ Y)
    (he : MeasurePreserving e μ μ) (n : ℕ) : MeasurePreserving (e^n) μ μ := by
  induction n with
  | zero =>
    rw [pow_zero]
    change MeasurePreserving id μ μ
    exact MeasurePreserving.id μ
  | succ n ih =>
    rw [pow_succ]
    change MeasurePreserving ((e^n) ∘ e) μ μ
    exact ih.comp he

omit [T2Space Y] [SecondCountableTopology Y] in
lemma separated_section_mass_bound (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ) (N : ℕ)
    {S : Set Y} (hS : MeasurableSet S)
    (hfree : ∀ x ∈ S, ∀ k : Fin N, (e^(k.val+1)) x ≠ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, finiteOrbitNeighbor e N x y → x=y) :
    (N+1:ℝ≥0∞)*μ S ≤ 1 := by
  have hdis {i j : ℕ} (hj : j ≤ N) (hij : i < j) :
      Disjoint ((e^i) '' S) ((e^j) '' S) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hdiff : i+(j-i)=j := Nat.add_sub_of_le hij.le
    have hxy : x=(e^(j-i)) y := by
      apply (e^i).injective
      rw [←Homeomorph.mul_apply,←pow_add,hdiff]
      exact hxz.trans hyz.symm
    let k : Fin N := ⟨j-i-1,by omega⟩
    have hk : k.val+1=j-i := by dsimp only [k]; omega
    have heq : x=y := hsep x hx y hy (Or.inr ⟨k,Or.inr (by simpa only [hk] using hxy.symm)⟩)
    subst y
    exact hfree x hx k (by simpa only [hk] using hxy.symm)
  have hpair : Pairwise (Disjoint on (fun i : Fin (N+1) => (e^i.val) '' S)) := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hdis (by omega) h
    · exact (hdis (by omega) h).symm
  have hm (i : Fin (N+1)) : MeasurableSet ((e^i.val) '' S) :=
    (e^i.val).measurableEmbedding.measurableSet_image.mpr hS
  have hv (i : Fin (N+1)) : μ ((e^i.val) '' S)=μ S := by
    have hp := measurePreserving_homeomorph_pow μ e he i.val
    calc
      μ ((e^i.val) '' S) = (μ.map (e^i.val)) ((e^i.val) '' S) := by rw [hp.map_eq]
      _ = μ ((e^i.val) ⁻¹' ((e^i.val) '' S)) := Measure.map_apply hp.measurable (hm i)
      _ = μ S := congrArg μ ((e^i.val).injective.preimage_image S)
  have H : (∑' i : Fin (N+1), μ ((e^i.val) '' S)) ≤ μ univ := by
    rw [←measure_iUnion hpair hm]
    exact measure_mono (subset_univ _)
  simpa only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add,Nat.cast_one,measure_univ] using H

/-- Inside an aperiodic measurable set, complete sections can have
arbitrarily small measure. Completeness refers to the represented orbits,
so no ergodicity of e is needed. -/
theorem exists_small_complete_orbit_section
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ n : ℕ, 0 < n → (e^n) x ≠ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧ μ.real S < ε ∧
      ∀ x ∈ A, ∃ y ∈ S, (homeomorphOrbitSetoid e).r x y := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  obtain ⟨S,hS,hSA,hsep,hmeet⟩ := exists_finite_orbit_section e N hA
    (fun x hx k => hfree x hx (k.val+1) (by omega))
  refine ⟨S,hS,hSA,?_,hmeet⟩
  have H := separated_section_mass_bound μ e he N hS
    (fun x hx k => hfree x (hSA hx) (k.val+1) (by omega)) hsep
  have Hr := ENNReal.toReal_mono (by simp) H
  rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp) (by simp)] at Hr
  simp only [ENNReal.toReal_natCast,ENNReal.toReal_one] at Hr
  change (N+1:ℝ)*μ.real S ≤ 1 at Hr
  have hS0 : 0 ≤ μ.real S := measureReal_nonneg
  have hN0 : (0:ℝ) < N+1 := by positivity
  have hNε : 1 < (N+1:ℝ)*ε := by
    have ht : 1 < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
    nlinarith
  nlinarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ForwardOrbitSection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete orbit section is visited in the future almost everywhere

Finite measure turns the forward saturation of a set into an invariant
set modulo null sets. No ergodicity assumption is needed.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] in
lemma ae_future_visits_of_orbit_section (μ : Measure Y) [IsFiniteMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    {S A : Set Y} (hS : MeasurableSet S)
    (hcover : ∀ x ∈ A, ∃ y ∈ S, (homeomorphOrbitSetoid e).r x y) :
    ∀ᵐ x ∂μ, x ∈ A → ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ (e^n) x ∈ S := by
  let U := ⋃ n : ℕ, (e^n) ⁻¹' S
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n =>
    hS.preimage (e^n).measurable
  have hpre : e ⁻¹' U ⊆ U := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨n+1,?_⟩
    simpa only [mem_preimage,pow_succ,Homeomorph.mul_apply] using hn
  have heq : e ⁻¹' U =ᵐ[μ] U := ae_eq_of_subset_of_measure_ge hpre
    (he.measure_preimage hU.nullMeasurableSet).symm.le
    (hU.preimage e.measurable).nullMeasurableSet (measure_ne_top μ U)
  have hnat (n : ℕ) : ∀ᵐ x ∂μ, (e^n) x ∈ U ↔ x ∈ U := by
    induction n with
    | zero => exact ae_of_all μ (fun _ => by simp)
    | succ n ih =>
      filter_upwards [he.quasiMeasurePreserving.ae ih,heq.mem_iff] with x hx heq
      simpa only [pow_succ,Homeomorph.mul_apply] using hx.trans heq
  have hinv : MeasurePreserving (e⁻¹ : Y ≃ₜ Y) μ μ :=
    MeasurePreserving.symm e.toMeasurableEquiv he
  have hint (k : ℤ) : ∀ᵐ x ∂μ, (e^k) x ∈ U ↔ x ∈ U := by
    cases k with
    | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hnat n
    | negSucc n =>
      have hi := (measurePreserving_homeomorph_pow μ e⁻¹ hinv (n+1)).quasiMeasurePreserving.ae
        (hnat (n+1))
      filter_upwards [hi] with x hx
      have hc : (e^(n+1)) ((e⁻¹^(n+1)) x)=x := by
        rw [←Homeomorph.mul_apply,inv_pow,mul_inv_cancel,Homeomorph.one_apply]
      rw [hc] at hx
      simpa only [zpow_negSucc,inv_pow] using hx.symm
  filter_upwards [ae_all_iff.mpr hint] with x hx hxA
  obtain ⟨y,hy,k,hk⟩ := hcover x hxA
  have hyU : y ∈ U := mem_iUnion.mpr ⟨0,by simpa using hy⟩
  have hxU : x ∈ U := (hx k).mp (hk.symm ▸ hyU)
  intro M
  have hMx : (e^M) x ∈ U := by
    simpa only [zpow_natCast] using (hx (M:ℤ)).mpr hxU
  obtain ⟨n,hn⟩ := mem_iUnion.mp hMx
  refine ⟨n+M,by omega,?_⟩
  simpa only [mem_preimage,pow_add,Homeomorph.mul_apply] using hn

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace

open Filter Set Topology

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma matrixBall_isOpen (n : ℕ) (r : ℝ) : IsOpen (matrixBall n r) := by
  simp only [matrixBall, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact ((continuous_apply j).comp ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)).sub
    continuous_const |>.abs

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix

open MeasureTheory Filter Set Module TopologicalSpace
namespace PrimeDegreePackets



theorem cube_grid_cover (d : ℕ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset (Fin d → ℝ),
      (∀ u ∈ s, ∀ i, |u i| ≤ R+1) ∧
      (s.card : ℝ) ≤ (2*R+2)^d / r^d ∧
      ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ R) →
        ∃ u ∈ s, ∀ i, |x i-u i| < r := by
  classical
  let N : ℕ := ⌈2*R/r⌉₊
  let g (k : Fin d → Fin (N+1)) : Fin d → ℝ := fun i => -R + (k i : ℕ)*r
  let s : Finset (Fin d → ℝ) := Finset.univ.image g
  have hN : (N:ℝ) < 2*R/r+1 := by
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) hr.le)
  have hNr : (N:ℝ)*r < 2*R+r := by
    have := (mul_lt_mul_iff_left₀ hr).mpr hN
    field_simp at this
    nlinarith
  refine ⟨s, ?_, ?_, ?_⟩
  · intro u hu i
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
    dsimp [g]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (k i).val) hr.le]
    · have hki : ((k i).val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (k i).isLt)
      nlinarith [mul_le_mul_of_nonneg_right hki hr.le]
  · have hcard : s.card ≤ (N+1)^d := by
      calc
        _ ≤ (Finset.univ : Finset (Fin d → Fin (N+1))).card := Finset.card_image_le
        _ = _ := by simp
    have hN1 : ((N+1:ℕ):ℝ) ≤ (2*R+2)/r := by
      apply (le_div_iff₀ hr).mpr
      push_cast
      nlinarith
    calc
      (s.card:ℝ) ≤ (((N+1)^d:ℕ):ℝ) := Nat.cast_le.mpr hcard
      _ = (((N+1:ℕ):ℝ))^d := Nat.cast_pow _ _
      _ ≤ ((2*R+2)/r)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hN1 d
      _ = _ := div_pow _ _ _
  · intro x hx
    have hx0 (i : Fin d) : 0 ≤ (x i+R)/r := by
      apply div_nonneg _ hr.le
      have := (abs_le.mp (hx i)).1
      linarith
    let k (i : Fin d) : Fin (N+1) := ⟨⌊(x i+R)/r⌋₊, by
      apply Nat.lt_succ_of_le
      apply (Nat.floor_mono ?_).trans (Nat.floor_le_ceil _)
      apply div_le_div_of_nonneg_right _ hr.le
      have := (abs_le.mp (hx i)).2
      linarith⟩
    refine ⟨g k, Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
    intro i
    have hlo := Nat.floor_le (hx0 i)
    have hhi := Nat.lt_floor_add_one ((x i+R)/r)
    have Hlo : (⌊(x i+R)/r⌋₊ : ℝ)*r ≤ x i+R := (le_div_iff₀ hr).mp hlo
    have Hhi : x i+R < ((⌊(x i+R)/r⌋₊ : ℝ)+1)*r := (div_lt_iff₀ hr).mp hhi
    dsimp [g,k]
    rw [abs_of_nonneg (by linarith)]
    linarith

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal

open scoped BigOperators Topology ENNReal Classical

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
namespace PrimeDegreePackets

lemma matrixBall_mono {n : ℕ} {r s : ℝ} (hrs : r ≤ s) :
    matrixBall n r ⊆ matrixBall n s := by
  intro g hg i j
  exact (hg i j).trans_le hrs



end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
namespace PrimeDegreePackets

lemma one_mem_matrixBall (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 : G n) ∈ matrixBall n r := by
  intro i j
  simpa using hr

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationCovers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise

open scoped BigOperators Topology ENNReal Classical Matrix


namespace PrimeDegreePackets

lemma rightAction_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) :
    rightAction (rightAction x g) a =
      rightAction (rightAction x a) (MulAut.conj a⁻¹ g) := by
  simp only [rightAction_mul,MulAut.conj_apply,inv_inv]
  congr 1
  group

lemma rightAction_iterate_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) (k : ℕ) :
    (fun y => rightAction y a)^[k] (rightAction x g) =
      rightAction ((fun y => rightAction y a)^[k] x) ((MulAut.conj a⁻¹)^[k] g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,rightAction_conjugation]
    simp only [Function.iterate_succ_apply']



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma conjugation_iterate {H : Type*} [Group H] (a g : H) (j : ℕ) :
    (MulAut.conj a⁻¹)^[j] g = (a^j)⁻¹*g*a^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [MulAut.conj_apply,inv_inv,pow_succ,_root_.mul_inv_rev]
    group



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.time_borelSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_measurableSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_nonempty _root_.OAI.DukePrimeDegree.EliminationChain.time_polish _root_.OAI.DukePrimeDegree.EliminationChain.time_secondCountable _root_.OAI.DukePrimeDegree.EliminationChain.time_standardBorel _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composing Gaussian root-coordinate charts

A finite sequence of compatible eliminations gives an actual open
embedding of the final transverse slice and all its real root
coordinates. Its parametrization is multiplication by the ordered
product of the elementary root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem param_zeroTime (c : EliminationChain P D) (s : c.FinalSlice) :
    (c.param (s, c.zeroTime)).val = s.val := by
  rw [c.param_val, c.word_zeroTime, mul_one]

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.time_borelSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_polish _root_.OAI.DukePrimeDegree.EliminationChain.time_secondCountable _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootIndexEquiv_val _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual charts for the full upper unipotent group

The complete Gaussian elimination chain supplies an open group chart.
Left translation and the discrete lattice covering then give local
product charts in the arithmetic quotient around every point. Every
time factor is an actual ordered product of positive-root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

@[simp] lemma upperRootParam_zero (n : ℕ) :
    upperRootParam n (upperRootIdentity n, (completeRootChain n).zeroTime) = 1 :=
  (completeRootChain n).param_zeroTime _

theorem upperRootQuotientParam_localHomeomorph (n : ℕ) (g : G n) :
    IsLocalHomeomorph (upperRootQuotientParam n g) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp
      (upperRootParam_isOpenEmbedding n).isLocalHomeomorph)

theorem exists_upperRootBox_at_coordinates (n : ℕ) (g : G n)
    (z : UpperRootTransverse n × UpperRootTime n) :
    ∃ B : UpperRootBox n g, z ∈ B.transverse ×ˢ B.time := by
  obtain ⟨U, hUz, hU⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (upperRootQuotientParam_localHomeomorph n g) z
  obtain ⟨V, W, hVo, hVz, hWo, hWz, hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V, W, hVo, hWo, he⟩, hVz, hWz⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CutFamilyCode
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integer codes for families of real cuts -/

noncomputable section
open MeasureTheory
namespace DukePrimeDegree

lemma finiteCutCode_measurable {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    {f : Fin N → Y → ℝ} (hf : ∀ i, Measurable (f i)) (c : Fin N → ℝ) :
    Measurable (finiteCutCode f c) := by
  apply (measurable_of_finite (Fintype.equivFin (Fin N → Bool))).comp
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_bool
  have he : (fun x => decide (f i x < c i)) ⁻¹' {true} = {x | f i x < c i} := by
    ext x
    simp
  rw [he]
  exact measurableSet_lt (hf i) measurable_const

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FirstCoverCode
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One covering label instead of the full vector of cut tests

A point is labeled by one cut containing it. There are N+1 labels for N
cuts. Equality of labels still puts covered points in the same small
set, while constancy of all cut tests implies constancy of this label.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

private lemma firstTrue_common {N : ℕ} (v w : Fin N → Bool)
    (hw : ∃ i, w i=true) (h : firstTrue v=firstTrue w) :
    ∃ i, v i=true ∧ w i=true := by
  classical
  have hv : ∃ i, v i=true := by
    by_contra hn
    have hh := congrArg Fin.val h
    simp only [firstTrue,dite_eq_right hn,dite_eq_left hw,Fin.val_zero] at hh
    omega
  have hi : hv.choose=hw.choose := by
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [firstTrue,dite_eq_left hv,dite_eq_left hw] at hh
    omega
  exact ⟨hw.choose,hi ▸ hv.choose_spec,hw.choose_spec⟩

lemma firstCoverCode_measurable {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    {f : Fin N → Y → ℝ} (hf : ∀ i, Measurable (f i)) (c : Fin N → ℝ) :
    Measurable (firstCoverCode f c) := by
  have h := (measurable_of_finite
    (fun u : Fin (Fintype.card (Fin N → Bool)) =>
      firstTrue ((Fintype.equivFin (Fin N → Bool)).symm u))).comp
        (finiteCutCode_measurable hf c)
  change Measurable (fun x => firstTrue (fun i => decide (f i x < c i)))
  simpa only [Function.comp_def,finiteCutCode,Equiv.symm_apply_apply] using h

lemma firstCoverCode_common {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (hx : ∃ i, f i x < c i) (h : firstCoverCode f c y=firstCoverCode f c x) :
    ∃ i, f i y < c i ∧ f i x < c i := by
  have hw : ∃ i, decide (f i x < c i)=true := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,decide_eq_true hi⟩
  obtain ⟨i,hi,hj⟩ := firstTrue_common (fun i => decide (f i y < c i))
    (fun i => decide (f i x < c i)) hw h
  exact ⟨i,of_decide_eq_true hi,of_decide_eq_true hj⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteTransverseCode
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite codes for bounded transverse coordinates

Only the transverse vector is observed. Equal labels give a quantitative
coordinate bound, with the number of labels controlled by a finite grid.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_bounded_vector_code {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (f : Y → Fin d → ℝ) (hf : Measurable f)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (K : ℕ) (B : Y → Fin K), Measurable B ∧
      (K : ℝ) ≤ 1+(2*R+2)^d/δ^d ∧
      ∀ x y, (∀ i, |f x i| ≤ R) → B y=B x →
        ∀ i, |f y i-f x i| < 2*δ := by
  classical
  obtain ⟨s,_,hcard,hcover⟩ := cube_grid_cover d hR hδ hδ1
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let g (i : Fin (Fintype.card s)) (x : Y) : ℝ := dist (f x) (e i).val
  let B := firstCoverCode g (fun _ => δ)
  refine ⟨Fintype.card s+1,B,?_,?_,?_⟩
  · exact firstCoverCode_measurable (fun i => hf.dist measurable_const) _
  · push_cast
    have hc : (Fintype.card s : ℝ) ≤ (2*R+2)^d/δ^d := by
      simpa only [Fintype.card_coe] using hcard
    linarith
  · intro x y hx hxy
    obtain ⟨c,hc,hclose⟩ := hcover (f x) hx
    have hcov : ∃ i, g i x < δ := by
      refine ⟨e.symm ⟨c,hc⟩,?_⟩
      change dist (f x) ((e (e.symm ⟨c,hc⟩)).val) < δ
      simp only [Equiv.apply_symm_apply]
      apply (dist_pi_lt_iff hδ).mpr
      intro i
      simpa only [Real.dist_eq] using hclose i
    obtain ⟨i,hiy,hix⟩ := firstCoverCode_common g (fun _ => δ) hcov hxy
    have hd : dist (f y) (f x) < 2*δ :=
      (dist_triangle_right (f y) (f x) (e i).val).trans_lt (by linarith)
    intro j
    simpa only [Real.dist_eq] using (dist_pi_lt_iff (by positivity : 0 < 2*δ)).mp hd j

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TransverseDiagonalData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal coordinates on the transverse lower triangular slice

Column ratios are fixed by the diagonal action; the logarithms of the
absolute diagonal entries are translated linearly. These are the actual
transverse coordinates, before choosing any finite entropy approximation.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma transverseLogDiagonal_diagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i=0) (t : ℝ) (s : UpperRootTransverse n) :
    transverseLogDiagonal (upperRootTransverseDiagonal ell hell t s) =
      fun i => transverseLogDiagonal s i+ell i*t := by
  funext i
  change Real.log |(s.val*diagonalOneParameter ell hell t).val i i| = _
  rw [mul_diagonalOneParameter_entry,abs_mul,abs_of_pos (Real.exp_pos _),
    Real.log_mul (abs_ne_zero.mpr (upperRootTransverse_diagonal_ne_zero s i))
      (Real.exp_ne_zero _),Real.log_exp]
  rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TransverseRootFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transverse coordinates of actual right root displacements

The transverse coordinate is constant on a right upper-unipotent leaf.
A right diagonal displacement translates its logarithmic diagonal exactly.
These identities allow return refinements to use transverse cells only.
-/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem transverse_eq_of_right_upperRoot {n : ℕ}
    (s r : UpperRootTransverse n) (u v : UpperRootTime n)
    (h : positiveRootGeneratedGroup (allPositiveRoots n))
    (he : upperRootParam n (s,u)*h.val=upperRootParam n (r,v)) : s=r := by
  obtain ⟨w,hw⟩ := upperRootWord_surjective n
    ⟨(completeRootChain n).word u*h.val,
      (positiveRootGeneratedGroup _).mul_mem (upperRootWord_mem n u) h.prop⟩
  have he' : upperRootParam n (s,w)=upperRootParam n (r,v) := by
    rw [upperRootParam_eq_mul,hw,←mul_assoc,←upperRootParam_eq_mul]
    exact he
  exact congrArg Prod.fst ((upperRootParam_isOpenEmbedding n).injective he')

theorem transverse_eq_of_right_diagonal_upperRoot {n : ℕ}
    (s r : UpperRootTransverse n) (u v : UpperRootTime n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (t : ℝ)
    (h : positiveRootGeneratedGroup (allPositiveRoots n))
    (he : upperRootParam n (s,u)*(diagonalOneParameter ell hell t*h.val)=
      upperRootParam n (r,v)) :
    r=upperRootTransverseDiagonal ell hell t s := by
  let u' := (completeRootChain n).rootDilation ell (-t) u
  have hp : upperRootParam n (upperRootTransverseDiagonal ell hell t s,u')=
      upperRootParam n (s,u)*diagonalOneParameter ell hell t := by
    rw [upperRootParam_eq_mul,upperRootParam_eq_mul]
    change (s.val*diagonalOneParameter ell hell t)*(completeRootChain n).word u'=_
    dsimp only [u']
    rw [(completeRootChain n).word_rootDilation ell hell (-t),neg_neg,
      diagonalOneParameter_neg]
    group
  apply Eq.symm
  apply transverse_eq_of_right_upperRoot _ _ u' v h
  rw [hp,mul_assoc]
  exact he

theorem transverseLogDiagonal_right_diagonal_upperRoot {n : ℕ}
    (s r : UpperRootTransverse n) (u v : UpperRootTime n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (t : ℝ)
    (h : positiveRootGeneratedGroup (allPositiveRoots n))
    (he : upperRootParam n (s,u)*(diagonalOneParameter ell hell t*h.val)=
      upperRootParam n (r,v)) :
    transverseLogDiagonal r=fun i => transverseLogDiagonal s i+ell i*t := by
  rw [transverse_eq_of_right_diagonal_upperRoot s r u v ell hell t h he]
  exact transverseLogDiagonal_diagonal ell hell t s

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TransverseReturnCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Return observations in actual upper-root quotient coordinates -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

namespace UpperRootBox
variable {n : ℕ} {g : G n}

theorem exists_measurable_logDiagonal (B : UpperRootBox n g) :
    ∃ f : X n → Fin n → ℝ, Measurable f ∧
      ∀ z : B.domain, f (B.param z)=transverseLogDiagonal z.val.1 := by
  obtain ⟨f,hf,he⟩ := B.embedding.measurableEmbedding.exists_measurable_extend
    ((continuous_transverseLogDiagonal n).measurable.comp
      (measurable_fst.comp measurable_subtype_coe)) (fun _ => inferInstance)
  exact ⟨f,hf,fun z => congrFun he z⟩

end UpperRootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_BilateralNeutralLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilateral observation fibers have neutral relative displacement

The same small radial cells are used in both time directions. Uniqueness
of the small lift identifies the two triangular lifts; their common lift
commutes with the diagonal flow. This supplies the geometry needed to
bound the entropy left over after the complete observation itinerary.
-/

noncomputable section
open Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma commute_diagonalOneParameter_of_weight_support {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (g : G n)
    (hg : ∀ i j, ell i ≠ ell j → g.val i j=0) (t : ℝ) :
    Commute g (diagonalOneParameter ell hell t) := by
  change g * diagonalOneParameter ell hell t = diagonalOneParameter ell hell t * g
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (g.val * Matrix.diagonal (fun k => Real.exp (ell k*t))) i j =
    (Matrix.diagonal (fun k => Real.exp (ell k*t)) * g.val) i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : ell i=ell j
  · rw [h,mul_comm]
  · rw [hg i j h]
    simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeakStableFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal and unipotent coordinates of a weak stable displacement -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Positive upper triangular matrices split into a positive diagonal
matrix and an actual ordered upper-root word. -/
theorem upper_triangular_positive_diagonal_factorization {n : ℕ} (g : G n)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u := by
  let v : Fin n → ℝ := fun i => Real.log (g.val i i)
  have hprod : ∏ i, g.val i i=1 := (Matrix.det_of_isUpperTriangular htri).symm.trans g.prop
  have hv : ∑ i, v i=0 := by
    dsimp [v]
    rw [←Real.log_prod (fun i _ => (hpos i).ne'),hprod,Real.log_one]
  let a := diagonalOneParameter v hv 1
  let u : G n := a⁻¹*g
  have hu : PositiveRootPattern (allPositiveRoots n) u := by
    intro i j hij
    have hij' : ¬ i < j := by simpa [allPositiveRoots] using hij
    have he : u.val i j=Real.exp (-v i)*g.val i j := by
      change ((diagonalOneParameter v hv 1)⁻¹*g).val i j = _
      rw [←diagonalOneParameter_neg]
      change (Matrix.diagonal (fun i => Real.exp (v i*(-1))) * g.val) i j = _
      rw [Matrix.diagonal_mul]
      congr 2
      ring
    rw [he]
    by_cases heq : i=j
    · subst j
      rw [Matrix.one_apply_eq]
      dsimp [v]
      rw [Real.exp_neg,Real.exp_log (hpos i),inv_mul_cancel₀ (hpos i).ne']
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm heq)
      rw [htri hji,Matrix.one_apply_ne heq,mul_zero]
  have hum : u ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootPattern_mem_generated (allPositiveRoots n)
      (fun p hp => (Finset.mem_filter.mp hp).2) (allPositiveRoots_closed n) hu
  obtain ⟨t,ht⟩ := upperRootWord_surjective n ⟨u,hum⟩
  refine ⟨v,hv,t,?_⟩
  rw [ht]
  change g=a*(a⁻¹*g)
  group

/-- A sufficiently small future lift has a neutral diagonal part. Its
remaining part belongs to the genuine strong stable unipotent group. -/
theorem small_weak_stable_factorization {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (hord : StrictMono ell) (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u ∧
      ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t) := by
  have htri : g.val.IsUpperTriangular := fun i j hji => hzero i j (hord hji)
  have hpos (i : Fin n) : 0 < g.val i i := by
    have hh := hg i i
    rw [Matrix.one_apply_eq] at hh
    have hh' := (abs_lt.mp hh).1
    linarith
  obtain ⟨v,hv,u,hu⟩ := upper_triangular_positive_diagonal_factorization g htri hpos
  refine ⟨v,hv,u,hu,?_⟩
  intro t
  apply commute_diagonalOneParameter_of_weight_support ell hell
  intro i j hij
  have hne : i ≠ j := by intro he; exact hij (congrArg ell he)
  change (Matrix.diagonal (fun i => Real.exp (v i*1))) i j=0
  exact Matrix.diagonal_apply_ne _ hne

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FineTransverseConjugates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fine transverse returns remove the weak stable diagonal -/

noncomputable section
open Matrix Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem upperRootWord_of_fine_transverse_returns {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0)
    (hfine : ∀ ε : ℝ, 0 < ε → ∃ (k : ℕ)
      (s r : UpperRootTransverse n) (u w : UpperRootTime n),
      upperRootParam n (s,u)*(diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)))=upperRootParam n (r,w) ∧
      ∀ i, |transverseLogDiagonal r i-transverseLogDiagonal s i| < ε) :
    ∃ v : UpperRootTime n, (completeRootChain n).word v=g := by
  obtain ⟨v,hv,t,hg',hcomm⟩ := small_weak_stable_factorization ell hell hord g hg hzero
  have hfactor (k : ℕ) :
      diagonalOneParameter ell hell (k:ℝ)*g*diagonalOneParameter ell hell (-(k:ℝ)) =
        diagonalOneParameter v hv 1 *
          (completeRootChain n).word ((completeRootChain n).rootDilation ell (k:ℝ) t) := by
    rw [hg',(completeRootChain n).word_rootDilation ell hell (k:ℝ)]
    calc
      _ = (diagonalOneParameter ell hell (k:ℝ)*diagonalOneParameter v hv 1)*
          ((completeRootChain n).word t*diagonalOneParameter ell hell (-(k:ℝ))) := by group
      _ = (diagonalOneParameter v hv 1*diagonalOneParameter ell hell (k:ℝ))*
          ((completeRootChain n).word t*diagonalOneParameter ell hell (-(k:ℝ))) := by
            rw [(hcomm (k:ℝ)).eq]
      _ = _ := by group
  have hlog (k : ℕ) (s r : UpperRootTransverse n) (u w : UpperRootTime n)
      (hk : upperRootParam n (s,u)*(diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)))=upperRootParam n (r,w)) :
      transverseLogDiagonal r=fun i => transverseLogDiagonal s i+v i := by
    rw [hfactor k] at hk
    simpa only [mul_one] using transverseLogDiagonal_right_diagonal_upperRoot
      s r u w v hv 1
      ⟨_,upperRootWord_mem n _⟩ hk
  have hvzero : v=0 := by
    funext i
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    by_contra hn
    obtain ⟨k,s,r,u,w,he,hk⟩ := hfine |v i| (lt_of_not_ge hn)
    have hi := hk i
    rw [hlog k s r u w he] at hi
    simp only [add_sub_cancel_left,lt_self_iff_false] at hi
  have ha : diagonalOneParameter v hv 1=1 := by
    apply Subtype.ext
    ext i j
    simp [diagonalOneParameter,hvzero,Matrix.one_apply]
  exact ⟨t,by simpa only [ha,one_mul] using hg'.symm⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ReturnLiftAlignment
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Aligning recurrent quotient lifts with transverse coordinates -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootBox_lift_alignment {n : ℕ} {a : G n} (B : UpperRootBox n a)
    (z w : B.domain) (ρ : ℝ)
    (hinj : Set.InjOn (fun g => rightAction (B.param z) g) (matrixBall n ρ))
    (hrel : (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n ρ)
    (g : G n) (hg : g ∈ matrixBall n ρ)
    (hact : rightAction (B.param z) g=B.param w) :
    upperRootParam n z.val*g=upperRootParam n w.val := by
  have hc : rightAction (B.param z)
      ((upperRootParam n z.val)⁻¹*upperRootParam n w.val)=B.param w := by
    change Quotient.mk _ ((a*upperRootParam n z.val)*
      ((upperRootParam n z.val)⁻¹*upperRootParam n w.val)) =
        Quotient.mk _ (a*upperRootParam n w.val)
    congr 1
    group
  have he := hinj hg hrel (hact.trans hc.symm)
  rw [he]
  group

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FinitePrefixChartCodes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite codes for a growing prefix of coordinate charts

The label records chart membership as well as the coordinate grid. A
single sufficiently advanced label therefore resolves any fixed chart.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

theorem exists_finite_prefix_chart_codes
    {Y : Type*} [MeasurableSpace Y] {d : ℕ}
    (A : ℕ → Set Y) (hA : ∀ i, MeasurableSet (A i))
    (f : ℕ → Y → Fin d → ℝ) (hf : ∀ i, Measurable (f i))
    (R : ℕ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i x, x ∈ A i → ∀ j, |f i x j| ≤ R i) :
    ∃ (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)),
      (∀ n, Measurable (B n)) ∧
      ∀ n i, i ≤ n → ∀ x ∈ A i, ∀ y, B n y=B n x →
        y ∈ A i ∧ ∀ j, |f i y j-f i x j| < 2*(1/(n+1:ℝ)) := by
  classical
  have hscale (n : ℕ) : (0:ℝ) < 1/(n+1) := by positivity
  have hscale1 (n : ℕ) : 1/(n+1:ℝ) ≤ 1 := by
    apply div_le_self zero_le_one
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose L C hC _hcard hclose using fun n (i : Fin (n+1)) =>
    exists_bounded_vector_code (f i.val) (hf i.val) (hR i.val) (hscale n) (hscale1 n)
  let Alphabet (n : ℕ) := ∀ i : Fin (n+1), Option (Fin (L n i))
  let F (n : ℕ) (x : Y) : Alphabet n := fun i =>
    if x ∈ A i.val then some (C n i x) else none
  let K (n : ℕ) := Fintype.card (Alphabet n)
  let B (n : ℕ) (x : Y) : Fin (K n) := Fintype.equivFin (Alphabet n) (F n x)
  have hBm (n : ℕ) : Measurable (B n) := by
    let : MeasurableSpace (Alphabet n) := ⊤
    apply (measurable_of_finite (Fintype.equivFin (Alphabet n))).comp
    apply measurable_to_countable'
    intro a
    change MeasurableSet {x | F n x=a}
    have he : {x | F n x=a} = ⋂ i : Fin (n+1), {x | F n x i=a i} := by
      ext x
      simp only [mem_ofPred_eq,mem_iInter]
      exact ⟨fun h i => congrFun h i,fun h => funext h⟩
    rw [he]
    apply MeasurableSet.iInter
    intro i
    let : MeasurableSpace (Option (Fin (L n i))) := ⊤
    have hFi : Measurable (fun x => F n x i) :=
      ((measurable_of_finite Option.some).comp (hC n i)).piecewise (hA i.val) measurable_const
    exact hFi (measurableSet_singleton (a i))
  refine ⟨K,B,hBm,?_⟩
  intro n i hin x hx y hxy
  let ii : Fin (n+1) := ⟨i,by omega⟩
  have hF : F n y=F n x := (Fintype.equivFin (Alphabet n)).injective hxy
  have hletter := congrFun hF ii
  have hy : y ∈ A i := by
    by_contra hy
    simp only [F,ii,ite_eq_left hx,ite_eq_right hy,reduceCtorEq] at hletter
  have hcode : C n ii y=C n ii x := by
    simpa only [F,ii,ite_eq_left hx,ite_eq_left hy,Option.some.injEq] using hletter
  exact ⟨hy,hclose n ii x y (hbound i x hx) hcode⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_EncodedObservationEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding a countable observation preserves its Shannon sum -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

lemma encoded_observation_information
    {Y α : Type*} [MeasurableSpace Y] [Encodable α]
    (μ : Measure Y) (P : Y → α) :
    (Summable (fun n : ℕ => Real.negMulLog (μ.real {x | Encodable.encode (P x)=n})) ↔
      Summable (fun a : α => Real.negMulLog (μ.real {x | P x=a}))) ∧
    (∑' n : ℕ, Real.negMulLog (μ.real {x | Encodable.encode (P x)=n})) =
      ∑' a : α, Real.negMulLog (μ.real {x | P x=a}) := by
  classical
  let f : ℕ → ℝ := fun n => Real.negMulLog (μ.real {x | Encodable.encode (P x)=n})
  have hout (n : ℕ) (hn : n ∉ range (Encodable.encode : α → ℕ)) : f n=0 := by
    have he : {x | Encodable.encode (P x)=n}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hn ⟨P x,hx⟩
    simp only [f,he,measureReal_empty,Real.negMulLog_zero]
  have he (a : α) : f (Encodable.encode a)=Real.negMulLog (μ.real {x | P x=a}) := by
    have hh : {x | Encodable.encode (P x)=Encodable.encode a}={x | P x=a} := by
      ext x
      exact Encodable.encode_injective.eq_iff
    change Real.negMulLog (μ.real {x | Encodable.encode (P x)=Encodable.encode a}) = _
    rw [hh]
  constructor
  · have h := Encodable.encode_injective.summable_iff hout
    simpa only [Function.comp_def,he] using h.symm
  · have h := Encodable.encode_injective.tsum_eq (f := f) (by
      intro n hn
      by_contra hnot
      exact hn (hout n hnot))
    simpa only [he] using h.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LastActiveObservation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable observations at the last active scale

Summably small sections overlap only finitely often almost everywhere.
Recording the largest active scale therefore preserves arbitrarily fine
visits while keeping the observation alphabet countable.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

lemma measurableSet_lastActiveSection {Y : Type*} [MeasurableSpace Y]
    {S : ℕ → Set Y} (hS : ∀ n, MeasurableSet (S n)) (n : ℕ) :
    MeasurableSet (lastActiveSection S n) := by
  have he : lastActiveSection S n = S n ∩ ⋂ m : ℕ, ⋂ (_ : n < m), (S m)ᶜ := by
    ext x
    simp only [lastActiveSection,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff]
  rw [he]
  exact (hS n).inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hS m).compl)

lemma lastActiveSection_unique {Y : Type*} {S : ℕ → Set Y} {n m : ℕ} {x : Y}
    (hn : x ∈ lastActiveSection S n) (hm : x ∈ lastActiveSection S m) : n=m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hn.2 m h hm.1).elim
  · exact h
  · exact (hm.2 n h hn.1).elim

lemma exists_lastActiveSection_of_finite {Y : Type*} {S : ℕ → Set Y} {x : Y}
    (hfin : {n | x ∈ S n}.Finite) {n : ℕ} (hn : x ∈ S n) :
    ∃ m, n ≤ m ∧ x ∈ lastActiveSection S m := by
  classical
  have hne : hfin.toFinset.Nonempty := ⟨n,hfin.mem_toFinset.mpr hn⟩
  let m := hfin.toFinset.max' hne
  have hm : x ∈ S m := hfin.mem_toFinset.mp (hfin.toFinset.max'_mem hne)
  refine ⟨m,hfin.toFinset.le_max' n (hfin.mem_toFinset.mpr hn),hm,?_⟩
  intro j hj hjS
  have hjle := hfin.toFinset.le_max' j (hfin.mem_toFinset.mpr hjS)
  exact (not_le_of_gt hj) hjle

lemma lastActiveObservationAtom_unique {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n))
    {a b : Option (Σ n : ℕ, Fin (K n))} {x : Y}
    (ha : x ∈ lastActiveObservationAtom S B a)
    (hb : x ∈ lastActiveObservationAtom S B b) : a=b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => exact (ha (mem_iUnion.mpr ⟨b.1,hb.1⟩)).elim
  | some a =>
      cases b with
      | none => exact (hb (mem_iUnion.mpr ⟨a.1,ha.1⟩)).elim
      | some b =>
        rcases a with ⟨n,i⟩
        rcases b with ⟨m,j⟩
        have he := lastActiveSection_unique ha.1 hb.1
        dsimp at he
        subst m
        have hij : i=j := ha.2.symm.trans hb.2
        subst j
        rfl

lemma lastActiveObservation_fiber {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (z : Option (Σ n : ℕ, Fin (K n))) :
    {x | lastActiveObservation S B x=z}=lastActiveObservationAtom S B z := by
  ext x
  constructor
  · intro hx
    have hm : x ∈ lastActiveObservationAtom S B (lastActiveObservation S B x) :=
      (lastActiveObservation_covers S B x).choose_spec
    rwa [hx] at hm
  · intro hx
    exact lastActiveObservationAtom_unique S B (lastActiveObservation_covers S B x).choose_spec hx

lemma measurable_lastActiveObservation {Y : Type*} [MeasurableSpace Y]
    {S : ℕ → Set Y} (hS : ∀ n, MeasurableSet (S n))
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n)) :
    @Measurable Y (Option (Σ n : ℕ, Fin (K n))) _ ⊤ (lastActiveObservation S B) := by
  let : MeasurableSpace (Option (Σ n : ℕ, Fin (K n))) := ⊤
  apply measurable_to_countable'
  intro z
  change MeasurableSet {x | lastActiveObservation S B x=z}
  rw [lastActiveObservation_fiber]
  cases z with
  | none => exact (MeasurableSet.iUnion (measurableSet_lastActiveSection hS)).compl
  | some z =>
      exact (measurableSet_lastActiveSection hS z.1).inter
        (hB z.1 (measurableSet_singleton z.2))

/-- A visit to scale n is recorded at some scale at least n whenever
only finitely many sections contain the current point. -/
lemma lastActiveObservation_scale_ge {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) {x : Y}
    (hfin : {n | x ∈ S n}.Finite) {n : ℕ} (hn : x ∈ S n) :
    ∃ m, n ≤ m ∧ lastActiveObservation S B x=some ⟨m,B m x⟩ := by
  obtain ⟨m,hnm,hm⟩ := exists_lastActiveSection_of_finite hfin hn
  refine ⟨m,hnm,?_⟩
  exact Set.ext_iff.mp (lastActiveObservation_fiber S B (some ⟨m,B m x⟩)) x |>.mpr ⟨hm,rfl⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableSparseFineObservation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One low-entropy observation for a countable coordinate atlas -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

theorem exists_countable_sparse_fine_observation
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    (A : ℕ → Set Y) (hA : ∀ i, MeasurableSet (A i))
    (hfree : ∀ i x, x ∈ A i → ∀ n : ℕ, 0 < n → (e^n) x ≠ x)
    {d : ℕ} (f : ℕ → Y → Fin d → ℝ) (hf : ∀ i, Measurable (f i))
    (R : ℕ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i x, x ∈ A i → ∀ j, |f i x j| ≤ R i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Y → ℕ, Measurable Q ∧
      Summable (fun n => Real.negMulLog (μ.real {x | Q x=n})) ∧
      (∑' n, Real.negMulLog (μ.real {x | Q x=n})) < ε ∧
      ∀ᵐ x ∂μ, ∀ i, x ∈ A i → ∀ y,
        (∀ k : ℕ, Q ((e^(k+1)) y)=Q ((e^(k+1)) x)) →
        ∀ η : ℝ, 0 < η → ∃ k : ℕ, (e^(k+1)) x ∈ A i ∧ (e^(k+1)) y ∈ A i ∧
          ∀ j, |f i ((e^(k+1)) y) j-f i ((e^(k+1)) x) j| < η := by
  obtain ⟨K,B,hB,hclose⟩ := exists_finite_prefix_chart_codes A hA f hf R hR hbound
  obtain ⟨δ,hδ,hδs,_,Hδ⟩ := exists_lastActiveObservation_entropy_budget
    (Y := Y) K hε
  choose S hS hSA hSm hcover using fun n : ℕ =>
    exists_small_complete_orbit_section μ e he (hA n.unpair.1)
      (hfree n.unpair.1) (hδ n)
  have hsμ : (∑' n, μ (S n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hδs.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro n
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (hδ n).le).mpr (hSm n).le
  have hfinite := ae_finite_setOfPred_mem hsμ
  have hfiniteAll : ∀ᵐ x ∂μ, ∀ k : ℕ, {n | (e^k) x ∈ S n}.Finite :=
    ae_all_iff.mpr fun k => (measurePreserving_homeomorph_pow μ e he k).quasiMeasurePreserving.ae hfinite
  have hvisitAll : ∀ᵐ x ∂μ, ∀ n, x ∈ A n.unpair.1 → ∀ M : ℕ,
      ∃ k : ℕ, M ≤ k ∧ (e^k) x ∈ S n :=
    ae_all_iff.mpr fun n => ae_future_visits_of_orbit_section μ e he (hS n) (hcover n)
  let I := Option (Σ n : ℕ, Fin (K n))
  let : MeasurableSpace I := ⊤
  let Q : Y → ℕ := fun x => Encodable.encode (lastActiveObservation S B x)
  have hQ : Measurable Q := (measurable_of_countable Encodable.encode).comp
    (measurable_lastActiveObservation hS B hB)
  have hcost := Hδ μ S hS (fun n => (hSm n).le) B hB
  have hencode := encoded_observation_information μ (lastActiveObservation S B)
  refine ⟨Q,hQ,hencode.1.mpr hcost.1,hencode.2.trans_lt hcost.2,?_⟩
  filter_upwards [hfiniteAll,hvisitAll] with x hxfin hxvisit
  intro i hxA y hxy η hη
  obtain ⟨p,hp⟩ := exists_nat_gt (2/η)
  let n := Nat.pair i p
  have hindex : n.unpair.1=i := by simp only [n,Nat.unpair_pair]
  have hxA' : x ∈ A n.unpair.1 := by rwa [hindex]
  obtain ⟨k,hk,hkx⟩ := hxvisit n hxA' 1
  obtain ⟨m,hnm,hm⟩ := lastActiveObservation_scale_ge S B (hxfin k) hkx
  have him : i ≤ m := (Nat.left_le_pair i p).trans hnm
  have hpm : p ≤ m := (Nat.right_le_pair i p).trans hnm
  have hkcode : lastActiveObservation S B ((e^k) y)=lastActiveObservation S B ((e^k) x) := by
    apply Encodable.encode_injective
    have hh := hxy (k-1)
    simpa only [Nat.sub_add_cancel hk] using hh
  have hycode : lastActiveObservation S B ((e^k) y)=some ⟨m,B m ((e^k) x)⟩ := hkcode.trans hm
  have hmy : (e^k) y ∈ lastActiveObservationAtom S B (some ⟨m,B m ((e^k) x)⟩) := by
    rw [←lastActiveObservation_fiber]
    exact hycode
  have hxmem : (e^k) x ∈ A i := by
    have H := hSA n hkx
    rwa [hindex] at H
  obtain ⟨hymem,hfine⟩ := hclose m i him _ hxmem _ hmy.2
  refine ⟨k-1,by simpa only [Nat.sub_add_cancel hk] using hxmem,
    by simpa only [Nat.sub_add_cancel hk] using hymem,?_⟩
  intro j
  have hpmR : (p:ℝ) ≤ m := by exact_mod_cast hpm
  have hlarge : 2 < (p:ℝ)*η := (div_lt_iff₀ hη).mp hp
  have hsmall : 2*(1/(m+1:ℝ)) < η := by
    have hd : (0:ℝ) < m+1 := by positivity
    rw [mul_one_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have H := (hfine j).trans hsmall
  simpa only [Nat.sub_add_cancel hk] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SmallUpperRootAtlas
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countably many small upper-root boxes

Both the relative group displacement and the transverse logarithmic
coordinates are controlled on each box. The radius can be chosen before
the atlas, as required by the height-dependent injectivity estimates.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

private theorem exists_small_upperRoot_product (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ (S : Set (UpperRootTransverse n)) (T : Set (UpperRootTime n)),
      IsOpen S ∧ IsOpen T ∧ upperRootIdentity n ∈ S ∧
      (completeRootChain n).zeroTime ∈ T ∧
      (∀ z ∈ S ×ˢ T, ∀ w ∈ S ×ˢ T,
        (upperRootParam n z)⁻¹*upperRootParam n w ∈ matrixBall n r) ∧
      ∀ z ∈ S ×ˢ T, ∀ i, |transverseLogDiagonal z.1 i| ≤ 1 := by
  let z₀ := (upperRootIdentity n,(completeRootChain n).zeroTime)
  have hc : Continuous (fun p :
      (UpperRootTransverse n × UpperRootTime n) ×
        (UpperRootTransverse n × UpperRootTime n) =>
      (upperRootParam n p.1)⁻¹*upperRootParam n p.2) :=
    ((upperRootParam_isOpenEmbedding n).continuous.comp continuous_fst).inv.mul
      ((upperRootParam_isOpenEmbedding n).continuous.comp continuous_snd)
  have hball : (fun p :
      (UpperRootTransverse n × UpperRootTime n) ×
        (UpperRootTransverse n × UpperRootTime n) =>
      (upperRootParam n p.1)⁻¹*upperRootParam n p.2) ⁻¹' matrixBall n r ∈
        𝓝 (z₀,z₀) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [inv_mul_cancel] using
      (matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr)
  obtain ⟨U,V,hU,hzU,hV,hzV,hUV⟩ := mem_nhds_prod_iff'.mp hball
  let D : Set (UpperRootTransverse n × UpperRootTime n) :=
    {z | ∀ i, |transverseLogDiagonal z.1 i| < 1}
  have hD : IsOpen D := by
    simp only [D,ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt
      (((continuous_apply i).comp (continuous_transverseLogDiagonal n)).comp
        continuous_fst).abs continuous_const
  have hzD : z₀ ∈ D := by
    intro i
    change |Real.log (|(1 : Matrix (Fin n) (Fin n) ℝ) i i|)| < 1
    simp
  have hnhds : U ∩ V ∩ D ∈ 𝓝 z₀ :=
    ((hU.inter hV).inter hD).mem_nhds ⟨⟨hzU,hzV⟩,hzD⟩
  obtain ⟨S,T,hS,hzS,hT,hzT,hST⟩ := mem_nhds_prod_iff'.mp hnhds
  refine ⟨S,T,hS,hT,hzS,hzT,?_,?_⟩
  · intro z hz w hw
    exact @hUV (z,w) (show (z,w) ∈ U ×ˢ V from
      ⟨(@hST z hz).1.1,(@hST w hw).1.2⟩)
  · intro z hz i
    exact ((hST hz).2 i).le

theorem exists_small_upperRootBox_at (n : ℕ) (x : X n)
    {r : ℝ} (hr : 0 < r) :
    ∃ (g : G n) (B : UpperRootBox n g), x ∈ B.range ∧
      (∀ z w : B.domain,
        (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n r) ∧
      ∀ z : B.domain, ∀ i, |transverseLogDiagonal z.val.1 i| ≤ 1 := by
  classical
  obtain ⟨S,T,hS,hT,hzS,hzT,hrel,hlog⟩ := exists_small_upperRoot_product n hr
  induction x using Quotient.inductionOn with
  | h g =>
    let z₀ := (upperRootIdentity n,(completeRootChain n).zeroTime)
    obtain ⟨B,hB⟩ := exists_upperRootBox_at_coordinates n g z₀
    let C : UpperRootBox n g := B.shrink (B.transverse ∩ S) (B.time ∩ T)
      (B.transverse_open.inter hS) (B.time_open.inter hT) inter_subset_left inter_subset_left
    refine ⟨g,C,⟨⟨z₀,⟨hB.1,hzS⟩,⟨hB.2,hzT⟩⟩,?_⟩,?_,?_⟩
    · change Quotient.mk _ (g*upperRootParam n z₀)=Quotient.mk _ g
      rw [upperRootParam_zero,mul_one]
    · intro z w
      exact hrel z.val ⟨z.prop.1.2,z.prop.2.2⟩ w.val ⟨w.prop.1.2,w.prop.2.2⟩
    · intro z i
      exact hlog z.val ⟨z.prop.1.2,z.prop.2.2⟩ i

theorem exists_countable_small_upperRoot_atlas (n : ℕ)
    {r : ℝ} (hr : 0 < r) :
    ∃ (g : ℕ → G n) (B : ∀ i, UpperRootBox n (g i)),
      (∀ x : X n, ∃ i, x ∈ (B i).range) ∧
      (∀ i, ∀ z w : (B i).domain,
        (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n r) ∧
      ∀ i, ∀ z : (B i).domain, ∀ j, |transverseLogDiagonal z.val.1 j| ≤ 1 := by
  classical
  choose g B hx hrel hlog using fun x : X n => exists_small_upperRootBox_at n x hr
  have hopen (x : X n) : IsOpen (B x).range := (B x).embedding.isOpen_range
  obtain ⟨f,hf⟩ := (HereditarilyLindelofSpace.isLindelof (univ : Set (X n))).indexed_countable_subcover
    (fun x => (B x).range) hopen (by
      intro x _
      exact mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨fun i => g (f i),fun i => B (f i),?_,fun i => hrel (f i),fun i => hlog (f i)⟩
  intro x
  exact mem_iUnion.mp (hf (mem_univ x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SparseUpperRootComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse fine returns remove the transverse part of a future lift -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma homeomorph_pow_apply_eq_iterate {Y : Type*} [TopologicalSpace Y]
    (e : Y ≃ₜ Y) (k : ℕ) (x : Y) : (e^k) x=(e : Y → Y)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ,Homeomorph.mul_apply,Function.iterate_succ_apply]
    exact ih (x := e x)

lemma diagonal_iterate_lift {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (x y : X n) (g : G n) (hg : rightAction x g=y) (k : ℕ) :
    rightAction ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)
      (diagonalOneParameter ell hell (k:ℝ)*g*diagonalOneParameter ell hell (-(k:ℝ))) =
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y := by
  rw [←hg,rightAction_iterate_conjugation,conjugation_iterate]
  congr 1
  have hp : (diagonalOneParameter ell hell (-1))^k =
      diagonalOneParameter ell hell (-(k:ℝ)) := by
    rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
  rw [hp,←diagonalOneParameter_neg,neg_neg]

theorem exists_sparse_upperRoot_comparison_oai {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (E : Set (X n)) (hE : MeasurableSet E)
    (hfree : ∀ x ∈ E, ∀ k : ℕ, 0 < k →
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x ≠ x)
    (H : X n → ℕ) (hH : Measurable H)
    (r : ℕ → ℝ) (hr : ∀ m, 0 < r m) (hr1 : ∀ m, r m ≤ 1) (hanti : Antitone r)
    (hinj : ∀ x, Set.InjOn (fun g => rightAction x g) (matrixBall n (r (H x))))
    (Q : X n → ℕ)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall n (r (H x)), rightAction x g=y ∧
        (∀ i j, ell j < ell i → g.val i j=0) ∧
        ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ)*g*
          diagonalOneParameter ell hell (-(k:ℝ)) ∈ matrixBall n
            (r (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : X n → ℕ, Measurable R ∧
      Summable (fun i => Real.negMulLog (μ.real {x | R x=i})) ∧
      (∑' i, Real.negMulLog (μ.real {x | R x=i})) < ε ∧
      ∀ᵐ x ∂μ, x ∈ E → ∀ y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y := by
  classical
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let e := rightActionHomeomorph (diagonalOneParameter ell hell (-1))
  have he (k : ℕ) (x : X n) : (e^k) x=T^[k] x := homeomorph_pow_apply_eq_iterate e k x
  choose g B hcover hrel hlog using fun m => exists_countable_small_upperRoot_atlas n (hr m)
  choose f hf hfval using fun m i => (B m i).exists_measurable_logDiagonal
  let A : ℕ → Set (X n) := fun j =>
    E ∩ {x | H x ≤ j.unpair.1} ∩ (B j.unpair.1 j.unpair.2).range
  have hA (j : ℕ) : MeasurableSet (A j) :=
    (hE.inter (hH measurableSet_Iic)).inter (B j.unpair.1 j.unpair.2).embedding.isOpen_range.measurableSet
  have hAf (j : ℕ) (x : X n) (hx : x ∈ A j) (k : ℕ) (hk : 0 < k) : (e^k) x ≠ x := by
    rw [he]
    exact hfree x hx.1.1 k hk
  have hfb (j : ℕ) (x : X n) (hx : x ∈ A j) (i : Fin n) :
      |f j.unpair.1 j.unpair.2 x i| ≤ 1 := by
    obtain ⟨z,rfl⟩ := hx.2
    rw [hfval]
    exact hlog _ _ z i
  obtain ⟨R,hR,hRs,hRent,hfine⟩ := exists_countable_sparse_fine_observation μ e hT
    A hA hAf (fun j => f j.unpair.1 j.unpair.2) (fun j => hf _ _)
    (fun _ => 1) (fun _ => zero_le_one) hfb hε
  refine ⟨R,hR,hRs,hRent,?_⟩
  filter_upwards [hfine] with x hx hxE y hQ hRxy
  obtain ⟨g₀,hg₀,hact,hzero,hsmall⟩ := hlift x y hQ
  obtain ⟨i,hi⟩ := hcover (H x) x
  let j := Nat.pair (H x) i
  have hj : j.unpair=(H x,i) := Nat.unpair_pair _ _
  have hxA : x ∈ A j := by
    change x ∈ E ∩ {x | H x ≤ j.unpair.1} ∩ (B j.unpair.1 j.unpair.2).range
    rw [hj]
    change x ∈ E ∩ {z | H z ≤ H x} ∩ (B (H x) i).range
    exact ⟨⟨hxE,by change H x ≤ H x; exact le_rfl⟩,hi⟩
  have hrxy : ∀ k : ℕ, R ((e^(k+1)) y)=R ((e^(k+1)) x) := by
    intro k
    simpa only [he] using hRxy k
  obtain ⟨u,hu⟩ := upperRootWord_of_fine_transverse_returns ell hell hord g₀
    (matrixBall_mono (hr1 _) hg₀) hzero (by
      intro η hη
      obtain ⟨k,hkx,hky,hclose⟩ := hx j hxA y hrxy η hη
      simp only [he] at hkx hky hclose
      have hkx' : T^[k+1] x ∈ A j := hkx
      have hky' : T^[k+1] y ∈ A j := hky
      rw [show A j=E ∩ {z | H z ≤ H x} ∩ (B (H x) i).range by
        dsimp only [A]; rw [hj]] at hkx' hky'
      obtain ⟨z,hz⟩ := hkx'.2
      obtain ⟨w,hw⟩ := hky'.2
      have hlocal : (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈
          matrixBall n (r (H (T^[k+1] x))) :=
        matrixBall_mono (hanti hkx'.1.2) (hrel (H x) i z w)
      have halign := upperRootBox_lift_alignment (B (H x) i) z w
        (r (H (T^[k+1] x))) (by simpa only [hz] using hinj (T^[k+1] x)) hlocal
        _ (hsmall (k+1)) (by
          rw [hz,hw]
          exact diagonal_iterate_lift ell hell x y g₀ hact (k+1))
      refine ⟨k+1,z.val.1,w.val.1,z.val.2,w.val.2,halign,?_⟩
      intro a
      have hh := hclose a
      simpa only [hj,Prod.fst,Prod.snd,←hz,←hw,hfval] using hh)
  exact ⟨u,by rw [hu]; exact hact⟩

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison_oai := @OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison_oai
