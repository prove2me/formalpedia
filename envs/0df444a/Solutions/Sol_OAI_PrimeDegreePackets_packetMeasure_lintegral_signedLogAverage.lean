-- Prove2me | solution 1 for OAI.PrimeDegreePackets.packetMeasure_lintegral_signedLogAverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:40.463729+00:00
-- url     : https://prove2.me/submissions/036fa6e2-5675-4236-a5b0-7bd0b003261c

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

open scoped NumberField Pointwise nonZeroDivisors
open NumberField



theorem finite_completedModule_interval
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    {N : Submodule (PadicInt p) (LocalAlgebra p K) |
      N ≤ completedLattice p M ∧ ∀ x ∈ completedLattice p M,
        (p : PadicInt p)^k • x ∈ N}.Finite := by
  classical
  let f : Submodule (PadicInt p) (LocalAlgebra p K) →
      AddSubgroup (Fin n → ZMod (p^k)) := fun N =>
    (N.comap (completedLattice p M).subtype).toAddSubgroup.map (completedReduction M hn p k)
  apply Set.Finite.of_finite_image (Set.toFinite (f '' _))
  intro L hL N hN he
  have hmem (P : Submodule (PadicInt p) (LocalAlgebra p K))
      (hP : ∀ x ∈ completedLattice p M, (p : PadicInt p)^k • x ∈ P)
      (x : completedLattice p M) :
      completedReduction M hn p k x ∈ f P ↔ (x : LocalAlgebra p K) ∈ P :=
    completedReduction_mem_image_iff M hn p k (P.comap (completedLattice p M).subtype)
      (fun y => hP y y.property) x
  ext x
  by_cases hx : x ∈ completedLattice p M
  · rw [← hmem L hL.2 ⟨x,hx⟩,← hmem N hN.2 ⟨x,hx⟩,he]
  · exact iff_of_false (fun h => hx (hL.1 h)) (fun h => hx (hN.1 h))

 
theorem localModuleChoices_finite
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] :
    (localModuleChoices M I p).Finite := by
  apply (finite_completedModule_interval (fractionalIdealFullLattice hn I) hn p
    ((saturationIndex M).factorization p)).subset
  intro N hN
  exact ⟨localModuleChoices_le M I p hN,
    fun x hx => localModuleChoices_primePower_mem M hn I p hN hx⟩

theorem globalLabels_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (globalLabels M I).Finite := by
  let (p : labelPrimes M) : Finite (localModuleChoices M I p.val) :=
    (localModuleChoices_finite M hn I p.val).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective _ (globalLabelCompletions_injective M hn I))


open Topology
open scoped Pointwise

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


open MeasureTheory
open scoped ENNReal

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationPreservesVolume _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors

 

theorem multiplierOrder_le_integralElements {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : multiplierOrder M ≤ integralElements K := by
  intro a ha
  have hne : M.carrier ≠ ⊥ := by
    intro h
    have H : (⊥ : Submodule ℚ K) = ⊤ := by simpa [h] using M.spans
    exact bot_ne_top H
  have hfg : M.carrier.FG := by
    rw [← fullLattice_span_basis M]
    exact Submodule.fg_span (Set.finite_range _)
  exact isIntegral_of_smul_mem_submodule M.carrier hne hfg a ha



lemma orbitVolume_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : orbitVolume x = orbitVolume y := by
  unfold orbitVolume
  rw [periodGroup_eq_of_diagonalOrbit_eq h]

 

lemma map_orbitMap_restrict_eq {d : ℕ} (x : X (d + 1))
    {s t : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain (periodGroup x) s volume)
    (ht : IsAddFundamentalDomain (periodGroup x) t volume) :
    Measure.map (orbitMap x) (volume.restrict s) =
      Measure.map (orbitMap x) (volume.restrict t) := by
  have : Countable (periodGroup x) := countable_of_Lindelof_of_discrete
  ext A hA
  rw [Measure.map_apply (continuous_orbitMap x).measurable hA,
    Measure.map_apply (continuous_orbitMap x).measurable hA,
    Measure.restrict_apply (hA.preimage (continuous_orbitMap x).measurable),
    Measure.restrict_apply (hA.preimage (continuous_orbitMap x).measurable)]
  apply hs.measure_set_eq ht (hA.preimage (continuous_orbitMap x).measurable)
  intro u
  ext v
  change orbitMap x (u.1 + v) ∈ A ↔ orbitMap x v ∈ A
  rw [orbitMap_add, (show orbitMap x u.1 = x from u.property)]

lemma map_orbitMap_add_restrict_eq {d : ℕ} (x : X (d + 1))
    {s : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain (periodGroup x) s volume) (u : LogCoordinates d) :
    Measure.map (fun v => orbitMap x (u + v)) (volume.restrict s) =
      Measure.map (orbitMap x) (volume.restrict s) := by
  have htrans := (measurePreserving_add_left (volume : Measure (LogCoordinates d)) u).restrict_image_emb (MeasurableEquiv.addLeft u).measurableEmbedding s
  have ht : IsAddFundamentalDomain (periodGroup x) ((fun v => u + v) '' s) volume :=
    hs.vadd_of_comm u
  calc
    _ = Measure.map (orbitMap x)
        (Measure.map (fun v => u + v) (volume.restrict s)) := by
      have ha : Measurable (fun v : LogCoordinates d => u + v) :=
        measurable_const.add measurable_id
      exact (Measure.map_map (continuous_orbitMap x).measurable ha).symm
    _ = Measure.map (orbitMap x) (volume.restrict ((fun v => u + v) '' s)) := by
      rw [htrans.map_eq]
    _ = _ := map_orbitMap_restrict_eq x ht hs



theorem orbitalHaar_orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    orbitalHaar (orbitMap x u) = orbitalHaar x := by
  have H : orbitMap (orbitMap x u) = fun v => orbitMap x (u + v) := by
    funext v
    exact (orbitMap_add x u v).symm
  by_cases hx : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume
  · have hy : HasAddFundamentalDomain (periodGroup (orbitMap x u)) (LogCoordinates d) volume := by
      rw [periodGroup_orbitMap]
      exact hx
    rw [orbitalHaar, dite_eq_left hy, orbitalHaar, dite_eq_left hx, H]
    have hs : IsAddFundamentalDomain (periodGroup x) hy.ExistsIsAddFundamentalDomain.choose volume := by
      have transport (P Q : AddSubgroup (LogCoordinates d)) (h : P = Q)
          (s : Set (LogCoordinates d)) : IsAddFundamentalDomain P s volume →
            IsAddFundamentalDomain Q s volume := by
        subst Q
        exact id
      exact transport _ _ (periodGroup_orbitMap x u) _ hy.ExistsIsAddFundamentalDomain.choose_spec
    exact (map_orbitMap_add_restrict_eq x hs u).trans
      (map_orbitMap_restrict_eq x hs hx.ExistsIsAddFundamentalDomain.choose_spec)
  · have hy : ¬ HasAddFundamentalDomain (periodGroup (orbitMap x u)) (LogCoordinates d) volume := by
      rwa [periodGroup_orbitMap]
    rw [orbitalHaar, dite_eq_right hy, orbitalHaar, dite_eq_right hx]

 

theorem orbitalHaar_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : orbitalHaar x = orbitalHaar y := by
  have hx := mem_diagonalOrbit_self x
  rw [h] at hx
  obtain ⟨u, rfl⟩ := hx
  exact orbitalHaar_orbitMap y u

theorem orbitProbability_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : orbitProbability x = orbitProbability y := by
  simp only [orbitProbability, orbitalHaar_eq_of_diagonalOrbit_eq h,
    orbitVolume_eq_of_diagonalOrbit_eq h]



open scoped Pointwise



open FractionalIdeal



lemma normalizedLattice_diagonal_invariant_iff
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (t : Fin n → ℝ) :
    (normalizedLattice M σ).map (diagonalLinear n t) = normalizedLattice M σ ↔
      (M.carrier.map (realEmbeddingMap σ)).map (diagonalLinear n t) =
        M.carrier.map (realEmbeddingMap σ) := by
  let c : ℝ := |(embeddingMatrix M σ).det| ^ (-(1 : ℝ) / n)
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr
    (embeddingMatrix_det_ne_zero M σ hn)) _).ne'
  have hinj : Function.Injective (diagonalLinear n (fun _ => c)) := by
    intro x y h
    ext i
    exact mul_left_cancel₀ hc (congrFun h i)
  unfold normalizedLattice
  rw [rowLattice_smul,rowLattice_embeddingMatrix,← Submodule.map_comp,
    diagonalLinear_commute,Submodule.map_comp]
  exact (Submodule.map_injective_of_injective hinj).eq_iff

 

lemma exists_integralUnit_of_carrier_preserving
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (b : K) (hb : b ≠ 0)
    (h : ∀ x : K, x ∈ M.carrier ↔ b * x ∈ M.carrier) :
    ∃ u : (𝓞 K)ˣ, (u : K) = b ∧ u ∈ unitStabilizer M := by
  have hbi : IsIntegral ℤ b := multiplierOrder_le_integralElements M
    (fun x hx => (h x).mp hx)
  have hbinv : IsIntegral ℤ b⁻¹ := multiplierOrder_le_integralElements M (x := b⁻¹)
    (fun x hx => (h (b⁻¹*x)).mpr (by simpa [← mul_assoc,hb] using hx))
  let u : (𝓞 K)ˣ :=
    ⟨⟨b,hbi⟩,⟨b⁻¹,hbinv⟩,by ext; exact mul_inv_cancel₀ hb,
      by ext; exact inv_mul_cancel₀ hb⟩
  exact ⟨u,rfl,h⟩

 

theorem periodGroup_le_orderedLogSubgroup
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    periodGroup (latticePoint M σ) ≤
      (orderedLogSubgroup σ (positiveUnitStabilizer M σ)).toAddSubgroup := by
  intro v hv
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  have he : rowLattice (g.1 * (diagonalFlow v).1) = rowLattice g.1 := by
    apply (quotient_eq_iff_rowLattice_eq (g * diagonalFlow v) g).mp
    change orbitMap (Quotient.mk _ g) v = Quotient.mk _ g
    rw [← latticePoint_eq_of_rowLattice_eq M σ g hg]
    exact hv
  let t : Fin (d+1) → ℝ := Fin.snoc (fun i : Fin d => Real.exp (v i)) (Real.exp (-∑ i, v i))
  change rowLattice (g.1 * Matrix.diagonal t) = rowLattice g.1 at he
  rw [rowLattice_mul_diagonal,hg] at he
  have hraw := (normalizedLattice_diagonal_invariant_iff M σ hn t).mp he
  have ht (i : Fin (d+1)) : 0 < t i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [t,Fin.snoc_last,Fin.snoc_castSucc] <;>
      exact Real.exp_pos _
  obtain ⟨b,hb,hbt,hset⟩ := diagonal_lattice_equality_iff_homothety M M σ
    (Nat.succ_pos d) t (fun i => (ht i).ne') (by rw [Submodule.map_comp]; exact hraw)
  have hpres (x : K) : x ∈ M.carrier ↔ b*x ∈ M.carrier := by
    constructor
    · intro hx
      change b*x ∈ (M.carrier : Set K)
      rw [hset]
      exact ⟨x,hx,rfl⟩
    · intro hx
      change b*x ∈ (M.carrier : Set K) at hx
      rw [hset] at hx
      obtain ⟨y,hy,he⟩ := hx
      exact (mul_left_cancel₀ hb he) ▸ hy
  obtain ⟨u,hu,hust⟩ := exists_integralUnit_of_carrier_preserving M b hb hpres
  apply (mem_orderedLogSubgroup σ _ v).mpr
  refine ⟨u,(mem_positiveUnitStabilizer M σ u).mpr ⟨hust,?_⟩,?_⟩
  · intro i
    change 0 < σ i (u : K)
    rw [hu,← hbt i]
    exact ht i
  · ext i
    rw [orderedUnitLog_apply,hu,← hbt i.castSucc]
    simp only [t,Fin.snoc_castSucc,abs_of_pos (Real.exp_pos _),Real.log_exp]

 

theorem periodGroup_eq_orderedLogSubgroup
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    periodGroup (latticePoint M σ) =
      (orderedLogSubgroup σ (positiveUnitStabilizer M σ)).toAddSubgroup :=
  le_antisymm (periodGroup_le_orderedLogSubgroup M σ hn hodd)
    (orderedLogSubgroup_le_periodGroup M σ hn hodd)

lemma orderedLogSubgroup_toAddSubgroup
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ) :
    (orderedLogSubgroup σ S).toAddSubgroup = S.toAddSubgroup.map (orderedUnitLog σ) := by
  ext v
  rw [Submodule.mem_toAddSubgroup,mem_orderedLogSubgroup]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨Additive.ofMul u,hu,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.toMul,hu,rfl⟩

lemma orderedUnitLog_ker
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLog σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [← NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
  ext u
  change orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K u) = 0 ↔ _
  exact EmbeddingLike.map_eq_zero_iff

 

theorem orderedLogSubgroup_relIndex
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (S T : Subgroup (𝓞 K)ˣ) :
    (orderedLogSubgroup σ S).toAddSubgroup.relIndex (orderedLogSubgroup σ T).toAddSubgroup =
      (S ⊔ NumberField.Units.torsion K).relIndex (T ⊔ NumberField.Units.torsion K) := by
  rw [orderedLogSubgroup_toAddSubgroup,orderedLogSubgroup_toAddSubgroup,
    AddSubgroup.relIndex_map_map,orderedUnitLog_ker,← OrderIso.map_sup,
    ← OrderIso.map_sup,Subgroup.relIndex_toAddSubgroup]

theorem orderedLogSubgroup_covolume_ratio
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] :
    ZLattice.covolume (orderedLogSubgroup σ S) /
      ZLattice.covolume (orderedLogSubgroup σ ⊤) =
      ((S ⊔ NumberField.Units.torsion K).index : ℝ) := by
  have hle : orderedLogSubgroup σ S ≤ orderedLogSubgroup σ ⊤ := by
    intro v hv
    obtain ⟨u,_,rfl⟩ := (mem_orderedLogSubgroup σ S v).mp hv
    exact (mem_orderedLogSubgroup σ ⊤ _).mpr ⟨u,Subgroup.mem_top u,rfl⟩
  rw [ZLattice.covolume_div_covolume_eq_relIndex _ _ hle,
    orderedLogSubgroup_relIndex,top_sup_eq,Subgroup.relIndex_top_right]

 

theorem orbitVolume_latticePoint_ratio
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    (orbitVolume (latticePoint M σ)).toReal /
      ZLattice.covolume (orderedLogSubgroup σ ⊤) =
      (((positiveUnitStabilizer M σ ⊔ NumberField.Units.torsion K).index) : ℝ) := by
  let := positiveUnitStabilizer_finiteIndex M σ
  rw [orbitVolume,periodGroup_eq_orderedLogSubgroup M σ hn hodd]
  exact orderedLogSubgroup_covolume_ratio σ (positiveUnitStabilizer M σ)

lemma compact_quotient_of_isZLattice {d : ℕ} (P : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P] :
    CompactSpace ((Fin d → ℝ) ⧸ P.toAddSubgroup) := by
  constructor
  rw [← Set.range_eq_univ.mpr (@QuotientAddGroup.mk_surjective _ _ P.toAddSubgroup)]
  apply IsZLattice.isCompact_range_of_periodic P
    (QuotientAddGroup.mk : (Fin d → ℝ) → (Fin d → ℝ) ⧸ P.toAddSubgroup)
    QuotientAddGroup.continuous_mk
  intro x p hp
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  simpa using hp

lemma map_quotient_restrict_eq {d : ℕ} (P L : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [DiscreteTopology L] (hLP : L ≤ P)
    {s t : Set (Fin d → ℝ)} (hs : IsAddFundamentalDomain L s volume)
    (ht : IsAddFundamentalDomain L t volume) :
    Measure.map (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) (volume.restrict s) =
      Measure.map QuotientAddGroup.mk (volume.restrict t) := by
  have : Countable L := countable_of_Lindelof_of_discrete
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  have hm : Measurable (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) :=
    QuotientAddGroup.continuous_mk.measurable
  ext A hA
  rw [Measure.map_apply hm hA,Measure.map_apply hm hA,
    Measure.restrict_apply (hA.preimage hm),Measure.restrict_apply (hA.preimage hm)]
  apply hs.measure_set_eq ht (hA.preimage hm)
  intro u
  ext v
  change (QuotientAddGroup.mk (u.val + v) : (Fin d → ℝ) ⧸ P.toAddSubgroup) ∈ A ↔ _
  have he : (QuotientAddGroup.mk (u.val + v) : (Fin d → ℝ) ⧸ P.toAddSubgroup) =
      QuotientAddGroup.mk v := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa using hLP u.property
  rw [he]
  rfl

lemma normalizedLatticeQuotientMeasure_invariant {d : ℕ}
    (P L : Submodule ℤ (Fin d → ℝ)) [DiscreteTopology P] [DiscreteTopology L]
    (hLP : L ≤ P) {s : Set (Fin d → ℝ)} (hs : IsAddFundamentalDomain L s volume) :
    (normalizedLatticeQuotientMeasure P s).IsAddLeftInvariant := by
  constructor
  intro a
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective a
  have hm : Measurable (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) :=
    QuotientAddGroup.continuous_mk.measurable
  have hmu : Measurable (fun v : Fin d → ℝ => u + v) := measurable_const.add measurable_id
  have htrans := (measurePreserving_add_left (volume : Measure (Fin d → ℝ)) u).restrict_image_emb
    (MeasurableEquiv.addLeft u).measurableEmbedding s
  have ht : IsAddFundamentalDomain L ((fun v => u + v) '' s) volume := hs.vadd_of_comm u
  unfold normalizedLatticeQuotientMeasure
  have hadd : Measurable (fun a : (Fin d → ℝ) ⧸ P.toAddSubgroup => QuotientAddGroup.mk u + a) :=
    (continuous_const_add _).measurable
  rw [Measure.map_smul, Measure.map_map hadd hm]
  have he : (fun a : (Fin d → ℝ) ⧸ P.toAddSubgroup => QuotientAddGroup.mk u + a) ∘
      QuotientAddGroup.mk = QuotientAddGroup.mk ∘ (fun v : Fin d → ℝ => u+v) := by
    funext v
    exact (map_add (QuotientAddGroup.mk' P.toAddSubgroup) u v).symm
  rw [he,← Measure.map_map hm hmu,htrans.map_eq,map_quotient_restrict_eq P L hLP ht hs]

lemma normalizedLatticeQuotientMeasure_probability {d : ℕ}
    (P L : Submodule ℤ (Fin d → ℝ)) [DiscreteTopology P] [DiscreteTopology L]
    [IsZLattice ℝ L] {s : Set (Fin d → ℝ)} (hs : IsAddFundamentalDomain L s volume) :
    IsProbabilityMeasure (normalizedLatticeQuotientMeasure P s) := by
  have hvol : volume s ≠ 0 ∧ volume s ≠ ⊤ := by
    have h := ZLattice.covolume_ne_zero L volume
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hs] at h
    exact ENNReal.toReal_ne_zero.mp h
  constructor
  rw [normalizedLatticeQuotientMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply QuotientAddGroup.continuous_mk.measurable MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  exact ENNReal.inv_mul_cancel hvol.1 hvol.2

 

theorem normalizedLatticeQuotientMeasure_eq {d : ℕ}
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume) :
    normalizedLatticeQuotientMeasure P s = normalizedLatticeQuotientMeasure P t := by
  let := compact_quotient_of_isZLattice P
  let := normalizedLatticeQuotientMeasure_invariant P L hLP hs
  let := normalizedLatticeQuotientMeasure_invariant P L' hL'P ht
  let := normalizedLatticeQuotientMeasure_probability P L hs
  let := normalizedLatticeQuotientMeasure_probability P L' ht
  have haar (U : Measure ((Fin d → ℝ) ⧸ P.toAddSubgroup))
      [U.IsAddLeftInvariant] [IsProbabilityMeasure U] : U.IsAddHaarMeasure := by
    apply Measure.isAddHaarMeasure_of_isCompact_nonempty_interior U Set.univ
      isCompact_univ (by simp) <;> simp
  let := haar (normalizedLatticeQuotientMeasure P s)
  let := haar (normalizedLatticeQuotientMeasure P t)
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

 

theorem normalized_periodic_map_eq {d : ℕ} {Y : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume)
    (f : (Fin d → ℝ) → Y) (hf : Continuous f)
    (hper : ∀ x p, p ∈ P → f (p+x) = f x) :
    (volume s)⁻¹ • Measure.map f (volume.restrict s) =
      (volume t)⁻¹ • Measure.map f (volume.restrict t) := by
  let F : ((Fin d → ℝ) ⧸ P.toAddSubgroup) → Y := Quotient.lift f (by
    intro u v huv
    have hmem : v-u ∈ P := by
      have h0 := QuotientAddGroup.leftRel_apply.mp huv
      rw [Submodule.mem_toAddSubgroup] at h0
      simpa only [sub_eq_neg_add] using h0
    simpa using (hper u (v-u) hmem).symm)
  have hF : Continuous F := (QuotientAddGroup.isQuotientMap_mk P.toAddSubgroup).continuous_iff.mpr hf
  have h := congrArg (Measure.map F) (normalizedLatticeQuotientMeasure_eq P L L' hLP hL'P hs ht)
  have he : F ∘ (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) = f := rfl
  simpa only [normalizedLatticeQuotientMeasure,Measure.map_smul,
    Measure.map_map hF.measurable QuotientAddGroup.continuous_mk.measurable,he] using h



theorem orbitProbability_eq_normalized_map_sublattice {d : ℕ}
    (x : X (d+1)) [IsZLattice ℝ (periodGroup x).toIntSubmodule]
    (L : Submodule ℤ (LogCoordinates d)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hLP : L ≤ (periodGroup x).toIntSubmodule) {s : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain L s volume) :
    orbitProbability x = (volume s)⁻¹ • Measure.map (orbitMap x) (volume.restrict s) := by
  have : Countable (periodGroup x) := countable_of_Lindelof_of_discrete
  let hF := periodGroup_hasFundamentalDomain x
  let t := hF.ExistsIsAddFundamentalDomain.choose
  have ht : IsAddFundamentalDomain (periodGroup x) t volume :=
    hF.ExistsIsAddFundamentalDomain.choose_spec
  have hv : orbitVolume x = volume t := ht.covolume_eq_volume volume
  rw [orbitProbability,hv,orbitalHaar,dite_eq_left hF]
  apply normalized_periodic_map_eq (periodGroup x).toIntSubmodule
    (periodGroup x).toIntSubmodule L le_rfl hLP ht hs (orbitMap x) (continuous_orbitMap x)
  intro u p hp
  rw [orbitMap_add,(show orbitMap x p = x from hp)]



lemma unit_smul_globalLabel_eq_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) (u : (𝓞 K)ˣ) :
    u • N = N ↔ u ∈ unitStabilizer (globalLabelLattice M I N) := by
  rw [Subtype.ext_iff, globalLabels_smul_val, ← (globalLabelLattice_spec M I N).1]
  let A := globalLabelLattice M I N
  change u • A.carrier = A.carrier ↔ ∀ x : K, x ∈ A.carrier ↔ (u : K) * x ∈ A.carrier
  rw [Units.smul_def]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,hx,rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y,hy,he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      have hxy : y = x := mul_left_cancel₀ (integralUnit u).ne_zero he
      exact hxy ▸ hy
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      exact (h y).mp hy
    · intro hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨(u⁻¹ : K)*x,?_,?_⟩
      · apply (h _).mpr
        simpa [← mul_assoc] using hx
      · change (u : K) * ((u⁻¹ : K)*x) = x
        simp

 

theorem signedGlobalLabel_stabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : SignedGlobalLabel M I) :
    let := signedGlobalLabelMulAction M σ I
    MulAction.stabilizer (𝓞 K)ˣ x = positiveUnitStabilizer (globalLabelLattice M I x.lattice) σ := by
  let := signedGlobalLabelMulAction M σ I
  ext u
  change (⟨u • x.lattice,(unitSigns σ u)⁻¹ * x.signs⟩ : SignedGlobalLabel M I) = x ↔ _
  rw [show (⟨u • x.lattice,(unitSigns σ u)⁻¹ * x.signs⟩ : SignedGlobalLabel M I) = x ↔
      u • x.lattice = x.lattice ∧ (unitSigns σ u)⁻¹*x.signs = x.signs from by
        constructor
        · intro h; exact ⟨congrArg SignedGlobalLabel.lattice h,congrArg SignedGlobalLabel.signs h⟩
        · rintro ⟨hN,hw⟩; exact SignedGlobalLabel.ext hN hw]
  simp only [unit_smul_globalLabel_eq_iff, _root_.mul_eq_right, inv_eq_one]
  rfl

theorem signedGlobalLabel_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Finite (SignedGlobalLabel M I) := by
  let := (globalLabels_finite M hn I).to_subtype
  exact Finite.of_injective (fun x : SignedGlobalLabel M I => (x.lattice,x.signs)) (by
    intro x y h; exact SignedGlobalLabel.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma positiveUnitStabilizer_inf_torsion {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    positiveUnitStabilizer N σ ⊓ NumberField.Units.torsion K = ⊥ := by
  ext u
  constructor
  · rintro ⟨hu,ht⟩
    rcases NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank (by simpa only [hn] using hodd) ⟨u,ht⟩ with h | h
    · exact h
    · change u = -1 at h
      have hp := ((mem_positiveUnitStabilizer N σ u).mp hu).2 (0 : Fin (d+1))
      simp [h,integralUnit] at hp
      norm_num at hp
  · intro hu
    rw [Subgroup.mem_bot] at hu
    subst u
    exact one_mem _

 

theorem positiveUnitStabilizer_index_eq_twice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    (positiveUnitStabilizer N σ).index =
      2 * (positiveUnitStabilizer N σ ⊔ NumberField.Units.torsion K).index := by
  have hidx : (positiveUnitStabilizer N σ).relIndex (NumberField.Units.torsion K) = 2 := by
    rw [← Subgroup.inf_relIndex_right,positiveUnitStabilizer_inf_torsion N σ hn hodd,
      Subgroup.relIndex_bot_left]
    exact NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by simpa only [hn] using hodd)
  have h := Subgroup.relIndex_mul_index (show positiveUnitStabilizer N σ ≤
    positiveUnitStabilizer N σ ⊔ NumberField.Units.torsion K from le_sup_left)
  rw [Subgroup.relIndex_sup_left,hidx] at h
  exact h.symm

lemma allSignedGlobalLabel_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) : Finite (AllSignedGlobalLabel M) := by
  let (c : ClassGroup (𝓞 K)) := signedGlobalLabel_finite M hn (classRepresentative K c)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma finite_orbitFiber_card {G α : Type*} [Group G] [MulAction G α] [Fintype α]
    (q : MulAction.orbitRel.Quotient G α) :
    Fintype.card {x : α // (Quotient.mk'' x : MulAction.orbitRel.Quotient G α) = q} =
      (MulAction.stabilizer G q.out).index := by
  have he : {x : α | (Quotient.mk'' x : MulAction.orbitRel.Quotient G α) = q} =
      MulAction.orbit G q.out := by
    ext x
    rw [← MulAction.orbitRel_apply,← Quotient.eq'',Quotient.out_eq']
    rfl
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.setCongr he)).trans (MulAction.index_stabilizer G q.out).symm

 

theorem sum_orbits_index_nsmul {G α A : Type*} [Group G] [MulAction G α]
    [Fintype α] [AddCommMonoid A] (f : MulAction.orbitRel.Quotient G α → A) :
    ∑ q, (MulAction.stabilizer G q.out).index • f q =
      ∑ x : α, f (Quotient.mk'' x) := by
  classical
  rw [← Fintype.sum_fiberwise (fun x : α => (Quotient.mk'' x : MulAction.orbitRel.Quotient G α))]
  apply Finset.sum_congr rfl
  intro q _
  have hi (x : {x : α // (Quotient.mk'' x : MulAction.orbitRel.Quotient G α) = q}) :
      f (Quotient.mk'' x.val) = f q := congrArg f x.property
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, finite_orbitFiber_card]

lemma sum_orbits_index_eq_card {G α : Type*} [Group G] [MulAction G α] [Fintype α] :
    ∑ q : MulAction.orbitRel.Quotient G α, (MulAction.stabilizer G q.out).index =
      Fintype.card α := by
  simpa using sum_orbits_index_nsmul (G := G) (α := α)
    (fun _ : MulAction.orbitRel.Quotient G α => (1 : ℕ))

 

theorem sum_orbits_index_smul_measure {G α Y : Type*} [Group G] [MulAction G α]
    [Fintype α] [MeasurableSpace Y] (orbitMeasures : MulAction.orbitRel.Quotient G α → Measure Y) :
    ∑ q, ((MulAction.stabilizer G q.out).index : ℝ≥0∞) • orbitMeasures q =
      ∑ x : α, orbitMeasures (Quotient.mk'' x) := by
  simpa only [Nat.cast_smul_eq_nsmul ℝ≥0∞] using sum_orbits_index_nsmul orbitMeasures

lemma allSignedGlobalLabel_stabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    MulAction.stabilizer (𝓞 K)ˣ x =
      positiveUnitStabilizer (globalLabelLattice M (classRepresentative K x.1) x.2.lattice) σ := by
  let := allSignedGlobalLabelMulAction M σ
  let := signedGlobalLabelMulAction M σ (classRepresentative K x.1)
  rw [← signedGlobalLabel_stabilizer M σ (classRepresentative K x.1) x.2]
  ext u
  change Sigma.mk x.1 (u • x.2) = x ↔ u • x.2 = x.2
  exact Sigma.mk.inj_iff.trans (by simp)

lemma signedPacketOrbitEquiv_mk {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    signedPacketOrbitEquiv M σ hn hodd (Quotient.mk'' x) = allSignedGlobalLabelOrbit M σ hodd x := rfl

lemma allSignedGlobalLabel_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    orbitVolume (allSignedGlobalLabelPoint M σ hodd x) =
      ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤) / 2) *
        (MulAction.stabilizer (𝓞 K)ˣ x).index := by
  let := allSignedGlobalLabelMulAction M σ
  let N := globalLabelLattice M (classRepresentative K x.1) x.2.lattice
  have he : orbitVolume (allSignedGlobalLabelPoint M σ hodd x) = orbitVolume (latticePoint N σ) := by
    change orbitVolume (rightAction (latticePoint N σ) (positiveSignMatrix hodd x.2.signs)) = _
    unfold orbitVolume
    rw [periodGroup_rightAction_of_diagonal _ _ (positiveSignMatrix_diagonal hodd x.2.signs)]
  rw [he,allSignedGlobalLabel_stabilizer]
  have hp : 0 < ZLattice.covolume (orderedLogSubgroup σ ⊤) := ZLattice.covolume_pos (orderedLogSubgroup σ ⊤)
  have hv := orbitVolume_latticePoint_ratio N σ hn hodd
  have hi := positiveUnitStabilizer_index_eq_twice N σ hn hodd
  have hr : (orbitVolume (latticePoint N σ)).toReal =
      (ZLattice.covolume (orderedLogSubgroup σ ⊤) / 2) * ((positiveUnitStabilizer N σ).index : ℝ) := by
    rw [hi]
    push_cast
    rw [div_eq_iff hp.ne'] at hv
    nlinarith
  have ht : orbitVolume (latticePoint N σ) ≠ ⊤ := by
    let := latticePoint_period_isZLattice N σ hn hodd
    exact (orbitVolume_ne_zero_ne_top _).2
  apply (ENNReal.toReal_eq_toReal_iff' ht (by finiteness)).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_natCast]
  exact hr

lemma signedPacketOrbitEquiv_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    letI := allSignedGlobalLabelMulAction M σ
    ∀ q : MulAction.orbitRel.Quotient (𝓞 K)ˣ (AllSignedGlobalLabel M),
    orbitVolume (orbitBasepoint (signedPacketOrbitEquiv M σ hn hodd q)) =
      ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤) / 2) *
        (MulAction.stabilizer (𝓞 K)ˣ q.out).index := by
  let := allSignedGlobalLabelMulAction M σ
  intro q
  have he : diagonalOrbit (orbitBasepoint (signedPacketOrbitEquiv M σ hn hodd q)) =
      diagonalOrbit (allSignedGlobalLabelPoint M σ hodd q.out) := by
    rw [orbitBasepoint_spec]
    change _ = (allSignedGlobalLabelOrbit M σ hodd q.out).val
    rw [← signedPacketOrbitEquiv_mk M σ hn hodd,Quotient.out_eq']
  rw [orbitVolume_eq_of_diagonalOrbit_eq he]
  exact allSignedGlobalLabel_volume M σ hn hodd q.out

lemma signedPacketOrbitEquiv_probability_mk {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    orbitProbability (orbitBasepoint (signedPacketOrbitEquiv M σ hn hodd (Quotient.mk'' x))) =
      orbitProbability (allSignedGlobalLabelPoint M σ hodd x) := by
  let := allSignedGlobalLabelMulAction M σ
  apply orbitProbability_eq_of_diagonalOrbit_eq
  rw [signedPacketOrbitEquiv_mk,orbitBasepoint_spec]
  rfl

 

theorem packetVolume_eq_signedLabelCount {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    ∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O) =
      ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤)/2) * Nat.card (AllSignedGlobalLabel M) := by
  let := allSignedGlobalLabelMulAction M σ
  let := allSignedGlobalLabel_finite M hn
  let := Fintype.ofFinite (AllSignedGlobalLabel M)
  let := (packetOrbits_finite M σ hn hodd).fintype
  rw [← (signedPacketOrbitEquiv M σ hn hodd).tsum_eq]
  simp_rw [signedPacketOrbitEquiv_volume M σ hn hodd]
  rw [ENNReal.tsum_mul_left,tsum_fintype,← Nat.cast_sum,sum_orbits_index_eq_card,Nat.card_eq_fintype_card]

 

theorem packetMeasure_eq_signedLabelAverage {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    packetMeasure M σ = (Nat.card (AllSignedGlobalLabel M) : ℝ≥0∞)⁻¹ •
      Measure.sum (fun x : AllSignedGlobalLabel M => orbitProbability (allSignedGlobalLabelPoint M σ hodd x)) := by
  let := allSignedGlobalLabelMulAction M σ
  let := allSignedGlobalLabel_finite M hn
  let := Fintype.ofFinite (AllSignedGlobalLabel M)
  let := (packetOrbits_finite M σ hn hodd).fintype
  let e := signedPacketOrbitEquiv M σ hn hodd
  let r := ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤)/2)
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.mpr (by exact div_pos (ZLattice.covolume_pos (orderedLogSubgroup σ ⊤)) (by norm_num))).ne'
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum : Measure.sum (fun O : packetOrbits M σ =>
      orbitVolume (orbitBasepoint O) • orbitProbability (orbitBasepoint O)) =
      r • Measure.sum (fun x : AllSignedGlobalLabel M => orbitProbability (allSignedGlobalLabelPoint M σ hodd x)) := by
    rw [Measure.sum_fintype,← e.sum_comp]
    dsimp only [e]
    simp_rw [signedPacketOrbitEquiv_volume M σ hn hodd,mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    rw [sum_orbits_index_smul_measure,Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro x _
    exact signedPacketOrbitEquiv_probability_mk M σ hn hodd x
  rw [packetMeasure,hsum,packetVolume_eq_signedLabelCount M σ hn hodd]
  change (r * (Nat.card (AllSignedGlobalLabel M) : ℝ≥0∞))⁻¹ • (r • _) = _
  rw [smul_smul,ENNReal.mul_inv (Or.inl hr0) (Or.inl hrt)]
  rw [mul_right_comm,ENNReal.inv_mul_cancel hr0 hrt,one_mul]

 

theorem normalized_measurable_periodic_map_eq {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume)
    (f : (Fin d → ℝ) → Y) (hf : Measurable f)
    (hper : ∀ x p, p ∈ P → f (p+x) = f x) :
    (volume s)⁻¹ • Measure.map f (volume.restrict s) =
      (volume t)⁻¹ • Measure.map f (volume.restrict t) := by
  let F : ((Fin d → ℝ) ⧸ P.toAddSubgroup) → Y := Quotient.lift f (by
    intro u v huv
    have hmem : v-u ∈ P := by
      have h0 := QuotientAddGroup.leftRel_apply.mp huv
      rw [Submodule.mem_toAddSubgroup] at h0
      simpa only [sub_eq_neg_add] using h0
    simpa using (hper u (v-u) hmem).symm)
  have hF : Measurable F := measurable_from_quotient.mpr hf
  have h := congrArg (Measure.map F) (normalizedLatticeQuotientMeasure_eq P L L' hLP hL'P hs ht)
  have he : F ∘ (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) = f := rfl
  simpa only [normalizedLatticeQuotientMeasure,Measure.map_smul,
    Measure.map_map hF QuotientAddGroup.continuous_mk.measurable,he] using h

 

theorem normalized_periodic_lintegral_eq {d : ℕ}
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hper : ∀ x p, p ∈ P → f (p+x) = f x) :
    (volume s)⁻¹ * ∫⁻ x in s, f x = (volume t)⁻¹ * ∫⁻ x in t, f x := by
  have h := congrArg (fun measure : Measure ℝ≥0∞ => ∫⁻ x, x ∂measure)
    (normalized_measurable_periodic_map_eq P L L' hLP hL'P hs ht f hf hper)
  simp only [lintegral_smul_measure,smul_eq_mul] at h
  rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hf,lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hf] at h
  exact h



lemma packetUnitKernel_finiteIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) :
    (packetUnitKernel M σ).FiniteIndex := by
  let := allSignedGlobalLabelMulAction M σ
  let := allSignedGlobalLabel_finite M hn
  change (MulAction.toPermHom (𝓞 K)ˣ (AllSignedGlobalLabel M)).ker.FiniteIndex
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma packetUnitKernel_action {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) {u : (𝓞 K)ˣ}
    (hu : u ∈ packetUnitKernel M σ) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    u • x = x := by
  let := allSignedGlobalLabelMulAction M σ
  have h : (MulAction.toPermHom (𝓞 K)ˣ (AllSignedGlobalLabel M)) u = 1 := hu
  exact congrArg (fun f : Equiv.Perm (AllSignedGlobalLabel M) => f x) h

lemma allSignedGlobalLabelPoint_unit_action {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) (u : (𝓞 K)ˣ) :
    letI := allSignedGlobalLabelMulAction M σ
    allSignedGlobalLabelPoint M σ hodd (u • x) =
      orbitMap (allSignedGlobalLabelPoint M σ hodd x) (orderedUnitLog σ (Additive.ofMul u)) := by
  let := allSignedGlobalLabelMulAction M σ
  let := signedGlobalLabelMulAction M σ (classRepresentative K x.1)
  exact signedGlobalLabelPoint_unit_action M σ hn hodd (classRepresentative K x.1) x.2 u

lemma packetUnitKernel_log_le_period {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    orderedLogSubgroup σ (packetUnitKernel M σ) ≤
      (periodGroup (allSignedGlobalLabelPoint M σ hodd x)).toIntSubmodule := by
  let := allSignedGlobalLabelMulAction M σ
  intro p hp
  obtain ⟨u,hu,rfl⟩ := (mem_orderedLogSubgroup σ (packetUnitKernel M σ) p).mp hp
  change orbitMap (allSignedGlobalLabelPoint M σ hodd x) (orderedUnitLog σ (Additive.ofMul u)) = _
  rw [← allSignedGlobalLabelPoint_unit_action M σ hn hodd x u,packetUnitKernel_action M σ hu x]

lemma allSignedGlobalLabelPoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    IsZLattice ℝ (periodGroup (allSignedGlobalLabelPoint M σ hodd x)).toIntSubmodule := by
  constructor
  change Submodule.span ℝ ((periodGroup (rightAction (latticePoint (globalLabelLattice M _ x.2.lattice) σ)
    (positiveSignMatrix hodd x.2.signs))).toIntSubmodule : Set (LogCoordinates d)) = ⊤
  rw [periodGroup_rightAction_of_diagonal _ _ (positiveSignMatrix_diagonal hodd x.2.signs)]
  exact (latticePoint_period_isZLattice _ σ hn hodd).span_top

 

lemma signedLabelSum_periodic {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    [Fintype (AllSignedGlobalLabel M)] (f : X (d+1) → ℝ≥0∞)
    (t p : LogCoordinates d) (hp : p ∈ orderedLogSubgroup σ ⊤) :
    ∑ x : AllSignedGlobalLabel M, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) (p+t)) =
      ∑ x : AllSignedGlobalLabel M, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) t) := by
  let := allSignedGlobalLabelMulAction M σ
  obtain ⟨u,_,rfl⟩ := (mem_orderedLogSubgroup σ ⊤ p).mp hp
  simp_rw [orbitMap_add,← allSignedGlobalLabelPoint_unit_action M σ hn hodd]
  exact Equiv.sum_comp (MulAction.toPerm u) (fun x : AllSignedGlobalLabel M =>
    f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) t))

 

theorem packetMeasure_lintegral_signedLogAverage_oai {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    [Fintype (AllSignedGlobalLabel M)] {t : Set (LogCoordinates d)}
    (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : X (d+1) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂packetMeasure M σ =
      (Nat.card (AllSignedGlobalLabel M) : ℝ≥0∞)⁻¹ * ((volume t)⁻¹ *
        ∫⁻ u in t, ∑ x : AllSignedGlobalLabel M, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u)) := by
  let := packetUnitKernel_finiteIndex M σ hn
  let P := orderedLogSubgroup σ (packetUnitKernel M σ)
  let L := orderedLogSubgroup σ ⊤
  let b := Module.Free.chooseBasis ℤ P
  let s := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ P b)
  have hs : IsAddFundamentalDomain P s volume := ZLattice.isAddFundamentalDomain b volume
  have hPL : P ≤ L := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := (mem_orderedLogSubgroup σ (packetUnitKernel M σ) p).mp hp
    exact (mem_orderedLogSubgroup σ ⊤ _).mpr ⟨u,Subgroup.mem_top u,rfl⟩
  have hprob (x : AllSignedGlobalLabel M) : orbitProbability (allSignedGlobalLabelPoint M σ hodd x) =
      (volume s)⁻¹ • Measure.map (orbitMap (allSignedGlobalLabelPoint M σ hodd x)) (volume.restrict s) := by
    let := allSignedGlobalLabelPoint_period_isZLattice M σ hn hodd x
    exact orbitProbability_eq_normalized_map_sublattice _ P
      (packetUnitKernel_log_le_period M σ hn hodd x) hs
  rw [packetMeasure_eq_signedLabelAverage M σ hn hodd,lintegral_smul_measure,smul_eq_mul]
  congr 1
  rw [lintegral_sum_measure,tsum_fintype]
  simp_rw [hprob,lintegral_smul_measure,smul_eq_mul]
  have hmap (x : AllSignedGlobalLabel M) :
      ∫⁻ y, f y ∂Measure.map (orbitMap (allSignedGlobalLabelPoint M σ hodd x)) (volume.restrict s) =
        ∫⁻ u in s, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u) :=
    lintegral_map hf (continuous_orbitMap _).measurable
  simp_rw [hmap]
  rw [← Finset.mul_sum]
  have hsum := lintegral_finsetSum («μ» := volume.restrict s) Finset.univ
    (f := fun x u => f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u))
    (fun x _ => hf.comp (continuous_orbitMap _).measurable)
  rw [← hsum]
  apply normalized_periodic_lintegral_eq L P L hPL le_rfl hs ht
  · exact Finset.measurable_sum _ (fun x _ => hf.comp (continuous_orbitMap _).measurable)
  · exact signedLabelSum_periodic M σ hn hodd f

end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.packetMeasure_lintegral_signedLogAverage_oai.{u_1} := @OAI.PrimeDegreePackets.packetMeasure_lintegral_signedLogAverage_oai.{u_1}
