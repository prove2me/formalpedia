-- Prove2me | solution 1 for OAI.MinimalVertex.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:55:06.607666+00:00
-- url     : https://prove2.me/submissions/16e4f316-7699-4a16-a8aa-dfb346bef6bc

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx012

section
-- module Solutions.OAIQ3_Vtx.Compat
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_Locality
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory

open UniformSpace Set
namespace StronglyRationalVOA.ProperCircleArc
lemma disjoint_complement (I : ProperCircleArc) : Disjoint I.carrier I.complement.carrier := by
  let : Fact (0 < 2*Real.pi) := ⟨SmoothCircleFunction.period_pos⟩
  apply Set.disjoint_left.mpr
  rintro x ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
  have hs' : s ∈ Ico I.left (I.left+2*Real.pi) := ⟨hs.1.le,hs.2.trans I.nondense'⟩
  have ht' : t ∈ Ico I.left (I.left+2*Real.pi) :=
    ⟨I.nonempty'.le.trans ht.1.le,ht.2⟩
  have hst : t=s := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht' hs').mp he
  have hlt : I.right < t := ht.1
  linarith [hs.2]
end StronglyRationalVOA.ProperCircleArc

open Set
open scoped Topology ContDiff

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ObservableScalars
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


theorem cklwStrongLocal (hc : A.toVertexAlgebra.C2Cofinite) : U.CKLWStrongLocal hc := by
  refine ⟨U.polynomialEnergyBounds hc,?_⟩
  intro I
  exact U.localAlgebra_locality hc I.isOpen_carrier I.complement.isOpen_carrier I.disjoint_complement
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open UniformSpace Set

open Set
open scoped Topology ContDiff

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ConformalNetContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


theorem cklwStrongLocal_and_conformalNet (hc : A.toVertexAlgebra.C2Cofinite) :
    U.CKLWStrongLocal hc ∧ Nonempty (IrreducibleConformalNetStructure (U.intervalAlgebra hc)) :=
  ⟨U.cklwStrongLocal hc,⟨U.conformalNetStructure hc⟩⟩
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MainClauseOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

theorem source_main_clause_one (_hSimple : A.toVertexAlgebra.IsSimple)
    (hSR : A.IsStronglyRational.{u,v}) :
    A.PolynomialEnergyBounds ∧ U.CKLWStrongLocal hSR.2.2 ∧
      Nonempty (IrreducibleConformalNetStructure (U.intervalAlgebra hSR.2.2)) :=
  ⟨U.polynomialEnergyBounds hSR.2.2,U.cklwStrongLocal_and_conformalNet hSR.2.2⟩
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MinimalComparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


noncomputable section
open Filter Set UniformSpace
open scoped Topology MatrixGroups
universe u v
namespace OAI.MinimalVertex
open StronglyRationalVOA

theorem cloned_entry_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) :
    Code.StronglyRationalVOA.ClosedGraphData.entry T hT i j = ClosedGraphData.entry T hT i j := by
  rfl

section Fields
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V}

theorem smearedMap_eq (A : CFTTypeVOA V) (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) :
    smearedMap A a d ha f hf = A.smearedMap a d ha f hf := by
  have h : ∀ v, Summable (fun m =>
      (f m • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
        (A.physicalMode a d m)) v) :=
    fun v => (A.summable_norm_physicalSmear ha d hf v).of_norm
  simp only [smearedMap, dite_eq_left h]
  rfl

theorem smoothSmearedField_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) :
    smoothSmearedField U hc a d f = U.smoothSmearedField hc a d f := by
  rw [smoothSmearedField, dite_eq_left ⟨U.polynomialEnergyBounds hc, f.rapid_coefficients⟩, smearedMap_eq]
  rfl

theorem closedSmoothField_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) :
    closedSmoothField U hc a d f = U.closedSmoothField hc a d f := by
  rw [closedSmoothField, smoothSmearedField_eq]
  rfl

theorem localGraphData_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : localGraphData U hc O = U.localGraphData hc O := by
  ext x
  simp only [localGraphData, CFTTypeVOA.UnitaryStructure.localGraphData, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, d, ha, f, hf, h, i, j, hx⟩
    refine ⟨a, d, ha, f, hf, i, j, ?_⟩
    simpa only [closedSmoothField_eq, cloned_entry_eq] using hx
  · rintro ⟨a, d, ha, f, hf, i, j, hx⟩
    have h : (closedSmoothField U hc a d f).IsClosed := by
      rw [closedSmoothField_eq]
      exact U.closedSmoothField_isClosed hc ha f
    refine ⟨a, d, ha, f, hf, h, i, j, ?_⟩
    simpa only [closedSmoothField_eq, cloned_entry_eq] using hx

theorem intervalAlgebra_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite) :
    intervalAlgebra U hc = U.intervalAlgebra hc := by
  funext I
  unfold intervalAlgebra localAlgebra CFTTypeVOA.UnitaryStructure.intervalAlgebra
    CFTTypeVOA.UnitaryStructure.localAlgebra
  rw [localGraphData_eq]
  rfl

theorem CKLWStrongLocal_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite) :
    CKLWStrongLocal U hc = U.CKLWStrongLocal hc := by
  unfold CKLWStrongLocal CFTTypeVOA.UnitaryStructure.CKLWStrongLocal
  rw [intervalAlgebra_eq]
  rfl
end Fields

section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_eq (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) :
    resolvent T hs z hz = SymmetricOperator.resolvent T hs z hz := by
  have h : ∃ R : H →L[ℂ] H, ∀ y, (R y, y + z • R y) ∈ T.graph :=
    ⟨SymmetricOperator.resolvent T hs z hz, SymmetricOperator.resolvent_graph T hs z hz⟩
  rw [resolvent, dite_eq_left h]
  ext y
  have he := SymmetricOperator.resolvent_on_graph T hs z hz (h.choose_spec y)
  rw [map_add, map_smul] at he
  exact (add_right_cancel he).symm

theorem boundedGenerator_eq (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) :
    boundedGenerator T hs r hr = SymmetricOperator.boundedGenerator T hs r hr := by
  unfold boundedGenerator SymmetricOperator.boundedGenerator
  simp only [resolvent_eq]

theorem approximatingFlow_eq (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (n : ℕ) (t : ℝ) :
    approximatingFlow T hs n t = SymmetricOperator.approximatingFlow T hs n t := by
  unfold approximatingFlow SymmetricOperator.approximatingFlow
  rw [boundedGenerator_eq]
  rfl

end Operators

theorem flow_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    flow T hs t = SymmetricOperator.flow T hs t := by
  have h : ∃ L : H →L[ℂ] H, ∀ x,
      Tendsto (fun n => approximatingFlow T hs n t x) atTop (𝓝 (L x)) := by
    simpa only [approximatingFlow_eq] using SymmetricOperator.exists_flow_limit T hs t
  rw [flow, dite_eq_left h]
  ext x
  have he : (fun n => approximatingFlow T hs n t x) =
      (fun n => SymmetricOperator.approximatingFlow T hs n t x) := by
    funext n
    rw [approximatingFlow_eq]
  have hx := (congrArg (fun f : ℕ → H => Tendsto f atTop (𝓝 (h.choose x))) he).mp
    (h.choose_spec x)
  exact tendsto_nhds_unique hx ((SymmetricOperator.exists_flow_limit T hs t).choose_spec x)

theorem projectiveStandardAction_eq :
    projectiveStandardAction = CircleMobiusGeometry.projectiveStandardAction := by
  have h : ∃ L : PSL(2,ℝ) →* Code.StronglyRationalVOA.CircleMobiusGeometry.Group,
      ∀ M : SL(2,ℝ), ∃ F : SmoothCircleLift, ∃ hF : Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F,
        L (QuotientGroup.mk M) =
          QuotientGroup.mk (⟨F, M, hF⟩ : Code.StronglyRationalVOA.CircleMobiusGeometry.lifts) := by
    refine ⟨CircleMobiusGeometry.projectiveStandardAction, ?_⟩
    intro M
    obtain ⟨F, hF⟩ := CircleMobiusGeometry.exists_implements M
    exact ⟨F, hF, CircleMobiusGeometry.standardAction_eq_mk hF⟩
  rw [projectiveStandardAction, dite_eq_left h]
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H M =>
    obtain ⟨F, hF, hM⟩ := h.choose_spec M
    exact hM.trans (CircleMobiusGeometry.standardAction_eq_mk hF).symm

theorem netStructure_of_original {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : ProperCircleArc → VonNeumannAlgebra H}
    (net : StronglyRationalVOA.IrreducibleConformalNetStructure N) :
    Nonempty (IrreducibleConformalNetStructure N) := by
  refine ⟨{
    separable := net.separable
    carrier_congr := net.carrier_congr
    isotony := net.isotony
    locality := net.locality
    mobius := net.mobius
    mobius_continuous := net.mobius_continuous
    diffeomorphism := net.diffeomorphism
    diffeomorphism_continuous := net.diffeomorphism_continuous
    extends_mobius := by
      intro F
      rw [projectiveStandardAction_eq]
      exact net.extends_mobius F
    covariance := net.covariance
    local_action := net.local_action
    vacuum := net.vacuum
    vacuum_norm := net.vacuum_norm
    vacuum_invariant := net.vacuum_invariant
    vacuum_unique := net.vacuum_unique
    vacuum_cyclic := net.vacuum_cyclic
    hamiltonian := net.hamiltonian
    hamiltonian_selfAdjoint := net.hamiltonian_selfAdjoint
    positive_energy := net.positive_energy
    rotation_flow := ?_
    irreducible := net.irreducible
  }⟩
  intro t
  rw [flow_eq]
  exact net.rotation_flow t

theorem main_oai {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)
    (hSimple : A.toVertexAlgebra.IsSimple) (hSR : A.IsStronglyRational.{u,v}) :
    A.PolynomialEnergyBounds ∧ CKLWStrongLocal U hSR.2.2 ∧
      Nonempty (IrreducibleConformalNetStructure (intervalAlgebra U hSR.2.2)) := by
  have h := U.source_main_clause_one hSimple hSR
  refine ⟨h.1, ?_, ?_⟩
  · rw [CKLWStrongLocal_eq]
    exact h.2.1
  · rw [intervalAlgebra_eq]
    exact netStructure_of_original h.2.2.some

end OAI.MinimalVertex

end
end

theorem solution.{u, v} : type_of% @OAI.MinimalVertex.main_oai.{u, v} := @OAI.MinimalVertex.main_oai.{u, v}
