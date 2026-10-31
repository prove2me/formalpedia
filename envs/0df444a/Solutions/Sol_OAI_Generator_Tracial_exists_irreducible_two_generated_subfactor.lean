-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:15:19.940501+00:00
-- url     : https://prove2.me/submissions/ced68d47-16f1-47c4-8eca-ec1efbfe954a

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg012
import Theorems.Thm_OAI_Generator_FiniteMatrixStage_generated_isII1
import Theorems.Thm_OAI_Generator_Tracial_exists_irreducible_matrix_energy_descent

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Target
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

theorem wstar_mono {s t : Set (H →L[ℂ] H)} (h : s ⊆ t) : wstar s ≤ wstar t := by
  intro x hx
  apply StarSubalgebra.mem_sInf.mpr
  intro S hS
  exact StarSubalgebra.mem_sInf.mp hx S ⟨hS.1, h.trans hS.2⟩

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wotClosed_normClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    IsClosed (S : Set (H →L[ℂ] H)) :=
  hS.preimage ContinuousLinearMapWOT.continuous_ofCLM

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
variable (hx : TraceOrthogonal τ P x)
include hx

theorem trace_zero : τ.trace x=0 := by simpa using hx (1 : P)

end TraceOrthogonal

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/

end

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_fixed (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : x.val ∈ N) :
    conditionalExpectation τ hNM x=x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM x x hx
  intro a
  simp only [sub_self,mul_zero]
  exact inner_zero_right _

theorem conditionalExpectation_trace (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.trace (conditionalExpectation τ hNM x)=τ.trace x := by
  have h := (conditionalExpectation_orthogonal τ hNM x).trace_zero τ
  rw [trace_sub,sub_eq_zero] at h
  exact h.symm

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_pythagoras (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x)^2+
      τ.norm₂ (x-conditionalExpectation τ hNM x)^2=τ.norm₂ x^2 := by
  have ho := conditionalExpectation_orthogonal τ hNM x
    ⟨star (conditionalExpectation τ hNM x),star_mem (conditionalExpectation_mem τ hNM x)⟩
  have hi : inner ℂ (baseVector τ (conditionalExpectation τ hNM x))
      (baseVector τ (x-conditionalExpectation τ hNM x))=0 := by
    rw [baseVector_inner_trace]; exact ho
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  rw [← map_add,add_sub_cancel] at h
  change τ.norm₂ x*τ.norm₂ x=τ.norm₂ (conditionalExpectation τ hNM x)*τ.norm₂ (conditionalExpectation τ hNM x)+
    τ.norm₂ (x-conditionalExpectation τ hNM x)*τ.norm₂ (x-conditionalExpectation τ hNM x) at h
  simpa only [pow_two] using h.symm

theorem conditionalExpectation_norm₂_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x) ≤ τ.norm₂ x := by
  have h := conditionalExpectation_pythagoras τ hNM x
  nlinarith [sq_nonneg (τ.norm₂ (x-conditionalExpectation τ hNM x)),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N P M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_tower (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (conditionalExpectation τ hPM x)=conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact conditionalExpectation_mem τ hNM x
  · have hP : TraceOrthogonal τ (insideAlgebra (M := M) (P := N))
        (x-conditionalExpectation τ hPM x) := by
      intro a
      exact conditionalExpectation_orthogonal τ hPM x
        ⟨(a : M.toStarSubalgebra),hNP a.property⟩
    have h := (conditionalExpectation_orthogonal τ hNM x).sub τ hP
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    abel

theorem conditionalExpectation_nested_energy (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x)^2+
      τ.norm₂ (conditionalExpectation τ hPM x-conditionalExpectation τ hNM x)^2=
        τ.norm₂ (conditionalExpectation τ hPM x)^2 := by
  have h := conditionalExpectation_pythagoras τ hNM (conditionalExpectation τ hPM x)
  rwa [conditionalExpectation_tower τ hNM hPM hNP x] at h

end

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

theorem mem_algebra (x : A) : x ∈ E.algebra ↔
    ∃ a : Matrix ι ι ℂ, (∑ i, ∑ j, a i j • E.entry i j) = x := Iff.rfl

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

theorem algebra_le_iff (S : StarSubalgebra ℂ A) :
    E.algebra ≤ S ↔ ∀ i j, E.entry i j ∈ S := by
  constructor
  · exact fun h i j => h (E.entry_mem i j)
  · intro h x hx
    obtain ⟨a,rfl⟩ := (E.mem_algebra x).mp hx
    exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h i j) _

theorem commute_algebra_iff (x : A) :
    (∀ a ∈ E.algebra, Commute a x) ↔ ∀ i j, Commute (E.entry i j) x := by
  constructor
  · exact fun h i j => h _ (E.entry_mem i j)
  · intro h a ha
    obtain ⟨b,rfl⟩ := (E.mem_algebra a).mp ha
    show (∑ i, ∑ j, b i j • E.entry i j)*x=x*(∑ i, ∑ j, b i j • E.entry i j)
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      (h _ _).eq]

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

omit [StarModule ℂ A] in
theorem product_entry (a b : ι × κ) :
    (E.product F hc).entry a b = E.entry a.1 b.1 * F.entry a.2 b.2 := rfl

omit [StarModule ℂ A] in
theorem product_sum_left (i j : ι) :
    (∑ k, (E.product F hc).entry (i,k) (j,k)) = E.entry i j := by
  simp only [product_entry, ← Finset.mul_sum, F.total, mul_one]

omit [StarModule ℂ A] in
theorem product_sum_right (k l : κ) :
    (∑ i, (E.product F hc).entry (i,k) (i,l)) = F.entry k l := by
  simp only [product_entry, ← Finset.sum_mul, E.total, one_mul]

theorem algebra_le_product_left : E.algebra ≤ (E.product F hc).algebra := by
  apply (E.algebra_le_iff _).mpr
  intro i j
  rw [← E.product_sum_left F hc i j]
  exact (E.product F hc).algebra.sum_mem fun k _ => (E.product F hc).entry_mem _ _

theorem algebra_le_product_right : F.algebra ≤ (E.product F hc).algebra := by
  apply (F.algebra_le_iff _).mpr
  intro k l
  rw [← E.product_sum_right F hc k l]
  exact (E.product F hc).algebra.sum_mem fun i _ => (E.product F hc).entry_mem _ _

theorem product_algebra_eq_sup : (E.product F hc).algebra = E.algebra ⊔ F.algebra := by
  apply le_antisymm
  · apply ((E.product F hc).algebra_le_iff _).mpr
    intro a b
    exact (E.algebra ⊔ F.algebra).mul_mem ((show E.algebra ≤ E.algebra ⊔ F.algebra from le_sup_left) (E.entry_mem a.1 b.1))
      ((show F.algebra ≤ E.algebra ⊔ F.algebra from le_sup_right) (F.entry_mem a.2 b.2))
  · exact sup_le (E.algebra_le_product_left F hc) (E.algebra_le_product_right F hc)

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem entry_mul_amplify (o i j : ι) (x : A) :
    E.entry i j * E.amplify o x = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.mul_sum,← mul_assoc,E.mul_entry]
  simp [ite_mul]

omit [StarModule ℂ A] in
theorem amplify_mul_entry (o i j : ι) (x : A) :
    E.amplify o x * E.entry i j = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.sum_mul,mul_assoc,E.mul_entry]
  simp [mul_ite]

theorem amplify_mem (o : ι) (x : A) : E.amplify o x ∈ E.commutant := by
  intro i j
  show E.entry i j * E.amplify o x = E.amplify o x * E.entry i j
  rw [E.entry_mul_amplify,E.amplify_mul_entry]

omit [StarModule ℂ A] in
theorem amplify_star (o : ι) (x : A) : star (E.amplify o x)=E.amplify o (star x) := by
  simp only [amplify,star_sum,star_mul,E.star_entry,mul_assoc]

omit [StarModule ℂ A] in
theorem amplify_zero (o : ι) : E.amplify o 0=0 := by simp [amplify]

omit [StarModule ℂ A] in
theorem amplify_corner (o i j : ι) (x : A) :
    E.entry i o*E.amplify o x*E.entry o j = E.entry i o*x*E.entry o j := by
  rw [E.entry_mul_amplify]
  simp only [mul_assoc,E.mul_entry,ite_true, if_true]

omit [StarModule ℂ A] in
theorem amplify_mul (o : ι) (x y : A) :
    E.amplify o x*E.amplify o y=E.amplify o (x*E.entry o o*y) := by
  simp only [amplify,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (E.entry i o*x*E.entry o i)*E.amplify o y = _
  rw [mul_assoc,E.entry_mul_amplify]
  simp only [mul_assoc]

theorem amplify_compression (o : ι) (x : A) (hx : x ∈ E.commutant) :
    E.amplify o (E.entry o o*x)=x := by
  simp only [amplify]
  calc _ = ∑ i, E.entry i i*x := by
             apply Finset.sum_congr rfl
             intro i hi
             rw [← mul_assoc,E.mul_entry,ite_eq_left rfl,mul_assoc,← (hx o i).eq,
               ← mul_assoc,E.mul_entry,ite_eq_left rfl]
       _ = x := by rw [← Finset.sum_mul,E.total,one_mul]

omit [StarModule ℂ A] in
theorem reconstruct (o : ι) (x : A) :
    (∑ i, ∑ j, E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j)=x := by
  simp only [E.amplify_corner]
  have h (i j : ι) : E.entry i o*(E.entry o i*x*E.entry j o)*E.entry o j=
      E.entry i i*x*E.entry j j := by
    calc _ = (E.entry i o*E.entry o i)*x*(E.entry j o*E.entry o j) := by
               simp only [mul_assoc]
         _ = _ := by simp only [E.mul_entry,ite_true, if_true]
  simp only [h,← Finset.mul_sum,E.total,mul_one,← Finset.sum_mul,one_mul]

/-- The commutant of a full unital matrix algebra in a scalar-center algebra
has scalar center. The finite matrix decomposition is constructed above. -/
theorem commutant_scalar_center (o : ι)
    (hfactor : ∀ c : A, (∀ a : A,a*c=c*a) → ∃ z : ℂ,c=z • (1 : A))
    (c : E.commutant) (hc : ∀ a : E.commutant,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.commutant) := by
  obtain ⟨z,hz⟩ := hfactor c.val (by
    intro x
    have h (i j : ι) : Commute
        (E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j) c.val := by
      have hm : Commute (E.amplify o (E.entry o i*x*E.entry j o)) c.val :=
        congrArg Subtype.val (hc ⟨_,E.amplify_mem o _⟩)
      exact ((c.property i o).mul_left hm).mul_left (c.property o j)
    rw [← E.reconstruct o x]
    simp only [Finset.sum_mul,Finset.mul_sum,(h _ _).eq])
  exact ⟨z,Subtype.ext hz⟩

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_projection (o : ι) : IsStarProjection (E.entry o o) := by
  exact ⟨by show E.entry o o*E.entry o o=E.entry o o; simpa using E.mul_entry o o o o,E.star_entry o o⟩

omit [StarModule ℂ A] in
theorem amplify_projection (o : ι) (q : A) (hq : IsStarProjection q)
    (hs : q*E.entry o o=q) : IsStarProjection (E.amplify o q) := by
  constructor
  · show E.amplify o q*E.amplify o q=E.amplify o q
    rw [E.amplify_mul,hs,hq.isIdempotentElem.eq]
  · show star (E.amplify o q)=E.amplify o q
    rw [E.amplify_star,hq.isSelfAdjoint.star_eq]

theorem commutant_diffuse (o : ι)
    (hdiff : ∀ p : A,IsStarProjection p → p ≠ 0 →
      ∃ q : A,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.commutant) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.commutant,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  have hpA : IsStarProjection p.val := hp.map E.commutant.subtype
  let r : A := E.entry o o*p.val
  have hr : IsStarProjection r := (E.diagonal_projection o).mul hpA (p.property o o)
  have hr0 : r ≠ 0 := by
    intro h
    have he := E.amplify_compression o p.val p.property
    rw [show E.entry o o*p.val=0 from h,E.amplify_zero] at he
    exact hp0 (Subtype.ext he.symm)
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff r hr hr0
  have hqs : q*E.entry o o=q := by
    have hre : r*E.entry o o=r := by
      dsimp [r]
      rw [mul_assoc,← (p.property o o).eq,← mul_assoc,
        (E.diagonal_projection o).isIdempotentElem.eq]
    calc q*E.entry o o = (q*r)*E.entry o o := by rw [hqr']
         _ = q*r := by rw [mul_assoc,hre]
         _ = q := hqr'
  have hsq : E.entry o o*q=q := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,E.star_entry] using congrArg star hqs
  let Q : E.commutant := ⟨E.amplify o q,E.amplify_mem o q⟩
  have hQ : IsStarProjection Q := by
    constructor
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isIdempotentElem.eq
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isSelfAdjoint.star_eq
  have hrec : E.entry o o*Q.val*E.entry o o=q := by
    change E.entry o o*E.amplify o q*E.entry o o=q
    rw [E.amplify_corner,hsq,hqs]
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro h
    have hz : Q.val=0 := congrArg Subtype.val h
    rw [hz,mul_zero,zero_mul] at hrec
    exact hq0 hrec.symm
  · intro h
    have hz : Q.val=p.val := congrArg Subtype.val h
    rw [hz,mul_assoc,← (p.property o o).eq,← mul_assoc,
      (E.diagonal_projection o).isIdempotentElem.eq] at hrec
    exact hqr hrec.symm
  · apply Subtype.ext
    change p.val*E.amplify o q=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul]
    congr 1
    rw [mul_assoc,hsq]
    exact hrq
  · apply Subtype.ext
    change E.amplify o q*p.val=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul,hqs]
    exact congrArg (E.amplify o) hqr'

open scoped BigOperators

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

theorem relative_scalar_center (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.relativeVonNeumann.toStarSubalgebra) := by
  obtain ⟨z,hz⟩ := E.commutant_scalar_center o hfactor (E.relativeEquiv.symm c) (by
    intro a
    apply E.relativeEquiv.injective
    change E.relativeEquiv (a*E.relativeEquiv.symm c)=
      E.relativeEquiv (E.relativeEquiv.symm c*a)
    rw [map_mul,map_mul,E.relativeEquiv.apply_symm_apply]
    exact hc (E.relativeEquiv a))
  refine ⟨z,?_⟩
  have h := congrArg E.relativeEquiv hz
  simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using h

theorem relative_diffuse (o : ι)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.relativeVonNeumann.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.relativeVonNeumann.toStarSubalgebra,
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := E.commutant_diffuse o hdiff
    (E.relativeEquiv.symm p) (hp.map E.relativeEquiv.symm) (by
      intro h
      apply hp0
      simpa using congrArg E.relativeEquiv h)
  refine ⟨E.relativeEquiv q,?_,?_,?_,?_,?_⟩
  · exact hq.map E.relativeEquiv.toStarAlgHom
  · intro h
    apply hq0
    exact E.relativeEquiv.injective (h.trans (map_zero E.relativeEquiv).symm)
  · intro h
    apply hqp
    exact E.relativeEquiv.injective (h.trans (E.relativeEquiv.apply_symm_apply p).symm)
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hpq
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hqp'

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
theorem commute_mapped_of_amplify (E : MatrixUnitSystem ι A) (o : ι)
    (f : A →⋆ₐ[ℂ] B) (y : B)
    (hE : ∀ i j,Commute (f (E.entry i j)) y)
    (hamp : ∀ a : A,Commute (f (E.amplify o a)) y) (x : A) : Commute (f x) y := by
  rw [← E.reconstruct o x,map_sum]
  apply Commute.sum_left
  intro i hi
  rw [map_sum]
  apply Commute.sum_left
  intro j hj
  rw [map_mul,map_mul]
  exact ((hE i o).mul_left (hamp _)).mul_left (hE o j)

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem ι N.toStarSubalgebra) (hNM : N ≤ M)

theorem relative_irreducible (o : ι)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
        ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,
      coordinateInclusion (E.relative_inclusion hNM) a*c=
        c*coordinateInclusion (E.relative_inclusion hNM) a) :
    ∃ z : ℂ,c=z • (1 : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra) := by
  let F := E.map (coordinateInclusion hNM)
  let cM := coordinateInclusion F.relativeVonNeumann_le c
  have hentries : ∀ i j,Commute (coordinateInclusion hNM (E.entry i j)) cM := by
    intro i j
    apply Subtype.ext
    exact ((F.relativeStar_mem c.val).mp c.property).2 i j
  have hamp (a : N.toStarSubalgebra) : Commute
      (coordinateInclusion hNM (E.amplify o a)) cM := by
    let b : E.relativeVonNeumann.toStarSubalgebra :=
      E.relativeEquiv ⟨E.amplify o a,E.amplify_mem o a⟩
    apply Subtype.ext
    exact congrArg (fun t : F.relativeVonNeumann.toStarSubalgebra => t.val) (hc b)
  obtain ⟨z,hz⟩ := hirr cM (fun x =>
    E.commute_mapped_of_amplify o (coordinateInclusion hNM) cM hentries hamp x)
  exact ⟨z,Subtype.ext (congrArg (fun t : M.toStarSubalgebra => t.val) hz)⟩

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! A separated idempotent is recovered from commutation with a norm-small
perturbation. This is an elementary substitute for the spectral-cut step. -/
section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem offDiagonal_eq_zero_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : p*x*(1-p)=0 := by
  let y := p*x*(1-p)
  have hleft : p*(a • p+t) = a • p+p*t := by
    rw [mul_add,mul_smul_comm,hp]
  have hright : (a • p+t)*(1-p)=t*(1-p) := by
    rw [add_mul,smul_mul_assoc,mul_sub,mul_one,hp,sub_self,smul_zero,zero_add]
  have he := congrArg (fun z : A => p*z*(1-p)) hx.eq
  have hy : a • y = y*t-t*y := by
    have ht : t*(1-p)=(1-p)*t := by
      rw [mul_sub,sub_mul,mul_one,one_mul,hpt.eq]
    have h : a • y+t*y=y*t := by
      calc a • y+t*y = (p*(a • p+t))*x*(1-p) := by
             rw [hleft,add_mul,add_mul,smul_mul_assoc,smul_mul_assoc]
             dsimp [y]
             rw [hpt.eq]
             simp only [mul_assoc]
        _ = p*((a • p+t)*x)*(1-p) := by simp only [mul_assoc]
        _ = p*(x*(a • p+t))*(1-p) := he
        _ = y*t := by
          simp only [mul_assoc]
          rw [hright,ht]
          simp only [y,mul_assoc]
    exact eq_sub_of_add_eq' (by simpa only [add_comm] using h)
  have han : 0 ≤ a := (mul_nonneg (by norm_num) (norm_nonneg t)).trans ha.le
  have hn : a*‖y‖ ≤ 2*‖t‖*‖y‖ := by
    calc a*‖y‖ = ‖a • y‖ := by rw [norm_smul,Real.norm_of_nonneg han]
      _ = ‖y*t-t*y‖ := congrArg norm hy
      _ ≤ ‖y*t‖+‖t*y‖ := norm_sub_le _ _
      _ ≤ ‖y‖*‖t‖+‖t‖*‖y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2*‖t‖*‖y‖ := by ring
  have hz : ‖y‖=0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hz

theorem commute_projection_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : Commute p x := by
  have h₁ := offDiagonal_eq_zero_of_gap p t x hp hpt a ha hx
  have hcp : (1-p)*(1-p)=1-p := by noncomm_ring [hp]
  have hcpt : Commute (1-p) (-t) := ((Commute.one_left t).sub_left hpt).neg_right
  have hcx : Commute (a • (1-p)+ -t) x := by
    have he : a • (1-p)+ -t = a • (1 : A)-(a • p+t) := by
      rw [smul_sub]; abel
    rw [he]
    exact ((Commute.one_left x).smul_left a).sub_left hx
  have h₂ := offDiagonal_eq_zero_of_gap (1-p) (-t) x hcp hcpt a
    (by simpa only [norm_neg] using ha) hcx
  simp only [sub_sub_cancel] at h₂
  show p*x=x*p
  have h₁' : p*x=p*x*p := by simpa only [mul_sub,mul_one,sub_eq_zero] using h₁
  have h₂' : x*p=p*x*p := by simpa only [sub_mul,one_mul,sub_eq_zero] using h₂
  exact h₁'.trans h₂'.symm

end

/-! Countably many commuting projections have one self-adjoint generator.
We use coefficients 3*4^(-(n+1)), whose strict gap admits direct norm recovery
through the double commutant. No trace, tensor model, or uniqueness is used. -/
namespace CommutingProjectionEncoding
open scoped BigOperators Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem weight_hasSum (n : ℕ) :
    HasSum (fun k => weight (n+k)) ((1/4 : ℝ)^n) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1)).mul_left ((3/4:ℝ)*(1/4)^n)
  convert! h using 1
  · ext k; simp only [weight,pow_add]; ring
  · ring

variable (e : ℕ → (H →L[ℂ] H)) (hp : ∀ n, IsStarProjection (e n))
include hp

theorem term_norm_le (n k : ℕ) : ‖(weight (n+k) • e (n+k) : (H →L[ℂ] H))‖ ≤ weight (n+k) := by
  rw [norm_smul,Real.norm_of_nonneg (weight_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (hp (n+k)).norm_le (weight_nonneg _)).trans_eq (mul_one _)

theorem tail_summable (n : ℕ) : Summable (fun k => (weight (n+k) • e (n+k) : (H →L[ℂ] H))) := by
  exact (weight_hasSum n).summable.of_norm_bounded (term_norm_le e hp n)

theorem tail_norm_le (n : ℕ) : ‖tail e n‖ ≤ (1/4 : ℝ)^n :=
  tsum_of_norm_bounded (weight_hasSum n) (term_norm_le e hp n)

theorem tail_step (n : ℕ) : tail e n = weight n • e n + tail e (n+1) := by
  have h := (tail_summable e hp n).tsum_eq_zero_add
  simpa only [tail,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem tail_selfAdjoint (n : ℕ) : IsSelfAdjoint (tail e n) := by
  have h := (tail_summable e hp n).hasSum.star
  simp only [star_smul,star_trivial,(hp _).isSelfAdjoint.star_eq] at h
  exact h.unique (tail_summable e hp n).hasSum

theorem tail_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (he : ∀ n, e n ∈ S) (n : ℕ) : tail e n ∈ S := by
  apply (wotClosed_normClosed S hS).mem_of_tendsto (tail_summable e hp n).hasSum
  exact Eventually.of_forall fun s => S.sum_mem fun k _ => by
    rw [← Complex.coe_smul]
    exact S.smul_mem (he (n+k)) _

variable (hc : ∀ i j, Commute (e i) (e j))
include hc

omit hp [CompleteSpace H] in
theorem projection_commutes_tail (i n : ℕ) : Commute (e i) (tail e n) :=
  Commute.tsum_right _ fun k => (hc i (n+k)).smul_right _

theorem projection_mem_of_tail_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (n : ℕ) (ht : tail e n ∈ S) : e n ∈ S := by
  change e n ∈ (S : Set (H →L[ℂ] H))
  rw [← wotClosed_bicommutant S hS]
  intro x hx
  have hxt : Commute (weight n • e n+tail e (n+1)) x := by
    rw [← tail_step e hp n]
    exact hx _ ht
  have hgap : 2*‖tail e (n+1)‖ < weight n := by
    have h := tail_norm_le e hp (n+1)
    have hn : 0 < (1/4:ℝ)^n := by positivity
    dsimp [weight]
    rw [pow_succ] at h
    nlinarith
  exact (commute_projection_of_gap (e n) (tail e (n+1)) x
    (hp n).isIdempotentElem.eq (projection_commutes_tail e hc n (n+1))
    (weight n) hgap hxt).eq.symm

theorem projection_mem_wstar (n : ℕ) : e n ∈ wstar {tail e 0} := by
  let S := wstar {tail e 0}
  have hS : WOTClosed S := wstar_closed _
  have ht : ∀ k, tail e k ∈ S := by
    intro k
    induction k with
    | zero => exact subset_wstar _ (Set.mem_singleton _)
    | succ k ih =>
      have he := projection_mem_of_tail_mem e hp hc S hS k ih
      have hs : weight k • e k ∈ S := by
        rw [← Complex.coe_smul]
        exact S.smul_mem he _
      have h := S.sub_mem ih hs
      rw [tail_step e hp k,add_sub_cancel_left] at h
      exact h
  exact projection_mem_of_tail_mem e hp hc S hS n (ht n)

theorem wstar_encoding : wstar {tail e 0} = wstar (Set.range e) := by
  apply le_antisymm
  · apply wstar_le (wstar_closed _)
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact tail_mem e hp (wstar (Set.range e)) (wstar_closed _)
      (fun n => subset_wstar (Set.range e) (Set.mem_range_self n)) 0
  · apply wstar_le (wstar_closed _)
    rintro x ⟨n,rfl⟩
    exact projection_mem_wstar e hp hc n

/-- Countable commuting-projection encoding without additional structural hypotheses. -/
theorem exists_selfAdjoint_generator :
    ∃ b : (H →L[ℂ] H), IsSelfAdjoint b ∧ ‖b‖ ≤ 1 ∧ wstar {b}=wstar (Set.range e) :=
  ⟨tail e 0,tail_selfAdjoint e hp 0,by simpa using tail_norm_le e hp 0,
    wstar_encoding e hp hc⟩

end CommutingProjectionEncoding

/-! The spectral separation step as an exact membership theorem for literal W*. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {D P M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_restricted (hPM : P ≤ M) (hDP : D ≤ P)
    (x : P.toStarSubalgebra) :
    conditionalExpectation τ (hDP.trans hPM) (coordinateInclusion hPM x)=
      coordinateInclusion hPM (conditionalExpectation (restrictedTrace τ hPM) hDP x) := by
  apply conditionalExpectation_eq_of_orthogonal τ (hDP.trans hPM)
  · exact conditionalExpectation_mem (restrictedTrace τ hPM) hDP x
  · intro a
    let b : insideAlgebra (M := P) (P := D) := ⟨⟨a.val.val,hDP a.property⟩,a.property⟩
    exact conditionalExpectation_orthogonal (restrictedTrace τ hPM) hDP x b

end Tracial
namespace MatrixUnitSystem
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem relative_antitone (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ M.toStarSubalgebra) (h : E.algebra ≤ F.algebra) :
    F.relativeVonNeumann ≤ E.relativeVonNeumann := by
  intro x hx
  have hx' := (F.relativeStar_mem x).mp hx
  apply (E.relativeStar_mem x).mpr
  refine ⟨hx'.1,?_⟩
  let y : M.toStarSubalgebra := ⟨x,hx'.1⟩
  have hF : ∀ i j,Commute (F.entry i j) y := fun i j => Subtype.ext (hx'.2 i j)
  intro i j
  exact congrArg Subtype.val (((F.commute_algebra_iff y).mpr hF) _ (h (E.entry_mem i j))).eq

/-- The product commutant is exactly the commutant of the new system inside
of the old commutant, with both algebras represented on the same H. -/
theorem relative_product_inside (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ i j k l,Commute (E.entry i j)
      ((F.map (coordinateInclusion E.relativeVonNeumann_le)).entry k l)) :
    (E.product (F.map (coordinateInclusion E.relativeVonNeumann_le)) hc).relativeVonNeumann =
      F.relativeVonNeumann := by
  let G := F.map (coordinateInclusion E.relativeVonNeumann_le)
  apply le_antisymm
  · intro x hx
    have hE := E.relative_antitone (E.product G hc) (E.algebra_le_product_left G hc) hx
    have hG := G.relative_antitone (E.product G hc) (E.algebra_le_product_right G hc) hx
    exact (F.relativeStar_mem x).mpr ⟨hE,((G.relativeStar_mem x).mp hG).2⟩
  · intro x hx
    have hF := (F.relativeStar_mem x).mp hx
    have hE := (E.relativeStar_mem x).mp hF.1
    apply ((E.product G hc).relativeStar_mem x).mpr
    refine ⟨hE.1,?_⟩
    intro a b
    change ((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)*x=
      x*((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)
    rw [mul_assoc,hF.2,← mul_assoc,hE.2,mul_assoc]

end MatrixUnitSystem

end

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_compatible_matrix_energy_descent (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (E : MatrixUnitSystem ι N.toStarSubalgebra) (o : ι)
    (x : M.toStarSubalgebra) (ht : τ.trace x=0)
    (hy : conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x ≠ 0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ F : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      ∃ hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m),
        E.algebra ≤ (E.product F hc).algebra ∧
        τ.norm₂ (conditionalExpectation τ
          ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
          (15/16 : ℝ)*τ.norm₂
            (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 := by
  let EM := E.map (coordinateInclusion hNM)
  let C := EM.relativeVonNeumann
  let hCM := EM.relativeVonNeumann_le
  let y := conditionalExpectation τ hCM x
  let yC : C.toStarSubalgebra := ⟨y.val,conditionalExpectation_mem τ hCM x⟩
  let τC := restrictedTrace τ hCM
  have hyC : yC ≠ 0 := by
    intro h
    apply hy
    exact Subtype.ext (congrArg (fun b : C.toStarSubalgebra => b.val) h)
  have htC : τC.trace yC=0 := (conditionalExpectation_trace τ hCM x).trans ht
  obtain ⟨k,n,hn,G,hG⟩ := exists_irreducible_matrix_energy_descent τC
    (E.relative_inclusion hNM) (E.relative_scalar_center o hfactor)
    (E.relative_diffuse o hdiff) (E.relative_irreducible hNM o hirr) yC hyC htC
  let F := G.map (coordinateInclusion E.relativeVonNeumann_le)
  have hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry l m).val).mp (G.entry l m).property).2 i j
  let GM := G.map (coordinateInclusion (E.relative_inclusion hNM))
  have hcM : ∀ i j l m,Commute (EM.entry i j)
      ((GM.map (coordinateInclusion hCM)).entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact congrArg (fun b : N.toStarSubalgebra => b.val) (hc i j l m).eq
  have hproduct : ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann =
      GM.relativeVonNeumann := by
    convert EM.relative_product_inside GM hcM using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  let hDC := GM.relativeVonNeumann_le
  have he : conditionalExpectation τ (hDC.trans hCM) x =
      coordinateInclusion hCM (conditionalExpectation τC hDC yC) := by
    rw [← conditionalExpectation_tower τ (hDC.trans hCM) hCM hDC x]
    exact conditionalExpectation_restricted τ hCM hDC yC
  refine ⟨k,n,hn,F,hc,E.algebra_le_product_left F hc,?_⟩
  have hnorm : τ.norm₂ (conditionalExpectation τ (hDC.trans hCM) x)^2 ≤
      (15/16 : ℝ)*τ.norm₂ y^2 := by
    rw [he]
    exact hG
  simpa only [hproduct] using hnorm

end Tracial

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem reindex_algebra (E : MatrixUnitSystem ι A) (e : κ ≃ ι) :
    (E.reindex e).algebra=E.algebra := by
  apply le_antisymm
  · exact ((E.reindex e).algebra_le_iff _).mpr (fun i j => E.entry_mem _ _)
  · apply (E.algebra_le_iff _).mpr
    intro i j
    simpa only [reindex,Equiv.apply_symm_apply] using
      (E.reindex e).entry_mem (e.symm i) (e.symm j)

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem map_algebra_mono (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (F : MatrixUnitSystem κ N.toStarSubalgebra) (h : E.algebra ≤ F.algebra)
    (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    (E.map f).algebra ≤ (F.map f).algebra := by
  apply ((E.map f).algebra_le_iff _).mpr
  intro i j
  obtain ⟨a,ha⟩ := (F.mem_algebra (E.entry i j)).mp (h (E.entry_mem i j))
  change f (E.entry i j) ∈ (F.map f).algebra
  rw [← ha]
  simp only [map_sum,map_smul]
  exact (F.map f).algebra.sum_mem fun k _ =>
    (F.map f).algebra.sum_mem fun l _ => (F.map f).algebra.smul_mem ((F.map f).entry_mem k l) _

theorem mapped_reindex_relative (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (e : κ ≃ ι) (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    ((E.reindex e).map f).relativeVonNeumann=(E.map f).relativeVonNeumann := by
  apply le_antisymm
  · exact (E.map f).relative_antitone _ (E.map_algebra_mono _ (E.reindex_algebra e).ge f)
  · exact ((E.reindex e).map f).relative_antitone _ ((E.reindex e).map_algebra_mono _
      (E.reindex_algebra e).le f)

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

theorem energy_nonneg (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) : 0 ≤ E.energy τ hNM x := sq_nonneg _

theorem commutant_antitone (E F : FiniteMatrixStage N) (hNM : N ≤ M)
    (hEF : E.units.algebra ≤ F.units.algebra) : F.commutant hNM ≤ E.commutant hNM :=
  (E.units.map (coordinateInclusion hNM)).relative_antitone _
    (E.units.map_algebra_mono F.units hEF (coordinateInclusion hNM))

theorem energy_antitone (E F : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (hEF : E.units.algebra ≤ F.units.algebra) (x : M.toStarSubalgebra) :
    F.energy τ hNM x ≤ E.energy τ hNM x := by
  have h := conditionalExpectation_nested_energy τ (F.commutant_le hNM) (E.commutant_le hNM)
    (E.commutant_antitone F hNM hEF) x
  dsimp [energy]
  nlinarith [sq_nonneg (τ.norm₂ (conditionalExpectation τ (E.commutant_le hNM) x-
    conditionalExpectation τ (F.commutant_le hNM) x))]

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/
section
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_countable_norm₂_dense (S : Set M.toStarSubalgebra)
    (hne : S.Nonempty) (hsep : TopologicalSpace.IsSeparable (baseVector τ '' S)) :
    ∃ a : ℕ → M.toStarSubalgebra,(∀ n,a n ∈ S) ∧
      ∀ b ∈ S,∀ ε : ℝ,0 < ε → ∃ n,τ.norm₂ (b-a n) < ε := by
  let T := baseVector τ '' S
  let : TopologicalSpace.SeparableSpace T := hsep.separableSpace
  let : Nonempty T := ⟨⟨baseVector τ hne.choose,Set.mem_image_of_mem _ hne.choose_spec⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := T)
  have hex (n : ℕ) : ∃ a ∈ S,baseVector τ a=(v n).val := (v n).property
  choose a ha he using hex
  refine ⟨a,ha,?_⟩
  intro b hb ε hε
  let z : T := ⟨baseVector τ b,Set.mem_image_of_mem _ hb⟩
  obtain ⟨w,⟨n,rfl⟩,hw⟩ := Metric.mem_closure_iff.mp (hv z) ε hε
  refine ⟨n,?_⟩
  change ‖baseVector τ (b-a n)‖ < ε
  rw [map_sub,he n]
  simpa only [Subtype.dist_eq,dist_eq_norm] using hw

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem scalar_common_commutant_of_dense_energy_decay (τ : TracialRepresentation M) (hNM : N ≤ M)
    (A : ℕ → FiniteMatrixStage N) (x : ℕ → M.toStarSubalgebra)
    (hdense : ∀ b : M.toStarSubalgebra,τ.trace b=0 → ∀ ε : ℝ,0 < ε →
      ∃ s,τ.norm₂ (b-x s) < ε)
    (hlim : ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0))
    (c : M.toStarSubalgebra) (hc : ∀ n,c.val ∈ (A n).commutant hNM) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  let y := c-τ.trace c • (1 : M.toStarSubalgebra)
  have hyt : τ.trace y=0 := by
    dsimp [y]
    rw [trace_sub,cornerTrace_smul,τ.trace_one,mul_one,sub_self]
  have hym (n : ℕ) : y.val ∈ (A n).commutant hNM :=
    ((A n).commutant hNM).sub_mem (hc n)
      (((A n).commutant hNM).smul_mem ((A n).commutant hNM).one_mem _)
  suffices y=0 from sub_eq_zero.mp this
  by_contra hy
  have hp : 0 < τ.norm₂ y := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hy ((τ.norm₂_eq_zero_iff y).mp h.symm))
  obtain ⟨s,hs⟩ := hdense y hyt (τ.norm₂ y/4) (by positivity)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp (hlim s)).2 ((τ.norm₂ y/4)^2) (by positivity)).exists
  let hDM := (A n).commutant_le hNM
  let z := conditionalExpectation τ hDM (x s)
  have hz : τ.norm₂ z < τ.norm₂ y/4 := by
    change τ.norm₂ z^2 < (τ.norm₂ y/4)^2 at hn
    nlinarith [show 0 ≤ τ.norm₂ z from norm_nonneg _]
  have hdiff : τ.norm₂ (y-z) ≤ τ.norm₂ (y-x s) := by
    have he : conditionalExpectation τ hDM (y-x s)=y-z := by
      change conditionalExpectationCLM τ hDM (y-x s)=y-z
      rw [map_sub]
      change conditionalExpectation τ hDM y-z=y-z
      rw [conditionalExpectation_fixed τ hDM y (hym n)]
    rw [← he]
    exact conditionalExpectation_norm₂_le τ hDM _
  have hadd := τ.norm₂_add_le (y-z) z
  rw [sub_add_cancel] at hadd
  linarith

end FiniteMatrixStage

end

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem stage_le_generated (A : ℕ → FiniteMatrixStage N) (n : ℕ) :
    (A n).units.concreteAlgebra ≤ generated A := by
  intro x hx
  exact subset_wstar _ (Set.mem_iUnion.mpr ⟨n,hx⟩)

theorem generated_le (A : ℕ → FiniteMatrixStage N) : generated A ≤ N.toStarSubalgebra := by
  apply wstar_le (vonNeumann_wotClosed N)
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact (A n).units.concreteAlgebra_le hn

theorem generated_minimal (A : ℕ → FiniteMatrixStage N)
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (hR : WOTClosed R)
    (h : ∀ n,(A n).units.concreteAlgebra ≤ R) : generated A ≤ R := by
  apply wstar_le hR
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact h n hn

theorem generated_relative_scalar (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ (A n).commutant hNM) →
      c=τ.trace c • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : generated A,a.val*c.val=c.val*a.val) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  apply hirr c
  intro n
  apply (((A n).units.map (coordinateInclusion hNM)).relativeStar_mem c.val).mpr
  refine ⟨c.property,?_⟩
  intro i j
  have hi : ((A n).units.entry i j).val ∈ (A n).units.concreteAlgebra := by
    exact ((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j)
  exact hc ⟨((A n).units.entry i j).val,stage_le_generated A n hi⟩

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generatedVonNeumann_le (A : ℕ → FiniteMatrixStage N) : generatedVonNeumann A ≤ N :=
  generated_le A

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TensorRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.FiniteMatrixStage

/-! A finite refinement retaining its actual commuting matrix factor.
The relation composes, so finite energy descent can retain these witnesses. -/
section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem TensorExtension.algebra_le {E F : FiniteMatrixStage N} (h : TensorExtension E F) :
    E.units.algebra ≤ F.units.algebra := by
  obtain ⟨G,_,hG⟩ := h
  rw [hG]
  exact le_sup_left

theorem TensorExtension.refl (E : FiniteMatrixStage N) : TensorExtension E E := by
  refine ⟨scalarStage N,fun _ _ _ _ => Commute.one_right _,?_⟩
  symm
  apply sup_eq_left.mpr
  apply ((scalarStage N).units.algebra_le_iff _).mpr
  intro i j
  exact E.units.algebra.one_mem

theorem TensorExtension.trans {E F G : FiniteMatrixStage N}
    (hEF : TensorExtension E F) (hFG : TensorExtension F G) : TensorExtension E G := by
  obtain ⟨D,hD,hFD⟩ := hEF
  obtain ⟨K,hK,hGK⟩ := hFG
  have hDF : D.units.algebra ≤ F.units.algebra := by rw [hFD]; exact le_sup_right
  have hEF : E.units.algebra ≤ F.units.algebra := by rw [hFD]; exact le_sup_left
  have hDK : ∀ i j k l,Commute (D.units.entry i j) (K.units.entry k l) := by
    intro i j k l
    exact (F.units.commute_algebra_iff _).mpr (fun a b => hK a b k l) _
      (hDF (D.units.entry_mem i j))
  let P := D.units.product K.units hDK
  let eqv := (Fintype.equivFin (Fin D.size × Fin K.size)).symm
  let L : FiniteMatrixStage N := ⟨Fintype.card (Fin D.size × Fin K.size),by
    simpa using Nat.mul_pos D.positive K.positive,P.reindex eqv⟩
  refine ⟨L,?_,?_⟩
  · intro i j k l
    change Commute (E.units.entry i j)
      (D.units.entry (eqv k).1 (eqv l).1*K.units.entry (eqv k).2 (eqv l).2)
    apply (hD i j _ _).mul_right
    exact (F.units.commute_algebra_iff _).mpr (fun a b => hK a b _ _) _
      (hEF (E.units.entry_mem i j))
  · change G.units.algebra=E.units.algebra ⊔ (P.reindex eqv).algebra
    rw [P.reindex_algebra,D.units.product_algebra_eq_sup,hGK,hFD,sup_assoc]

theorem exists_tensor_refinement_descent (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (ht : τ.trace x=0) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      F.energy τ hNM x ≤ (15/16 : ℝ)*E.energy τ hNM x := by
  by_cases hz : conditionalExpectation τ (E.commutant_le hNM) x=0
  · refine ⟨E,TensorExtension.refl E,?_⟩
    simp [energy,hz]
  · obtain ⟨k,n,hn,F,hc,_,hdesc⟩ := exists_compatible_matrix_energy_descent τ hNM
      hfactor hdiff hirr E.units ⟨0,E.positive⟩ x ht hz
    have hnpos : 0 < n := by rw [hn]; positivity
    let G := E.units.product F hc
    let eqv := (Fintype.equivFin (Fin E.size × Fin n)).symm
    let S : FiniteMatrixStage N := ⟨Fintype.card (Fin E.size × Fin n),by
      simpa using Nat.mul_pos E.positive hnpos,G.reindex eqv⟩
    refine ⟨S,⟨⟨n,hnpos,F⟩,hc,?_⟩,?_⟩
    · change (G.reindex eqv).algebra=E.units.algebra ⊔ F.algebra
      rw [G.reindex_algebra,E.units.product_algebra_eq_sup]
    · change τ.norm₂ (conditionalExpectation τ
        ((G.reindex eqv).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤ _
      simp only [G.mapped_reindex_relative eqv (coordinateInclusion hNM)]
      exact hdesc

end

/-! Tensor-factor-retaining compatible refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/
section
open scoped BigOperators
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hfactor hdiff hirr

theorem exists_tensor_finite_family_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)*E.energy τ hNM (x s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨E,TensorExtension.refl E,by simp⟩
  | @insert s S hs ih =>
    obtain ⟨F,hEF,hF⟩ := ih (fun t ht' => ht t (Finset.mem_insert_of_mem ht'))
    obtain ⟨G,hFG,hG⟩ := F.exists_tensor_refinement_descent τ hNM hfactor hdiff hirr (x s)
      (ht s (Finset.mem_insert_self s S))
    refine ⟨G,hEF.trans hFG,?_⟩
    intro t ht'
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact hG.trans (mul_le_mul_of_nonneg_left (E.energy_antitone F τ hNM hEF.algebra_le _) (by norm_num))
    · exact (F.energy_antitone G τ hNM hFG.algebra_le _).trans (hF t ht')

theorem exists_tensor_iterated_energy_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (r : ℕ) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)^r*E.energy τ hNM (x s) := by
  induction r with
  | zero => exact ⟨E,TensorExtension.refl E,by simp⟩
  | succ r ih =>
    obtain ⟨F,hEF,hF⟩ := ih
    obtain ⟨G,hFG,hG⟩ := exists_tensor_finite_family_descent τ hNM hfactor hdiff hirr S x ht F
    refine ⟨G,hEF.trans hFG,?_⟩
    intro s hs
    calc G.energy τ hNM (x s) ≤ (15/16 : ℝ)*F.energy τ hNM (x s) := hG s hs
      _ ≤ (15/16 : ℝ)*((15/16 : ℝ)^r*E.energy τ hNM (x s)) :=
        mul_le_mul_of_nonneg_left (hF s hs) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem exists_tensor_finite_matrix_energy_budget {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      (∑ s ∈ S,F.energy τ hNM (x s)) < ε := by
  let A := ∑ s ∈ S,E.energy τ hNM (x s)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun s _ => E.energy_nonneg τ hNM (x s))
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε/(A+1) from div_pos hε (by positivity)) (by norm_num : (15/16 : ℝ) < 1)
  obtain ⟨F,hEF,hF⟩ := exists_tensor_iterated_energy_descent τ hNM hfactor hdiff hirr S x ht E r
  refine ⟨F,hEF,?_⟩
  have hbound : (∑ s ∈ S,F.energy τ hNM (x s)) ≤ (15/16 : ℝ)^r*A := by
    calc (∑ s ∈ S,F.energy τ hNM (x s)) ≤
        ∑ s ∈ S,(15/16 : ℝ)^r*E.energy τ hNM (x s) :=
          Finset.sum_le_sum (fun s hs => hF s hs)
      _ = _ := (Finset.mul_sum S _ _).symm
  have hsmall := (lt_div_iff₀ (by positivity : 0 < A+1)).mp hr
  have hp : 0 ≤ (15/16 : ℝ)^r := by positivity
  nlinarith

end

/-! A single increasing sequence of full matrix algebras simultaneously
kills every member of a supplied countable centered family in commutant L2. -/
open Filter
open scoped BigOperators Topology
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_countable_tensor_refinement (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : ℕ → M.toStarSubalgebra) (ht : ∀ s,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=E ∧
      (∀ n,TensorExtension (A n) (A (n+1))) ∧
      Monotone (fun n => (A n).units.algebra) ∧
      (∀ n,(∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n) ∧
      ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0) := by
  have hex (n : ℕ) (F : FiniteMatrixStage N) := exists_tensor_finite_matrix_energy_budget τ hNM
    hfactor hdiff hirr (Finset.range (n+1)) x (fun s _ => ht s) F
    ((1/2 : ℝ)^(n+1)) (by positivity)
  let next (n : ℕ) (F : FiniteMatrixStage N) := (hex n F).choose
  let A : ℕ → FiniteMatrixStage N := fun n => Nat.rec E (fun n F => next n F) n
  have hstep (n : ℕ) : TensorExtension (A n) (A (n+1)) ∧
      (∑ s ∈ Finset.range (n+1),(A (n+1)).energy τ hNM (x s)) < (1/2 : ℝ)^(n+1) :=
    (hex n (A n)).choose_spec
  have hbudget (n : ℕ) :
      (∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n := by
    cases n with
    | zero => simp
    | succ n => exact (hstep n).2
  refine ⟨A,rfl,fun n => (hstep n).1,
    monotone_nat_of_le_succ (fun n => (hstep n).1.algebra_le),hbudget,?_⟩
  intro s
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => (A n).energy_nonneg τ hNM (x s)))
    ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  filter_upwards [eventually_ge_atTop (s+1)] with n hn
  exact (Finset.single_le_sum (fun t _ => (A n).energy_nonneg τ hNM (x t))
    (Finset.mem_range.mpr (by omega))).trans (hbudget n).le

end Generator.FiniteMatrixStage

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixGenerators
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Diagonal projections and one full-support rank-one projection generate
every finite full matrix algebra, including matrices larger than size two. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [DecidableEq ι] in
theorem fullProjectionMatrix_projection [Nonempty ι] :
    IsStarProjection (fullProjectionMatrix (ι := ι)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · ext i j
    simp only [Matrix.mul_apply,fullProjectionMatrix,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul]
    field_simp
  · ext i j
    simp [fullProjectionMatrix,Matrix.star_apply]

theorem fullProjection_projection [Nonempty ι] : IsStarProjection E.fullProjection :=
  (fullProjectionMatrix_projection (ι := ι)).map E.hom

omit [StarModule ℂ A] in
theorem diagonal_commute (i j : ι) : Commute (E.entry i i) (E.entry j j) := by
  show E.entry i i*E.entry j j=E.entry j j*E.entry i i
  by_cases h : i=j
  · subst j; rfl
  · simp [E.mul_entry,h,Ne.symm h]

theorem cut_fullProjection (i j : ι) :
    E.entry i i*E.fullProjection*E.entry j j=(Fintype.card ι : ℂ)⁻¹ • E.entry i j := by
  simp only [fullProjection,hom_apply,fullProjectionMatrix,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,E.mul_entry,smul_ite,smul_zero]
  simp [E.mul_entry,smul_ite]

theorem recover_entry [Nonempty ι] (i j : ι) :
    (Fintype.card ι : ℂ) • (E.entry i i*E.fullProjection*E.entry j j)=E.entry i j := by
  rw [E.cut_fullProjection,smul_smul,mul_inv_cancel₀,one_smul]
  exact_mod_cast Fintype.card_ne_zero

theorem fullProjection_mem : E.fullProjection ∈ E.algebra := ⟨_,rfl⟩

theorem algebra_le_of_projection_mem [Nonempty ι] (S : StarSubalgebra ℂ A)
    (hd : ∀ i,E.entry i i ∈ S) (hq : E.fullProjection ∈ S) : E.algebra ≤ S := by
  apply (E.algebra_le_iff S).mpr
  intro i j
  rw [← E.recover_entry i j]
  exact S.smul_mem (S.mul_mem (S.mul_mem (hd i) hq) (hd j)) _

end MatrixUnitSystem

/-! Two actual self-adjoint generators for the weak closure of countably
many pairwise commuting finite full matrix factors. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem countable_projection_generator {ι : Type*} [Countable ι] [Nonempty ι]
    (e : ι → (H →L[ℂ] H)) (hp : ∀ i,IsStarProjection (e i))
    (hc : ∀ i j,Commute (e i) (e j)) :
    ∃ b : H →L[ℂ] H,IsSelfAdjoint b ∧ ‖b‖ ≤ 1 ∧ wstar {b}=wstar (Set.range e) := by
  obtain ⟨f,hf⟩ := exists_surjective_nat ι
  obtain ⟨b,hb,hn,hgen⟩ := CommutingProjectionEncoding.exists_selfAdjoint_generator
    (fun n => e (f n)) (fun n => hp (f n)) (fun n m => hc (f n) (f m))
  refine ⟨b,hb,hn,hgen.trans ?_⟩
  congr 1
  ext x
  constructor
  · rintro ⟨n,rfl⟩; exact ⟨f n,rfl⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨n,rfl⟩ := hf i
    exact ⟨n,rfl⟩

namespace MatrixUnitSystem
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem fullProjection_commute (E : MatrixUnitSystem ι A) (F : MatrixUnitSystem κ A)
    (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l)) :
    Commute E.fullProjection F.fullProjection := by
  apply (E.commute_algebra_iff _).mpr _ _ E.fullProjection_mem
  intro i j
  exact ((F.commute_algebra_iff _).mpr (fun k l => (hc i j k l).symm) _
    F.fullProjection_mem).symm

end MatrixUnitSystem
namespace FiniteMatrixStage
variable {N : VonNeumannAlgebra H}

theorem two_generators_of_commuting_factors (F : ℕ → FiniteMatrixStage N)
    (hc : ∀ n m,n ≠ m → ∀ i j k l,
      Commute ((F n).units.entry i j) ((F m).units.entry k l)) :
    ∃ a ∈ generated F,∃ b ∈ generated F,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=generated F := by
  classical
  let I := (n : ℕ) × Fin (F n).size
  let : Nonempty I := ⟨⟨0,⟨0,(F 0).positive⟩⟩⟩
  let (n : ℕ) : Nonempty (Fin (F n).size) := ⟨⟨0,(F n).positive⟩⟩
  let d : I → (H →L[ℂ] H) := fun i => ((F i.1).units.entry i.2 i.2).val
  let q : ℕ → (H →L[ℂ] H) := fun n => (F n).units.fullProjection.val
  have hdproj (i : I) : IsStarProjection (d i) :=
    ((F i.1).units.diagonal_projection i.2).map N.toStarSubalgebra.subtype
  have hqproj (n : ℕ) : IsStarProjection (q n) :=
    (F n).units.fullProjection_projection.map N.toStarSubalgebra.subtype
  have hdcomm (i j : I) : Commute (d i) (d j) := by
    obtain ⟨n,i⟩ := i
    obtain ⟨m,j⟩ := j
    by_cases h : n=m
    · subst m
      exact congrArg Subtype.val ((F n).units.diagonal_commute i j).eq
    · exact congrArg Subtype.val (hc n m h i i j j).eq
  have hqcomm (n m : ℕ) : Commute (q n) (q m) := by
    by_cases h : n=m
    · subst m; exact Commute.refl _
    · exact congrArg Subtype.val ((F n).units.fullProjection_commute (F m).units (hc n m h)).eq
  obtain ⟨a,ha,_,hagen⟩ := countable_projection_generator d hdproj hdcomm
  obtain ⟨b,hb,_,hbgen⟩ := countable_projection_generator q hqproj hqcomm
  have hdmem (i : I) : d i ∈ generated F :=
    stage_le_generated F i.1 (((F i.1).units.mem_concreteAlgebra _).mpr
      ((F i.1).units.entry_mem i.2 i.2))
  have hqmem (n : ℕ) : q n ∈ generated F :=
    stage_le_generated F n (((F n).units.mem_concreteAlgebra _).mpr (F n).units.fullProjection_mem)
  have hamem : a ∈ generated F := by
    have hle : wstar {a} ≤ generated F := by
      rw [hagen]
      exact wstar_le (generated_closed F) (by rintro _ ⟨i,rfl⟩; exact hdmem i)
    exact hle (subset_wstar _ rfl)
  have hbmem : b ∈ generated F := by
    have hle : wstar {b} ≤ generated F := by
      rw [hbgen]
      exact wstar_le (generated_closed F) (by rintro _ ⟨n,rfl⟩; exact hqmem n)
    exact hle (subset_wstar _ rfl)
  refine ⟨a,hamem,b,hbmem,ha,hb,le_antisymm ?_ ?_⟩
  · exact wstar_le (generated_closed F) (by rintro _ (rfl | rfl) <;> assumption)
  · apply generated_minimal F _ (wstar_closed _)
    intro n x hx
    let y : N.toStarSubalgebra := ⟨x,(F n).units.concreteAlgebra_le hx⟩
    let S := (wstar {a,b}).comap N.toStarSubalgebra.subtype
    have hdS (i : Fin (F n).size) : (F n).units.entry i i ∈ S := by
      change d ⟨n,i⟩ ∈ wstar {a,b}
      apply (wstar_mono (s := {a}) (t := {a,b}) (by simp))
      rw [hagen]
      exact subset_wstar (Set.range d) (Set.mem_range_self (⟨n,i⟩ : I))
    have hqS : (F n).units.fullProjection ∈ S := by
      change q n ∈ wstar {a,b}
      apply (wstar_mono (s := {b}) (t := {a,b}) (by simp))
      rw [hbgen]
      exact subset_wstar _ (Set.mem_range_self n)
    exact (F n).units.algebra_le_of_projection_mem S hdS hqS
      (((F n).units.mem_concreteAlgebra y).mp hx)

end FiniteMatrixStage

end

/-! The retained tensor extensions supply commuting factors generating
exactly the original matrix-union weak closure. -/
namespace FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

theorem concrete_le_iff (E : FiniteMatrixStage N) (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    E.units.concreteAlgebra ≤ S ↔ E.units.algebra ≤ S.comap N.toStarSubalgebra.subtype := by
  constructor
  · intro h x hx
    exact h ((E.units.mem_concreteAlgebra x).mpr hx)
  · intro h x hx
    let y : N.toStarSubalgebra := ⟨x,E.units.concreteAlgebra_le hx⟩
    exact h ((E.units.mem_concreteAlgebra y).mp hx)

theorem exists_commuting_factors_of_tensor_extensions (A : ℕ → FiniteMatrixStage N)
    (hzero : A 0=scalarStage N) (hstep : ∀ n,TensorExtension (A n) (A (n+1))) :
    ∃ F : ℕ → FiniteMatrixStage N,
      (∀ n m,n ≠ m → ∀ i j k l,Commute ((F n).units.entry i j) ((F m).units.entry k l)) ∧
      generated F=generated A := by
  have hm : Monotone (fun n => (A n).units.algebra) :=
    monotone_nat_of_le_succ (fun n => (hstep n).algebra_le)
  choose F hc he using hstep
  have hFA (n : ℕ) : (F n).units.algebra ≤ (A (n+1)).units.algebra := by
    rw [he n]; exact le_sup_right
  have hcomm_lt (n m : ℕ) (hnm : n < m) (i j : Fin (F n).size) (k l : Fin (F m).size) :
      Commute ((F n).units.entry i j) ((F m).units.entry k l) := by
    exact ((A m).units.commute_algebra_iff _).mpr (fun a b => hc m a b k l) _
      (hm (Nat.succ_le_of_lt hnm) (hFA n ((F n).units.entry_mem i j)))
  refine ⟨F,?_,le_antisymm ?_ ?_⟩
  · intro n m hnm i j k l
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hcomm_lt n m h i j k l
    · exact (hcomm_lt m n h k l i j).symm
  · apply generated_minimal F _ (generated_closed A)
    intro n
    apply ((F n).concrete_le_iff _).mpr
    exact (hFA n).trans (((A (n+1)).concrete_le_iff _).mp (stage_le_generated A (n+1)))
  · apply generated_minimal A _ (generated_closed F)
    intro n
    apply ((A n).concrete_le_iff _).mpr
    induction n with
    | zero =>
      rw [hzero]
      apply ((scalarStage N).units.algebra_le_iff _).mpr
      intro i j
      exact (generated F).one_mem
    | succ n ih =>
      rw [he n]
      exact sup_le ih (((F n).concrete_le_iff _).mp (stage_le_generated F n))

theorem two_generators_of_tensor_extensions (A : ℕ → FiniteMatrixStage N)
    (hzero : A 0=scalarStage N) (hstep : ∀ n,TensorExtension (A n) (A (n+1))) :
    ∃ a ∈ generated A,∃ b ∈ generated A,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=generated A := by
  obtain ⟨F,hF,hgen⟩ := exists_commuting_factors_of_tensor_extensions A hzero hstep
  rw [← hgen]
  exact two_generators_of_commuting_factors F hF

end FiniteMatrixStage

/-! The represented irreducible matrix subfactor can be constructed together
with two self-adjoint generators, without hyperfinite uniqueness. -/
namespace Tracial
open UltrapowerBridge FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_irreducible_two_generated_subfactor_oai
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ P : VonNeumannAlgebra H,P ≤ N ∧ IsII1Factor P.toStarSubalgebra ∧
      (∀ c : M.toStarSubalgebra,(∀ a : P.toStarSubalgebra,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra)) ∧
      ∃ a ∈ P,∃ b ∈ P,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=P.toStarSubalgebra := by
  let S : Set M.toStarSubalgebra := {b | τ.trace b=0}
  obtain ⟨x,hx,hdense⟩ := exists_countable_norm₂_dense τ S
    ⟨0,by change τ.trace 0=0; simp [TracialRepresentation.trace]⟩
    (hsep.mono (Set.image_subset_range _ _))
  obtain ⟨A,hA,hstep,_,_,hlim⟩ := exists_countable_tensor_refinement τ hNM
    hfactor hdiff hirr x hx (scalarStage N)
  have hscalar := generated_relative_scalar A τ hNM
    (scalar_common_commutant_of_dense_energy_decay τ hNM A x hdense hlim)
  obtain ⟨a,ha,b,hb,hsa,hsb,hgen⟩ := two_generators_of_tensor_extensions A hA hstep
  exact ⟨generatedVonNeumann A,generatedVonNeumann_le A,
    generated_isII1 A τ hNM hdiff hscalar,hscalar,a,ha,b,hb,hsa,hsb,hgen⟩

end Tracial

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor_oai.{u_1} := @OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor_oai.{u_1}
