-- Prove2me | solution 1 for OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:12:20.409748+00:00
-- url     : https://prove2.me/submissions/c61aabe7-c5c4-4281-98b9-f0c0a7cc3ed3

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg012
import Theorems.Thm_OAI_Generator_Tracial_exists_matrixUnits_for_partition

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_sub (x y : M.toStarSubalgebra) :
    Q.pinch (x-y) = Q.pinch x - Q.pinch y := by
  simp [pinch, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem pinch_smul (c : ℂ) (x : M.toStarSubalgebra) :
    Q.pinch (c • x) = c • Q.pinch x := by
  simp [pinch, Finset.smul_sum]

theorem pinch_left (i : Fin Q.size) (x : M.toStarSubalgebra) :
    (Q.piece i).val * Q.pinch x = (Q.piece i).val * x * (Q.piece i).val := by
  rw [pinch, Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp only [← mul_assoc, (Q.piece i).property.isIdempotentElem.eq]
  · intro j _ hji
    simp only [← mul_assoc, Q.orthogonal i j hji.symm, zero_mul]
  · simp

theorem pinch_idempotent (x : M.toStarSubalgebra) : Q.pinch (Q.pinch x) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change (Q.piece i).val * Q.pinch x * (Q.piece i).val = _
  rw [Q.pinch_left]
  simp only [mul_assoc, (Q.piece i).property.isIdempotentElem.eq]

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

theorem trace_compression_pairing (q : AlgebraProjection M) (x y : M.toStarSubalgebra) :
    τ.trace (star (q.val*x*q.val)*y) = τ.trace (star x*(q.val*y*q.val)) := by
  simp only [star_mul, q.property.isSelfAdjoint.star_eq]
  rw [mul_assoc q.val (star x*q.val), τ.trace_mul_comm q.val]
  simp only [mul_assoc]

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_pairing (x y : M.toStarSubalgebra) :
    τ.trace (star (Q.pinch x)*y) = τ.trace (star x*Q.pinch y) := by
  simp only [pinch, star_sum, Finset.sum_mul, Finset.mul_sum]
  change coordinateTraceLinear τ _ = coordinateTraceLinear τ _
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i _ => trace_compression_pairing τ (Q.piece i) x y)

theorem pinch_residual_orthogonal (x : M.toStarSubalgebra) :
    inner ℂ (baseVector τ (Q.pinch x)) (baseVector τ (x-Q.pinch x)) = 0 := by
  rw [baseVector_inner_trace]
  rw [Q.pinch_pairing τ, Q.pinch_sub, Q.pinch_idempotent, sub_self, mul_zero]
  exact inner_zero_right _

theorem pinch_pythagoras (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 + τ.norm₂ (x-Q.pinch x)^2 = τ.norm₂ x^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (baseVector τ (Q.pinch x)) (baseVector τ (x-Q.pinch x))
    (Q.pinch_residual_orthogonal τ x)
  rw [← map_add, add_sub_cancel] at h
  change τ.norm₂ x * τ.norm₂ x = τ.norm₂ (Q.pinch x)*τ.norm₂ (Q.pinch x) +
    τ.norm₂ (x-Q.pinch x)*τ.norm₂ (x-Q.pinch x) at h
  simpa only [pow_two] using h.symm

theorem pinch_norm₂_le (x : M.toStarSubalgebra) : τ.norm₂ (Q.pinch x) ≤ τ.norm₂ x := by
  have h := Q.pinch_pythagoras τ x
  nlinarith [sq_nonneg (τ.norm₂ (x-Q.pinch x)), show 0 ≤ τ.norm₂ x from norm_nonneg _,
    show 0 ≤ τ.norm₂ (Q.pinch x) from norm_nonneg _]

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

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

end

end Generator

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

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

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

theorem sandwich (a : Matrix ι ι ℂ) (o i j : ι) :
    E.entry o i * E.hom a * E.entry j o = a i j • E.entry o o := by
  simp only [hom_apply, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    E.mul_entry, smul_ite, smul_zero]
  simp [E.mul_entry, smul_ite]

theorem hom_injective (o : ι) (ho : E.entry o o ≠ 0) : Function.Injective E.hom := by
  intro a b hab
  ext i j
  have h := congrArg (fun x => E.entry o i*x*E.entry j o) hab
  rw [E.sandwich, E.sandwich] at h
  exact (smul_left_injective ℂ ho) h

theorem mem_algebra (x : A) : x ∈ E.algebra ↔
    ∃ a : Matrix ι ι ℂ, (∑ i, ∑ j, a i j • E.entry i j) = x := Iff.rfl

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_ne_zero [Nontrivial A] (o : ι) : E.entry o o ≠ 0 := by
  intro h
  have hz (i : ι) : E.entry i i = 0 := by
    have hio : E.entry i o = 0 := by
      have hm := E.mul_entry i o o o
      simpa [h] using hm.symm
    have hm := E.mul_entry i o o i
    simpa [hio] using hm.symm
  have ht := E.total
  simp only [hz, Finset.sum_const_zero] at ht
  exact zero_ne_one ht

theorem injective [Nontrivial A] [Nonempty ι] : Function.Injective E.hom :=
  E.hom_injective (Classical.arbitrary ι) (E.diagonal_ne_zero _)

theorem algebra_le_iff (S : StarSubalgebra ℂ A) :
    E.algebra ≤ S ↔ ∀ i j, E.entry i j ∈ S := by
  constructor
  · exact fun h i j => h (E.entry_mem i j)
  · intro h x hx
    obtain ⟨a,rfl⟩ := (E.mem_algebra x).mp hx
    exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h i j) _

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

omit [StarModule ℂ A] in
theorem product_entry (a b : ι × κ) :
    (E.product F hc).entry a b = E.entry a.1 b.1 * F.entry a.2 b.2 := rfl

omit [StarModule ℂ A] in
theorem product_sum_left (i j : ι) :
    (∑ k, (E.product F hc).entry (i,k) (j,k)) = E.entry i j := by
  simp only [product_entry, ← Finset.mul_sum, F.total, mul_one]

theorem algebra_le_product_left : E.algebra ≤ (E.product F hc).algebra := by
  apply (E.algebra_le_iff _).mpr
  intro i j
  rw [← E.product_sum_left F hc i j]
  exact (E.product F hc).algebra.sum_mem fun k _ => (E.product F hc).entry_mem _ _

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Tracial
theorem exists_matrixAlgebra_for_unit_partition (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (Q : CornerPartition (identityProjection M)) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Generator.MatrixUnitSystem (Fin Q.size) M.toStarSubalgebra,
      (∀ i, E.entry i i=(Q.piece i).val) ∧
      Function.Injective E.hom ∧
      E.concreteAlgebra ≤ M.toStarSubalgebra ∧ WOTClosed E.concreteAlgebra := by
  obtain ⟨e,hd,hs,hm,hu⟩ := exists_matrixUnits_for_partition τ hfactor Q hn ht
  let E : Generator.MatrixUnitSystem (Fin Q.size) M.toStarSubalgebra := ⟨e,hs,hm,hu⟩
  have : Nontrivial M.toStarSubalgebra := by
    apply nontrivial_of_ne (0 : M.toStarSubalgebra) 1
    intro h
    have ht := congrArg τ.trace h
    have hz : τ.trace 0=0 := by simp [TracialRepresentation.trace]
    rw [hz,τ.trace_one] at ht
    exact zero_ne_one ht
  have : Nonempty (Fin Q.size) := ⟨⟨0,hn⟩⟩
  exact ⟨E,hd,E.injective,E.concreteAlgebra_le,E.concreteAlgebra_wotClosed⟩

end Tracial
end

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

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators
namespace Bell
variable {n : ℕ} [NeZero n]

theorem mul_leftEntry (X : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ)
    (i j : ZMod n) (a b : ZMod n × ZMod n) :
    (X * leftEntry i j) a b = if b.1=j then X a (i,b.2) else 0 := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,leftEntry,mul_ite,mul_one,mul_zero]
  by_cases h : b.1=j
  · simp [h,ite_and]
  · simp [h]

theorem projection_sandwich (s f i j : ZMod n) :
    projection s f * leftEntry i j * projection s f =
      if i=j then (n : ℂ)⁻¹ • projection s f else 0 := by
  apply Matrix.ext
  intro a b
  have hr : (if i=j then (n : ℂ)⁻¹ • projection s f else 0) a b =
      if i=j then (n : ℂ)⁻¹ * projection s f a b else 0 := by
    split_ifs <;> rfl
  rw [hr]
  rw [Matrix.mul_apply]
  simp only [mul_leftEntry,Fintype.sum_prod_type,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  have hterm (k : ZMod n) : projection s f a (i,k)*projection s f (j,k) b =
      if a.2=a.1+s ∧ b.2=b.1+s ∧ i=j then
        if k=i+s then (n : ℂ)⁻¹^2 * ZMod.stdAddChar (f*(a.1-b.1)) else 0
      else 0 := by
    by_cases ha : a.2=a.1+s
    · by_cases hb : b.2=b.1+s
      · by_cases hij : i=j
        · subst j
          by_cases hk : k=i+s
          · simp only [projection,ha,hb,hk,and_self,ite_true, if_true]
            calc
              _ = (n : ℂ)⁻¹^2 * (ZMod.stdAddChar (f*(a.1-i)) *
                    ZMod.stdAddChar (f*(i-b.1))) := by ring
              _ = _ := by rw [← AddChar.map_add_eq_mul,
                show f*(a.1-i)+f*(i-b.1)=f*(a.1-b.1) by ring]
          · simp [projection,ha,hb,hk]
        · by_cases hk : k=i+s
          · simp [projection,ha,hb,hij,hk]
          · simp [projection,ha,hb,hij,hk]
      · simp [projection,hb]
    · simp [projection,ha]
  simp_rw [hterm]
  by_cases hij : i=j <;> by_cases h : a.2=a.1+s ∧ b.2=b.1+s <;>
    simp [hij,h,projection,pow_two,mul_assoc]

end Bell

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators
namespace MatrixUnitSystem

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra) (τ : TracialRepresentation M)

theorem trace_diagonal_eq (i j : ι) : τ.trace (E.entry i i)=τ.trace (E.entry j j) := by
  have h := τ.trace_mul_comm (E.entry i j) (E.entry j i)
  simpa only [E.mul_entry,ite_true, if_true] using h

theorem trace_off_diagonal (i j : ι) (hij : i ≠ j) : τ.trace (E.entry i j)=0 := by
  have h := τ.trace_mul_comm (E.entry i i) (E.entry i j)
  simpa [E.mul_entry,hij,Ne.symm hij,TracialRepresentation.trace] using h

theorem trace_diagonal (o : ι) :
    τ.trace (E.entry o o)=(Fintype.card ι : ℂ)⁻¹ := by
  have h : (Fintype.card ι : ℂ)*τ.trace (E.entry o o)=1 := by
    calc _ = ∑ i, τ.trace (E.entry i i) := by
               simp only [E.trace_diagonal_eq τ _ o,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
         _ = τ.trace (∑ i,E.entry i i) := by
               let t : M.toStarSubalgebra →+ ℂ :=
                 { toFun := τ.trace, map_zero' := by simp [TracialRepresentation.trace],
                   map_add' := τ.trace_add }
               exact (map_sum t _ _).symm
         _ = 1 := by rw [E.total,τ.trace_one]
  exact eq_inv_of_mul_eq_one_right h

theorem trace_hom (_ : ι) (a : Matrix ι ι ℂ) :
    τ.trace (E.hom a)=(Fintype.card ι : ℂ)⁻¹*Matrix.trace a := by
  have hsum (b : ι → M.toStarSubalgebra) : τ.trace (∑ i,b i)=∑ i,τ.trace (b i) := by
    let t : M.toStarSubalgebra →+ ℂ :=
      { toFun := τ.trace, map_zero' := by simp [TracialRepresentation.trace],
                   map_add' := τ.trace_add }
    exact map_sum t _ _
  rw [E.hom_apply,hsum]
  simp only [hsum,τ.trace_smul]
  have hentry (i j : ι) : τ.trace (E.entry i j)=
      if i=j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
    split
    · next h => subst j; exact E.trace_diagonal τ i
    · next h => exact E.trace_off_diagonal τ i j h
  simp only [hentry,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  rw [Matrix.trace,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n]
variable (E F : MatrixUnitSystem (ZMod n) M.toStarSubalgebra)
variable (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l))

theorem product_hom_leftEntry (i j : ZMod n) :
    (E.product F hc).hom (Bell.leftEntry i j) = E.entry i j := by
  simp only [hom_apply,Fintype.sum_prod_type,Bell.leftEntry,ite_smul,one_smul,zero_smul]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  rw [← E.product_sum_left F hc i j]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single j]
  · simp
  · intro l hl hlj
    simp [hlj]
  · simp

theorem bellPiece_sandwich_entry (s f i j : ZMod n) :
    (E.bellPiece F hc s f).val * E.entry i j * (E.bellPiece F hc s f).val =
      if i=j then (n : ℂ)⁻¹ • (E.bellPiece F hc s f).val else 0 := by
  rw [← E.product_hom_leftEntry F hc i j]
  change ((E.product F hc).hom _ * (E.product F hc).hom _) * (E.product F hc).hom _ = _
  rw [← map_mul,← map_mul,Bell.projection_sandwich]
  split <;> simp [bellPiece,map_smul]

theorem bellPartition_pinch_entry (i j : ZMod n) :
    (E.bellPartition F hc).pinch (E.entry i j) =
      if i=j then (n : ℂ)⁻¹ • (1 : M.toStarSubalgebra) else 0 := by
  have hpiece (a : Fin (E.bellPartition F hc).size) :
      ((E.bellPartition F hc).piece a).val * E.entry i j *
        ((E.bellPartition F hc).piece a).val =
      if i=j then (n : ℂ)⁻¹ • ((E.bellPartition F hc).piece a).val else 0 :=
    E.bellPiece_sandwich_entry F hc _ _ i j
  unfold CornerPartition.pinch
  simp_rw [hpiece]
  split
  · simp only [← Finset.smul_sum,(E.bellPartition F hc).total]
    rfl
  · simp

theorem bellPartition_pinch_algebra (τ : TracialRepresentation M)
    (x : M.toStarSubalgebra) (hx : x ∈ E.algebra) :
    (E.bellPartition F hc).pinch x = τ.trace x • (1 : M.toStarSubalgebra) := by
  obtain ⟨a,rfl⟩ := hx
  change (E.bellPartition F hc).pinch (E.hom a)=τ.trace (E.hom a) • 1
  rw [E.trace_hom τ 0]
  have hsum (y : ZMod n → M.toStarSubalgebra) :
      (E.bellPartition F hc).pinch (∑ i,y i) =
        ∑ i,(E.bellPartition F hc).pinch (y i) := by
    simp only [CornerPartition.pinch,Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_comm
  simp only [hom_apply,hsum,CornerPartition.pinch_smul,E.bellPartition_pinch_entry F hc,
    smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,smul_smul]
  rw [← Finset.sum_smul,Matrix.trace,Finset.mul_sum]
  congr 1
  simp [ZMod.card,mul_comm]

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_UniformPartitions
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite equal-trace partitions in an actual diffuse algebra, constructed
by repeated exact trace cuts. No matrix units or comparison theorem are
assumed. These partitions do not yet approximate an arbitrary given
spectral partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_uniform_trace_partition (n : ℕ) (p : AlgebraProjection M)
    (r : ℝ) (hr : 0 ≤ r) (ht : τ.trace p.val=((n : ℝ)*r : ℂ)) :
    ∃ Q : CornerPartition p,Q.size=n ∧ ∀ i,τ.trace (Q.piece i).val=(r : ℂ) := by
  induction n generalizing p with
  | zero =>
    have hp0 : p.val=0 := by
      by_contra h
      have hpos := projection_trace_pos τ p.val p.property h
      simp only [Nat.cast_zero,zero_mul,Complex.ofReal_zero] at ht
      rw [ht,Complex.zero_re] at hpos
      exact (lt_irrefl 0 hpos)
    refine ⟨⟨0,Fin.elim0,fun i => Fin.elim0 i,?_⟩,rfl,fun i => Fin.elim0 i⟩
    simpa only [Finset.univ_eq_empty,Finset.sum_empty] using hp0.symm
  | succ n ih =>
    have hrp : r ≤ (τ.trace p.val).re := by
      have htR := congrArg Complex.re ht
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero,Nat.cast_succ] at htR
      rw [htR]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨q,hq,hpq,hqp,hqt⟩ :=
      exists_exact_trace_subprojection τ hdiff p.val p.property r hr hrp
    let s : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
    have hst : τ.trace s.val=((n : ℝ)*r : ℂ) := by
      change τ.trace (p.val-q)=_
      rw [trace_sub,ht,hqt]
      push_cast
      ring
    obtain ⟨Q,hsize,hQ⟩ := ih s hst
    have hleft (i : Fin Q.size) : q*(Q.piece i).val=0 := by
      have hle : (p.val-q)*(Q.piece i).val=(Q.piece i).val := Q.piece_le i
      calc q*(Q.piece i).val = q*((p.val-q)*(Q.piece i).val) := by rw [hle]
        _ = 0 := by rw [← mul_assoc,mul_sub,hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
    have hright (i : Fin Q.size) : (Q.piece i).val*q=0 := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq,
        (Q.piece i).property.isSelfAdjoint.star_eq,star_zero] using congrArg star (hleft i)
    let a : Fin (Q.size+1) → AlgebraProjection M := Fin.cons ⟨q,hq⟩ Q.piece
    have ha (i j : Fin (Q.size+1)) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact hleft j
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact hright i
        · intro hij
          exact Q.orthogonal i j (fun h => hij (congrArg Fin.succ h))
    have hat : (∑ i,(a i).val)=p.val := by
      rw [Fin.sum_univ_succ]
      change q+(∑ i,(Q.piece i).val)=p.val
      rw [Q.total]
      change q+(p.val-q)=p.val
      abel
    let R : CornerPartition p := ⟨Q.size+1,a,ha,hat⟩
    refine ⟨R,congrArg (fun k => k+1) hsize,?_⟩
    intro i
    exact Fin.cases hqt hQ i

/-! Complete finitely many orthogonal grid-trace projections to an actual
equal-trace unit partition, retaining explicit disjoint groups of pieces. -/

/-! Quantitative equal-trace approximation by rounding down spectral pieces.
All projections and partitions are constructed in the given diffuse algebra. -/

end

/-! A finite commuting self-adjoint family admits simultaneous L2 spectral
approximation on one constructed dyadic equal-trace partition. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

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

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

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

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_commuting_matrix_extension
    (τ : TracialRepresentation M) (E : MatrixUnitSystem ι M.toStarSubalgebra) (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (n : ℕ) (hn : 0 < n) :
    ∃ F : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l),
        Function.Injective F.hom ∧
        (∀ j,τ.trace (F.entry j j)=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
        E.algebra ≤ (E.product F hc).algebra ∧
        WOTClosed (E.product F hc).concreteAlgebra := by
  let C := E.relativeVonNeumann
  let τC := restrictedTrace τ E.relativeVonNeumann_le
  obtain ⟨Q,hsize,ht⟩ := exists_uniform_trace_partition τC (E.relative_diffuse o hdiff)
    n (identityProjection C) (n : ℝ)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n)) (by
      change τC.trace 1=(n : ℂ)*(((n : ℝ)⁻¹ : ℝ) : ℂ)
      simp [τC.trace_one,hn.ne'])
  subst n
  obtain ⟨G,hdiag,hG,hGM,hGW⟩ := exists_matrixAlgebra_for_unit_partition τC
    (E.relative_scalar_center o hfactor) Q hn (fun i j => (ht i).trans (ht j).symm)
  let f := coordinateInclusion E.relativeVonNeumann_le
  let F := G.map f
  have hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l) := by
    intro i j k l
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry k l).val).mp (G.entry k l).property).2 i j
  refine ⟨F,hc,?_,?_,E.algebra_le_product_left F hc,
    (E.product F hc).concreteAlgebra_wotClosed⟩
  · intro a b hab
    apply hG
    have hm (a : Matrix (Fin Q.size) (Fin Q.size) ℂ) : F.hom a=f (G.hom a) := by
      simp only [MatrixUnitSystem.hom_apply,map_sum,map_smul]
      rfl
    rw [hm,hm] at hab
    exact (StarSubalgebra.inclusion_injective E.relativeVonNeumann_le) hab
  · intro j
    change τC.trace (G.entry j j)=_
    rw [hdiag]
    exact ht j

end Tracial

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

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

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

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bicommutantVonNeumann_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantVonNeumann S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  exact bicommutantStar_coe S

theorem wstar_starAlgebra_eq_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    wstar (S : Set (H →L[ℂ] H))=(bicommutantVonNeumann S).toStarSubalgebra := by
  apply le_antisymm
  · apply wstar_le (Tracial.vonNeumann_wotClosed _)
    intro a ha
    change a ∈ (bicommutantVonNeumann S : Set (H →L[ℂ] H))
    rw [bicommutantVonNeumann_coe]
    exact fun b hb => (hb a ha).symm
  · intro a ha
    have hb : a ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
      rwa [← bicommutantVonNeumann_coe]
    rw [← SetLike.mem_coe,← wotClosed_bicommutant _ (wstar_closed _)]
    exact fun b hb' => hb b (fun c hc => hb' c (subset_wstar _ hc))

namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {N M : VonNeumannAlgebra H}

theorem stageUnion_coe (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    (stageUnion A : Set (H →L[ℂ] H))=⋃ n,((A n).units.concreteAlgebra : Set (H →L[ℂ] H)) :=
  StarSubalgebra.coe_iSup_of_directed hA.directed_le

theorem generated_eq_wstar_union (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    generated A=wstar (stageUnion A : Set (H →L[ℂ] H)) := by
  rw [stageUnion_coe A hA]
  rfl

theorem exists_stage_strong_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (T : generated A)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ a : (A n).units.concreteAlgebra,∀ x ∈ s,‖T.val x-a.val x‖ < ε := by
  have hT : T.val ∈ Set.centralizer (Set.centralizer (stageUnion A : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    change T.val ∈ (bicommutantVonNeumann (stageUnion A)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,← generated_eq_wstar_union A hA]
    exact T.property
  obtain ⟨a,ha⟩ := bicommutant_finite_strong_approximation (stageUnion A) T.val hT s ε hε
  have hm := a.property
  rw [← SetLike.mem_coe,stageUnion_coe A hA] at hm
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hm
  exact ⟨n,⟨a.val,hn⟩,ha⟩

theorem exists_stage_norm₂_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ a : M.toStarSubalgebra,a.val ∈ (A n).units.concreteAlgebra ∧ τ.norm₂ (x-a) < ε := by
  classical
  obtain ⟨n,a,ha⟩ := exists_stage_strong_approximation A hA ⟨x.val,hx⟩ {τ.vector} ε hε
  exact ⟨n,⟨a.val,hNM ((A n).units.concreteAlgebra_le a.property)⟩,a.property,
    ha τ.vector (Finset.mem_singleton_self _)⟩

end FiniteMatrixStage

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixExpectation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Construct contractive expectations onto the actual finite matrix stages.
For every element of their weak closure, these expectations converge in L2
and remain in its operator norm ball. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem conditionalExpectation_best_approximation (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x y : M.toStarSubalgebra) (hy : y.val ∈ N) :
    τ.norm₂ (x-conditionalExpectation τ hNM x) ≤ τ.norm₂ (x-y) := by
  have he : conditionalExpectation τ hNM (x-y)=conditionalExpectation τ hNM x-y := by
    change conditionalExpectationCLM τ hNM (x-y)=_
    rw [map_sub]
    change conditionalExpectation τ hNM x-conditionalExpectation τ hNM y=_
    rw [conditionalExpectation_fixed τ hNM y hy]
  have h := conditionalExpectation_pythagoras τ hNM (x-y)
  rw [he,show x-y-(conditionalExpectation τ hNM x-y)=x-conditionalExpectation τ hNM x by abel] at h
  nlinarith [sq_nonneg (τ.norm₂ (conditionalExpectation τ hNM x-y)),
    show 0 ≤ τ.norm₂ (x-y) from norm_nonneg _]

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem stageExpectation_mem (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    (E.stageExpectation τ hNM x).val ∈ E.units.concreteAlgebra :=
  conditionalExpectation_mem τ (E.stageVonNeumann_le.trans hNM) x

theorem stageExpectation_norm₂_tendsto (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) :
    Tendsto (fun n => τ.norm₂ (x-(A n).stageExpectation τ hNM x)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n,y,hy,he⟩ := exists_stage_norm₂_approximation A hA τ hNM x hx ε hε
  refine ⟨n,?_⟩
  intro m hm
  have h := conditionalExpectation_best_approximation τ
    ((A m).stageVonNeumann_le.trans hNM) x y (hA hm hy)
  change τ.norm₂ (x-(A m).stageExpectation τ hNM x) ≤ τ.norm₂ (x-y) at h
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (show 0 ≤ τ.norm₂ _ from norm_nonneg _)]
    using h.trans_lt he

end FiniteMatrixStage

/-! Construct scalarizing partitions for an actual finite matrix algebra
inside a diffuse finite factor. No chain or pinching hypothesis is assumed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_scalar_pinching_for_matrixUnits
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    {n : ℕ} (hn : 0 < n) (E : MatrixUnitSystem (Fin n) M.toStarSubalgebra) :
    ∃ Q : CornerPartition (identityProjection M),
      ∀ x : M.toStarSubalgebra,x ∈ E.algebra → Q.pinch x=τ.trace x • (1 : M.toStarSubalgebra) := by
  let : NeZero n := ⟨hn.ne'⟩
  let e : ZMod n ≃ Fin n := Fintype.equivOfCardEq (by simp)
  let E' := E.reindex e
  obtain ⟨F,hc,_,_,_,_⟩ := exists_commuting_matrix_extension τ E' 0 hfactor hdiff n hn
  let F' := F.reindex e
  have hc' : ∀ i j k l,Commute (E'.entry i j) (F'.entry k l) :=
    fun i j k l => hc i j (e k) (e l)
  refine ⟨E'.bellPartition F' hc',fun x hx => ?_⟩
  apply E'.bellPartition_pinch_algebra F' hc' τ x
  rwa [MatrixUnitSystem.reindex_algebra]

end Tracial

/-! Finite matrix approximation and Bell partitions give actual small
pinching energy. The commuting matrix factor is constructed, not assumed. -/
open Filter
open scoped BigOperators Topology
namespace FiniteMatrixStage

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

theorem exists_matrix_approximated_centered_partition (τ : TracialRepresentation N)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    {ι : Type*} (F : Finset ι) (x : ι → N.toStarSubalgebra)
    (hx : ∀ i ∈ F,(x i).val ∈ generated A)
    (ht : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection N),
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  have hi (i : ι) (hi : i ∈ F) : Tendsto
      (fun n => τ.norm₂ (x i-(A n).stageExpectation τ le_rfl (x i))^2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      (stageExpectation_norm₂_tendsto A hA τ le_rfl (x i) (hx i hi)).pow 2
  have hlim : Tendsto
      (fun n => ∑ i ∈ F,τ.norm₂ (x i-(A n).stageExpectation τ le_rfl (x i))^2)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum F hi
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨Q,hQ⟩ := exists_scalar_pinching_for_matrixUnits τ hfactor hdiff
    (A n).positive (A n).units
  refine ⟨Q,lt_of_le_of_lt (Finset.sum_le_sum fun i hi => ?_) hn⟩
  have hm : (A n).stageExpectation τ le_rfl (x i) ∈ (A n).units.algebra :=
    ((A n).units.mem_concreteAlgebra _).mp ((A n).stageExpectation_mem τ le_rfl (x i))
  have hz : Q.pinch ((A n).stageExpectation τ le_rfl (x i))=0 := by
    rw [hQ _ hm]
    change τ.trace (conditionalExpectation τ _ (x i)) • (1 : N.toStarSubalgebra)=0
    rw [conditionalExpectation_trace,ht i hi,zero_smul]
  have he : Q.pinch (x i)=Q.pinch (x i-(A n).stageExpectation τ le_rfl (x i)) := by
    rw [Q.pinch_sub,hz,sub_zero]
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (Q.pinch_norm₂_le τ _) 2

theorem restrictStage_concreteAlgebra (E : FiniteMatrixStage N) (R : VonNeumannAlgebra H)
    (hER : E.units.concreteAlgebra ≤ R.toStarSubalgebra) :
    (E.restrictStage R hER).units.concreteAlgebra=E.units.concreteAlgebra := by
  have hh (a : Matrix (Fin E.size) (Fin E.size) ℂ) :
      (E.restrictStage R hER).units.concreteHom a = E.units.concreteHom a := by
    change R.toStarSubalgebra.subtype ((E.restrictStage R hER).units.hom a) =
      N.toStarSubalgebra.subtype (E.units.hom a)
    change R.toStarSubalgebra.subtype
        (∑ i, ∑ j, a i j • (E.restrictStage R hER).units.entry i j) =
      N.toStarSubalgebra.subtype (∑ i, ∑ j, a i j • E.units.entry i j)
    simp only [map_sum,map_smul]
    rfl
  change (E.restrictStage R hER).units.concreteHom.range=E.units.concreteHom.range
  congr 1
  exact DFunLike.ext _ _ hh

theorem exists_matrix_generated_centered_partition_oai (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation (generatedVonNeumann A))
    (hfactor : IsII1Factor (generated A))
    {ι : Type*} (F : Finset ι) (x : ι → (generatedVonNeumann A).toStarSubalgebra)
    (ht : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection (generatedVonNeumann A)),
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  let B (n : ℕ) := (A n).restrictStage (generatedVonNeumann A) (stage_le_generated A n)
  have hB (n : ℕ) : (B n).units.concreteAlgebra=(A n).units.concreteAlgebra :=
    (A n).restrictStage_concreteAlgebra _ _
  have hmono : Monotone (fun n => (B n).units.concreteAlgebra) := by
    simpa only [hB] using hA
  have hgen : generated B=generated A := by simp only [generated,hB]
  apply exists_matrix_approximated_centered_partition τ
    (fun c hc => by
      obtain ⟨z,hz⟩ := hfactor.factor c hc
      refine ⟨z,?_⟩
      apply Subtype.ext
      exact congrArg (fun x : generated A => (x : H →L[ℂ] H)) hz)
    hfactor.diffuse B hmono F x (fun i _ => ?_) ht ε hε
  rw [hgen]
  exact (x i).property

end

/-! Countably many finite matrix algebras give L2 separability of their weak closure. -/
open UltrapowerBridge Tracial

end FiniteMatrixStage

/-! The actual finite-stage conditional expectations converge strongly and
adjoint-strongly on every vector in the given representation. The generated
algebra also has a constructed separable faithful cyclic Hilbert representation. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition_oai.{u_1, u_2} := @OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition_oai.{u_1, u_2}
