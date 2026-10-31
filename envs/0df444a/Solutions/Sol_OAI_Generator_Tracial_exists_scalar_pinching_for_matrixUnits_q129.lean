-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:53:39.660393+00:00
-- url     : https://prove2.me/submissions/043c8d11-6d44-4b4d-a2cf-dafdebadf523

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G008
import Theorems.Thm_OAI_Generator_Tracial_exists_commuting_matrix_extension_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

omit [StarModule ℂ A] in
theorem product_entry (a b : ι × κ) :
    (E.product F hc).entry a b = E.entry a.1 b.1 * F.entry a.2 b.2 := rfl

omit [StarModule ℂ A] in
theorem product_sum_left (i j : ι) :
    (∑ k, (E.product F hc).entry (i,k) (j,k)) = E.entry i j := by
  simp only [product_entry, ← Finset.mul_sum, F.total, mul_one]

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

theorem pinch_smul (c : ℂ) (x : M.toStarSubalgebra) :
    Q.pinch (c • x) = c • Q.pinch x := by
  simp [pinch, Finset.smul_sum]

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixExpectation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Construct contractive expectations onto the actual finite matrix stages.
For every element of their weak closure, these expectations converge in L2
and remain in its operator norm ball. -/
open Filter
open scoped Topology

/-! Construct scalarizing partitions for an actual finite matrix algebra
inside a diffuse finite factor. No chain or pinching hypothesis is assumed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_scalar_pinching_for_matrixUnits_q129_oai
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
  obtain ⟨F,hc,_,_,_,_⟩ := exists_commuting_matrix_extension_q129 τ E' 0 hfactor hdiff n hn
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

/-! The actual finite-stage conditional expectations converge strongly and
adjoint-strongly on every vector in the given representation. The generated
algebra also has a constructed separable faithful cyclic Hilbert representation. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129_oai.{u_1} := @OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129_oai.{u_1}
