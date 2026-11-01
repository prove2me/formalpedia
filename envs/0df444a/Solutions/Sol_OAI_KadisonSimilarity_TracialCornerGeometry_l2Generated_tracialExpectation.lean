-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:59:41.554743+00:00
-- url     : https://prove2.me/submissions/d17e67c5-c936-4ad3-a161-7bdf1deac20a

import Mathlib
import Definitions.Def_OAIQ075A018
import Definitions.Def_OAIQ075A036

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialNormalSpan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed star subalgebra of a finite von Neumann algebra generates
exactly the bounded elements in the closure of its trace vectors. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonSimilarity.ambient_closed
variable (S : StarSubalgebra ℂ M.toStarSubalgebra) [IsClosed (S : Set M.toStarSubalgebra)]

theorem tracialSeedVonNeumann_le : tracialSeedVonNeumann S ≤ M := by
  intro T hT
  change T ∈ representationVonNeumannAlgebra (tracialSeedRepresentation S) at hT
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  intro b hb
  apply hT b
  rintro _ ⟨a, rfl⟩
  exact hb _ a.val.property

theorem seed_mem_tracialSeedVonNeumann (a : S) :
    ((a : M.toStarSubalgebra) : H →L[ℂ] H) ∈ tracialSeedVonNeumann S :=
  mem_representationVonNeumannAlgebra (tracialSeedRepresentation S) a

theorem normal_mem_iff_traceVector_mem_seed_closure (τ : TracialRepresentation M)
    (x : M.toStarSubalgebra) :
    (x : H →L[ℂ] H) ∈ tracialSeedVonNeumann S ↔
      baseVector τ x ∈ closure (baseVector τ '' (S : Set M.toStarSubalgebra)) := by
  constructor
  · intro hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a, _, ha, _⟩ := twoVectorKaplanskyInput (tracialSeedRepresentation S)
      (x : H →L[ℂ] H) hx τ.vector τ.vector (ε / 2) (by positivity)
    refine ⟨baseVector τ (a : M.toStarSubalgebra), ⟨a, a.property, rfl⟩, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact ha.trans_lt (by linarith)
  · intro hx
    apply mem_of_traceVector_mem_closure τ (tracialSeedVonNeumann_le S) x
    apply closure_mono _ hx
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, seed_mem_tracialSeedVonNeumann S ⟨a, ha⟩, rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GeneratedNormalRange
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded L²-generated algebra has a normal range whenever the
ambient tracial geometry has a faithful normal left range. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

namespace TracialCornerGeometry
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem exists_l2Generated_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) (S : StarSubalgebra ℂ A) :
    ∃ N : VonNeumannAlgebra H, (G.l2GeneratedAlgebra S).map G.left = N.toStarSubalgebra := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  let S₀ := S.topologicalClosure
  let S₁ : StarSubalgebra ℂ M.toStarSubalgebra := S₀.map e.toStarAlgHom
  have hS₀ : IsClosed (S₀ : Set A) := S.isClosed_topologicalClosure
  let : IsClosed (S₀ : Set A) := hS₀
  have hS₁ : IsClosed (S₁ : Set M.toStarSubalgebra) := by
    change IsClosed (e '' (S₀ : Set A))
    exact (StarAlgEquiv.isometry e).isClosedEmbedding.isClosedMap _ hS₀
  let : IsClosed (S₁ : Set M.toStarSubalgebra) := hS₁
  let N := tracialSeedVonNeumann S₁
  have hN : N ≤ M := tracialSeedVonNeumann_le S₁
  have hv (a : A) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have hset : Generator.Tracial.baseVector τ '' (S₁ : Set M.toStarSubalgebra) =
      Set.range (G.baseAlgebraVectors S₀) := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, heq⟩ := hb
      change e a = b at heq
      subst b
      exact ⟨⟨a, ha⟩, (hv a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e (a : A), ⟨(a : A), a.property, rfl⟩, hv (a : A)⟩
  have hmem (a : A) : G.left a ∈ N ↔ a ∈ G.l2GeneratedAlgebra S := by
    have h := normal_mem_iff_traceVector_mem_seed_closure S₁ τ (e a)
    rw [hv, hset] at h
    exact h
  refine ⟨N, ?_⟩
  ext T
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hmem a).mpr ha
  · intro hT
    have hTM : T ∈ G.left.range := by
      rw [hrange]
      exact hN hT
    obtain ⟨a, rfl⟩ := hTM
    exact ⟨a, (hmem a).mp hT, rfl⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalTracialExpectations
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-preserving expectations on the actual normal subalgebras of a
faithful tracial geometry, including its constructed L²-generated algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem tracialExpectation_of_normal_range
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (S : StarSubalgebra ℂ A) (N : VonNeumannAlgebra H)
    (hSrange : S.map G.left = N.toStarSubalgebra) :
    Nonempty (TracialExpectation G.trace S) := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  have hNM : N ≤ M := by
    intro T hT
    change T ∈ M.toStarSubalgebra
    rw [← hrange]
    change T ∈ N.toStarSubalgebra at hT
    rw [← hSrange] at hT
    obtain ⟨a, _, rfl⟩ := hT
    exact ⟨a, rfl⟩
  have he : (insideAlgebra (M := M) (P := N)).comap e.toStarAlgHom = S := by
    ext a
    change G.left a ∈ N.toStarSubalgebra ↔ a ∈ S
    rw [← hSrange]
    constructor
    · rintro ⟨b, hb, heq⟩
      exact (G.left_injective hf heq) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  have E := (concreteTracialExpectation τ hNM).comapEquiv e
    (fun a => G.normalTracialRepresentation_trace h1 hf M hrange a)
  rw [he] at E
  exact ⟨E⟩

theorem l2Generated_tracialExpectation_oai
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (S : StarSubalgebra ℂ A) :
    Nonempty (TracialExpectation G.trace (G.l2GeneratedAlgebra S)) := by
  obtain ⟨N, hN⟩ := G.exists_l2Generated_normal_range h1 hf M hrange S
  exact G.tracialExpectation_of_normal_range h1 hf M hrange _ N hN

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation_oai.{u_1, u_2}
