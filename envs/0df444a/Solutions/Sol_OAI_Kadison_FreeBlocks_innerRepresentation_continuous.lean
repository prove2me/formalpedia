-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.innerRepresentation_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:03:57.45688+00:00
-- url     : https://prove2.me/submissions/32acd215-e5a3-4c52-8c61-c8766a2ceb0f

import Mathlib
import Definitions.Def_OAIQ039C059

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContinuity

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : X → E →ₗᵢ[ℂ] E)

lemma isClosed_vectors : IsClosed (vectors T : Set E) := by
  apply IsSeqClosed.isClosed
  intro u x hu hux
  have hl : TendstoUniformly (fun n g => T g (u n)) (fun g => T g x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hux ε hε] with n hn
    intro g
    simpa only [LinearIsometry.dist_map,dist_comm] using hn
  exact hl.continuous (Eventually.of_forall hu).frequently

lemma of_denseRange {ι : Type*} (v : ι → E) (hd : DenseRange v)
    (hv : ∀ i, Continuous fun g => T g (v i)) (x : E) : Continuous fun g => T g x := by
  have hs : Set.range v ⊆ (vectors T : Set E) := by rintro _ ⟨i,rfl⟩; exact hv i
  have he : (Set.univ : Set E) ⊆ (vectors T : Set E) := by
    rw [← hd.closure_range]
    exact (isClosed_vectors T).closure_subset_iff.mpr hs
  exact he (Set.mem_univ x)

end Kadison.StrongContinuity

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertStrong
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped TensorProduct InnerProductSpace Topology CStarAlgebra ComplexOrder

open UniformSpace

namespace Kadison

namespace StrongContinuity

variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma completion (T : X → E →ₗᵢ[ℂ] E)
    (hT : ∀ x, Continuous fun g => T g x) (x : Completion E) :
    Continuous fun g => completionIsometry (T g) x := by
  apply of_denseRange _ (fun x : E => (x : Completion E)) Completion.denseRange_coe _ x
  intro y
  simpa only [completionIsometry_coe, Function.comp_def] using (Completion.continuous_coe E).comp (hT y)

lemma tensor (T : X → E →ₗᵢ[ℂ] E) (S : X → F →ₗᵢ[ℂ] F)
    (hT : ∀ x, Continuous fun g => T g x) (hS : ∀ x, Continuous fun g => S g x)
    (x : E ⊗[ℂ] F) : Continuous fun g => TensorProduct.mapIsometry (T g) (S g) x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy =>
    convert hx.add hy using 1
    all_goals try with_reducible_and_instances rfl
    ext g
    exact map_add (TensorProduct.mapIsometry (T g) (S g)) x y
  | tmul x y =>
    simpa only [TensorProduct.mapIsometry_apply,TensorProduct.map_tmul,LinearIsometry.coe_toLinearMap,Function.comp_def]
      using (TensorProduct.continuous_tmul (𝕜:=ℂ) (E:=E) (F:=F)).comp ((hT x).prodMk (hS y))

lemma hilbertSum {ι H : Type*} {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ∀ i, V i →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ V U)
    (T : X → H →ₗᵢ[ℂ] H) (hT : ∀ i x, Continuous fun g => T g (U i x))
    (x : H) : Continuous fun g => T g x := by
  have hs : (⨆ i, LinearMap.range (U i).toLinearMap) ≤ vectors T := by
    apply iSup_le
    rintro i _ ⟨x,rfl⟩
    exact hT i x
  have ht := Submodule.topologicalClosure_minimal _ hs (isClosed_vectors T)
  rw [← hU.OrthogonalFamily.range_linearIsometry,
    LinearMap.range_eq_top.mpr hU.surjective_isometry] at ht
  exact ht (Submodule.mem_top : x∈(⊤:Submodule ℂ H))

end StrongContinuity

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionGroup
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma algebraVector_continuous (τ : A →ₚ[ℂ] ℂ) : Continuous (algebraVector τ) := by
  have he : (algebraVector τ : A → τ.GNS) = fun a => τ.gnsStarAlgHom a (vacuum τ) := by
    funext a
    exact (left_vacuum τ a).symm
  rw [he]
  exact (map_continuous τ.gnsStarAlgHom).clm_apply continuous_const

end Kadison.TracialGNS

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {X : Type*} [TopologicalSpace X] (α : X → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)
  (hc : ∀ i a, Continuous fun g => α g i a)

include hc

lemma letterIso_continuous (i : ι) (x : letterSpace t S i) :
    Continuous fun g => letterIso t S (α g) (hmem g) (hτ g) i x := by
  apply Continuous.subtype_mk
  apply (Completion.isUniformEmbedding_coe (preSpace t)).isEmbedding.continuous_iff.mpr
  exact (TracialGNS.algebraVector_continuous t.functional).comp (hc i (letterValue t S i x))

lemma tensorIso_continuous : ∀ is (x : tensor t S is),
    Continuous fun g => tensorIso t S (α g) (hmem g) (hτ g) is x
  | [], _ => continuous_const
  | i::is,x => StrongContinuity.tensor _ _ (letterIso_continuous t S α hmem hτ hc i)
      (tensorIso_continuous is) x

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_continuous (x : t.functional.GNS) :
    Continuous fun g => action t S (α g) (hmem g) (hτ g) hfree hgen x := by
  apply StrongContinuity.hilbertSum (wordInclusion t S hfree)
    (isHilbertSum_of_generation t S hfree hgen) _ _ x
  intro is y
  have he : (fun g => action t S (α g) (hmem g) (hτ g) hfree hgen
      (wordInclusion t S hfree is y)) = fun g => wordInclusion t S hfree is
        (completionIsometry (tensorIso t S (α g) (hmem g) (hτ g) is.val) y) := by
    funext g
    exact HilbertDiagonal.onSum_insert _ _ _ _ _ _
  rw [he]
  exact (wordInclusion t S hfree is).continuous.comp
    (StrongContinuity.completion _ (tensorIso_continuous t S α hmem hτ hc is.val) y)

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable {G : Type*} [Group G] (α : G → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)
  (h1 : ∀ i a, α 1 i a=a)
  (hmul : ∀ g h i a, α (g*h) i a=α g i (α h i a))

lemma representation_continuous [TopologicalSpace G]
    (hc : ∀ i a, Continuous fun g => α g i a) (x : t.functional.GNS) :
    Continuous fun g => representation t S hfree hgen α hmem hτ h1 hmul g x :=
  action_continuous t S α hmem hτ hc hfree hgen x

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeInnerFamily
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct CStarAlgebra

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι)
  (hS : S i=f.range)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_continuous (k : ι) (a : A) :
    Continuous fun u : unitary D => innerFamily f i u k a := by
  by_cases hk : k=i
  · subst k
    simp only [innerFamily_self]
    exact (((map_continuous f).comp continuous_subtype_val).mul continuous_const).mul
      ((map_continuous f).comp continuous_subtype_val.star)
  · simpa only [innerFamily_other f i _ hk] using (continuous_const : Continuous fun _ : unitary D => a)

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualCovariance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

omit [PartialOrder D] [StarOrderedRing D] in
lemma innerRepresentation_continuous_oai (x : t.functional.GNS) :
    Continuous fun u => innerRepresentation t ht f S i hS hfree hgen u x :=
  representation_continuous t S hfree hgen (innerFamily f i) (innerFamily_mem f S i hS)
    (innerFamily_trace t ht f i) (innerFamily_one f i) (innerFamily_mul f i)
    (innerFamily_continuous f i) x

end Kadison.FreeBlocks

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.innerRepresentation_continuous_oai.{u_1} := @OAI.Kadison.FreeBlocks.innerRepresentation_continuous_oai.{u_1}
