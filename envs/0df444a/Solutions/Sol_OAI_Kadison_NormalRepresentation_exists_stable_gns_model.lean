-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.exists_stable_gns_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:53:02.786458+00:00
-- url     : https://prove2.me/submissions/3aa8edaa-18d5-44f8-b73e-5c62e2526e74

import Mathlib
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_FaithfulNormalFunctional_gnsEmbedding_intertwines
import Theorems.Thm_OAI_Kadison_HilbertModuleSB_exists_unitary_of_embeddings
import Theorems.Thm_OAI_Kadison_NormalRepresentation_exists_countable_gns_embedding

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulNormalFunctional
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H]

variable (x : ℕ → H)

variable [InnerProductSpace ℂ H] [CompleteSpace H]


lemma functional_faithful (hd : DenseRange x) (T : H →L[ℂ] H)
    (hz : functional x (star T*T)=0) : T=0 := by
  have hzero (n : ℕ) : T (x n)=0 := by
    have hterm : term x n (star T*T)=0 := by
      apply le_antisymm ?_ (term_nonneg x n (star_mul_self_nonneg _))
      have ht := (term_summable x (star T*T)).le_tsum n
        (fun j _ => term_nonneg x j (star_mul_self_nonneg _))
      exact ht.trans_eq hz
    change (weight x n:ℂ)*inner ℂ (x n) (T.adjoint (T (x n)))=0 at hterm
    rw [ContinuousLinearMap.adjoint_inner_right] at hterm
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (weight_pos x n))))
  ext y
  exact hd.induction_on y (isClosed_eq T.continuous continuous_const) hzero

lemma functional_boundedWOT (C : ℝ) :
    Continuous (fun a : {T : H →WOT[ℂ] H // ‖T.toCLM‖≤C} => functional x a.val.toCLM) := by
  apply continuous_tsum
    (u:=fun n => (1/2:ℝ)^n*max C 0)
  · intro n
    exact continuous_const.mul (ContinuousLinearMapWOT.continuous_inner_apply
      continuous_subtype_val (x n) (x n))
  · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_right _
  · intro n a
    exact (term_bound x n a.val.toCLM).trans (mul_le_mul_of_nonneg_left
      (a.property.trans (le_max_left _ _)) (by positivity))

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulNormalStateProducer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison

namespace FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H) (M : VonNeumannAlgebra H)

lemma restricted_faithful (hd : DenseRange x) (a : M)
    (hz : restricted x M (star a*a)=0) : a=0 :=
  Subtype.ext (functional_faithful x hd (a : H →L[ℂ] H) hz)

lemma restricted_normal : NormalGNS.BoundedWOTContinuous M (restricted x M) := by
  intro C
  let f : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} →
      {T : H →WOT[ℂ] H // ‖T.toCLM‖≤C} := fun a => ⟨a.val,a.property.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk (fun a => a.property.2)
  exact (functional_boundedWOT x C).comp hf

end FaithfulNormalFunctional

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteReindex
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι κ : Type*}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma reindex_intertwines (e : ι ↪ κ) (T : H →L[ℂ] H) (x : Space ι H) :
    reindex e (map T x)=map T (reindex e x) := by
  classical
  ext k
  by_cases hk : k∈Set.range e
  · obtain ⟨i,rfl⟩ := hk
    simp only [reindex_apply,map_apply]
  · change Function.extend e (map T x) 0 k=T (Function.extend e x 0 k)
    rw [Function.extend_apply' _ _ _ hk,Function.extend_apply' _ _ _ hk]
    exact (map_zero T).symm

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableGNSModule
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison
namespace InfiniteAmplification

variable {ι H G : Type*} [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma stableEmbedding_intertwines (V : H →ₗᵢ[ℂ] Space ι G)
    (S : H →L[ℂ] H) (T : G →L[ℂ] G) (hV : ∀ x i,V (S x) i=T (V x i))
    (x : Space ℕ H) :
    stableEmbedding V (map S x)=map T (stableEmbedding V x) := by
  let := Encodable.ofCountable (ℕ×ι)
  change reindex (Encodable.encode' (ℕ×ι)) (flatten (mapIsometry V (map S x)))=
    map T (reindex (Encodable.encode' (ℕ×ι)) (flatten (mapIsometry V x)))
  rw [←reindex_intertwines]
  congr 1
  ext p
  exact hV (x p.1) p.2

private lemma stable_unitary_of_embeddings {A : Type*} [CStarAlgebra A]
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (V : H →ₗᵢ[ℂ] Space ι G) (W : G →ₗᵢ[ℂ] Space ℕ H)
    (hV : ∀ a x i, V (φ a x) i=ψ a (V x i))
    (hW : ∀ a x i, W (ψ a x) i=φ a (W x i)) :
    ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G,
      ∀ a x, U (map (φ a) x)=map (ψ a) (U x) := by
  exact HilbertModuleSB.exists_unitary_of_embeddings
    ((diagonal (ι:=ℕ) (H:=H)).comp φ) ((diagonal (ι:=ℕ) (H:=G)).comp ψ)
    (stableEmbedding V) (stableEmbedding W)
    (fun a x => stableEmbedding_intertwines V (φ a) (ψ a) (hV a) x)
    (fun a x => stableEmbedding_intertwines W (ψ a) (φ a) (hW a) x)

end InfiniteAmplification

namespace NormalRepresentation

open InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

private lemma stable_gns_model_of_embedding [TopologicalSpace.SeparableSpace H]
    (τ : M →ₚ[ℂ] ℂ) (hn : NormalGNS.BoundedWOTContinuous M τ)
    (hf : ∀ a, τ (star a*a)=0 → a=0)
    (W : τ.GNS →ₗᵢ[ℂ] Space ℕ H)
    (hW : ∀ (a : M) x i, W (τ.gnsStarAlgHom a x) i=a.val (W x i)) :
    ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ τ.GNS,
      ∀ (a : M) x, U (map a.val x)=map (τ.gnsStarAlgHom a) (U x) := by
  have embeddings := exists_countable_gns_embedding (H:=H) M τ hn hf
  obtain ⟨ι,hι,V,hV⟩ := embeddings
  let : Countable ι := hι
  exact stable_unitary_of_embeddings (H:=H) (G:=τ.GNS) (ι:=ι) (A:=M)
    M.subtype τ.gnsStarAlgHom V W hV hW

theorem exists_stable_gns_model_oai [TopologicalSpace.SeparableSpace H] :
    ∃ τ : M →ₚ[ℂ] ℂ, NormalGNS.BoundedWOTContinuous M τ ∧
      (∀ a,τ (star a*a)=0 → a=0) ∧
      ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ τ.GNS,
        ∀ (a : M) x,U (map (a : H →L[ℂ] H) x)=map (τ.gnsStarAlgHom a) (U x) := by
  let x : ℕ → H := TopologicalSpace.denseSeq H
  have hx : DenseRange x := TopologicalSpace.denseRange_denseSeq H
  let τ := FaithfulNormalFunctional.restricted x M
  have hn := FaithfulNormalFunctional.restricted_normal x M
  have hf := FaithfulNormalFunctional.restricted_faithful x M hx
  refine ⟨τ,hn,hf,?_⟩
  exact stable_gns_model_of_embedding M τ hn hf
    (FaithfulNormalFunctional.gnsEmbedding x M)
    (FaithfulNormalFunctional.gnsEmbedding_intertwines x M)

end NormalRepresentation

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalRepresentation.exists_stable_gns_model_oai.{u_1} := @OAI.Kadison.NormalRepresentation.exists_stable_gns_model_oai.{u_1}
