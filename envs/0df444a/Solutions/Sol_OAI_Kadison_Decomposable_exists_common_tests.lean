-- Prove2me | solution 1 for OAI.Kadison.Decomposable.exists_common_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:48:41.829491+00:00
-- url     : https://prove2.me/submissions/c1855675-346c-4b22-b781-7376bbec1fb7

import Mathlib
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C056

section
-- module Solutions.OAIQ039_CM.Commutator_StrongDenseTests
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

open scoped Topology

namespace Kadison

variable {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma strong_tendsto_of_dense_tests {ι κ : Type*} {l : Filter ι}
    (v : κ → H) (hv : DenseRange v) (T : ι → H →L[ℂ] G) (A : H →L[ℂ] G)
    (hT : ∀ i,‖T i‖≤1) (hA : ‖A‖≤1)
    (ht : ∀ j,Tendsto (fun i => T i (v j)) l (𝓝 (A (v j)))) :
    ∀ ξ,Tendsto (fun i => T i ξ) l (𝓝 (A ξ)) := by
  intro ξ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := Metric.denseRange_iff.mp hv ξ (ε/4) (by positivity)
  have hs : ‖ξ-v j‖<ε/4 := by simpa only [dist_eq_norm,norm_sub_rev] using hj
  have he := Metric.tendsto_nhds.mp (ht j) (ε/2) (by positivity)
  filter_upwards [he] with i hi
  rw [dist_eq_norm] at hi ⊢
  have h1 : ‖T i (ξ-v j)‖≤‖ξ-v j‖ :=
    ((T i).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hT i) (norm_nonneg (ξ-v j)))
  have h2 : ‖A (v j-ξ)‖≤‖ξ-v j‖ :=
    (A.le_opNorm _).trans (by simpa only [one_mul,norm_sub_rev] using
      mul_le_mul_of_nonneg_right hA (norm_nonneg (v j-ξ)))
  have hid : T i ξ-A ξ=T i (ξ-v j)+(T i (v j)-A (v j))+A (v j-ξ) := by
    simp only [map_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans_lt (by
    have hn := norm_add_le (T i (ξ-v j)) (T i (v j)-A (v j))
    linarith)

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableStarHomTests
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma countableContractions_norm (n : ℕ) : ‖countableContractions (A:=A) n‖≤1 :=
  (TopologicalSpace.denseSeq (CStarContractions A) n).property

omit [PartialOrder A] [StarOrderedRing A] in
lemma countableContractions_approx (a : A) (ha : ‖a‖≤1) {ε : ℝ} (hε : 0<ε) :
    ∃ n,‖countableContractions (A:=A) n-a‖<ε := by
  obtain ⟨n,hn⟩ := Metric.denseRange_iff.mp
    (TopologicalSpace.denseRange_denseSeq (CStarContractions A)) ⟨a,ha⟩ ε hε
  exact ⟨n,by simpa only [Subtype.dist_eq,dist_eq_norm,norm_sub_rev,countableContractions] using hn⟩

theorem countableContractions_strong_dense (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) (hnT : ‖T‖≤1) :
    ∃ k : ℕ → ℕ,∀ ξ,Tendsto
      (fun n => φ (countableContractions (A:=A) (k n)) ξ) atTop (𝓝 (T ξ)) := by
  classical
  let v : ℕ → H := TopologicalSpace.denseSeq H
  have hap (n : ℕ) : ∃ k : ℕ,∀ j : Fin n,
      ‖φ (countableContractions (A:=A) k) (v j)-T (v j)‖<1/((n:ℝ)+1) := by
    let ε : ℝ := 1/((n:ℝ)+1)
    have hε : 0<ε := by dsimp [ε]; positivity
    obtain ⟨a,ha,he⟩ := Kaplansky.range_contraction_finite_approx φ (Fin n) hT hnT
      (fun j => v j) (ε/2) (by positivity)
    let M : ℝ := 1+∑ j : Fin n,‖v j‖
    have hM : 0<M := by dsimp [M]; positivity
    obtain ⟨k,hk⟩ := countableContractions_approx a ha (div_pos (half_pos hε) hM)
    refine ⟨k,?_⟩
    intro j
    have hvM : ‖v j‖≤M := by
      have hh := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => norm_nonneg (v i))
        (Finset.mem_univ j)
      dsimp only [M]
      linarith
    have hsmall : ‖φ (countableContractions (A:=A) k-a) (v j)‖<ε/2 := by
      calc
        ‖φ (countableContractions (A:=A) k-a) (v j)‖≤
            ‖φ (countableContractions (A:=A) k-a)‖*‖v j‖ :=
          (φ (countableContractions (A:=A) k-a)).le_opNorm _
        _≤‖countableContractions (A:=A) k-a‖*‖v j‖ :=
          mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le φ _) (norm_nonneg _)
        _≤‖countableContractions (A:=A) k-a‖*M :=
          mul_le_mul_of_nonneg_left hvM (norm_nonneg _)
        _<(ε/2/M)*M := mul_lt_mul_of_pos_right hk hM
        _=ε/2 := div_mul_cancel₀ _ (ne_of_gt hM)
    have hid : φ (countableContractions (A:=A) k) (v j)-T (v j)=
        φ (countableContractions (A:=A) k-a) (v j)+(φ a (v j)-T (v j)) := by
      simp only [map_sub,sub_apply]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans_lt (by linarith [he j])
  choose k hk using hap
  have hlim (j : ℕ) : Tendsto (fun n => φ (countableContractions (A:=A) (k n)) (v j))
      atTop (𝓝 (T (v j))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop (j+1)] with n hn
    exact (hk n ⟨j,by omega⟩).le
  exact ⟨k,strong_tendsto_of_dense_tests v (TopologicalSpace.denseRange_denseSeq H)
    (fun n => φ (countableContractions (A:=A) (k n))) T
    (fun n => (NonUnitalStarAlgHom.norm_apply_le φ _).trans (countableContractions_norm _))
    hnT hlim⟩

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentationFieldTests
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]

omit [IsFiniteMeasure μ] in
theorem exists_common_tests_oai
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ)
    (hact : ∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x)) :
    ∃ (test : ℕ → Ω → H →L[ℂ] H)
      (ht : ∀ n ξ,AEStronglyMeasurable (fun x => test n x ξ) μ)
      (hb : ∀ n,∀ᵐ x ∂μ,‖test n x‖≤1),
      (∀ n,operator μ (test n) (ht n) (hb n)∈NormalGNS.bicommutant ρ.range) ∧
      (∀ n,∀ᵐ x ∂μ,test n x∈NormalGNS.bicommutant (σ x).range) ∧
      (∀ᵐ x ∂μ,∀ T : H →L[ℂ] H,T∈NormalGNS.bicommutant (σ x).range → ‖T‖≤1 →
        ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) x ξ) atTop (𝓝 (T ξ))) ∧
      (∀ T : Lp H 2 μ →L[ℂ] Lp H 2 μ,T∈NormalGNS.bicommutant ρ.range → ‖T‖≤1 →
        ∃ k : ℕ → ℕ,∀ f,Tendsto
          (fun n => operator μ (test (k n)) (ht (k n)) (hb (k n)) f) atTop (𝓝 (T f))) := by
  let test : ℕ → Ω → H →L[ℂ] H := fun n x => σ x (countableContractions (A:=A) n)
  have ht : ∀ n ξ,AEStronglyMeasurable (fun x => test n x ξ) μ :=
    fun n ξ => hm _ ξ
  have hb : ∀ n,∀ᵐ x ∂μ,‖test n x‖≤1 := fun n => Eventually.of_forall (fun x =>
    (NonUnitalStarAlgHom.norm_apply_le (σ x) _).trans (countableContractions_norm n))
  have he (n : ℕ) : operator μ (test n) (ht n) (hb n)=ρ (countableContractions (A:=A) n) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (operator_ae μ (test n) (ht n) (hb n) f).trans (hact _ f).symm
  refine ⟨test,ht,hb,?_,?_,?_,?_⟩
  · intro n
    rw [he]
    exact NormalGNS.subset_bicommutant ρ.range ⟨_,rfl⟩
  · intro n
    exact Eventually.of_forall (fun x => NormalGNS.subset_bicommutant (σ x).range ⟨_,rfl⟩)
  · apply Eventually.of_forall
    intro x T hT hn
    exact countableContractions_strong_dense (σ x) T
      ((NormalGNS.mem_bicommutant _ _).mp hT) hn
  · intro T hT hn
    obtain ⟨k,hk⟩ := countableContractions_strong_dense ρ T
      ((NormalGNS.mem_bicommutant _ _).mp hT) hn
    refine ⟨k,?_⟩
    intro f
    simpa only [he] using hk f

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.Decomposable.exists_common_tests_oai := @OAI.Kadison.Decomposable.exists_common_tests_oai
