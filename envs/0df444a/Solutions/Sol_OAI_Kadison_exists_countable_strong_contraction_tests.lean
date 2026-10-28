-- Prove2me | solution 1 for OAI.Kadison.exists_countable_strong_contraction_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:09:45.054059+00:00
-- url     : https://prove2.me/submissions/770861c7-9adc-446b-8f57-5508f2c17615

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_StrongDenseTests
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
-- module Solutions.OAIQ039_CM.Commutator_CountableStrongTests
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem exists_countable_strong_contraction_tests_oai (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → H →L[ℂ] H,(∀ n,test n∈P ∧ ‖test n‖≤1) ∧
      ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
        ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ)) := by
  let v : ℕ → H := TopologicalSpace.denseSeq H
  let S : Set (ℕ → H) := {f | ∃ A : H →L[ℂ] H,A∈P ∧ ‖A‖≤1 ∧ ∀ j,f j=A (v j)}
  have hS : S.Nonempty := ⟨fun _ => 0,0,P.zero_mem,by simp,by simp⟩
  let : Nonempty S := hS.to_subtype
  let s : ℕ → S := TopologicalSpace.denseSeq S
  choose test hP hb ht using (fun n => (s n).property)
  refine ⟨test,fun n => ⟨hP n,hb n⟩,?_⟩
  intro A hA hnA
  let f : S := ⟨fun j => A (v j),A,hA,hnA,fun _ => rfl⟩
  have hd : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  obtain ⟨u,hu,hl⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose k hk using hu
  have hlim : Tendsto (fun n => s (k n)) atTop (𝓝 f) := by
    have he : (fun n => s (k n))=u := funext hk
    rwa [he]
  have hj (j : ℕ) : Tendsto (fun n => test (k n) (v j)) atTop (𝓝 (A (v j))) := by
    have hv := (continuous_apply j |>.comp continuous_subtype_val).tendsto f |>.comp hlim
    change Tendsto (fun n => (s (k n)).val j) atTop (𝓝 (A (v j))) at hv
    simpa only [ht] using hv
  exact ⟨k,strong_tendsto_of_dense_tests v (TopologicalSpace.denseRange_denseSeq H)
    (fun n => test (k n)) A (fun n => hb (k n)) hnA hj⟩

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.exists_countable_strong_contraction_tests_oai.{u_1} := @OAI.Kadison.exists_countable_strong_contraction_tests_oai.{u_1}
