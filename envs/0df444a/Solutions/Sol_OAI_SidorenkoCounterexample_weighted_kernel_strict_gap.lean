-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.weighted_kernel_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T07:13:07.32849+00:00
-- url     : https://prove2.me/submissions/f044dcde-9a62-4e50-9398-5816f9201c38

import Definitions.Def_SidorenkoWeightedKernelData
import Definitions.Def_SidorenkoCertificateAssembly2
attribute [local instance] OAI.SidorenkoCounterexample.OrientedKernel.finiteX OAI.SidorenkoCounterexample.OrientedKernel.finiteY OAI.SidorenkoCounterexample.OrientedKernel.nonemptyX OAI.SidorenkoCounterexample.OrientedKernel.nonemptyY
attribute [local instance] OAI.SidorenkoCounterexample.SymmetricCounterKernel.finite OAI.SidorenkoCounterexample.SymmetricCounterKernel.nonempty

open scoped BigOperators
open OAI.SidorenkoCounterexample

namespace OAI.SidorenkoCounterexample
open Classical

lemma faces_image : ∀ j : Fin 22, faces j = Finset.univ.image (faceVertex j) := by decide

noncomputable def reindexedKernel (W : SymmetricCounterKernel) : WeightedKernelData := by
  let e : Fin (Fintype.card W.Ω) ≃ W.Ω := (Fintype.equivFin W.Ω).symm
  exact {
    size := Fintype.card W.Ω
    size_pos := Fintype.card_pos
    weight := fun a => W.law.weight (e a)
    weight_nonneg := fun a => W.law.nonneg (e a)
    weight_total := by
      rw [Fintype.sum_equiv e (fun a => W.law.weight (e a)) W.law.weight (fun _ => rfl)]
      exact W.law.total
    value := fun a b => W.value (e a) (e b)
    value_symm := fun a b => W.symm (e a) (e b)
    value_nonneg := fun a b => W.nonneg (e a) (e b)
    value_le_one := fun a b => W.le_one (e a) (e b)
  }

lemma reindexedKernel_mean (W : SymmetricCounterKernel) :
    kernelEdgeMean (reindexedKernel W) = kernelMean W.law W.law W.value := by
  let e : Fin (Fintype.card W.Ω) ≃ W.Ω := (Fintype.equivFin W.Ω).symm
  unfold kernelEdgeMean kernelMean FiniteLaw.mean
  simp only [reindexedKernel, Finset.mul_sum]
  apply Fintype.sum_equiv e
  intro a
  change (∑ b, W.law.weight (e a) * W.law.weight (e b) * W.value (e a) (e b)) =
    ∑ b, W.law.weight (e a) * (W.law.weight b * W.value (e a) b)
  apply Fintype.sum_equiv e
  intro b
  ring

lemma reindexedKernel_moment (W : SymmetricCounterKernel) :
    kernelPatternMoment (reindexedKernel W) = bipartiteMoment W.law W.law W.value := by
  let e : Fin (Fintype.card W.Ω) ≃ W.Ω := (Fintype.equivFin W.Ω).symm
  rw [← sourceMoment_eq_bipartite]
  unfold kernelPatternMoment FiniteLaw.mean FiniteLaw.independent
  simp only [reindexedKernel]
  let E : (PatternVertex → Fin (Fintype.card W.Ω)) ≃ (PatternVertex → W.Ω) :=
    Equiv.arrowCongr (Equiv.refl PatternVertex) e
  apply Fintype.sum_equiv E
  intro f
  change (∏ v : PatternVertex, W.law.weight (e (f v))) *
      (∏ j : Fin 22, ∏ i ∈ faces j, W.value (e (f (.inl i))) (e (f (.inr j)))) =
    (∏ v : PatternVertex, W.law.weight (e (f v))) *
      (∏ k : ActCorner, W.value (e (f (.inl (cornerPoint k)))) (e (f (.inr k.1))))
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [faces_image, Finset.prod_image (fun a _ b _ h => faceVertex_injective j h)]
  rfl

theorem reindex_strict_kernel (W : SymmetricCounterKernel) :
    ∃ K : WeightedKernelData,
      0 < kernelEdgeMean K ∧ kernelPatternMoment K < (kernelEdgeMean K) ^ 66 := by
  refine ⟨reindexedKernel W, ?_, ?_⟩
  · rw [reindexedKernel_mean]
    exact W.mean_pos
  · rw [reindexedKernel_moment, reindexedKernel_mean]
    exact W.gap

end OAI.SidorenkoCounterexample


theorem solution :
    ∃ K : OAI.SidorenkoCounterexample.WeightedKernelData,
      0 < OAI.SidorenkoCounterexample.kernelEdgeMean K ∧
      OAI.SidorenkoCounterexample.kernelPatternMoment K <
        (OAI.SidorenkoCounterexample.kernelEdgeMean K) ^ 66 := by
  obtain ⟨W⟩ := OAI.SidorenkoCounterexample.exists_symmetric_kernel
  exact OAI.SidorenkoCounterexample.reindex_strict_kernel W

