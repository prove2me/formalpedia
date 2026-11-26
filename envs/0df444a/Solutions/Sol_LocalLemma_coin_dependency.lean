-- Prove2me | solution 1 for LocalLemma.coin_dependency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:22:33.517325+00:00
-- url     : https://prove2.me/submissions/df887812-936c-40ce-ac46-55d83e85c8d5

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Theorems.Thm_LocalLemma_CoordDep_mono
public import Theorems.Thm_LocalLemma_CoordDep_measurableSet
public import Theorems.Thm_LocalLemma_coin_indep_comap

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → Set (ι → Bool)) (D : Fin n → Finset ι) (hA : ∀ i, CoordDep (A i) (D i))
    (Γ : SimpleGraph (Fin n)) (hΓ : ∀ i j, j ≠ i → ¬ Γ.Adj i j → Disjoint (D i) (D j)) :
    ∀ i, Indep (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j})
      (coinMeasure ι) := by
  classical
  intro i
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (coin_indep_comap (D i)) ?_) ?_
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (hA i).measurableSet
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    obtain ⟨j, hji, hadj, rfl⟩ := ht
    refine ((hA j).mono ?_).measurableSet
    intro x hx
    rw [Finset.mem_compl]
    exact fun hx' => Finset.disjoint_left.1 (hΓ i j hji hadj) hx' hx
end LocalLemma
