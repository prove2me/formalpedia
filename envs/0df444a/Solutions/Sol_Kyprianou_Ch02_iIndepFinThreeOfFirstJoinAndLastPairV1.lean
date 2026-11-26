-- Prove2me | solution 1 for Kyprianou.Ch02.iIndepFinThreeOfFirstJoinAndLastPairV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:29:52.68157+00:00
-- url     : https://prove2.me/submissions/33283851-1bef-42f4-8abb-ab554687e399

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : Fin 3 → MeasurableSpace Ω)
    (h0 : Indep (m 0) (m 1 ⊔ m 2) P)
    (h12 : Indep (m 1) (m 2) P) :
    iIndep m P := by
  rw [iIndep_iff]
  intro s f hf
  have key : ∀ t : Finset (Fin 3), t ⊆ {1, 2} → (∀ i ∈ t, MeasurableSet[m i] (f i)) → P (⋂ i ∈ t, f i) = ∏ i ∈ t, P (f i) := by
    intro t ht hm
    have H : ∀ u : Finset (Fin 3), u ⊆ {1, 2} → u = ∅ ∨ u = {1} ∨ u = {2} ∨ u = {1, 2} := by decide
    have hcases := H t ht
    rcases hcases with rfl | rfl | rfl | rfl
    · have e : (⋂ i ∈ (∅ : Finset (Fin 3)), f i) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_iInter₂.2 fun i hi => absurd hi (Finset.notMem_empty i)
      rw [e, Finset.prod_empty]
      exact measure_univ
    · rw [Finset.prod_singleton, Finset.set_biInter_singleton]
    · rw [Finset.prod_singleton, Finset.set_biInter_singleton]
    · have h1 := hm 1 (by simp)
      have h2 := hm 2 (by simp)
      have := (Indep_iff _ _ _).1 h12 (f 1) (f 2) h1 h2
      rw [Finset.prod_pair (by decide : (1:Fin 3) ≠ 2)]
      rw [show (⋂ i ∈ ({1, 2} : Finset (Fin 3)), f i) = f 1 ∩ f 2 by
        rw [Finset.set_biInter_insert, Finset.set_biInter_singleton]]
      exact this
  by_cases h0s : (0 : Fin 3) ∈ s
  · set t := s.erase 0 with ht
    have hs : s = insert 0 t := (Finset.insert_erase h0s).symm
    have h0t : (0 : Fin 3) ∉ t := Finset.notMem_erase _ _
    have htsub : t ⊆ {1, 2} := by
      intro i hi
      have : i ≠ 0 := (Finset.mem_erase.1 hi).1
      exact (by decide : ∀ j : Fin 3, j ≠ 0 → j ∈ ({1, 2} : Finset (Fin 3))) i this
    have hmt : ∀ i ∈ t, MeasurableSet[m i] (f i) := fun i hi => hf i (Finset.mem_of_mem_erase hi)
    have hbig : MeasurableSet[m 1 ⊔ m 2] (⋂ i ∈ t, f i) := by
      refine t.measurableSet_biInter fun i hi => ?_
      have := htsub hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact (le_sup_left : m 1 ≤ m 1 ⊔ m 2) _ (hmt _ hi)
      · exact (le_sup_right : m 2 ≤ m 1 ⊔ m 2) _ (hmt _ hi)
    have := (Indep_iff _ _ _).1 h0 (f 0) (⋂ i ∈ t, f i) (hf 0 h0s) hbig
    rw [hs, Finset.set_biInter_insert, Finset.prod_insert h0t, this, key t htsub hmt]
  · refine key s ?_ hf
    intro i hi
    have : i ≠ 0 := fun h => h0s (h ▸ hi)
    fin_cases i <;> simp_all

end Kyprianou.Ch02
