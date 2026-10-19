-- Prove2me | solution 1 for OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:26:00.871975+00:00
-- url     : https://prove2.me/submissions/66e9c8b6-6648-4cd8-aeb6-b8c3c328e71f

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

open OAI OAI.Problem356
universe uAlpha uBeta uIndex uKappa
open MeasureTheory Set
open scoped ENNReal
variable {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]


theorem solution [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i)) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧
      Measure.map f μ = Measure.sum (fun i => Measure.map (T i) (μ.restrict (B i))) := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty ι›
  let idx : α → ι := fun x => if h : ∃ i, x ∈ B i then Classical.choose h else i0
  have hidx : ∀ i x, x ∈ B i → idx x = i := by
    intro i x hx
    have h : ∃ i, x ∈ B i := ⟨i, hx⟩
    simp only [idx, dif_pos h]
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (Classical.choose_spec h) hx
  let f : α → β := fun x => T (idx x) x
  have hEq : ∀ i, EqOn f (T i) (B i) := by
    intro i x hx
    simp only [f, hidx i x hx]
  have hpre : ∀ s, f ⁻¹' s = (⋃ i, B i ∩ T i ⁻¹' s) ∪ ((⋃ i, B i)ᶜ ∩ T i0 ⁻¹' s) := by
    intro s
    ext x
    by_cases hx : ∃ i, x ∈ B i
    · obtain ⟨i, hi⟩ := hx
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff]
      rw [hEq i hi]
      constructor
      · intro h; exact Or.inl ⟨i, hi, h⟩
      · rintro (⟨j, hj, h⟩ | ⟨h, _⟩)
        · have : i = j := by
            by_contra hne; exact Set.disjoint_left.mp (hdisj hne) hi hj
          subst this; exact h
        · exact absurd ⟨i, hi⟩ h
    · have hfx : f x = T i0 x := by simp only [f, idx, dif_neg hx]
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff, hfx]
      constructor
      · intro h; exact Or.inr ⟨hx, h⟩
      · rintro (⟨j, hj, h⟩ | ⟨_, h⟩)
        · exact absurd ⟨j, hj⟩ hx
        · exact h
  have hfm : Measurable f := by
    intro s hs
    rw [hpre s]
    exact (MeasurableSet.iUnion fun i => (hB i).inter (hT i hs)).union
      ((MeasurableSet.iUnion hB).compl.inter (hT i0 hs))
  refine ⟨f, hfm, hEq, ?_⟩
  ext s hs
  rw [Measure.map_apply hfm hs, Measure.sum_apply _ hs]
  have hnull : μ (⋃ i, B i)ᶜ = 0 := ae_iff.mp hcover
  rw [← measure_inter_conull hnull, Set.inter_iUnion,
    measure_iUnion (fun i j hij => Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hij))
      (fun i => (hfm hs).inter (hB i))]
  refine tsum_congr (fun i => ?_)
  rw [Measure.map_apply (hT i) hs, Measure.restrict_apply (hT i hs)]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h, hx⟩; exact ⟨(hEq i hx) ▸ h, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨(hEq i hx).symm ▸ h, hx⟩

