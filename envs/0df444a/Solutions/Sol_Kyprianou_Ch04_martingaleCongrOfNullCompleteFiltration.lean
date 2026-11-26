-- Prove2me | solution 1 for Kyprianou.Ch04.martingaleCongrOfNullCompleteFiltration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:42:13.489+00:00
-- url     : https://prove2.me/submissions/76646eba-e8b8-4615-aef1-bf2284019818

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- In a null-complete filtration, an arbitrary modification of a real martingale is a martingale. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (M Y : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (he : ∀ t, M t =ᵐ[P] Y t) : Martingale Y F P := by
  apply hM.congr
  · intro t
    apply Measurable.stronglyMeasurable
    intro B hB
    have ht : ∀ᵐ w ∂P, M t w = Y t w := he t
    rw [ae_iff] at ht
    obtain ⟨N,hsub,hm,hzero⟩ := exists_measurable_superset_of_null ht
    have hU : MeasurableSet[F t] (M t ⁻¹' B) := hM.stronglyAdapted t |>.measurable hB
    have hA : Y t ⁻¹' B = ((M t ⁻¹' B) \ N) ∪ ((Y t ⁻¹' B) ∩ N) := by
      ext w
      by_cases hw : w ∈ N
      · simp [hw]
      · have hw' : M t w = Y t w := not_not.mp (fun hbad => hw (hsub hbad))
        simp [hw,hw']
    rw [hA]
    exact (hU.diff (hNull t N N hm hzero subset_rfl)).union
      (hNull t N _ hm hzero Set.inter_subset_right)
  · exact he
