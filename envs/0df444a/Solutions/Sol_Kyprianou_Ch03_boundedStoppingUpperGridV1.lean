-- Prove2me | solution 1 for Kyprianou.Ch03.boundedStoppingUpperGridV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:30:24.038807+00:00
-- url     : https://prove2.me/submissions/49ee5eb5-6969-4254-80b8-392ce3746d7b

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedUpperGridV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (rho : Omega → NNReal)
    (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal)))
    (n : NNReal) (hBound : ∀ w, rho w ≤ n)
    : ∃ (G : ℕ → Omega → NNReal),
      (∀ k, IsStoppingTime F (fun w => (G k w : WithTop NNReal))) ∧
      (∀ k, (Set.range (fun w => (G k w : WithTop NNReal))).Countable) ∧
      (∀ k w, rho w ≤ G k w) ∧ (∀ k w, G k w ≤ n) ∧
      (∀ w, Tendsto (fun k => G k w) atTop (nhds (rho w))) := by
  classical
  obtain ⟨T, hCount, hFib, _, hT⟩ :=
    Kyprianou.Ch03.strongMarkovExtendedUpperGridV1 F
      (fun w => (rho w : WithTop NNReal)) hStop rho (fun _ _ => rfl)
  have hCount' (k : ℕ) : (Set.range (T k)).Countable := Countable.to_set (hCount k)
  have hFinite (w : Omega) : (rho w : WithTop NNReal) ≠ ⊤ := WithTop.coe_ne_top
  have hD : {w : Omega | (rho w : WithTop NNReal) ≠ ⊤} = Set.univ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hFinite w
  have hTstop (k : ℕ) : IsStoppingTime F (fun w => (T k w : WithTop NNReal)) := by
    intro t
    have he : {w | (T k w : WithTop NNReal) ≤ (t : WithTop NNReal)} =
        ⋃ s ∈ (Set.range (T k) ∩ Set.Iic t), {w | T k w = s} := by
      ext w
      simp only [Set.mem_setOf_eq, WithTop.coe_le_coe, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, Set.mem_Iic]
      exact ⟨fun h => ⟨T k w, ⟨⟨w,rfl⟩,h⟩,rfl⟩, fun ⟨s, hs, heq⟩ => by simpa [heq] using hs.2⟩
    rw [he]
    apply MeasurableSet.biUnion ((hCount' k).mono Set.inter_subset_left)
    intro s hs
    have hf := hFib k s
    rw [hD, Set.univ_inter] at hf
    exact F.mono hs.2 _ hf
  let G : ℕ → Omega → NNReal := fun k w => min (T k w) n
  refine ⟨G, ?_, ?_, ?_, fun k w => min_le_right _ _, ?_⟩
  · intro k
    simpa only [G, WithTop.coe_min] using (hTstop k).min_const n
  · intro k
    exact ((hCount' k).image (fun s => ((min s n : NNReal) : WithTop NNReal))).mono
      (by rintro _ ⟨w,rfl⟩; exact ⟨T k w,⟨w,rfl⟩,rfl⟩)
  · intro k w
    exact le_min ((hT w (hFinite w)).1 k) (hBound w)
  · intro w
    have hc : Tendsto (fun _ : ℕ => n) atTop (nhds n) := tendsto_const_nhds
    simpa only [G, min_eq_left (hBound w)] using ((hT w (hFinite w)).2.min hc)
