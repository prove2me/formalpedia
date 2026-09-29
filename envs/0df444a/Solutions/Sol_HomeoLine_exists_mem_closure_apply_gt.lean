-- Prove2me | solution 1 for HomeoLine.exists_mem_closure_apply_gt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T15:46:42.130081+00:00
-- url     : https://prove2.me/submissions/dc05c128-3504-4f47-a08d-2f0f486b1302

import Mathlib


/-!
Brin–Squier, *Groups of piecewise linear homeomorphisms of the real line*,
Invent. math. **79** (1985), Lemma (3.5).

The paper proves this by covering `[c, d]` with the connected components of `supp f` and
`supp g`, extracting a finite subcover, and inducting on its cardinality, invoking (3.4)
(`exists_zpow_apply_gt`) at the base and at each step.  The formalization below takes a
shorter but equally elementary route which needs neither (3.4) nor compactness:

Let `H = ⟨f, g⟩` and let `V = H · c` be the orbit of `c`.  If no `z ∈ H` satisfies `d < z c`
then `V` is bounded above by `d`, so `m = sSup V` exists and lies in `[c, d]` (it is `≥ c`
because `c = 1 · c ∈ V`).  Every `w ∈ H` permutes `V`, i.e. `w '' V = V`; since an order
isomorphism of `ℝ` preserves suprema of nonempty bounded-above sets, `w m = sSup (w '' V) = m`.
So `m ∈ [c, d]` is fixed by both `f` and `g`, contradicting the hypothesis at `t = m`.
-/

/-- **Brin–Squier (3.5).**  If two orientation-preserving homeomorphisms `f`, `g` of `ℝ` between
them move every point of `[c, d]`, then some element of the subgroup they generate carries `c`
beyond `d`. -/
theorem solution (f g : ℝ ≃o ℝ) {c d : ℝ}
    (h : ∀ t ∈ Set.Icc c d, f t ≠ t ∨ g t ≠ t) :
    ∃ z ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)), d < z c := by
  by_contra hcon
  push Not at hcon
  set H : Subgroup (ℝ ≃o ℝ) := Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) with hH
  set V : Set ℝ := {x : ℝ | ∃ z ∈ H, z c = x} with hV
  have hcV : c ∈ V := ⟨1, one_mem H, rfl⟩
  have hne : V.Nonempty := ⟨c, hcV⟩
  have hub : ∀ x ∈ V, x ≤ d := by
    rintro x ⟨z, hz, rfl⟩
    exact hcon z hz
  have hbdd : BddAbove V := ⟨d, hub⟩
  set m : ℝ := sSup V with hm
  have hcm : c ≤ m := le_csSup hbdd hcV
  have hmd : m ≤ d := csSup_le hne hub
  have key : ∀ w ∈ H, w m = m := by
    intro w hw
    have himg : w '' V = V := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨w * z, mul_mem hw hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(w⁻¹ * z) c, ⟨w⁻¹ * z, mul_mem (inv_mem hw) hz, rfl⟩, ?_⟩
        have : w * (w⁻¹ * z) = z := by
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        exact congrArg (fun u : ℝ ≃o ℝ => u c) this
    calc w m = sSup (w '' V) := w.map_csSup' hne hbdd
      _ = m := by rw [himg]
  have hfm : f m = m := key f (Subgroup.subset_closure (by simp))
  have hgm : g m = m := key g (Subgroup.subset_closure (by simp))
  rcases h m ⟨hcm, hmd⟩ with hh | hh
  · exact hh hfm
  · exact hh hgm

