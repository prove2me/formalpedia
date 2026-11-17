-- Prove2me | solution 1 for N25.Alg.finite_of_surjective_of_expanding
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:22:01.101202+00:00
-- url     : https://prove2.me/submissions/d2012527-7eb4-4f5b-9934-199ee24a7518

import Mathlib

namespace N25.Alg

/-- A surjection expanding a height with finite bounded sublevel sets has finite domain. -/
theorem _root_.solution {X : Type*} (f : X → X) (hf : Function.Surjective f)
    (q : X → ℝ) (hq : ∀ B : ℝ, {x | q x ≤ B}.Finite) (c C : ℝ) (hc : 1 < c)
    (h : ∀ x, c * q x - C ≤ q (f x)) : Finite X := by
  classical
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hg_inj : Function.Injective g := hg.injective
  have hbound (x : X) : q x ≤ C / (c - 1) := by
    let B : ℝ := max (q x) (C / (c - 1))
    let S : Set X := {z | q z ≤ B}
    have hx : x ∈ S := by
      change q x ≤ max (q x) (C / (c - 1))
      exact le_max_left _ _
    have hCB : C ≤ (c - 1) * B := by
      have hb : C / (c - 1) ≤ B := le_max_right _ _
      simpa [mul_comm] using (div_le_iff₀ (by linarith : 0 < c - 1)).mp hb
    have hgS (z : S) : g z ∈ S := by
      have hz : q z ≤ B := z.2
      have hh := h (g z)
      rw [hg z] at hh
      change q (g z) ≤ B
      nlinarith
    let gs : S → S := fun z => ⟨g z, hgS z⟩
    have hgs : Function.Injective gs := by
      intro u v huv
      apply Subtype.ext
      exact hg_inj (congrArg Subtype.val huv)
    have : Finite S := (hq B).to_subtype
    have hsurj : Function.Surjective gs := Finite.surjective_of_injective hgs
    have hfS (z : X) (hz : z ∈ S) : f z ∈ S := by
      obtain ⟨w, hw⟩ := hsurj ⟨z, hz⟩
      have hgw : g w = z := congrArg Subtype.val hw
      have hfw : f z = w := by rw [← hgw, hg w]
      rw [hfw]
      exact w.2
    have hne : (hq B).toFinset.Nonempty := ⟨x, by simpa [S] using hx⟩
    obtain ⟨z, hz, hzmax⟩ := Finset.exists_max_image (hq B).toFinset q hne
    have hzS : z ∈ S := by simpa [S] using hz
    have hmax : q (f z) ≤ q z := hzmax (f z) (by simpa [S] using hfS z hzS)
    have hzx : q x ≤ q z := hzmax x (by simpa [S] using hx)
    have hh := h z
    have hzc : q z ≤ C / (c - 1) := by
      apply (le_div_iff₀ (by linarith : 0 < c - 1)).mpr
      nlinarith
    exact hzx.trans hzc
  apply Set.finite_univ_iff.mp
  exact (hq (C / (c - 1))).subset (by intro x _; exact hbound x)

end N25.Alg
