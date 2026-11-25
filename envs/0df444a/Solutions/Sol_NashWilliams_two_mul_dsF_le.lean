-- Prove2me | solution 1 for NashWilliams.two_mul_dsF_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:21:40.799042+00:00
-- url     : https://prove2.me/submissions/17680ced-e18e-4044-954c-f506d2e2a715

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
public import Theorems.Thm_NashWilliams_dsF_eq_sum
public import Theorems.Thm_NashWilliams_cutF_eq_sum


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {K : ℕ} {T : Finset V} {s : V} {ends : ι → V × V} {F : Finset ι}
    (hin : Inside T ends F) (hreq : Req K (T.erase s) ends F) (heven : Even (cutF ends F {s}))
    {X : Finset V} (hXT : X ⊆ T.erase s) (hXne : X.Nonempty) (hXT' : X ≠ T.erase s)
    (hXc : cutF ends F X ≤ K + 1) : 2 * dsF s ends F X ≤ cutF ends F {s} := by
  set Y := T.erase s \ X with hY
  have hYK : K ≤ cutF ends F Y := by
    refine hreq Y sdiff_subset ?_ ?_
    · obtain ⟨t, htT, htX⟩ : ∃ t ∈ T.erase s, t ∉ X := by
        by_contra! h
        exact hXT' (Subset.antisymm hXT h)
      exact ⟨t, mem_sdiff.2 ⟨htT, htX⟩⟩
    · intro h
      obtain ⟨x, hx⟩ := hXne
      have : x ∈ Y := by rw [h]; exact hXT hx
      simp [hY, hx] at this
  have key : cutF ends F Y + 2 * dsF s ends F X = cutF ends F X + cutF ends F {s} := by
    simp only [cutF_eq_sum, dsF_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    obtain ⟨h1, h2⟩ := hin l hl
    have hsX : s ∉ X := fun h => by simpa using hXT h
    have hX1 : (ends l).1 ∈ X → (ends l).1 ≠ s := fun h h' => hsX (h' ▸ h)
    have hX2 : (ends l).2 ∈ X → (ends l).2 ≠ s := fun h h' => hsX (h' ▸ h)
    unfold cr jn
    by_cases a1 : (ends l).1 = s <;> by_cases a2 : (ends l).2 = s <;>
      by_cases b1 : (ends l).1 ∈ X <;> by_cases b2 : (ends l).2 ∈ X <;> simp_all
  obtain ⟨r, hr⟩ := heven
  omega
end NashWilliams
