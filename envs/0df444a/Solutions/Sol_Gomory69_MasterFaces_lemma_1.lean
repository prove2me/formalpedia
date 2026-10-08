-- Prove2me | solution 1 for Gomory69.MasterFaces.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:59:41.680932+00:00
-- url     : https://prove2.me/submissions/02de50ed-06bd-4745-aa2e-71c0cb57f5ff

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron



namespace Gomory69.MasterFaces

section Basic
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {N : Finset G} {π₀ : ℝ}

lemma dot_add (c x y : N → ℝ) : dot c (x + y) = dot c x + dot c y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul (c x : N → ℝ) (a : ℝ) : dot c (a • x) = a * dot c x := by
  simp [dot, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

lemma dot_sub (c x y : N → ℝ) : dot c (x - y) = dot c x - dot c y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

lemma dot_single (c : N → ℝ) (g : N) (a : ℝ) : dot c (Pi.single g a) = c g * a := by
  simp [dot, Pi.single_apply]

lemma dot_single' (g : N) (x : N → ℝ) : dot (Pi.single g 1) x = x g := by
  simp [dot, Pi.single_apply]

lemma cast_add (t s : N → ℕ) : castSolution (t + s) = castSolution t + castSolution s := by
  funext g; simp [castSolution]

lemma cast_single (g : N) (m : ℕ) : castSolution (Pi.single g m : N → ℕ) = Pi.single g (m : ℝ) := by
  funext h; by_cases hh : h = g
  · subst hh; simp [castSolution]
  · simp [castSolution, Pi.single_apply, hh]

lemma sol_add {a b : G} {t s : N → ℕ} (ht : GroupSolution N a t) (hs : GroupSolution N b s) :
    GroupSolution N (a + b) (t + s) := by
  unfold GroupSolution at *
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [ht, hs]

lemma sol_single (g : N) (m : ℕ) : GroupSolution N (m • (g : G)) (Pi.single g m) := by
  unfold GroupSolution
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

lemma aff_dot (c : N → ℝ) (d : ℝ) (S : Set (N → ℝ)) (hS : ∀ x ∈ S, dot c x = d)
    (x : N → ℝ) (hx : x ∈ affineSpan ℝ S) : dot c x = d := by
  refine affineSpan_induction hx (fun y hy => hS y hy) ?_
  intro a u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add]
  rw [dot_add, dot_smul, dot_sub, hu, hv, hw]; ring

lemma point_on_plane (π : N → ℝ) (π₀ : ℝ) (hπ : π ≠ 0) : ∃ x, dot π x = π₀ := by
  obtain ⟨k, hk⟩ : ∃ k, π k ≠ 0 := by
    by_contra h; push_neg at h; exact hπ (funext h)
  exact ⟨Pi.single k (π₀ / π k), by rw [dot_single]; field_simp⟩

lemma tight_nonempty {g₀ : G} {π : N → ℝ} {π₀ : ℝ} (hface : IsFace N g₀ π π₀) :
    ∃ t : N → ℕ, GroupSolution N g₀ t ∧ dot π (castSolution t) = π₀ := by
  obtain ⟨hπ, _, hspan⟩ := hface
  obtain ⟨x, hx⟩ := point_on_plane π π₀ hπ
  have hx' : x ∈ (↑(affineSpan ℝ (tightSolutions N g₀ π π₀)) : Set (N → ℝ)) := by
    rw [hspan]; exact hx
  by_contra h
  push_neg at h
  have : tightSolutions N g₀ π π₀ = ∅ := by
    ext y; simp only [tightSolutions, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨t, ht, rfl, hd⟩; exact h t ht hd
  rw [this] at hx'
  simp at hx'

lemma face_nonneg {g₀ : G} {π : N → ℝ} {π₀ : ℝ} (hface : IsFace N g₀ π π₀) (g : N) :
    0 ≤ π g := by
  obtain ⟨t, ht, hd⟩ := tight_nonempty hface
  have hm : 0 < addOrderOf (g : G) := addOrderOf_pos _
  have hs := sol_add ht (sol_single g (addOrderOf (g : G)))
  rw [addOrderOf_nsmul_eq_zero, add_zero] at hs
  have := hface.2.1 _ hs
  rw [cast_add, dot_add, cast_single, dot_single, hd] at this
  have hm' : (0:ℝ) < addOrderOf (g : G) := by exact_mod_cast hm
  by_contra hneg; push_neg at hneg
  nlinarith

lemma theorem_6_core {g₀ : G} {π : N → ℝ} {π₀ : ℝ} (hface : IsFace N g₀ π π₀) :
    (∀ g : N, 0 ≤ π g) ∧ 0 ≤ π₀ := by
  refine ⟨face_nonneg hface, ?_⟩
  obtain ⟨t, ht, hd⟩ := tight_nonempty hface
  rw [← hd]
  unfold dot
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (face_nonneg hface g) (by simp [castSolution]))

lemma tight_with (hπ₀ : 0 < π₀) {g₀ : G} {π : N → ℝ} (hface : IsFace N g₀ π π₀) (g : N) :
    ∃ t : N → ℕ, GroupSolution N g₀ t ∧ dot π (castSolution t) = π₀ ∧ 1 ≤ t g := by
  by_contra h
  push_neg at h
  have hall : ∀ x ∈ tightSolutions N g₀ π π₀, dot (Pi.single g 1) x = 0 := by
    rintro x ⟨t, ht, rfl, hd⟩
    have := h t ht hd
    rw [dot_single']; simp [castSolution]; omega
  have hz : ∀ x, dot π x = π₀ → x g = 0 := by
    intro x hx
    have hx' : x ∈ (↑(affineSpan ℝ (tightSolutions N g₀ π π₀)) : Set (N → ℝ)) := by
      rw [hface.2.2]; exact hx
    have := aff_dot _ _ _ hall x hx'
    rwa [dot_single'] at this
  by_cases hg : π g = 0
  · obtain ⟨x, hx⟩ := point_on_plane π π₀ hface.1
    have h1 := hz x hx
    have h2 := hz (x + Pi.single g 1) (by rw [dot_add, dot_single, hg, hx]; ring)
    simp [h1] at h2
  · have := hz (Pi.single g (π₀ / π g)) (by rw [dot_single]; field_simp)
    simp at this
    rcases this with h | h
    · exact hπ₀.ne' h
    · exact hg h

lemma split_off {g₀ : G} {π : N → ℝ} (g : N) {t : N → ℕ} (ht : GroupSolution N g₀ t) (h1 : 1 ≤ t g) :
    ∃ t' : N → ℕ, t = t' + (Pi.single g 1 : N → ℕ) ∧ GroupSolution N (g₀ - g) t' ∧
      dot π (castSolution t') = dot π (castSolution t) - π g := by
  obtain ⟨t', e⟩ : ∃ t' : N → ℕ, t = t' + (Pi.single g 1 : N → ℕ) := by
    refine ⟨fun h => if h = g then t g - 1 else t h, ?_⟩
    funext h; rw [Pi.add_apply]; by_cases hh : h = g
    · subst hh; simp; omega
    · simp [Pi.single_apply, hh]
  subst e
  refine ⟨t', rfl, ?_, ?_⟩
  · have hs := sol_single g 1
    unfold GroupSolution at *
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] at ht
    rw [hs] at ht
    rw [← ht]; simp
  · rw [cast_add, dot_add, cast_single, dot_single]; simp

lemma theorem_10_core (hπ₀ : 0 < π₀) {g₀ : G} {π : N → ℝ} (hface : IsFace N g₀ π π₀) (g : N) :
    ∀ s : N → ℕ, GroupSolution N (g : G) s → π g ≤ dot π (castSolution s) := by
  intro s hs
  obtain ⟨t, ht, hd, h1⟩ := tight_with hπ₀ hface g
  obtain ⟨t', e, ht', hd'⟩ := split_off (π := π) g ht h1
  have hsol : GroupSolution N g₀ (t' + s) := by
    have := sol_add ht' hs
    simpa using this
  have := hface.2.1 _ hsol
  rw [cast_add, dot_add, hd', hd] at this
  linarith

lemma single2 (g1 g2 : N) : GroupSolution N ((g1 : G) + g2) (Pi.single g1 1 + Pi.single g2 1) := by
  have := sol_add (sol_single g1 1) (sol_single g2 1)
  simpa using this

lemma dot_single2 (π : N → ℝ) (g1 g2 : N) :
    dot π (castSolution (Pi.single g1 1 + Pi.single g2 1 : N → ℕ)) = π g1 + π g2 := by
  rw [cast_add, dot_add, cast_single, cast_single, dot_single, dot_single]; simp

lemma corollary_1_core {g₀ : G} {π : N → ℝ} {π₀ : ℝ} (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀)
    (g₁ g₂ g : N) (hsum : (g : G) = (g₁ : G) + (g₂ : G)) : π g ≤ π g₁ + π g₂ := by
  have := theorem_10_core hπ₀ hface g _ (hsum ▸ single2 g₁ g₂)
  rwa [dot_single2] at this

lemma corollary_2_core {g₀ : G} {π : N → ℝ} {π₀ : ℝ} (hπ₀ : 0 < π₀) (hface : IsFace N g₀ π π₀)
    (g₁ g₂ : N) (hsum : (g₁ : G) + (g₂ : G) = g₀) : π g₁ + π g₂ = π₀ := by
  apply le_antisymm
  · obtain ⟨t, ht, hd, h1⟩ := tight_with hπ₀ hface g₁
    obtain ⟨t', e, ht', hd'⟩ := split_off (π := π) g₁ ht h1
    have : (g₀ - g₁ : G) = g₂ := by rw [← hsum]; abel
    rw [this] at ht'
    have := theorem_10_core hπ₀ hface g₂ _ ht'
    linarith
  · have := hface.2.1 _ (hsum ▸ single2 g₁ g₂)
    rwa [dot_single2] at this

lemma lemma_2_core (hπ₀ : 0 < π₀) {g₀ : G} {π : N → ℝ} (hface : IsFace N g₀ π π₀) (g : N) :
    ∃ t : N → ℕ, GroupSolution N g₀ t ∧ dot π (castSolution t) = π₀ ∧ 0 < t g := by
  obtain ⟨t, h1, h2, h3⟩ := tight_with hπ₀ hface g
  exact ⟨t, h1, h2, h3⟩

lemma lemma_1_core {g₀ h : G} {π : N → ℝ} {t t' : N → ℕ} (ht : IsShortest N g₀ π t)
    (ht' : GroupSolution N h t') (hle : ∀ g : N, t' g ≤ t g) : IsShortest N h π t' := by
  refine ⟨ht', ?_⟩
  intro s hs
  obtain ⟨r, e⟩ : ∃ r : N → ℕ, t = t' + r := ⟨fun g => t g - t' g, by
    funext g; rw [Pi.add_apply]; have := hle g; omega⟩
  have hr : GroupSolution N (g₀ - h) r := by
    have h0 := ht.1
    unfold GroupSolution at *
    rw [e] at h0
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] at h0
    rw [ht'] at h0
    rw [← h0]; abel
  have hsol : GroupSolution N g₀ (r + s) := by
    have := sol_add hr hs
    simpa using this
  have h1 := ht.2 _ hsol
  rw [e, cast_add, dot_add] at h1
  rw [cast_add, dot_add] at h1
  linarith

end Basic

section Master
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma mem_master {g : G} (hg : g ≠ 0) : g ∈ masterSupport G := by simp [masterSupport, hg]

lemma ne_zero_of_master (g : MasterIndex G) : (g : G) ≠ 0 := by
  have := g.2; simpa [masterSupport] using this

lemma ext_coe (π : MasterIndex G → ℝ) (g : MasterIndex G) : extendZero π (g : G) = π g := by
  unfold extendZero; rw [dif_neg (ne_zero_of_master g)]

lemma ext_mk (π : MasterIndex G → ℝ) {g : G} (hg : g ≠ 0) :
    extendZero π g = π ⟨g, mem_master hg⟩ := by
  unfold extendZero; rw [dif_neg hg]

lemma ext0 (π : MasterIndex G → ℝ) : extendZero π 0 = 0 := by simp [extendZero]

lemma theorem_17_core (g₀ : G) (hg₀ : g₀ ≠ 0) (π : MasterIndex G → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) (hface : IsFace (masterSupport G) g₀ π π₀) :
    (∀ g : MasterIndex G,
      extendZero π (g : G) + extendZero π (g₀ - (g : G)) = π₀) ∧
    (∀ g h : MasterIndex G,
      extendZero π ((g : G) + (h : G)) ≤ π g + π h) ∧
    extendZero π g₀ = π₀ := by
  have h3 : extendZero π g₀ = π₀ := by
    rw [ext_mk π hg₀]
    set g0 : MasterIndex G := ⟨g₀, mem_master hg₀⟩ with hg0
    apply le_antisymm
    · obtain ⟨t, ht, hd⟩ := tight_nonempty hface
      have := theorem_10_core hπ₀ hface g0 t ht
      linarith
    · have hs := sol_single g0 1
      have h1 : (1 : ℕ) • (g0 : G) = g₀ := by simp [hg0]
      rw [h1] at hs
      have := hface.2.1 _ hs
      rw [cast_single, dot_single] at this
      simpa using this
  refine ⟨?_, ?_, h3⟩
  · intro g
    by_cases h : g₀ - (g : G) = 0
    · have : (g : G) = g₀ := by rw [sub_eq_zero] at h; exact h.symm
      rw [h, ext0, add_zero, this, h3]
    · rw [ext_coe, ext_mk π h]
      exact corollary_2_core hπ₀ hface g ⟨_, mem_master h⟩ (by simp)
  · intro g h
    by_cases hz : (g : G) + (h : G) = 0
    · rw [hz, ext0]
      exact add_nonneg (face_nonneg hface g) (face_nonneg hface h)
    · rw [ext_mk π hz]
      exact corollary_1_core hπ₀ hface g h _ rfl

end Master
end Gomory69.MasterFaces

open Gomory69.MasterFaces


theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : (0 : G) ∉ N) (g₀ h : G) (π : N → ℝ)
    (t t' : N → ℕ) (ht : IsShortest N g₀ π t)
    (ht' : GroupSolution N h t') (hle : ∀ g : N, t' g ≤ t g) :
    IsShortest N h π t' := by
  exact lemma_1_core ht ht' hle
