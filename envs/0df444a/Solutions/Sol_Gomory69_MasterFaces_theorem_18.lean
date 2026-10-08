-- Prove2me | solution 1 for Gomory69.MasterFaces.theorem_18
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:06:52.312838+00:00
-- url     : https://prove2.me/submissions/c70de524-462d-443c-bcdb-98be24c8789b

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_BasicFeasible



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

section Aff
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {N : Finset G} {π₀ : ℝ}

lemma aff_iff_span (hπ₀ : 0 < π₀) {π : N → ℝ} (hπ : π ≠ 0) (S : Set (N → ℝ))
    (hS : ∀ x ∈ S, dot π x = π₀) :
    (↑(affineSpan ℝ S) : Set (N → ℝ)) = {x | dot π x = π₀} ↔ Submodule.span ℝ S = ⊤ := by
  obtain ⟨x₀, hx₀⟩ := point_on_plane π π₀ hπ
  constructor
  · intro h
    rw [eq_top_iff]
    intro y _
    have hH : ∀ x, dot π x = π₀ → x ∈ Submodule.span ℝ S := by
      intro x hx
      have hx' : x ∈ (↑(affineSpan ℝ S) : Set (N → ℝ)) := by rw [h]; exact hx
      exact affineSpan_le_toAffineSubspace_span hx'
    have h1 : x₀ ∈ Submodule.span ℝ S := hH _ hx₀
    have h2 : (x₀ + (y - (dot π y / π₀) • x₀)) ∈ Submodule.span ℝ S :=
      hH _ (by rw [dot_add, dot_sub, dot_smul, hx₀]; field_simp; ring)
    have : y = (dot π y / π₀) • x₀ + (x₀ + (y - (dot π y / π₀) • x₀)) - x₀ := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ h1) h2) h1
  · intro h
    ext x
    constructor
    · intro hx; exact aff_dot π π₀ S hS x hx
    · intro hx
      have hx : dot π x = π₀ := hx
      obtain ⟨s₀, hs₀⟩ : S.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, Submodule.span_empty] at h
        have : x₀ ∈ (⊥ : Submodule ℝ (N → ℝ)) := by rw [h]; trivial
        rw [Submodule.mem_bot] at this
        rw [this] at hx₀
        simp [dot] at hx₀
        exact hπ₀.ne hx₀
      have key : ∀ y ∈ Submodule.span ℝ S, y - (dot π y / π₀) • s₀ ∈ vectorSpan ℝ S := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          rw [hS y hy, div_self hπ₀.ne', one_smul]
          exact vsub_mem_vectorSpan ℝ hy hs₀
        | zero =>
          have : dot π (0 : N → ℝ) = 0 := by simp [dot]
          simp [this]
        | add a b _ _ ha hb =>
          have : (a + b) - (dot π (a + b) / π₀) • s₀
              = (a - (dot π a / π₀) • s₀) + (b - (dot π b / π₀) • s₀) := by
            rw [dot_add, add_div, add_smul]; abel
          rw [this]; exact add_mem ha hb
        | smul c a _ ha =>
          have : (c • a) - (dot π (c • a) / π₀) • s₀ = c • (a - (dot π a / π₀) • s₀) := by
            rw [dot_smul, mul_div_assoc, mul_smul, smul_sub]
          rw [this]; exact Submodule.smul_mem _ _ ha
      have k2 := key x (by rw [h]; trivial)
      rw [hx, div_self hπ₀.ne', one_smul] at k2
      have hs₀' : s₀ ∈ affineSpan ℝ S := subset_affineSpan ℝ S hs₀
      have := AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact k2) hs₀'
      simpa using this

lemma face_iff_span (hπ₀ : 0 < π₀) {g₀ : G} {π : N → ℝ} :
    IsFace N g₀ π π₀ ↔ π ≠ 0 ∧ (∀ t : N → ℕ, GroupSolution N g₀ t → π₀ ≤ dot π (castSolution t)) ∧
      Submodule.span ℝ (tightSolutions N g₀ π π₀) = ⊤ := by
  unfold IsFace
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [← aff_iff_span hπ₀ h1]
    · exact h3
    · rintro x ⟨t, _, rfl, hd⟩; exact hd
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [aff_iff_span hπ₀ h1]
    · exact h3
    · rintro x ⟨t, _, rfl, hd⟩; exact hd

lemma rowEval_dot (a x : N → ℝ) : rowEval a x = dot x a := by
  unfold rowEval dot; apply Finset.sum_congr rfl; intros; ring

lemma image_tight (g₀ : G) (π : N → ℝ) (π₀ : ℝ) :
    (fun t : {t : N → ℕ // GroupSolution N g₀ t} => castSolution t.val) ''
      {r | rowEval (castSolution r.val) π = π₀} = tightSolutions N g₀ π π₀ := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.val, r.2, rfl, by rw [← rowEval_dot]; exact hr⟩
  · rintro ⟨t, ht, rfl, hd⟩
    exact ⟨⟨t, ht⟩, by simp only [Set.mem_setOf_eq]; rw [rowEval_dot]; exact hd, rfl⟩

lemma theorem_7_core (hNne : N.Nonempty) {g₀ : G} {π : N → ℝ} (hπ₀ : 0 < π₀) :
    IsFace N g₀ π π₀ ↔ IsTBasicFeasible N g₀ π₀ π := by
  unfold IsTBasicFeasible IsBasicFeasible
  rw [image_tight, face_iff_span hπ₀]
  constructor
  · rintro ⟨_, hin, hsp⟩
    refine ⟨fun r => ⟨fun h => absurd h (Set.notMem_empty _), fun _ => ?_⟩, hsp⟩
    rw [rowEval_dot]; exact hin _ r.2
  · rintro ⟨hfe, hsp⟩
    refine ⟨?_, fun t ht => ?_, hsp⟩
    · intro h0
      subst h0
      have hemp : tightSolutions N g₀ (0 : N → ℝ) π₀ = ∅ := by
        ext y; simp only [tightSolutions, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨t, _, rfl, hd⟩
        simp [dot] at hd; exact hπ₀.ne hd
      rw [hemp, Submodule.span_empty] at hsp
      obtain ⟨g, hg⟩ := hNne
      have : (Pi.single ⟨g, hg⟩ 1 : N → ℝ) ∈ (⊥ : Submodule ℝ (N → ℝ)) := by rw [hsp]; trivial
      rw [Submodule.mem_bot] at this
      have := congrFun this ⟨g, hg⟩
      simp at this
    · have := (hfe ⟨t, ht⟩).2 (Set.notMem_empty _)
      rwa [rowEval_dot] at this

end Aff

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

section Sys13
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma span_top_iff_ann {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Set (κ → ℝ)) :
    Submodule.span ℝ A = ⊤ ↔ ∀ ρ : κ → ℝ, (∀ a ∈ A, ∑ k, ρ k * a k = 0) → ρ = 0 := by
  constructor
  · intro h ρ hρ
    have key : ∀ y ∈ Submodule.span ℝ A, ∑ k, ρ k * y k = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hρ y hy
      | zero => simp
      | add a b _ _ ha hb => simp [mul_add, Finset.sum_add_distrib, ha, hb]
      | smul c a _ ha =>
        have : ∑ k, ρ k * (c • a) k = c * ∑ k, ρ k * a k := by
          simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intros; ring
        rw [this, ha, mul_zero]
    funext k
    have := key (Pi.single k 1) (by rw [h]; trivial)
    simpa [Pi.single_apply] using this
  · intro h
    by_contra hne
    obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top (Submodule.span ℝ A)
      (lt_top_iff_ne_top.2 hne)
    have hfy : ∀ y : κ → ℝ, f y = ∑ k, f (Pi.single k 1) * y k := by
      intro y
      have : y = ∑ k, y k • (Pi.single k 1 : κ → ℝ) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [this]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [map_smul, smul_eq_mul, mul_comm]
    apply hf
    have hρ := h (fun k => f (Pi.single k 1)) (by
      intro a ha
      have := hle (Submodule.subset_span ha)
      rw [LinearMap.mem_ker] at this
      rw [hfy a] at this; exact this)
    have hz : ∀ k, f (Pi.single k 1) = 0 := fun k => congrFun hρ k
    refine LinearMap.ext fun y => ?_
    rw [hfy y]
    simp [hz]

lemma rowEval_coord (h : G) (ρ : MasterIndex G → ℝ) : rowEval (coord h) ρ = extendZero ρ h := by
  unfold rowEval coord
  by_cases hh : h = 0
  · rw [hh, extendZero, dif_pos rfl]
    apply Finset.sum_eq_zero; intro k _
    simp [ne_zero_of_master k]
  · rw [ext_mk ρ hh, Finset.sum_eq_single ⟨h, mem_master hh⟩]
    · simp
    · intro b _ hb
      have : (b : G) ≠ h := fun e => hb (Subtype.ext e)
      simp [this]
    · simp

lemma rowEval_add {κ : Type*} [Fintype κ] (a b x : κ → ℝ) :
    rowEval (a + b) x = rowEval a x + rowEval b x := by
  simp [rowEval, add_mul, Finset.sum_add_distrib]

lemma rowEval_sub {κ : Type*} [Fintype κ] (a b x : κ → ℝ) :
    rowEval (a - b) x = rowEval a x - rowEval b x := by
  simp [rowEval, sub_mul, Finset.sum_sub_distrib]

lemma feas_iff (g₀ : G) (π₀ : ℝ) (π : MasterIndex G → ℝ) :
    System13Feasible g₀ π₀ π ↔
      (extendZero π g₀ = π₀) ∧
      (∀ g : MasterIndex G, (g : G) ≠ g₀ → extendZero π (g : G) + extendZero π (g₀ - g) = π₀) ∧
      (∀ g h : MasterIndex G, extendZero π ((g : G) + h) ≤ π g + π h) ∧
      (∀ g : MasterIndex G, 0 ≤ π g) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := (H .target).1 (by simp [row13Equation])
      simpa [row13Coeff, rowEval_coord, row13Rhs] using this
    · intro g hg
      have := (H (.complement g hg)).1 (by simp [row13Equation])
      simpa [row13Coeff, rowEval_add, rowEval_coord, row13Rhs] using this
    · intro g h
      have := (H (.subadd g h)).2 (by simp [row13Equation])
      simp only [row13Coeff, rowEval_add, rowEval_sub, rowEval_coord, row13Rhs, ext_coe] at this
      linarith
    · intro g
      have := (H (.nonnegative g)).2 (by simp [row13Equation])
      simpa [row13Coeff, rowEval_coord, row13Rhs, ext_coe] using this
  · rintro ⟨h1, h2, h3, h4⟩ r
    cases r with
    | target =>
      refine ⟨fun _ => ?_, fun h => absurd (by simp [row13Equation]) h⟩
      simpa [row13Coeff, rowEval_coord, row13Rhs] using h1
    | complement g hg =>
      refine ⟨fun _ => ?_, fun h => absurd (by simp [row13Equation]) h⟩
      simpa [row13Coeff, rowEval_add, rowEval_coord, row13Rhs] using h2 g hg
    | subadd g h =>
      refine ⟨fun h' => absurd h' (by simp [row13Equation]), fun _ => ?_⟩
      simp only [row13Coeff, rowEval_add, rowEval_sub, rowEval_coord, row13Rhs, ext_coe]
      linarith [h3 g h]
    | nonnegative g =>
      refine ⟨fun h' => absurd h' (by simp [row13Equation]), fun _ => ?_⟩
      simpa [row13Coeff, rowEval_coord, row13Rhs, ext_coe] using h4 g

lemma chain (π ρ : MasterIndex G → ℝ)
    (hsub : ∀ g h : MasterIndex G, extendZero π ((g : G) + h) ≤ π g + π h)
    (hρ : ∀ g h : MasterIndex G, extendZero π ((g : G) + h) = π g + π h →
      extendZero ρ ((g : G) + h) = ρ g + ρ h) :
    ∀ n : ℕ, ∀ t : MasterIndex G → ℕ, ∑ g, t g = n →
      extendZero π (∑ g, t g • (g : G)) ≤ dot π (castSolution t) ∧
      (dot π (castSolution t) = extendZero π (∑ g, t g • (g : G)) →
        dot ρ (castSolution t) = extendZero ρ (∑ g, t g • (g : G))) := by
  have hsub' : ∀ (k : G) (g : MasterIndex G),
      extendZero π (k + g) ≤ extendZero π k + π g := by
    intro k g
    by_cases hk : k = 0
    · subst hk; rw [zero_add, ext0, zero_add, ext_coe]
    · rw [ext_mk π hk]; exact hsub ⟨k, mem_master hk⟩ g
  have hρ' : ∀ (k : G) (g : MasterIndex G),
      extendZero π (k + g) = extendZero π k + π g →
      extendZero ρ (k + g) = extendZero ρ k + ρ g := by
    intro k g
    by_cases hk : k = 0
    · subst hk; intro _; rw [zero_add, ext0, zero_add, ext_coe]
    · rw [ext_mk π hk, ext_mk ρ hk]; exact hρ ⟨k, mem_master hk⟩ g
  intro n
  induction n with
  | zero =>
    intro t ht
    have h0 : ∀ g, t g = 0 := fun g => (Finset.sum_eq_zero_iff.1 ht) g (Finset.mem_univ g)
    have : t = 0 := funext h0
    subst this
    simp [dot, castSolution, ext0]
  | succ n ih =>
    intro t ht
    obtain ⟨g, hg⟩ : ∃ g, 1 ≤ t g := by
      by_contra hcon
      push_neg at hcon
      have : ∑ g, t g = 0 := Finset.sum_eq_zero (fun g _ => by have := hcon g; omega)
      omega
    obtain ⟨t', e, ht', hd'⟩ := split_off (π := π) g (g₀ := ∑ g, t g • (g : G)) (t := t) rfl hg
    have hsum : ∑ g, t' g = n := by
      have : ∑ g, t g = ∑ g, t' g + 1 := by
        rw [e]; simp [Finset.sum_add_distrib, Pi.single_apply]
      omega
    obtain ⟨ih1, ih2⟩ := ih t' hsum
    have hk : (∑ g, t g • (g : G)) = (∑ g, t' g • (g : G)) + g := by
      have : (∑ g, t' g • (g : G)) = (∑ g, t g • (g : G)) - g := ht'
      rw [this]; abel
    rw [hk]
    have hs := hsub' (∑ g, t' g • (g : G)) g
    refine ⟨?_, ?_⟩
    · linarith
    · intro hEq
      have hdt : dot π (castSolution t) = dot π (castSolution t') + π g := by linarith
      have h1 : extendZero π (∑ g, t' g • (g : G)) = dot π (castSolution t') := by linarith
      have h2 : extendZero π ((∑ g, t' g • (g : G)) + g) =
          extendZero π (∑ g, t' g • (g : G)) + π g := by linarith
      have := ih2 h1.symm
      have h3 := hρ' _ g h2
      have hdr : dot ρ (castSolution t) = dot ρ (castSolution t') + ρ g := by
        rw [e, cast_add, dot_add, cast_single, dot_single]; simp
      rw [hdr, this, h3]


def kv (g₀ : G) (g : MasterIndex G) (hne : (g : G) ≠ g₀) : MasterIndex G :=
  ⟨g₀ - g, mem_master (sub_ne_zero.2 (fun e => hne e.symm))⟩

lemma coe_kv (g₀ : G) (g : MasterIndex G) (hne : (g : G) ≠ g₀) : (kv g₀ g hne : G) = g₀ - g := rfl

lemma ptm {g₀ : G} {π ρ : MasterIndex G → ℝ} {π₀ : ℝ}
    (hpt : ∀ t : MasterIndex G → ℕ, GroupSolution (masterSupport G) g₀ t →
      dot π (castSolution t) = π₀ → dot ρ (castSolution t) = 0)
    (g k : MasterIndex G) (m : ℕ) (h1 : (k : G) + m • (g : G) = g₀)
    (h2 : π k + m * π g = π₀) : ρ k + m * ρ g = 0 := by
  have hs : GroupSolution (masterSupport G) g₀
      ((Pi.single k 1 : MasterIndex G → ℕ) + (Pi.single g m : MasterIndex G → ℕ)) := by
    have := sol_add (sol_single k 1) (sol_single g m)
    rwa [one_smul, h1] at this
  have hd : ∀ c : MasterIndex G → ℝ,
      dot c (castSolution ((Pi.single k 1 : MasterIndex G → ℕ) + (Pi.single g m : MasterIndex G → ℕ)))
        = c k + c g * m := by
    intro c; rw [cast_add, dot_add, cast_single, cast_single, dot_single, dot_single]; simp
  have := hpt _ hs (by rw [hd]; linarith)
  rw [hd] at this; linarith

lemma pt3 {g₀ : G} {π ρ : MasterIndex G → ℝ} {π₀ : ℝ}
    (hpt : ∀ t : MasterIndex G → ℕ, GroupSolution (masterSupport G) g₀ t →
      dot π (castSolution t) = π₀ → dot ρ (castSolution t) = 0)
    (g h k : MasterIndex G) (h1 : (g : G) + h + k = g₀)
    (h2 : π g + π h + π k = π₀) : ρ g + ρ h + ρ k = 0 := by
  have hs : GroupSolution (masterSupport G) g₀
      ((Pi.single g 1 : MasterIndex G → ℕ) + (Pi.single h 1 : MasterIndex G → ℕ)
        + (Pi.single k 1 : MasterIndex G → ℕ)) := by
    have := sol_add (sol_add (sol_single g 1) (sol_single h 1)) (sol_single k 1)
    rwa [one_smul, one_smul, one_smul, h1] at this
  have hd : ∀ c : MasterIndex G → ℝ,
      dot c (castSolution ((Pi.single g 1 : MasterIndex G → ℕ) + (Pi.single h 1 : MasterIndex G → ℕ)
        + (Pi.single k 1 : MasterIndex G → ℕ))) = c g + c h + c k := by
    intro c; rw [cast_add, cast_add, dot_add, dot_add, cast_single, cast_single, cast_single,
      dot_single, dot_single, dot_single]; simp
  have := hpt _ hs (by rw [hd]; linarith)
  rw [hd] at this; linarith

lemma theorem_18_core (g₀ : G) (hg₀ : g₀ ≠ 0) (π : MasterIndex G → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) :
    IsFace (masterSupport G) g₀ π π₀ ↔ IsSystem13Basic g₀ π₀ π := by
  unfold IsSystem13Basic IsBasicFeasible
  constructor
  · intro hf
    obtain ⟨T1, T2, T3⟩ := theorem_17_core g₀ hg₀ π π₀ hπ₀ hf
    have hfeas : System13Feasible g₀ π₀ π :=
      (feas_iff g₀ π₀ π).2 ⟨T3, fun g _ => T1 g, T2, face_nonneg hf⟩
    refine ⟨hfeas, ?_⟩
    rw [span_top_iff_ann]
    intro ρ hρ
    have hrow : ∀ r, rowEval (row13Coeff g₀ r) π = row13Rhs g₀ π₀ r →
        rowEval (row13Coeff g₀ r) ρ = 0 := by
      intro r hr; rw [rowEval_dot]; exact hρ _ ⟨r, hr, rfl⟩
    have hρtarget : extendZero ρ g₀ = 0 := by
      have := hrow .target (by simpa [row13Coeff, rowEval_coord, row13Rhs] using T3)
      simpa [row13Coeff, rowEval_coord] using this
    have hρsub : ∀ g h : MasterIndex G, extendZero π ((g : G) + h) = π g + π h →
        extendZero ρ ((g : G) + h) = ρ g + ρ h := by
      intro g h he
      have := hrow (.subadd g h) (by
        simp only [row13Coeff, rowEval_add, rowEval_sub, rowEval_coord, row13Rhs, ext_coe]
        linarith)
      simp only [row13Coeff, rowEval_add, rowEval_sub, rowEval_coord, ext_coe] at this
      linarith
    refine (span_top_iff_ann _).1 ((face_iff_span hπ₀).1 hf).2.2 ρ (fun x hx => ?_)
    obtain ⟨t, ht, rfl, hd⟩ := hx
    have key := (chain π ρ T2 hρsub _ t rfl).2
    have ht' : (∑ g, t g • (g : G)) = g₀ := ht
    rw [ht'] at key
    have := key (by rw [hd, T3]); rw [hρtarget] at this
    exact this
  · rintro ⟨hfeas, hsp⟩
    obtain ⟨T3, T1, T2, T4⟩ := (feas_iff g₀ π₀ π).1 hfeas
    set g0v : MasterIndex G := ⟨g₀, mem_master hg₀⟩ with hg0v
    have hπg0 : π g0v = π₀ := by rw [ext_mk π hg₀] at T3; exact T3
    have hπne : π ≠ 0 := by
      intro h0; rw [h0] at hπg0; simp at hπg0; linarith
    rw [face_iff_span hπ₀]
    refine ⟨hπne, ?_, ?_⟩
    · intro t ht
      have := (chain π 0 T2 (by intro g h _; simp [extendZero]) _ t rfl).1
      have ht' : (∑ g, t g • (g : G)) = g₀ := ht
      rw [ht', T3] at this; exact this
    · rw [span_top_iff_ann]
      intro ρ hρ
      have hpt : ∀ t : MasterIndex G → ℕ, GroupSolution (masterSupport G) g₀ t →
          dot π (castSolution t) = π₀ → dot ρ (castSolution t) = 0 :=
        fun t ht hd => hρ _ ⟨t, ht, rfl, hd⟩
      have hρ1 : ρ g0v = 0 := by
        have := ptm hpt g0v g0v 0 (by simp [hg0v]) (by simp [hπg0])
        simpa using this
      have hρg0 : extendZero ρ g₀ = 0 := by rw [ext_mk ρ hg₀]; exact hρ1
      have hcomp : ∀ g : MasterIndex G, ∀ hne : (g : G) ≠ g₀,
          π g + π (kv g₀ g hne) = π₀ := by
        intro g hne
        have := T1 g hne
        rw [ext_coe, ext_mk π (sub_ne_zero.2 (fun e => hne e.symm))] at this
        exact this
      refine (span_top_iff_ann _).1 hsp ρ ?_
      rintro a ⟨r, hr, rfl⟩
      suffices hsuf : rowEval (row13Coeff g₀ r) ρ = 0 by
        rw [rowEval_dot] at hsuf; exact hsuf
      cases r with
      | target =>
        simpa [row13Coeff, rowEval_coord] using hρg0
      | complement g hne =>
        simp only [row13Coeff, rowEval_add, rowEval_coord]
        have := ptm hpt (kv g₀ g hne) g 1 (by rw [coe_kv]; simp) (by
          have := hcomp g hne; simp; linarith)
        rw [ext_coe, ext_mk ρ (sub_ne_zero.2 (fun e => hne e.symm))]
        simp at this
        exact this
      | subadd g h =>
        have hr0 : rowEval (row13Coeff g₀ (.subadd g h)) π = row13Rhs g₀ π₀ (.subadd g h) := hr
        have hr' : π g + π h = extendZero π ((g : G) + h) := by
          simp only [row13Coeff, rowEval_add, rowEval_sub, rowEval_coord, row13Rhs, ext_coe] at hr0
          linarith
        simp only [row13Coeff, rowEval_add, rowEval_sub, rowEval_coord, ext_coe]
        by_cases hs0 : (g : G) + h = 0
        · rw [hs0, ext0] at hr' ⊢
          have := pt3 hpt g h g0v (by simp [hg0v, hs0]) (by linarith)
          linarith
        · by_cases hsg : (g : G) + h = g₀
          · rw [hsg] at hr'
            rw [hsg, hρg0]
            have := ptm hpt h g 1 (by simp [hsg]) (by simp; linarith [T3])
            simp at this; linarith
          · rw [ext_mk π hs0] at hr'
            rw [ext_mk ρ hs0]
            set s' : MasterIndex G := ⟨(g : G) + h, mem_master hs0⟩ with hs'
            have hsne : (s' : G) ≠ g₀ := hsg
            have c1 := hcomp s' hsne
            have c2 := pt3 hpt g h (kv g₀ s' hsne) (by rw [coe_kv]; simp [hs']) (by linarith)
            have c3 := ptm hpt (kv g₀ s' hsne) s' 1 (by rw [coe_kv]; simp) (by simp; linarith)
            simp at c3
            linarith
      | nonnegative g =>
        have hr0 : rowEval (row13Coeff g₀ (.nonnegative g)) π = row13Rhs g₀ π₀ (.nonnegative g) := hr
        have hπg : π g = 0 := by
          simp only [row13Coeff, rowEval_coord, row13Rhs, ext_coe] at hr0; exact hr0
        have hgne : (g : G) ≠ g₀ := by
          intro e
          have : g = g0v := Subtype.ext e
          rw [this, hπg0] at hπg; linarith
        have c1 := hcomp g hgne
        have hk : π (kv g₀ g hgne) = π₀ := by linarith
        have hM : 0 < addOrderOf (g : G) := addOrderOf_pos _
        have d1 := ptm hpt g (kv g₀ g hgne) 1 (by rw [coe_kv]; simp) (by rw [hk, hπg]; ring)
        have d2 := ptm hpt g (kv g₀ g hgne) (addOrderOf (g : G) + 1)
          (by rw [coe_kv, add_nsmul, addOrderOf_nsmul_eq_zero]; simp)
          (by rw [hk, hπg]; ring)
        simp only [row13Coeff, rowEval_coord, ext_coe]
        have hMr : (0 : ℝ) < addOrderOf (g : G) := by exact_mod_cast hM
        push_cast at d2
        simp at d1
        by_contra hne
        have : (addOrderOf (g : G) : ℝ) * ρ g = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact hne h

end Sys13

end Gomory69.MasterFaces

open Gomory69.MasterFaces


theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (hg₀ : g₀ ≠ 0) (π : MasterIndex G → ℝ) (π₀ : ℝ)
    (hπ₀ : 0 < π₀) :
    IsFace (masterSupport G) g₀ π π₀ ↔ IsSystem13Basic g₀ π₀ π := by
  exact theorem_18_core g₀ hg₀ π π₀ hπ₀
