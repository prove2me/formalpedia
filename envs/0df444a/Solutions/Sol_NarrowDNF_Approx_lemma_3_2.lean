-- Prove2me | solution 1 for NarrowDNF.Approx.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:54:26.536688+00:00
-- url     : https://prove2.me/submissions/746f4217-e6b5-48db-b3b1-afb40b4eb579

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Shifts

section
set_option autoImplicit false
namespace NarrowDNF.Dev.L32
open NarrowDNF.Approx

variable {n : ℕ}

lemma sigma_eq {A B : Finset (Fin n)} (f : A → Bool) (g : B → Bool) (h : A = B)
    (hf : ∀ k (hk : k ∈ A), f ⟨k, hk⟩ = g ⟨k, h ▸ hk⟩) :
    (⟨A, f⟩ : Σ S : Finset (Fin n), S → Bool) = ⟨B, g⟩ := by
  subst h
  congr
  funext ⟨k, hk⟩
  exact hf k hk

lemma sigma_agree {A B : Finset (Fin n)} (f : A → Bool) (g : B → Bool)
    (h : (⟨A, f⟩ : Σ S : Finset (Fin n), S → Bool) = ⟨B, g⟩) :
    ∃ hAB : A = B, ∀ k (hk : k ∈ A), f ⟨k, hk⟩ = g ⟨k, hAB ▸ hk⟩ := by
  obtain ⟨hAB, hh⟩ := Sigma.mk.inj_iff.mp h
  subst hAB
  refine ⟨rfl, fun k hk => ?_⟩
  have := eq_of_heq hh
  exact congrFun this ⟨k, hk⟩

lemma atom_iff (J : ActivationFamily n) (x y : Cube n) :
    atom J x = atom J y ↔
      activeUnion J x = activeUnion J y ∧ ∀ k ∈ activeUnion J x, x k = y k := by
  constructor
  · intro h
    obtain ⟨hAB, hk⟩ := sigma_agree _ _ h
    exact ⟨hAB, fun k hk' => hk k hk'⟩
  · rintro ⟨hA, hk⟩
    exact sigma_eq _ _ hA (fun k hk' => hk k hk')

lemma mem_activeUnion (J : ActivationFamily n) (x : Cube n) (k : Fin n) :
    k ∈ activeUnion J x ↔ ∃ S : Finset (Fin n), J S (fun i => x i) = true ∧ k ∈ S := by
  classical
  simp [activeUnion, Finset.mem_biUnion]

lemma act_mono (J : ActivationFamily n) (hJ : IncreasingActivations J) {x y : Cube n}
    (hxy : x ≤ y) (S : Finset (Fin n)) (h : J S (fun i => x i) = true) :
    J S (fun i => y i) = true := by
  have : J S (fun i => x i) ≤ J S (fun i => y i) := hJ S (fun k => hxy k)
  rw [h] at this
  cases h2 : J S (fun i => y i)
  · rw [h2] at this; exact absurd this (by decide)
  · rfl

lemma act_sub (J : ActivationFamily n) (x : Cube n) (S : Finset (Fin n))
    (h : J S (fun i => x i) = true) : S ⊆ activeUnion J x :=
  fun k hk => (mem_activeUnion J x k).2 ⟨S, h, hk⟩

lemma act_congr (J : ActivationFamily n) (x y : Cube n) (S : Finset (Fin n))
    (h : ∀ k ∈ S, x k = y k) : J S (fun i => x i) = J S (fun i => y i) := by
  congr 1
  funext k
  exact h k k.2

lemma update_false_le (x : Cube n) (i : Fin n) : Function.update x i false ≤ x := by
  intro k
  by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma K1 (J : ActivationFamily n) (hJ : IncreasingActivations J) (i : Fin n) (x y : Cube n)
    (h : atom J x = atom J y) :
    atom J (Function.update x i false) = atom J (Function.update y i false) := by
  rw [atom_iff] at h ⊢
  obtain ⟨hA, hag⟩ := h
  have agree : ∀ k ∈ activeUnion J x, Function.update x i false k = Function.update y i false k := by
    intro k hk
    by_cases hki : k = i
    · subst hki; simp
    · simp [Function.update_of_ne hki, hag k hk]
  have key : ∀ S, J S (fun k => Function.update x i false k) = true ↔
      J S (fun k => Function.update y i false k) = true := by
    intro S
    constructor
    · intro hS
      have h1 := act_mono J hJ (update_false_le x i) S hS
      have h2 := act_sub J x S h1
      rw [← act_congr J _ _ S (fun k hk => agree k (h2 hk))]
      exact hS
    · intro hS
      have h1 := act_mono J hJ (update_false_le y i) S hS
      have h2 := act_sub J y S h1
      rw [← hA] at h2
      rw [act_congr J _ _ S (fun k hk => agree k (h2 hk))]
      exact hS
  have hU : activeUnion J (Function.update x i false) = activeUnion J (Function.update y i false) := by
    ext k
    rw [mem_activeUnion, mem_activeUnion]
    constructor
    · rintro ⟨S, hS, hk⟩; exact ⟨S, (key S).1 hS, hk⟩
    · rintro ⟨S, hS, hk⟩; exact ⟨S, (key S).2 hS, hk⟩
  refine ⟨hU, fun k hk => ?_⟩
  rw [mem_activeUnion] at hk
  obtain ⟨S, hS, hkS⟩ := hk
  have h1 := act_mono J hJ (update_false_le x i) S hS
  exact agree k (act_sub J x S h1 hkS)

lemma K2 (J : ActivationFamily n) (hJ : IncreasingActivations J) (i : Fin n) (x : Cube n)
    (hi : i ∉ activeUnion J x) :
    atom J (Function.update x i false) = atom J x := by
  rw [atom_iff]
  have key : ∀ S, J S (fun k => Function.update x i false k) = true ↔ J S (fun k => x k) = true := by
    intro S
    constructor
    · exact act_mono J hJ (update_false_le x i) S
    · intro hS
      have h2 := act_sub J x S hS
      have : i ∉ S := fun h => hi (h2 h)
      rw [act_congr J _ x S (fun k hk => ?_)]
      · exact hS
      · have : k ≠ i := fun h => ‹i ∉ S› (h ▸ hk)
        simp [Function.update_of_ne this]
  have hU : activeUnion J (Function.update x i false) = activeUnion J x := by
    ext k
    rw [mem_activeUnion, mem_activeUnion]
    constructor
    · rintro ⟨S, hS, hk⟩; exact ⟨S, (key S).1 hS, hk⟩
    · rintro ⟨S, hS, hk⟩; exact ⟨S, (key S).2 hS, hk⟩
  refine ⟨hU, fun k hk => ?_⟩
  have : k ≠ i := fun h => hi (h ▸ (hU ▸ hk))
  simp [Function.update_of_ne this]

lemma update_self_of (x : Cube n) (i : Fin n) (b : Bool) (h : x i = b) :
    Function.update x i b = x := by
  rw [Function.update_eq_self_iff]; exact h.symm

theorem part1 (i : Fin n) (J : ActivationFamily n) (v : Cube n → Bool)
    (hJ : IncreasingActivations J) (hv : AdaptiveMeasurable J v) :
    AdaptiveMeasurable J (upper i v) := by
  intro x y hxy
  have hA := (atom_iff J x y).1 hxy
  by_cases hi : i ∈ activeUnion J x
  · have hxi : x i = y i := hA.2 i hi
    have hK := hv _ _ (K1 J hJ i x y hxy)
    have hvxy := hv x y hxy
    unfold upper
    rw [← hxi]
    cases hx : x i
    · simpa using hK
    · rw [update_self_of x i true hx, update_self_of y i true (hxi.symm.trans hx)]
      simp [hK, hvxy]
  · have hiy : i ∉ activeUnion J y := hA.1 ▸ hi
    have h1 := hv _ _ (K2 J hJ i x hi)
    have h2 := hv _ _ (K2 J hJ i y hiy)
    have hvxy := hv x y hxy
    have ux : upper i v x = v x := by
      unfold upper
      cases hx : x i
      · simpa using h1
      · rw [update_self_of x i true hx]; simp [h1]
    have uy : upper i v y = v y := by
      unfold upper
      cases hy : y i
      · simpa using h2
      · rw [update_self_of y i true hy]; simp [h2]
    rw [ux, uy, hvxy]

lemma force_singleton_activeUnion (J : ActivationFamily n) (i : Fin n) (x : Cube n) :
    activeUnion (force J {i}) x = activeUnion J (Function.update x i true) := by
  ext k
  rw [mem_activeUnion, mem_activeUnion]
  have key : ∀ S : Finset (Fin n), force J {i} S (fun k => x k) = J S (fun k => Function.update x i true k) := by
    intro S
    unfold force
    congr 1
    funext k
    by_cases h : (k : Fin n) = i
    · simp [h]
    · simp [h, Function.update_of_ne h]
  simp only [key]

lemma force_increasing (J : ActivationFamily n) (hJ : IncreasingActivations J) (D : Finset (Fin n)) :
    IncreasingActivations (force J D) := by
  intro S a b hab
  unfold force
  apply hJ S
  intro k
  by_cases h : (k : Fin n) ∈ D
  · simp [h]
  · simpa [h] using hab k

theorem part2 (i : Fin n) (J : ActivationFamily n) (v : Cube n → Bool)
    (hJ : IncreasingActivations J) (hv : AdaptiveMeasurable J v) :
    AdaptiveMeasurable (force J {i}) (lower i v) := by
  intro x y hxy
  have hA := (atom_iff _ x y).1 hxy
  simp only [force_singleton_activeUnion] at hA
  obtain ⟨hA1, hA2⟩ := hA
  have hat : atom J (Function.update x i true) = atom J (Function.update y i true) := by
    rw [atom_iff]
    refine ⟨hA1, fun k hk => ?_⟩
    by_cases hki : k = i
    · subst hki; simp
    · simp [Function.update_of_ne hki, hA2 k hk]
  have h_t := hv _ _ hat
  have h_f := hv _ _ (K1 J hJ i _ _ hat)
  simp only [Function.update_idem] at h_f
  by_cases hi : i ∈ activeUnion J (Function.update x i true)
  · have hxi : x i = y i := hA2 i hi
    unfold lower
    rw [← hxi]
    cases hx : x i
    · simp [h_t, h_f]
    · simp [h_t]
  · have hiy : i ∉ activeUnion J (Function.update y i true) := hA1 ▸ hi
    have g1 := hv _ _ (K2 J hJ i _ hi)
    have g2 := hv _ _ (K2 J hJ i _ hiy)
    simp only [Function.update_idem] at g1 g2
    have lx : lower i v x = v (Function.update x i true) := by
      unfold lower
      split_ifs <;> simp [g1]
    have ly : lower i v y = v (Function.update y i true) := by
      unfold lower
      split_ifs <;> simp [g2]
    rw [lx, ly, h_t]

lemma force_force (J : ActivationFamily n) (D E : Finset (Fin n)) :
    force (force J D) E = force J (D ∪ E) := by
  funext S z
  unfold force
  congr 1
  funext k
  by_cases h1 : (k : Fin n) ∈ D <;> by_cases h2 : (k : Fin n) ∈ E <;> simp [h1, h2]

lemma force_empty (J : ActivationFamily n) : force J ∅ = J := by
  funext S z
  unfold force
  simp

lemma lowerCoordinates_append (s : List (Fin n × Bool)) (t : Fin n × Bool) :
    lowerCoordinates (s ++ [t]) = if t.2 then insert t.1 (lowerCoordinates s) else lowerCoordinates s := by
  obtain ⟨a, b⟩ := t
  cases b <;> simp [lowerCoordinates, List.filterMap_append]

theorem part3 (J : ActivationFamily n) (v : Cube n → Bool)
    (hJ : IncreasingActivations J) (hv : AdaptiveMeasurable J v) (s : List (Fin n × Bool)) :
    AdaptiveMeasurable (force J (lowerCoordinates s)) (applyShifts s v) := by
  induction s using List.reverseRecOn with
  | nil =>
    have : lowerCoordinates ([] : List (Fin n × Bool)) = ∅ := by simp [lowerCoordinates]
    rw [this, force_empty]
    simpa [applyShifts] using hv
  | append_singleton s t ih =>
    have hinc := force_increasing J hJ (lowerCoordinates s)
    have happ : applyShifts (s ++ [t]) v =
        (if t.2 then lower t.1 (applyShifts s v) else upper t.1 (applyShifts s v)) := by
      simp [applyShifts, List.foldl_append]
    rw [happ, lowerCoordinates_append]
    cases hb : t.2
    · simpa [hb] using part1 t.1 _ _ hinc ih
    · have := part2 t.1 _ _ hinc ih
      rw [force_force] at this
      have e : lowerCoordinates s ∪ {t.1} = insert t.1 (lowerCoordinates s) := by
        rw [Finset.union_comm]; rfl
      rw [e] at this
      simpa [hb] using this

end NarrowDNF.Dev.L32

namespace NarrowDNF.Approx
open NarrowDNF.Dev.L32 in
theorem chk_lemma_3_2 {n : ℕ} (i : Fin n) (J : ActivationFamily n) (v : Cube n → Bool)
    (hJ : IncreasingActivations J) (hv : AdaptiveMeasurable J v) :
    AdaptiveMeasurable J (upper i v) ∧
    AdaptiveMeasurable (force J {i}) (lower i v) ∧
    (∀ s : List (Fin n × Bool),
      AdaptiveMeasurable (force J (lowerCoordinates s)) (applyShifts s v)) :=
  ⟨part1 i J v hJ hv, part2 i J v hJ hv, part3 J v hJ hv⟩
end NarrowDNF.Approx
end

theorem solution : type_of% @NarrowDNF.Approx.chk_lemma_3_2 := @NarrowDNF.Approx.chk_lemma_3_2
