-- Prove2me | solution 1 for LovaszSchrijver.NPlus.contraction_support_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:37:42.01486+00:00
-- url     : https://prove2.me/submissions/7a0e31da-34c8-4fba-9b1e-c9083b069085

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_Constraints



namespace LovaszSchrijver.NPlus

theorem csb_arith (m s t i : ℕ) (hm : m % 2 = 1) (hs : s < m) (ht : t < m) (hi : i < m)
    (hsi : s ≠ i) (hti : t ≠ i) (h : t = (s + 1) % m) :
    (if i < s then s else s + 1) % 2 ≠ (if i < t then t else t + 1) % 2 := by
  rcases Nat.lt_or_ge (s + 1) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    split_ifs <;> omega
  · have : s + 1 = m := by omega
    rw [this, Nat.mod_self] at h
    split_ifs <;> omega

theorem csb_two {V : Type} (G : SimpleGraph V) (S : Set V) (a b : V)
    (hS : ∀ w ∈ S, w = a ∨ w = b) : (G.induce S).Colorable 2 := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (fun w : S => if (w : V) = a then (0 : Fin 2) else 1) ?_⟩
  intro x y hxy
  have hne : (x : V) ≠ y := G.ne_of_adj hxy
  rcases hS x x.2 with hx | hx <;> rcases hS y y.2 with hy | hy
  · exact absurd (hx.trans hy.symm) hne
  · have : (y : V) ≠ a := fun h => hne (hx.trans h.symm)
    simp [hx, this]
  · have : (x : V) ≠ a := fun h => hne (h.trans hy.symm)
    simp [hy, this]
  · exact absurd (hx.trans hy.symm) hne

theorem csb_hole {V : Type} (G : SimpleGraph V) (C : Finset V) (hC : IsOddHole G C)
    (S : Set V) (hS : ∀ w ∈ S, w ∈ C) (v : V) (hv : v ∈ C) (hvS : v ∉ S) :
    (G.induce S).Colorable 2 := by
  classical
  obtain ⟨m, hodd, hm3, f, hf⟩ := hC
  have hm : m % 2 = 1 := Nat.odd_iff.mp hodd
  let i : Fin m := f.symm ⟨v, hv⟩
  let idx : S → Fin m := fun w => f.symm ⟨w, hS w w.2⟩
  let n : S → ℕ := fun w => if i.val < (idx w).val then (idx w).val else (idx w).val + 1
  refine ⟨SimpleGraph.Coloring.mk (fun w : S => if n w % 2 = 0 then (0 : Fin 2) else 1) ?_⟩
  intro x y hxy
  have hfx : ((f (idx x) : C) : V) = x := by simp [idx]
  have hfy : ((f (idx y) : C) : V) = y := by simp [idx]
  have hadj : G.Adj ((f (idx x) : C) : V) ((f (idx y) : C) : V) := by
    rw [hfx, hfy]; exact hxy
  have hxi : (idx x).val ≠ i.val := by
    intro h
    have : idx x = i := Fin.ext h
    apply hvS
    have : ((f (idx x) : C) : V) = v := by rw [this]; simp [i]
    rw [← this, hfx]; exact x.2
  have hyi : (idx y).val ≠ i.val := by
    intro h
    have : idx y = i := Fin.ext h
    apply hvS
    have : ((f (idx y) : C) : V) = v := by rw [this]; simp [i]
    rw [← this, hfy]; exact y.2
  have key : n x % 2 ≠ n y % 2 := by
    rcases (hf _ _).mp hadj with h | h
    · exact csb_arith m _ _ _ hm (idx x).2 (idx y).2 i.2 hxi hyi h
    · exact (csb_arith m _ _ _ hm (idx y).2 (idx x).2 i.2 hyi hxi h).symm
  intro heq
  apply key
  split_ifs at heq with h1 h2 h2 <;> first | omega | exact absurd heq (by decide)

theorem csb_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card → ∀ v, 0 < chi B v →
        (G.induce {w | 0 < contractCoeff G (chi B) v w}).Colorable 2) ∧
    (∀ C : Finset V, IsOddHole G C → ∀ v, 0 < chi C v →
        (G.induce {w | 0 < contractCoeff G (chi C) v w}).Colorable 2) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ → ∀ v, 0 < wheelCoeff U u₀ v →
        (G.induce {w | 0 < contractCoeff G (wheelCoeff U u₀) v w}).Colorable 2) ∧
    (∀ D : Finset V, IsOddAntihole G D → ∀ v, 0 < chi D v →
        (G.induce {w | 0 < contractCoeff G (chi D) v w}).Colorable 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB _ v hv
    have hvB : v ∈ B := by by_contra h; simp [chi, h] at hv
    apply csb_two G _ v v
    intro w hw
    simp only [Set.mem_setOf_eq, contractCoeff, chi] at hw
    split_ifs at hw with h1 h2
    · exact absurd hw (lt_irrefl _)
    · exfalso; apply h1; right
      by_cases hwv : w = v
      · exact absurd (Or.inl hwv) h1
      · exact hB hvB h2 (Ne.symm hwv)
    · exact absurd hw (lt_irrefl _)
  · intro C hC v hv
    have hvC : v ∈ C := by by_contra h; simp [chi, h] at hv
    apply csb_hole G C hC _ _ v hvC
    · simp [contractCoeff]
    · intro w hw
      simp only [Set.mem_setOf_eq, contractCoeff, chi] at hw
      split_ifs at hw with h1 h2
      · exact absurd hw (lt_irrefl _)
      · exact h2
      · exact absurd hw (lt_irrefl _)
  · intro U u₀ hW v hv
    obtain ⟨hu₀, hC, hadj⟩ := hW
    by_cases hvu : v = u₀
    · subst hvu
      apply csb_two G _ v v
      intro w hw
      simp only [Set.mem_setOf_eq, contractCoeff, wheelCoeff] at hw
      split_ifs at hw with h1 h2 h3
      · exact absurd hw (lt_irrefl _)
      · exact absurd (Or.inl h2) h1
      · exact absurd (Or.inr (hadj w (Finset.mem_erase.mpr ⟨h2, h3⟩))) h1
      · exact absurd hw (lt_irrefl _)
    · have hvU : v ∈ U := by
        by_contra h; simp [wheelCoeff, hvu, h] at hv
      apply csb_hole G _ hC _ _ v (Finset.mem_erase.mpr ⟨hvu, hvU⟩)
      · simp [contractCoeff]
      · intro w hw
        simp only [Set.mem_setOf_eq, contractCoeff, wheelCoeff] at hw
        split_ifs at hw with h1 h2 h3
        · exact absurd hw (lt_irrefl _)
        · exfalso; apply h1; right; rw [h2]; exact (hadj v (Finset.mem_erase.mpr ⟨hvu, hvU⟩)).symm
        · exact Finset.mem_erase.mpr ⟨h2, h3⟩
        · exact absurd hw (lt_irrefl _)
  · intro D hD v hv
    have hvD : v ∈ D := by by_contra h; simp [chi, h] at hv
    obtain ⟨hD5, m, hodd, hm3, f, hf⟩ := hD
    have hm : m % 2 = 1 := Nat.odd_iff.mp hodd
    have hmcard : m = D.card := by
      have := Fintype.card_congr f; simpa using this
    let i : Fin m := f.symm ⟨v, hvD⟩
    have hi1 : (i.val + 1) % m < m := Nat.mod_lt _ (by omega)
    have hi2 : (i.val + (m - 1)) % m < m := Nat.mod_lt _ (by omega)
    apply csb_two G _ (f ⟨_, hi1⟩ : V) (f ⟨_, hi2⟩ : V)
    intro w hw
    simp only [Set.mem_setOf_eq, contractCoeff, chi] at hw
    split_ifs at hw with h1 h2
    · exact absurd hw (lt_irrefl _)
    · push_neg at h1
      let s : Fin m := f.symm ⟨w, h2⟩
      have hfs : ((f s : D) : V) = w := by simp [s]
      have hfi : ((f i : D) : V) = v := by simp [i]
      have hcadj : Gᶜ.Adj ((f i : D) : V) ((f s : D) : V) := by
        rw [hfs, hfi]
        rw [SimpleGraph.compl_adj]
        exact ⟨fun h => h1.1 h.symm, h1.2⟩
      rcases (hf _ _).mp hcadj with h | h
      · left; rw [← hfs]; congr 2; exact Fin.ext h
      · right; rw [← hfs]; congr 2; apply Fin.ext
        show s.val = (i.val + (m - 1)) % m
        have hs := s.2
        have hi := i.2
        rcases Nat.lt_or_ge (s.val + 1) m with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at h
          rw [h]
          rw [show s.val + 1 + (m - 1) = s.val + m by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt hs]
        · have : s.val + 1 = m := by omega
          rw [this, Nat.mod_self] at h
          rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    · exact absurd hw (lt_irrefl _)

end LovaszSchrijver.NPlus

open LovaszSchrijver.NPlus


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card → ∀ v, 0 < chi B v →
        (G.induce {w | 0 < contractCoeff G (chi B) v w}).Colorable 2) ∧
    (∀ C : Finset V, IsOddHole G C → ∀ v, 0 < chi C v →
        (G.induce {w | 0 < contractCoeff G (chi C) v w}).Colorable 2) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ → ∀ v, 0 < wheelCoeff U u₀ v →
        (G.induce {w | 0 < contractCoeff G (wheelCoeff U u₀) v w}).Colorable 2) ∧
    (∀ D : Finset V, IsOddAntihole G D → ∀ v, 0 < chi D v →
        (G.induce {w | 0 < contractCoeff G (chi D) v w}).Colorable 2) := by
  exact csb_core G hG
