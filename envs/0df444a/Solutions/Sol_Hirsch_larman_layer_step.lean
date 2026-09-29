-- Prove2me | solution 1 for Hirsch.larman_layer_step
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:41:18.182242+00:00
-- url     : https://prove2.me/submissions/979e1731-4b6b-4a6d-84a0-7a0e917a58a2

-- Port of elmismisimoxhunca submission 101bba85-6a84-476a-b203-353ae59bd7f3, from Mathlib c5ea003 to 0df444a.
import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Theorems.Thm_Hirsch_relaxation_vertex
import Theorems.Thm_Hirsch_relaxation_exit_vertex
import Theorems.Thm_Hirsch_bounded_relaxation_cut
import Theorems.Thm_Hirsch_facet_walk
import Theorems.Thm_Hirsch_gdist_reach

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace LarmanLayerAstra

private theorem adj_symm {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {x y : E} (h : Adj P x y) : Adj P y x := by
  refine ⟨h.1.symm, ?_⟩
  rw [segment_symm]
  exact h.2

-- Endpoint lemma from the accepted Kalai--Kleitman proof.
private theorem adj_right_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {a b : E} (h : Adj P a b) : b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1:ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1:ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      have h5 : p * s + q * t ≤ p * 1 + q * 1 := by
        have := hs.2; have := ht.2
        nlinarith
      nlinarith [hs.2, ht.2, hs.1, ht.1]
    rw [hs1]
    module
  exact h.2.extremePoints_subset_extremePoints hb

private theorem reach_append {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {L : ℕ} {u x y : E} (h : Reach P L u x)
    (hxy : x = y ∨ Adj P x y) : Reach P (L + 1) u y := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => if i ≤ L then w i else y, by simpa using h0, by simp, ?_⟩
  intro i hi
  by_cases hiL : i < L
  · have hi1 : i + 1 ≤ L := hiL
    simpa only [if_pos hiL.le, if_pos hi1] using hstep i hiL
  · have hiL : i = L := by omega
    subst i
    simpa [hL] using hxy

private theorem distance_step {d n : ℕ}
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    (hbd : Bornology.IsBounded (Hpoly a b))
    {u x y : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hy : y ∈ Set.extremePoints ℝ (Hpoly a b))
    (hxy : x = y ∨ Adj (Hpoly a b) x y) :
    gdist (Hpoly a b) u x ≤ gdist (Hpoly a b) u y + 1 := by
  have hyx : y = x ∨ Adj (Hpoly a b) y x :=
    hxy.elim (fun h => Or.inl h.symm) (fun h => Or.inr (adj_symm h))
  exact Nat.sInf_le (reach_append (gdist_reach d n a b hbd u y hu hy) hyx)

private theorem segment_hyperplane {d : ℕ} {c x y z : EuclideanSpace ℝ (Fin d)}
    {M : ℝ} (hx : ⟪c, x⟫ = M) (hy : ⟪c, y⟫ = M)
    (hz : z ∈ segment ℝ x y) : ⟪c, z⟫ = M := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [inner_add_right, inner_smul_right, hx, hy]
  rw [← add_mul, hst, one_mul]

end LarmanLayerAstra

open LarmanLayerAstra

set_option maxHeartbeats 1000000 in
theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (r : Fin n) (har : a r ≠ 0) (T : Finset (Fin n)) (hrT : r ∈ T) (B : ℕ)
    (IH : ∀ (a' : Fin T.card → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin T.card → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (y z : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ Set.extremePoints ℝ (Hpoly a b)) (hz : z ∈ Set.extremePoints ℝ (Hpoly a b))
    (hyr : ⟪a r, y⟫ = b r) (hzr : ⟪a r, z⟫ = b r)
    (hyT : ∀ j, ⟪a j, y⟫ = b j → j ∈ T) (hzT : ∀ j, ⟪a j, z⟫ = b j → j ∈ T)
    (hback : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a r, w⟫ = b r →
      (∃ j, j ∉ T ∧ ⟪a j, w⟫ = b j) → gdist (Hpoly a b) u w + 1 ≤ gdist (Hpoly a b) u y) :
    gdist (Hpoly a b) u z ≤ gdist (Hpoly a b) u y + B := by
  classical
  -- Keep the selected rows and add one bounding cut.
  obtain ⟨M, hM, hbounded⟩ := bounded_relaxation_cut d n a b hbd T y hy hyT
  let e : T ≃ Fin T.card := T.equivFin
  let aQ : Fin (T.card + 1) → EuclideanSpace ℝ (Fin d) :=
    Fin.snoc (fun k => a (e.symm k)) (-∑ j ∈ T, a j)
  let bQ : Fin (T.card + 1) → ℝ := Fin.snoc (fun k => b (e.symm k)) M
  have hrepr : Hpoly aQ bQ = {x : EuclideanSpace ℝ (Fin d) |
      (∀ j ∈ T, ⟪a j, x⟫ ≤ b j) ∧ ⟪-∑ j ∈ T, a j, x⟫ ≤ M} := by
    ext x
    constructor
    · intro hx
      constructor
      · intro j hj
        have hh := hx (e ⟨j, hj⟩).castSucc
        simpa [aQ, bQ] using hh
      · have hh := hx (Fin.last T.card)
        simpa [aQ, bQ] using hh
    · intro hx i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa [aQ, bQ] using hx.2
      · simpa [aQ, bQ] using hx.1 (e.symm k) (e.symm k).2
  have hPQ : Hpoly a b ⊆ Hpoly aQ bQ := by
    intro x hx
    rw [hrepr]
    exact ⟨fun j _ => hx j, hM x hx⟩
  have hQ : ∀ x ∈ Hpoly aQ bQ, ∀ j ∈ T, ⟪a j, x⟫ ≤ b j := by
    intro x hx
    rw [hrepr] at hx
    exact hx.1
  have hbdQ : Bornology.IsBounded (Hpoly aQ bQ) := by
    rw [hrepr]
    exact hbounded
  let rQ : Fin (T.card + 1) := (e ⟨r, hrT⟩).castSucc
  have haQ : aQ rQ = a r := by simp [aQ, rQ]
  have hbQ : bQ rQ = b r := by simp [bQ, rQ]
  have hyQ : y ∈ Set.extremePoints ℝ (Hpoly aQ bQ) :=
    relaxation_vertex d n a b T (Hpoly aQ bQ) hQ y hy (hPQ hy.1) hyT
  have hzQ : z ∈ Set.extremePoints ℝ (Hpoly aQ bQ) :=
    relaxation_vertex d n a b T (Hpoly aQ bQ) hQ z hz (hPQ hz.1) hzT
  have hyF : y ∈ Set.extremePoints ℝ
      {x | x ∈ Hpoly aQ bQ ∧ ⟪aQ rQ, x⟫ = bQ rQ} := by
    exact inter_extremePoints_subset_extremePoints_of_subset (fun _ hx => hx.1)
      ⟨⟨hyQ.1, by simpa [haQ, hbQ] using hyr⟩, hyQ⟩
  have hzF : z ∈ Set.extremePoints ℝ
      {x | x ∈ Hpoly aQ bQ ∧ ⟪aQ rQ, x⟫ = bQ rQ} := by
    exact inter_extremePoints_subset_extremePoints_of_subset (fun _ hx => hx.1)
      ⟨⟨hzQ.1, by simpa [haQ, hbQ] using hzr⟩, hzQ⟩
  obtain ⟨w, hw0, hwB, hstep, hface⟩ :=
    facet_walk d T.card aQ bQ rQ (by simpa [haQ] using har) hbdQ B IH z y hzF hyF
  have hplane : ∀ j ≤ B, ⟪a r, w j⟫ = b r := by
    intro j hj
    simpa [haQ, hbQ] using (hface j hj).2
  -- Follow the relaxed walk from z. An exit already proves the desired bound.
  have hinv : ∀ j, j ≤ B →
      (gdist (Hpoly a b) u z ≤ gdist (Hpoly a b) u y + B) ∨
      (w j ∈ Set.extremePoints ℝ (Hpoly a b) ∧
        gdist (Hpoly a b) u z ≤ gdist (Hpoly a b) u (w j) + j) := by
    intro j
    induction j with
    | zero =>
        intro _
        right
        simpa [hw0] using (And.intro hz (le_refl (gdist (Hpoly a b) u z)))
    | succ j ih =>
        intro hj
        rcases ih (by omega) with hdone | ⟨hwj, hdist⟩
        · exact Or.inl hdone
        have hjB : j < B := by omega
        rcases hstep j hjB with heq | hadj
        · right
          rw [← heq]
          exact ⟨hwj, by omega⟩
        obtain ⟨hinside, hexit⟩ :=
          relaxation_exit_vertex d n a b T (Hpoly aQ bQ) hPQ hQ
            (w j) (w (j + 1)) hwj.1 hadj
        by_cases hnext : w (j + 1) ∈ Hpoly a b
        · have hedge := hinside hnext
          have hvertex := adj_right_extreme hedge
          have hdiststep := distance_step hbd hu hvertex (Or.inr hedge)
          exact Or.inr ⟨hvertex, by omega⟩
        · obtain ⟨v, hvseg, hvstep, hvrow⟩ := hexit hnext
          have hv : v ∈ Set.extremePoints ℝ (Hpoly a b) := by
            rcases hvstep with heq | hedge
            · simpa [heq] using hwj
            · exact adj_right_extreme hedge
          have hvr : ⟪a r, v⟫ = b r :=
            segment_hyperplane (hplane j (by omega)) (hplane (j + 1) hj) hvseg
          have hlow := hback v hv hvr hvrow
          have hdiststep := distance_step hbd hu hv
            (hvstep.elim (fun h => Or.inl h.symm) (fun h => Or.inr h))
          exact Or.inl (by omega)
  rcases hinv B le_rfl with hdone | ⟨_, hdist⟩
  · exact hdone
  · simpa [hwB] using hdist

#print axioms solution
