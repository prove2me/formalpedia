-- Prove2me | solution 1 for MetricTSP.tour_of_parity_join
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T22:25:11.117103+00:00
-- url     : https://prove2.me/submissions/ee101fc9-7e64-4419-a50c-5d01f1e3018f

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

set_option maxHeartbeats 1000000

namespace MetricTSP

open Finset

variable {n : ℕ}

/-! ### Closed walks with natural-number indexing -/

/-- Cost of the closed walk `f 0 → f 1 → ⋯ → f (L-1) → f 0`. -/
noncomputable def walkCost (c : Fin n → Fin n → ℝ) (L : ℕ) (f : ℕ → Fin n) : ℝ :=
  ∑ i ∈ Finset.range L, c (f i) (f ((i + 1) % L))

/-- Key modular identity for rotations. -/
lemma rot_mod_key (L a x : ℕ) (hL : 0 < L) (hx : x < L) :
    (a + x + (L - a % L)) % L = x := by
  have hdm := Nat.div_add_mod a L
  have hr := Nat.mod_lt a hL
  have hmul : L * (a / L + 1) = L * (a / L) + L := by ring
  have h2 : a + x + (L - a % L) = L * (a / L + 1) + x := by omega
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]

/-- Rotating the start of a closed walk does not change its cost. -/
lemma walkCost_rotate (c : Fin n → Fin n → ℝ) (L : ℕ) (hL : 0 < L) (f : ℕ → Fin n)
    (a : ℕ) :
    walkCost c L (fun i => f ((a + i) % L)) = walkCost c L f := by
  unfold walkCost
  apply Finset.sum_nbij' (fun i => (a + i) % L) (fun j => (j + (L - a % L)) % L)
  · intro i _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hL)
  · intro j _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hL)
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mod_add_mod]
    exact rot_mod_key L a i hL hi
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.add_mod_mod]
    rw [show a + (j + (L - a % L)) = a + j + (L - a % L) from by ring]
    exact rot_mod_key L a j hL hj
  · intro i hi
    rw [Finset.mem_range] at hi
    show c (f ((a + i) % L)) (f ((a + (i + 1) % L) % L))
      = c (f ((a + i) % L)) (f (((a + i) % L + 1) % L))
    congr 2
    rw [Nat.add_mod_mod, Nat.mod_add_mod]
    rw [show a + (i + 1) = a + i + 1 from by ring]

/-- Concatenating two closed walks that share their starting vertex. -/
lemma walkCost_append (c : Fin n → Fin n → ℝ) (L1 L2 : ℕ) (h1 : 0 < L1) (h2 : 0 < L2)
    (f1 f2 : ℕ → Fin n) (hshare : f1 0 = f2 0) :
    walkCost c (L1 + L2) (fun i => if i < L1 then f1 i else f2 (i - L1))
      = walkCost c L1 f1 + walkCost c L2 f2 := by
  unfold walkCost
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : (i + 1) % (L1 + L2) = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [e1]
    by_cases hlast : i + 1 = L1
    · have e2 : (i + 1) % L1 = 0 := by rw [hlast, Nat.mod_self]
      rw [e2]
      beta_reduce
      rw [if_pos hi, if_neg (show ¬ i + 1 < L1 by omega)]
      have e3 : i + 1 - L1 = 0 := by omega
      rw [e3, ← hshare]
    · have e2 : (i + 1) % L1 = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [e2]
      beta_reduce
      rw [if_pos hi, if_pos (show i + 1 < L1 by omega)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have eL : ¬ L1 + i < L1 := by omega
    have eidx : L1 + i - L1 = i := by omega
    by_cases hlast : i + 1 = L2
    · have e1 : (L1 + i + 1) % (L1 + L2) = 0 := by
        rw [show L1 + i + 1 = L1 + L2 from by omega, Nat.mod_self]
      have e2 : (i + 1) % L2 = 0 := by rw [hlast, Nat.mod_self]
      rw [e1, e2]
      beta_reduce
      rw [if_neg eL, eidx, if_pos h1, hshare]
    · have e1 : (L1 + i + 1) % (L1 + L2) = L1 + i + 1 := Nat.mod_eq_of_lt (by omega)
      have e2 : (i + 1) % L2 = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      beta_reduce
      rw [if_neg eL, eidx, if_neg (show ¬ L1 + i + 1 < L1 by omega)]
      congr 2
      omega

/-- Merging two closed walks at a shared vertex `f1 a = f2 b`. -/
noncomputable def mergeWalk (L1 L2 a b : ℕ) (f1 f2 : ℕ → Fin n) : ℕ → Fin n :=
  fun i => if i < L1 then f1 ((a + i) % L1) else f2 ((b + (i - L1)) % L2)

lemma mergeWalk_cost (c : Fin n → Fin n → ℝ) (L1 L2 a b : ℕ) (h1 : 0 < L1)
    (h2 : 0 < L2) (ha : a < L1) (hb : b < L2) (f1 f2 : ℕ → Fin n)
    (hshare : f1 a = f2 b) :
    walkCost c (L1 + L2) (mergeWalk L1 L2 a b f1 f2)
      = walkCost c L1 f1 + walkCost c L2 f2 := by
  have hsh : (fun i => f1 ((a + i) % L1)) 0 = (fun j => f2 ((b + j) % L2)) 0 := by
    show f1 ((a + 0) % L1) = f2 ((b + 0) % L2)
    rw [Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact hshare
  have h := walkCost_append c L1 L2 h1 h2 (fun i => f1 ((a + i) % L1))
    (fun j => f2 ((b + j) % L2)) hsh
  rw [walkCost_rotate c L1 h1 f1 a, walkCost_rotate c L2 h2 f2 b] at h
  calc walkCost c (L1 + L2) (mergeWalk L1 L2 a b f1 f2)
      = walkCost c (L1 + L2) (fun i => if i < L1 then (fun i => f1 ((a + i) % L1)) i
          else (fun j => f2 ((b + j) % L2)) (i - L1)) := rfl
    _ = _ := h

lemma mergeWalk_mem (L1 L2 a b : ℕ) (h1 : 0 < L1) (h2 : 0 < L2)
    (f1 f2 : ℕ → Fin n) (v : Fin n) :
    (∃ i, i < L1 + L2 ∧ mergeWalk L1 L2 a b f1 f2 i = v)
      ↔ (∃ i, i < L1 ∧ f1 i = v) ∨ (∃ i, i < L2 ∧ f2 i = v) := by
  unfold mergeWalk
  constructor
  · rintro ⟨i, hi, hv⟩
    by_cases hiL : i < L1
    · rw [if_pos hiL] at hv
      exact Or.inl ⟨(a + i) % L1, Nat.mod_lt _ h1, hv⟩
    · rw [if_neg hiL] at hv
      exact Or.inr ⟨(b + (i - L1)) % L2, Nat.mod_lt _ h2, hv⟩
  · rintro (⟨j, hj, hv⟩ | ⟨j, hj, hv⟩)
    · refine ⟨(j + (L1 - a % L1)) % L1, by
        have := Nat.mod_lt (j + (L1 - a % L1)) h1
        omega, ?_⟩
      rw [if_pos (Nat.mod_lt _ h1)]
      rw [Nat.add_mod_mod, show a + (j + (L1 - a % L1)) = a + j + (L1 - a % L1) from by
        ring, rot_mod_key L1 a j h1 hj]
      exact hv
    · set i := L1 + (j + (L2 - b % L2)) % L2 with hidef
      have hmod := Nat.mod_lt (j + (L2 - b % L2)) h2
      refine ⟨i, by omega, ?_⟩
      rw [if_neg (by omega), show i - L1 = (j + (L2 - b % L2)) % L2 from by omega]
      rw [Nat.add_mod_mod, show b + (j + (L2 - b % L2)) = b + j + (L2 - b % L2) from by
        ring, rot_mod_key L2 b j h2 hj]
      exact hv

/-- Dropping the final index of a closed walk, by the triangle inequality. -/
lemma walkCost_dropLast (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (M : ℕ)
    (hM : 1 ≤ M) (f : ℕ → Fin n) :
    walkCost c (M + 1) f ≤ walkCost c (M + 2) f := by
  unfold walkCost
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ (n := M)]
  have hstep : ∀ i ∈ Finset.range M,
      c (f i) (f ((i + 1) % (M + 1))) = c (f i) (f ((i + 1) % (M + 2))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Finset.sum_congr rfl hstep]
  have e1 : (M + 1) % (M + 1) = 0 := Nat.mod_self _
  have e2 : (M + 1) % (M + 2) = M + 1 := Nat.mod_eq_of_lt (by omega)
  have e3 : (M + 2) % (M + 2) = 0 := Nat.mod_self _
  have e4 : (M + 1 + 1) % (M + 2) = 0 := by rw [show M + 1 + 1 = M + 2 from rfl, e3]
  rw [e1, e2, e4]
  have htri := hc.2.2 (f M) (f (M + 1)) (f 0)
  linarith

lemma rot_val' {m : ℕ} (i : Fin m) : (finRotate m i).val = (i.val + 1) % m := by
  have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp i.pos⟩
  rw [finRotate_apply, Fin.add_def, Fin.val_one']
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

/-- A closed walk that covers every city can be shortcut to a Hamiltonian tour. -/
lemma tour_of_walk (c : Fin n → Fin n → ℝ) (hn : 3 ≤ n) (hc : IsMetricCost c) :
    ∀ L, 0 < L → ∀ f : ℕ → Fin n, (∀ v : Fin n, ∃ i, i < L ∧ f i = v) →
    ∃ π : Equiv.Perm (Fin n), tourCost c π ≤ walkCost c L f := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro hL f hcov
    by_cases hbig : n < L
    · -- find a duplicate pair and delete one occurrence
      obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to
          (s := Finset.range L) (t := Finset.univ) (f := f)
          (by simpa using hbig) (fun a _ => Finset.mem_univ (f a))
      rw [Finset.mem_range] at hx hy
      -- normalize to a < b
      obtain ⟨a, b, ha, hb, hab, hfab⟩ :
          ∃ a b, a < L ∧ b < L ∧ a ≠ b ∧ f a = f b := ⟨x, y, hx, hy, hxy, hfxy⟩
      -- rotate so the deleted occurrence `b` sits at the last index L-1
      set g : ℕ → Fin n := fun i => f ((b + 1 + i) % L) with hg
      have hgrot : walkCost c L g = walkCost c L f :=
        walkCost_rotate c L (by omega) f (b + 1)
      have hglast : g (L - 1) = f b := by
        show f ((b + 1 + (L - 1)) % L) = f b
        congr 1
        have hdm := Nat.div_add_mod (b + 1 + (L - 1)) L
        have h1 : b + 1 + (L - 1) = b + L := by omega
        rw [h1]
        rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod_of_dvd _ dvd_rfl]
        exact Nat.mod_eq_of_lt hb
      -- the shortened walk still covers everything
      have hcov' : ∀ v : Fin n, ∃ i, i < L - 1 ∧ g i = v := by
        intro v
        obtain ⟨j, hj, hfj⟩ := hcov v
        by_cases hjb : j = b
        · -- use the other copy `a`
          refine ⟨(a + (L - (b + 1) % L)) % L, ?_, ?_⟩
          · have hlt := Nat.mod_lt (a + (L - (b + 1) % L)) (show 0 < L by omega)
            -- it cannot be L-1 because rotation is injective and L-1 ↦ b ≠ a
            rcases Nat.lt_or_ge ((a + (L - (b + 1) % L)) % L) (L - 1) with h | h
            · exact h
            · exfalso
              have heq : (a + (L - (b + 1) % L)) % L = L - 1 := by omega
              have : (b + 1 + ((a + (L - (b + 1) % L)) % L)) % L = a := by
                rw [Nat.add_mod_mod]
                rw [show b + 1 + (a + (L - (b + 1) % L)) = b + 1 + a + (L - (b + 1) % L)
                  from by ring]
                exact rot_mod_key L (b + 1) a (by omega) ha
              rw [heq] at this
              have hb' : (b + 1 + (L - 1)) % L = b := by
                have h1 : b + 1 + (L - 1) = b + L := by omega
                rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero,
                  Nat.mod_mod_of_dvd _ dvd_rfl]
                exact Nat.mod_eq_of_lt hb
              rw [hb'] at this
              omega
          · show f ((b + 1 + (a + (L - (b + 1) % L)) % L) % L) = v
            rw [Nat.add_mod_mod]
            rw [show b + 1 + (a + (L - (b + 1) % L)) = b + 1 + a + (L - (b + 1) % L)
              from by ring]
            rw [rot_mod_key L (b + 1) a (by omega) ha]
            rw [← hfj, hjb]
            exact hfab
        · -- j ≠ b: its preimage under the rotation is below L-1
          refine ⟨(j + (L - (b + 1) % L)) % L, ?_, ?_⟩
          · have hlt := Nat.mod_lt (j + (L - (b + 1) % L)) (show 0 < L by omega)
            rcases Nat.lt_or_ge ((j + (L - (b + 1) % L)) % L) (L - 1) with h | h
            · exact h
            · exfalso
              have heq : (j + (L - (b + 1) % L)) % L = L - 1 := by omega
              have : (b + 1 + ((j + (L - (b + 1) % L)) % L)) % L = j := by
                rw [Nat.add_mod_mod]
                rw [show b + 1 + (j + (L - (b + 1) % L)) = b + 1 + j + (L - (b + 1) % L)
                  from by ring]
                exact rot_mod_key L (b + 1) j (by omega) hj
              rw [heq] at this
              have hb' : (b + 1 + (L - 1)) % L = b := by
                have h1 : b + 1 + (L - 1) = b + L := by omega
                rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero,
                  Nat.mod_mod_of_dvd _ dvd_rfl]
                exact Nat.mod_eq_of_lt hb
              rw [hb'] at this
              omega
          · show f ((b + 1 + (j + (L - (b + 1) % L)) % L) % L) = v
            rw [Nat.add_mod_mod]
            rw [show b + 1 + (j + (L - (b + 1) % L)) = b + 1 + j + (L - (b + 1) % L)
              from by ring]
            rw [rot_mod_key L (b + 1) j (by omega) hj]
            exact hfj
      -- cost decreases when dropping the last index
      have hdrop : walkCost c (L - 1) g ≤ walkCost c L g := by
        have h1 : 1 ≤ L - 2 := by omega
        have h2 := walkCost_dropLast c hc (L - 2) h1 g
        rw [show (L - 2) + 1 = L - 1 from by omega,
          show (L - 2) + 2 = L from by omega] at h2
        exact h2
      obtain ⟨π, hπ⟩ := ih (L - 1) (by omega) (by omega) g hcov'
      exact ⟨π, by linarith⟩
    · -- L ≤ n: coverage forces L = n and injectivity
      push_neg at hbig
      have hLn : L = n := by
        by_contra hne
        have hlt : L < n := by omega
        -- range L cannot cover n distinct values
        have : (Finset.univ : Finset (Fin n)) ⊆ (Finset.range L).image f := by
          intro v _
          obtain ⟨i, hi, hfi⟩ := hcov v
          exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hfi⟩
        have hcard := Finset.card_le_card this
        rw [Finset.card_univ, Fintype.card_fin] at hcard
        have := Finset.card_image_le (s := Finset.range L) (f := f)
        rw [Finset.card_range] at this
        omega
      have hLn2 : n = L := hLn.symm
      subst hLn2
      set g : Fin n → Fin n := fun i => f i.val with hgdef
      have hsurj : Function.Surjective g := by
        intro v
        obtain ⟨i, hi, hfi⟩ := hcov v
        exact ⟨⟨i, hi⟩, hfi⟩
      have hbij : Function.Bijective g :=
        (Finite.surjective_iff_bijective).mp hsurj
      refine ⟨Equiv.ofBijective g hbij, le_of_eq ?_⟩
      unfold tourCost walkCost
      rw [← Fin.sum_univ_eq_sum_range (fun i => c (f i) (f ((i + 1) % n)))]
      apply Finset.sum_congr rfl
      intro i _
      show c (f i.val) (f ((finRotate n i).val)) = c (f i.val) (f ((i.val + 1) % n))
      rw [rot_val']

/-! ### Multigraphs as symmetric multiplicity functions -/

/-- Degree of a vertex in a multigraph. -/
def mDeg (m : Fin n → Fin n → ℕ) (v : Fin n) : ℕ := ∑ u, m v u

/-- Total cost of a multigraph. -/
noncomputable def mCost (c : Fin n → Fin n → ℝ) (m : Fin n → Fin n → ℕ) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, (m u v : ℝ) * c u v

/-- The edge multiset of the injective cyclic sequence `g 0, …, g (j-1)`. -/
def cycEdge (j : ℕ) (g : ℕ → Fin n) (u v : Fin n) : ℕ :=
  ((Finset.range j).filter (fun i =>
    (g i = u ∧ g ((i + 1) % j) = v) ∨ (g i = v ∧ g ((i + 1) % j) = u))).card

/-- Cyclic neighbours in an injective cycle are distinct. -/
lemma cyc_step_ne (j : ℕ) (hj : 2 ≤ j) (g : ℕ → Fin n)
    (hinj : ∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2) (i : ℕ) (hi : i < j) :
    g i ≠ g ((i + 1) % j) := by
  intro h
  have h1 := hinj i ((i + 1) % j) hi (Nat.mod_lt _ (by omega)) h
  rcases Nat.lt_or_ge (i + 1) j with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1
    omega
  · have : i + 1 = j := by omega
    rw [this, Nat.mod_self] at h1
    omega

lemma cycEdge_symm (j : ℕ) (g : ℕ → Fin n) (u v : Fin n) :
    cycEdge j g u v = cycEdge j g v u := by
  unfold cycEdge
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

lemma cycEdge_diag (j : ℕ) (hj : 2 ≤ j) (g : ℕ → Fin n)
    (hinj : ∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2) (v : Fin n) :
    cycEdge j g v v = 0 := by
  unfold cycEdge
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  rw [Finset.mem_range] at hi
  have hne := cyc_step_ne j hj g hinj i hi
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact hne (h1.trans h2.symm)

lemma cycEdge_card (j : ℕ) (g : ℕ → Fin n) (u v : Fin n) :
    (cycEdge j g u v : ℝ) = ∑ i ∈ Finset.range j,
      (if (g i = u ∧ g ((i + 1) % j) = v) ∨ (g i = v ∧ g ((i + 1) % j) = u)
        then (1 : ℝ) else 0) := by
  unfold cycEdge
  rw [Finset.card_filter]
  push_cast
  rfl

/-- The rotation `i ↦ (i+1) % j` permutes the index range. -/
lemma count_rot (j : ℕ) (hj : 0 < j) (P : Fin n → Prop) [DecidablePred P]
    (g : ℕ → Fin n) :
    ((Finset.range j).filter (fun i => P (g ((i + 1) % j)))).card
      = ((Finset.range j).filter (fun i => P (g i))).card := by
  apply Finset.card_nbij' (fun i => (i + 1) % j) (fun i => (i + (j - 1)) % j)
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨Nat.mod_lt _ hj, hi.2⟩
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨Nat.mod_lt _ hj, ?_⟩
    have : ((i + (j - 1)) % j + 1) % j = i := by
      rw [Nat.mod_add_mod, show i + (j - 1) + 1 = i + j from by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hi.1
    rw [this]
    exact hi.2
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    show ((i + 1) % j + (j - 1)) % j = i
    rw [Nat.mod_add_mod, show i + 1 + (j - 1) = i + j from by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hi.1
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    show ((i + (j - 1)) % j + 1) % j = i
    rw [Nat.mod_add_mod, show i + (j - 1) + 1 = i + j from by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hi.1

/-- An injective cyclic sequence passes through each of its vertices once. -/
lemma count_visit (j : ℕ) (g : ℕ → Fin n)
    (hinj : ∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2) (v : Fin n) :
    ((Finset.range j).filter (fun i => g i = v)).card
      = if ∃ i, i < j ∧ g i = v then 1 else 0 := by
  by_cases hex : ∃ i, i < j ∧ g i = v
  · obtain ⟨i0, hi0, hgi0⟩ := hex
    rw [if_pos ⟨i0, hi0, hgi0⟩]
    rw [show (Finset.range j).filter (fun i => g i = v) = {i0} from ?_]
    · exact Finset.card_singleton i0
    · ext i
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hgi⟩
        exact hinj i i0 hi hi0 (hgi.trans hgi0.symm)
      · rintro rfl
        exact ⟨hi0, hgi0⟩
  · rw [if_neg hex, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    exact fun hgi => hex ⟨i, hi, hgi⟩

/-- Degree of the edge multiset of an injective cycle: `2` on the cycle, `0` off it. -/
lemma cycEdge_deg (j : ℕ) (hj : 2 ≤ j) (g : ℕ → Fin n)
    (hinj : ∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2) (v : Fin n) :
    mDeg (cycEdge j g) v = if ∃ i, i < j ∧ g i = v then 2 else 0 := by
  classical
  unfold mDeg cycEdge
  have hstep : ∀ i ∈ Finset.range j,
      ((Finset.range j).filter (fun i' => False)).card = 0 := by
    intro i _
    simp
  -- turn the sum of cardinalities into a double indicator sum
  have hexp : ∀ u : Fin n, ((Finset.range j).filter (fun i =>
      (g i = v ∧ g ((i + 1) % j) = u) ∨ (g i = u ∧ g ((i + 1) % j) = v))).card
      = ∑ i ∈ Finset.range j, (if (g i = v ∧ g ((i + 1) % j) = u)
          ∨ (g i = u ∧ g ((i + 1) % j) = v) then 1 else 0) := by
    intro u
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun u _ => hexp u), Finset.sum_comm]
  have hinner : ∀ i ∈ Finset.range j,
      (∑ u : Fin n, if (g i = v ∧ g ((i + 1) % j) = u)
          ∨ (g i = u ∧ g ((i + 1) % j) = v) then 1 else 0)
      = (if g i = v then 1 else 0) + (if g ((i + 1) % j) = v then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hne := cyc_step_ne j hj g hinj i hi
    by_cases h1 : g i = v
    · rw [if_pos h1, if_neg (fun h => hne (h1.trans h.symm))]
      have hcong : ∀ u : Fin n, ((g i = v ∧ g ((i + 1) % j) = u)
          ∨ (g i = u ∧ g ((i + 1) % j) = v)) ↔ u = g ((i + 1) % j) := by
        intro u
        constructor
        · rintro (⟨_, h⟩ | ⟨hu, h⟩)
          · exact h.symm
          · exact absurd (h1.trans h.symm) hne
        · rintro rfl
          exact Or.inl ⟨h1, rfl⟩
      rw [Finset.sum_congr rfl (fun u _ => if_congr (hcong u) rfl rfl)]
      rw [Finset.sum_ite_eq' Finset.univ (g ((i + 1) % j)) (fun _ => (1 : ℕ))]
      rw [if_pos (Finset.mem_univ _)]
    · by_cases h2 : g ((i + 1) % j) = v
      · rw [if_neg h1, if_pos h2]
        have hcong : ∀ u : Fin n, ((g i = v ∧ g ((i + 1) % j) = u)
            ∨ (g i = u ∧ g ((i + 1) % j) = v)) ↔ u = g i := by
          intro u
          constructor
          · rintro (⟨h, _⟩ | ⟨hu, _⟩)
            · exact absurd h h1
            · exact hu.symm
          · rintro rfl
            exact Or.inr ⟨rfl, h2⟩
        rw [Finset.sum_congr rfl (fun u _ => if_congr (hcong u) rfl rfl)]
        rw [Finset.sum_ite_eq' Finset.univ (g i) (fun _ => (1 : ℕ))]
        rw [if_pos (Finset.mem_univ _)]
      · rw [if_neg h1, if_neg h2]
        apply Finset.sum_eq_zero
        intro u _
        rw [if_neg]
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact h1 h
        · exact h2 h
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
  rw [← Finset.card_filter, ← Finset.card_filter]
  rw [count_rot j (by omega) (fun w => w = v) g, count_visit j g hinj v]
  by_cases hex : ∃ i, i < j ∧ g i = v
  · rw [if_pos hex, if_pos hex]
  · rw [if_neg hex, if_neg hex]

/-- Double indicator sum over an ordered pair. -/
lemma sum_pair_ind (c : Fin n → Fin n → ℝ) (A B : Fin n) :
    (∑ u, ∑ v, if u = A ∧ v = B then c u v else 0) = c A B := by
  have h1 : ∀ u : Fin n, (∑ v, if u = A ∧ v = B then c u v else 0)
      = if u = A then c u B else 0 := by
    intro u
    by_cases hu : u = A
    · rw [if_pos hu]
      rw [Finset.sum_congr rfl (fun v _ => if_congr (and_iff_right hu) rfl rfl)]
      rw [Finset.sum_ite_eq' Finset.univ B (fun v => c u v)]
      rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hu]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (fun h => hu h.1)]
  rw [Finset.sum_congr rfl (fun u _ => h1 u)]
  rw [Finset.sum_ite_eq' Finset.univ A (fun u => c u B)]
  rw [if_pos (Finset.mem_univ _)]

/-- Splitting the symmetric pair indicator when the endpoints differ. -/
lemma pair_ind_split (c : Fin n → Fin n → ℝ) (A B u v : Fin n) (hAB : A ≠ B) :
    (if (A = u ∧ B = v) ∨ (A = v ∧ B = u) then c u v else 0)
      = (if u = A ∧ v = B then c u v else 0) + (if u = B ∧ v = A then c u v else 0) := by
  by_cases h1 : u = A ∧ v = B
  · rw [if_pos h1, if_neg (fun h : u = B ∧ v = A => hAB (h1.1.symm.trans h.1)),
      add_zero, if_pos (Or.inl ⟨h1.1.symm, h1.2.symm⟩)]
  · by_cases h2 : u = B ∧ v = A
    · rw [if_neg h1, if_pos h2, zero_add, if_pos (Or.inr ⟨h2.2.symm, h2.1.symm⟩)]
    · rw [if_neg h1, if_neg h2, add_zero]
      rw [if_neg]
      rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact h1 ⟨ha.symm, hb.symm⟩
      · exact h2 ⟨hb.symm, ha.symm⟩

/-- The multigraph cost of a cycle's edge multiset is its walk cost. -/
lemma cycEdge_cost (c : Fin n → Fin n → ℝ) (hsym : ∀ u v, c u v = c v u)
    (j : ℕ) (hj : 2 ≤ j) (g : ℕ → Fin n)
    (hinj : ∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2) :
    mCost c (cycEdge j g) = walkCost c j g := by
  unfold mCost walkCost
  calc (1 / 2) * ∑ u, ∑ v, (cycEdge j g u v : ℝ) * c u v
      = (1 / 2) * ∑ u, ∑ v, ∑ i ∈ Finset.range j,
          (if (g i = u ∧ g ((i + 1) % j) = v)
            ∨ (g i = v ∧ g ((i + 1) % j) = u) then c u v else 0) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        rw [cycEdge_card, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : (g i = u ∧ g ((i + 1) % j) = v) ∨ (g i = v ∧ g ((i + 1) % j) = u)
        · rw [if_pos h, if_pos h, one_mul]
        · rw [if_neg h, if_neg h, zero_mul]
    _ = (1 / 2) * ∑ i ∈ Finset.range j, ∑ u, ∑ v,
          (if (g i = u ∧ g ((i + 1) % j) = v)
            ∨ (g i = v ∧ g ((i + 1) % j) = u) then c u v else 0) := by
        congr 1
        rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => Finset.sum_comm)]
        exact Finset.sum_comm
    _ = ∑ i ∈ Finset.range j, c (g i) (g ((i + 1) % j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hne := cyc_step_ne j hj g hinj i hi
        have hsplit : ∀ u v : Fin n, (if (g i = u ∧ g ((i + 1) % j) = v)
            ∨ (g i = v ∧ g ((i + 1) % j) = u) then c u v else 0)
            = (if u = g i ∧ v = g ((i + 1) % j) then c u v else 0)
              + (if u = g ((i + 1) % j) ∧ v = g i then c u v else 0) :=
          fun u v => pair_ind_split c (g i) (g ((i + 1) % j)) u v hne
        rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl
          (fun v _ => hsplit u v))]
        rw [Finset.sum_congr rfl (fun u _ => Finset.sum_add_distrib)]
        rw [Finset.sum_add_distrib]
        rw [sum_pair_ind c (g i) (g ((i + 1) % j)),
          sum_pair_ind c (g ((i + 1) % j)) (g i)]
        rw [hsym (g ((i + 1) % j)) (g i)]
        ring

/-- A cycle's edge multiset is dominated by any multigraph it lives in. -/
lemma cycEdge_le (m : Fin n → Fin n → ℕ) (hsym : ∀ u v, m u v = m v u)
    (j : ℕ) (hj : 2 ≤ j) (g : ℕ → Fin n)
    (hinj : ∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2)
    (hpos : ∀ i, i < j → 0 < m (g i) (g ((i + 1) % j)))
    (h2 : j = 2 → 2 ≤ m (g 0) (g 1)) (u v : Fin n) :
    cycEdge j g u v ≤ m u v := by
  rcases Nat.lt_or_ge j 3 with hj2 | hj3
  · -- j = 2
    have hj2' : j = 2 := by omega
    subst hj2'
    unfold cycEdge
    by_cases hmatch : (u = g 0 ∧ v = g 1) ∨ (u = g 1 ∧ v = g 0)
    · have hcard : ((Finset.range 2).filter (fun i =>
          (g i = u ∧ g ((i + 1) % 2) = v) ∨ (g i = v ∧ g ((i + 1) % 2) = u))).card ≤ 2 := by
        calc _ ≤ (Finset.range 2).card := Finset.card_filter_le _ _
          _ = 2 := Finset.card_range 2
      rcases hmatch with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · have hm2 : 2 ≤ m u v := by
          rw [hu, hv]
          exact h2 rfl
        exact le_trans hcard hm2
      · have hm2 : 2 ≤ m u v := by
          rw [hu, hv, hsym (g 1) (g 0)]
          exact h2 rfl
        exact le_trans hcard hm2
    · rw [show ((Finset.range 2).filter (fun i =>
          (g i = u ∧ g ((i + 1) % 2) = v) ∨ (g i = v ∧ g ((i + 1) % 2) = u))) = ∅ from ?_]
      · simp
      · rw [Finset.filter_eq_empty_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        interval_cases i
        · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
          · exact hmatch (Or.inl ⟨ha.symm, hb.symm⟩)
          · exact hmatch (Or.inr ⟨hb.symm, ha.symm⟩)
        · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
          · exact hmatch (Or.inr ⟨ha.symm, hb.symm⟩)
          · exact hmatch (Or.inl ⟨hb.symm, ha.symm⟩)
  · -- j ≥ 3 : at most one index fits, and it witnesses a positive edge
    unfold cycEdge
    set F := (Finset.range j).filter (fun i =>
      (g i = u ∧ g ((i + 1) % j) = v) ∨ (g i = v ∧ g ((i + 1) % j) = u)) with hF
    have hone : ∀ i1 ∈ F, ∀ i2 ∈ F, i1 = i2 := by
      intro i1 hi1 i2 hi2
      rw [hF, Finset.mem_filter, Finset.mem_range] at hi1 hi2
      obtain ⟨hi1r, hc1⟩ := hi1
      obtain ⟨hi2r, hc2⟩ := hi2
      have hmod1 : (i1 + 1) % j < j := Nat.mod_lt _ (by omega)
      have hmod2 : (i2 + 1) % j < j := Nat.mod_lt _ (by omega)
      rcases hc1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;> rcases hc2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
      · exact hinj i1 i2 hi1r hi2r (ha1.trans ha2.symm)
      · -- g i1 = u, g' i1 = v ; g i2 = v, g' i2 = u : forces (i1+2) % j = i1
        exfalso
        have e1 : i2 = (i1 + 1) % j := hinj i2 ((i1 + 1) % j) hi2r hmod1 (ha2.trans hb1.symm)
        have e2 : (i2 + 1) % j = i1 := hinj ((i2 + 1) % j) i1 hmod2 hi1r (hb2.trans ha1.symm)
        rw [e1, Nat.mod_add_mod] at e2
        rcases Nat.lt_or_ge (i1 + 2) j with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at e2
          omega
        · have hcase : i1 + 2 = j ∨ i1 + 2 = j + 1 := by omega
          rcases hcase with hc | hc
          · rw [hc, Nat.mod_self] at e2
            omega
          · rw [hc, show j + 1 = 1 + j from by omega, Nat.add_mod_right] at e2
            have : (1 : ℕ) % j = 1 := Nat.mod_eq_of_lt (by omega)
            rw [this] at e2
            omega
      · exfalso
        have e1 : i1 = (i2 + 1) % j := hinj i1 ((i2 + 1) % j) hi1r hmod2 (ha1.trans hb2.symm)
        have e2 : (i1 + 1) % j = i2 := hinj ((i1 + 1) % j) i2 hmod1 hi2r (hb1.trans ha2.symm)
        rw [e1, Nat.mod_add_mod] at e2
        rcases Nat.lt_or_ge (i2 + 2) j with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at e2
          omega
        · have hcase : i2 + 2 = j ∨ i2 + 2 = j + 1 := by omega
          rcases hcase with hc | hc
          · rw [hc, Nat.mod_self] at e2
            omega
          · rw [hc, show j + 1 = 1 + j from by omega, Nat.add_mod_right] at e2
            have : (1 : ℕ) % j = 1 := Nat.mod_eq_of_lt (by omega)
            rw [this] at e2
            omega
      · exact hinj i1 i2 hi1r hi2r (ha1.trans ha2.symm)
    rcases Finset.eq_empty_or_nonempty F with hFe | ⟨i0, hi0⟩
    · rw [hFe]
      simp
    · have hcard : F.card ≤ 1 := Finset.card_le_one.mpr hone
      have hi0' := hi0
      rw [hF, Finset.mem_filter, Finset.mem_range] at hi0'
      obtain ⟨hi0r, hc0⟩ := hi0'
      have hpos0 := hpos i0 hi0r
      rcases hc0 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [← ha, ← hb]
        omega
      · rw [← ha, ← hb, hsym (g ((i0 + 1) % j)) (g i0)]
        omega

lemma mDeg_pos_witness (m : Fin n → Fin n → ℕ) (v : Fin n) (h : 0 < mDeg m v) :
    ∃ u, 0 < m v u := by
  by_contra hc
  push_neg at hc
  unfold mDeg at h
  rw [Finset.sum_eq_zero (fun u _ => Nat.le_zero.mp (hc u))] at h
  omega

lemma mDeg_pos_of_edge (m : Fin n → Fin n → ℕ) (u v : Fin n) (h : 0 < m u v) :
    0 < mDeg m u := by
  unfold mDeg
  calc 0 < m u v := h
    _ ≤ ∑ w, m u w := Finset.single_le_sum (f := fun w => m u w)
        (fun w _ => Nat.zero_le _) (Finset.mem_univ v)

/-- In a simple (multiplicity ≤ 1) even multigraph, a non-backtracking
continuation exists at the end of any edge. -/
lemma next_edge (m : Fin n → Fin n → ℕ) (hone : ∀ u v, m u v ≤ 1)
    (heven : ∀ v, Even (mDeg m v)) (prev e : Fin n) (hedge : 0 < m e prev) :
    ∃ u, 0 < m e u ∧ u ≠ prev := by
  by_contra hc
  push_neg at hc
  have hall : ∀ u, u ≠ prev → m e u = 0 := by
    intro u hu
    by_contra hpos
    exact hu (hc u (by omega))
  have hsum : mDeg m e = m e prev := by
    unfold mDeg
    rw [Finset.sum_eq_single prev (fun b _ hb => hall b hb) (fun h => absurd
      (Finset.mem_univ prev) h)]
  have h1 : m e prev = 1 := by
    have := hone e prev
    omega
  have := heven e
  rw [hsum, h1] at this
  exact Nat.not_even_one this

/-- Finding an injective cycle (or a doubled edge) in an even multigraph. -/
lemma find_cycle (m : Fin n → Fin n → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hdiag : ∀ v, m v v = 0) (heven : ∀ v, Even (mDeg m v)) (v0 : Fin n)
    (hv0 : 0 < mDeg m v0) :
    ∃ (j : ℕ) (g : ℕ → Fin n), 2 ≤ j ∧
      (∀ i1 i2, i1 < j → i2 < j → g i1 = g i2 → i1 = i2) ∧
      (∀ i, i < j → 0 < m (g i) (g ((i + 1) % j))) ∧
      (j = 2 → 2 ≤ m (g 0) (g 1)) := by
  by_cases hdouble : ∃ u v, 2 ≤ m u v
  · obtain ⟨u, v, huv⟩ := hdouble
    have hne : u ≠ v := by
      intro h
      rw [h, hdiag v] at huv
      omega
    refine ⟨2, fun i => if i = 0 then u else v, le_refl 2, ?_, ?_, ?_⟩
    · intro i1 i2 hi1 hi2 hg
      interval_cases i1 <;> interval_cases i2 <;> simp_all
    · intro i hi
      interval_cases i
      · show 0 < m (if (0:ℕ) = 0 then u else v) (if (1 % 2 : ℕ) = 0 then u else v)
        norm_num
        omega
      · show 0 < m (if (1:ℕ) = 0 then u else v) (if (2 % 2 : ℕ) = 0 then u else v)
        norm_num
        rw [hsym]
        omega
    · intro _
      show 2 ≤ m (if (0:ℕ) = 0 then u else v) (if (1:ℕ) = 0 then u else v)
      norm_num
      exact huv
  · push_neg at hdouble
    have hone : ∀ u v, m u v ≤ 1 := fun u v => by have := hdouble u v; omega
    -- extend an injective path until it closes into a cycle
    suffices haux : ∀ (fuel t : ℕ) (g : ℕ → Fin n), 1 ≤ t → t ≤ n → n - t < fuel →
        (∀ i1 i2, i1 < t → i2 < t → g i1 = g i2 → i1 = i2) →
        (∀ i, i + 1 < t → 0 < m (g i) (g (i + 1))) →
        (0 < mDeg m (g (t - 1))) →
        ∃ (j : ℕ) (gc : ℕ → Fin n), 2 ≤ j ∧
          (∀ i1 i2, i1 < j → i2 < j → gc i1 = gc i2 → i1 = i2) ∧
          (∀ i, i < j → 0 < m (gc i) (gc ((i + 1) % j))) ∧
          (j = 2 → 2 ≤ m (gc 0) (gc 1)) by
      have hn1 : 1 ≤ n := v0.pos
      exact haux (n + 1) 1 (fun _ => v0) (le_refl 1) hn1 (by omega)
        (fun i1 i2 h1 h2 _ => by omega) (fun i hi => absurd hi (by omega)) (by simpa using hv0)
    intro fuel
    induction fuel with
    | zero =>
      intro t g _ _ hfuel
      omega
    | succ f ih =>
      intro t g ht1 htn hfuel hinj hpath hdeg
      set e := g (t - 1) with he
      -- find a continuation that does not backtrack
      have hu : ∃ u, 0 < m e u ∧ (2 ≤ t → u ≠ g (t - 2)) := by
        rcases Nat.lt_or_ge t 2 with ht' | ht'
        · obtain ⟨u, hu⟩ := mDeg_pos_witness m e hdeg
          exact ⟨u, hu, fun h => absurd h (by omega)⟩
        · have hedge : 0 < m e (g (t - 2)) := by
            have := hpath (t - 2) (by omega)
            rw [show t - 2 + 1 = t - 1 from by omega] at this
            rw [hsym]
            exact this
          obtain ⟨u, hu1, hu2⟩ := next_edge m hone heven (g (t - 2)) e hedge
          exact ⟨u, hu1, fun _ => hu2⟩
      obtain ⟨u, hue, hunb⟩ := hu
      have hue' : u ≠ e := by
        intro h
        rw [h, hdiag e] at hue
        omega
      by_cases honpath : ∃ s, s < t ∧ g s = u
      · -- the path closes into a cycle
        obtain ⟨s, hst, hgs⟩ := honpath
        have hs1 : s ≠ t - 1 := by
          intro h
          apply hue'
          rw [← hgs, h, he]
        have hs2 : s ≠ t - 2 := by
          intro h
          rcases Nat.lt_or_ge t 2 with ht' | ht'
          · omega
          · exact (hunb ht') (h ▸ hgs).symm
        have hs3 : s + 3 ≤ t := by omega
        refine ⟨t - s, fun i => g (s + i), by omega, ?_, ?_, ?_⟩
        · intro i1 i2 hi1 hi2 hg
          have := hinj (s + i1) (s + i2) (by omega) (by omega) hg
          omega
        · intro i hi
          rcases Nat.lt_or_ge (i + 1) (t - s) with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt]
            have := hpath (s + i) (by omega)
            rw [show s + i + 1 = s + (i + 1) from by omega] at this
            exact this
          · have hieq : i + 1 = t - s := by omega
            rw [hieq, Nat.mod_self]
            show 0 < m (g (s + i)) (g (s + 0))
            rw [Nat.add_zero, hgs, show s + i = t - 1 from by omega]
            exact hue
        · intro h2
          omega
      · -- extend the path by the fresh vertex u
        push_neg at honpath
        have htn' : t + 1 ≤ n := by
          have hcard : (Finset.image (fun i : ℕ => if i = t then u else g i)
              (Finset.range (t + 1))).card = t + 1 := by
            rw [Finset.card_image_of_injOn, Finset.card_range]
            intro i1 hi1 i2 hi2 hg
            rw [Finset.mem_coe, Finset.mem_range] at hi1 hi2
            replace hg : (if i1 = t then u else g i1) = (if i2 = t then u else g i2) := hg
            by_cases h1 : i1 = t <;> by_cases h2 : i2 = t
            · omega
            · rw [if_pos h1, if_neg h2] at hg
              exact absurd hg.symm (honpath i2 (by omega))
            · rw [if_neg h1, if_pos h2] at hg
              exact absurd hg (honpath i1 (by omega))
            · rw [if_neg h1, if_neg h2] at hg
              have := hinj i1 i2 (by omega) (by omega) hg
              omega
          have := Finset.card_le_univ (Finset.image (fun i : ℕ => if i = t then u else g i)
            (Finset.range (t + 1)))
          rw [hcard, Fintype.card_fin] at this
          exact this
        refine ih (t + 1) (fun i => if i = t then u else g i) (by omega) htn' (by omega)
          ?_ ?_ ?_
        · intro i1 i2 hi1 hi2 hg
          replace hg : (if i1 = t then u else g i1) = (if i2 = t then u else g i2) := hg
          by_cases h1 : i1 = t <;> by_cases h2 : i2 = t
          · omega
          · rw [if_pos h1, if_neg h2] at hg
            exact absurd hg.symm (honpath i2 (by omega))
          · rw [if_neg h1, if_pos h2] at hg
            exact absurd hg (honpath i1 (by omega))
          · rw [if_neg h1, if_neg h2] at hg
            exact hinj i1 i2 (by omega) (by omega) hg
        · intro i hi
          show 0 < m (if i = t then u else g i) (if i + 1 = t then u else g (i + 1))
          by_cases hit : i + 1 = t
          · rw [if_neg (by omega : ¬ i = t), if_pos hit]
            rw [show i = t - 1 from by omega]
            exact hue
          · rw [if_neg (by omega : ¬ i = t), if_neg hit]
            exact hpath i (by omega)
        · show 0 < mDeg m (if t + 1 - 1 = t then u else g (t + 1 - 1))
          rw [if_pos (by omega)]
          apply mDeg_pos_of_edge m u e
          rw [hsym]
          exact hue

lemma cycEdge_pos_mem (j : ℕ) (g : ℕ → Fin n) (u v : Fin n)
    (h : 0 < cycEdge j g u v) :
    (∃ i, i < j ∧ g i = u) ∧ (∃ i, i < j ∧ g i = v) := by
  unfold cycEdge at h
  rw [Finset.card_pos] at h
  obtain ⟨i, hi⟩ := h
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hir, hc⟩ := hi
  have hmod : (i + 1) % j < j := Nat.mod_lt _ (by omega)
  rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨⟨i, hir, ha⟩, ⟨(i + 1) % j, hmod, hb⟩⟩
  · exact ⟨⟨(i + 1) % j, hmod, hb⟩, ⟨i, hir, ha⟩⟩

/-- Every even multigraph decomposes into injective cycles. -/
lemma decompose (c : Fin n → Fin n → ℝ) (hcsym : ∀ u v, c u v = c v u) :
    ∀ (mass : ℕ) (m : Fin n → Fin n → ℕ), (∑ u, ∑ v, m u v) = mass →
    (∀ u v, m u v = m v u) → (∀ v, m v v = 0) → (∀ v, Even (mDeg m v)) →
    ∃ cycles : List (ℕ × (ℕ → Fin n)),
      (∀ u v, m u v = (cycles.map (fun cyc => cycEdge cyc.1 cyc.2 u v)).sum) ∧
      (∀ cyc ∈ cycles, 2 ≤ cyc.1 ∧
        (∀ i1 i2, i1 < cyc.1 → i2 < cyc.1 → cyc.2 i1 = cyc.2 i2 → i1 = i2)) ∧
      mCost c m = (cycles.map (fun cyc => walkCost c cyc.1 cyc.2)).sum := by
  intro mass
  induction mass using Nat.strong_induction_on with
  | _ mass ih =>
    intro m hmass hsym hdiag heven
    rcases Nat.eq_zero_or_pos mass with h0 | hpos
    · -- the empty decomposition
      refine ⟨[], ?_, ?_, ?_⟩
      · intro u v
        have hz : m u v = 0 := by
          subst h0
          by_contra hmz
          have h1 : 0 < ∑ v', m u v' :=
            lt_of_lt_of_le (Nat.pos_of_ne_zero hmz)
              (Finset.single_le_sum (f := fun v' => m u v') (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ v))
          have h2 : 0 < ∑ u', ∑ v', m u' v' :=
            lt_of_lt_of_le h1
              (Finset.single_le_sum (f := fun u' => ∑ v', m u' v')
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
          omega
        simpa using hz
      · intro cyc hcyc
        exact absurd hcyc (List.not_mem_nil)
      · have hz : ∀ u v, m u v = 0 := by
          intro u v
          subst h0
          by_contra hmz
          have h1 : 0 < ∑ v', m u v' :=
            lt_of_lt_of_le (Nat.pos_of_ne_zero hmz)
              (Finset.single_le_sum (f := fun v' => m u v') (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ v))
          have h2 : 0 < ∑ u', ∑ v', m u' v' :=
            lt_of_lt_of_le h1
              (Finset.single_le_sum (f := fun u' => ∑ v', m u' v')
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
          omega
        unfold mCost
        rw [Finset.sum_eq_zero (fun u (_ : u ∈ Finset.univ) => Finset.sum_eq_zero
          (fun v (_ : v ∈ Finset.univ) => by rw [hz u v]; push_cast; ring))]
        simp
    · -- extract one cycle and recurse
      have hex : ∃ u v, 0 < m u v := by
        by_contra hc
        push_neg at hc
        have : (∑ u, ∑ v, m u v) = 0 := by
          apply Finset.sum_eq_zero
          intro u _
          apply Finset.sum_eq_zero
          intro v _
          have := hc u v
          omega
        omega
      obtain ⟨u0, v0', hu0⟩ := hex
      obtain ⟨j, g, hj, hinj, hgpos, hg2⟩ := find_cycle m hsym hdiag heven u0
        (mDeg_pos_of_edge m u0 v0' hu0)
      have hle : ∀ u v, cycEdge j g u v ≤ m u v :=
        cycEdge_le m hsym j hj g hinj hgpos hg2
      set m' : Fin n → Fin n → ℕ := fun u v => m u v - cycEdge j g u v with hm'
      have hpoint : ∀ u v, m u v = m' u v + cycEdge j g u v := by
        intro u v
        have := hle u v
        show m u v = m u v - cycEdge j g u v + cycEdge j g u v
        omega
      have hsym' : ∀ u v, m' u v = m' v u := by
        intro u v
        show m u v - cycEdge j g u v = m v u - cycEdge j g v u
        rw [hsym u v, cycEdge_symm]
      have hdiag' : ∀ v, m' v v = 0 := by
        intro v
        show m v v - cycEdge j g v v = 0
        rw [hdiag v]
        omega
      have hdegsum : ∀ v, mDeg m v = mDeg m' v + mDeg (cycEdge j g) v := by
        intro v
        unfold mDeg
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        exact hpoint v u
      have heven' : ∀ v, Even (mDeg m' v) := by
        intro v
        have h1 := heven v
        have h2 := hdegsum v
        have h3 := cycEdge_deg j hj g hinj v
        rw [Nat.even_iff] at h1 ⊢
        by_cases hex : ∃ i, i < j ∧ g i = v
        · rw [if_pos hex] at h3
          omega
        · rw [if_neg hex] at h3
          omega
      have hmasslt : (∑ u, ∑ v, m' u v) < mass := by
        have hsplit : (∑ u, ∑ v, m u v)
            = (∑ u, ∑ v, m' u v) + (∑ u, ∑ v, cycEdge j g u v) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          exact hpoint u v
        have hcycpos : 0 < ∑ u, ∑ v, cycEdge j g u v := by
          have h0 : 0 < cycEdge j g (g 0) (g (1 % j)) := by
            unfold cycEdge
            rw [Finset.card_pos]
            exact ⟨0, by
              rw [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩⟩
          calc 0 < cycEdge j g (g 0) (g (1 % j)) := h0
            _ ≤ ∑ v, cycEdge j g (g 0) v :=
              Finset.single_le_sum (f := fun v => cycEdge j g (g 0) v)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
            _ ≤ ∑ u, ∑ v, cycEdge j g u v :=
              Finset.single_le_sum (f := fun u => ∑ v, cycEdge j g u v)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        omega
      obtain ⟨cycles', ha', hb', hc'⟩ := ih (∑ u, ∑ v, m' u v) (by omega) m' rfl
        hsym' hdiag' heven'
      refine ⟨(j, g) :: cycles', ?_, ?_, ?_⟩
      · intro u v
        rw [List.map_cons, List.sum_cons]
        rw [hpoint u v, ha' u v]
        ring
      · intro cyc hcyc
        rcases List.mem_cons.mp hcyc with rfl | htail
        · exact ⟨hj, hinj⟩
        · exact hb' cyc htail
      · rw [List.map_cons, List.sum_cons]
        have hcost : mCost c m = mCost c m' + mCost c (cycEdge j g) := by
          unfold mCost
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          rw [hpoint u v]
          push_cast
          ring
        rw [hcost, hc', cycEdge_cost c hcsym j hj g hinj]
        ring

/-- The support graph of a multigraph. -/
def mSupport (m : Fin n → Fin n → ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ 0 < m u v ∧ 0 < m v u
  symm := ⟨fun u v ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- Any cycle of the remaining list that is reachable from the current walk can
be replaced by one that actually shares a vertex with the walk. -/
lemma reach_share (m : Fin n → Fin n → ℕ) (R : List (ℕ × (ℕ → Fin n)))
    (L : ℕ) (W : ℕ → Fin n)
    (hii : ∀ u v, u ≠ v → 0 < m u v →
        ((∃ i, i < L ∧ W i = u) ∧ (∃ i, i < L ∧ W i = v)) ∨
        (∃ cyc ∈ R, (∃ i, i < cyc.1 ∧ cyc.2 i = u) ∧ (∃ i, i < cyc.1 ∧ cyc.2 i = v))) :
    ∀ (y z : Fin n), (mSupport m).Walk y z → (∃ i, i < L ∧ W i = y) →
      (∃ i, i < L ∧ W i = z) ∨
      ∃ cyc ∈ R, ∃ a b, a < L ∧ b < cyc.1 ∧ W a = cyc.2 b := by
  intro y z p
  induction p with
  | nil =>
    intro hy
    exact Or.inl hy
  | @cons y' b' z' hadj p' ihp =>
    intro hy
    obtain ⟨hne, hpos, _⟩ := hadj
    rcases hii y' b' hne hpos with ⟨hyW, hbW⟩ | ⟨cyc, hcyc, ⟨i1, hi1, hgi1⟩, _⟩
    · exact ihp hbW
    · obtain ⟨a, haL, haW⟩ := hy
      exact Or.inr ⟨cyc, hcyc, a, i1, haL, hi1, haW.trans hgi1.symm⟩

/-- Absorb all remaining cycles into a single closed walk of the same total cost. -/
lemma absorb (c : Fin n → Fin n → ℝ) (m : Fin n → Fin n → ℕ)
    (hconn : (mSupport m).Connected) :
    ∀ (len : ℕ) (R : List (ℕ × (ℕ → Fin n))), R.length ≤ len →
    ∀ (L : ℕ) (W : ℕ → Fin n), 0 < L →
    (∀ cyc ∈ R, 0 < cyc.1) →
    (∀ v, 0 < mDeg m v → (∃ i, i < L ∧ W i = v) ∨
        ∃ cyc ∈ R, ∃ i, i < cyc.1 ∧ cyc.2 i = v) →
    (∀ u v, u ≠ v → 0 < m u v →
        ((∃ i, i < L ∧ W i = u) ∧ (∃ i, i < L ∧ W i = v)) ∨
        (∃ cyc ∈ R, (∃ i, i < cyc.1 ∧ cyc.2 i = u) ∧ (∃ i, i < cyc.1 ∧ cyc.2 i = v))) →
    ∃ (L' : ℕ) (W' : ℕ → Fin n), 0 < L' ∧
      walkCost c L' W' = walkCost c L W
        + (R.map (fun cyc => walkCost c cyc.1 cyc.2)).sum ∧
      (∀ v, ((∃ i, i < L ∧ W i = v) ∨ 0 < mDeg m v) → ∃ i, i < L' ∧ W' i = v) := by
  classical
  intro len
  induction len with
  | zero =>
    intro R hRlen L W hL hRpos hi hii
    have hR : R = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hRlen)
    subst hR
    refine ⟨L, W, hL, by simp, ?_⟩
    intro v hv
    rcases hv with h | h
    · exact h
    · rcases hi v h with h' | ⟨cyc, hcyc, _⟩
      · exact h'
      · exact absurd hcyc (List.not_mem_nil)
  | succ len ihlen =>
    intro R hRlen L W hL hRpos hi hii
    rcases R with _ | ⟨r0, rest⟩
    · -- empty list: same as the base case
      refine ⟨L, W, hL, by simp, ?_⟩
      intro v hv
      rcases hv with h | h
      · exact h
      · rcases hi v h with h' | ⟨cyc, hcyc, _⟩
        · exact h'
        · exact absurd hcyc (List.not_mem_nil)
    · -- find a cycle sharing a vertex with the walk
      set R : List (ℕ × (ℕ → Fin n)) := r0 :: rest with hRdef
      have hr0R : r0 ∈ R := List.mem_cons_self
      have hr0pos : 0 < r0.1 := hRpos r0 hr0R
      have hreach := (hconn.preconnected (W 0) (r0.2 0)).some
      have hkey := reach_share m R L W hii (W 0) (r0.2 0) hreach ⟨0, hL, rfl⟩
      have hshare : ∃ r ∈ R, ∃ a b, a < L ∧ b < r.1 ∧ W a = r.2 b := by
        rcases hkey with ⟨i, hiL, hWi⟩ | h
        · exact ⟨r0, hr0R, i, 0, hiL, hr0pos, hWi⟩
        · exact h
      obtain ⟨r, hrR, a, b, haL, hbr, hWab⟩ := hshare
      have hrpos : 0 < r.1 := hRpos r hrR
      -- merge it into the walk
      have hmc := mergeWalk_cost c L r.1 a b hL hrpos haL hbr W r.2 hWab
      have hmm := mergeWalk_mem (n := n) L r.1 a b hL hrpos W r.2
      have hlen' : (R.erase r).length ≤ len := by
        rw [List.length_erase_of_mem hrR]
        have : 1 ≤ R.length := by
          rw [hRdef]
          simp
        omega
      have hRpos' : ∀ cyc ∈ R.erase r, 0 < cyc.1 :=
        fun cyc hcyc => hRpos cyc (List.mem_of_mem_erase hcyc)
      have hi' : ∀ v, 0 < mDeg m v →
          (∃ i, i < L + r.1 ∧ mergeWalk L r.1 a b W r.2 i = v) ∨
          ∃ cyc ∈ R.erase r, ∃ i, i < cyc.1 ∧ cyc.2 i = v := by
        intro v hv
        rcases hi v hv with hW | ⟨cyc, hcyc, i, hicyc, hgi⟩
        · exact Or.inl ((hmm v).mpr (Or.inl hW))
        · by_cases hceq : cyc = r
          · subst hceq
            exact Or.inl ((hmm v).mpr (Or.inr ⟨i, hicyc, hgi⟩))
          · exact Or.inr ⟨cyc, (List.mem_erase_of_ne hceq).mpr hcyc, i, hicyc, hgi⟩
      have hii' : ∀ u v, u ≠ v → 0 < m u v →
          ((∃ i, i < L + r.1 ∧ mergeWalk L r.1 a b W r.2 i = u) ∧
            (∃ i, i < L + r.1 ∧ mergeWalk L r.1 a b W r.2 i = v)) ∨
          (∃ cyc ∈ R.erase r, (∃ i, i < cyc.1 ∧ cyc.2 i = u) ∧
            (∃ i, i < cyc.1 ∧ cyc.2 i = v)) := by
        intro u v hne hpos
        rcases hii u v hne hpos with ⟨hu, hv⟩ | ⟨cyc, hcyc, hcu, hcv⟩
        · exact Or.inl ⟨(hmm u).mpr (Or.inl hu), (hmm v).mpr (Or.inl hv)⟩
        · by_cases hceq : cyc = r
          · subst hceq
            exact Or.inl ⟨(hmm u).mpr (Or.inr hcu), (hmm v).mpr (Or.inr hcv)⟩
          · exact Or.inr ⟨cyc, (List.mem_erase_of_ne hceq).mpr hcyc, hcu, hcv⟩
      obtain ⟨L', W', hL', hcost', hcov'⟩ := ihlen (R.erase r) hlen' (L + r.1)
        (mergeWalk L r.1 a b W r.2) (by omega) hRpos' hi' hii'
      refine ⟨L', W', hL', ?_, ?_⟩
      · rw [hcost', hmc]
        have hperm : List.Perm R (r :: R.erase r) := List.perm_cons_erase hrR
        have hsum := (hperm.map (fun cyc => walkCost c cyc.1 cyc.2)).sum_eq
        rw [hsum, List.map_cons, List.sum_cons]
        ring
      · intro v hv
        apply hcov'
        rcases hv with hW | hdeg
        · exact Or.inl ((hmm v).mpr (Or.inl hW))
        · exact Or.inr hdeg

/-- **Euler tour with shortcuts**: a connected even multigraph supports a
Hamiltonian tour of at most its total cost. -/
lemma euler_tour (c : Fin n → Fin n → ℝ) (hn : 3 ≤ n) (hc : IsMetricCost c)
    (m : Fin n → Fin n → ℕ) (hsym : ∀ u v, m u v = m v u) (hdiag : ∀ v, m v v = 0)
    (heven : ∀ v, Even (mDeg m v)) (hconn : (mSupport m).Connected) :
    ∃ π : Equiv.Perm (Fin n), tourCost c π ≤ mCost c m := by
  have hdegall : ∀ v, 0 < mDeg m v := by
    intro v
    haveI : Nontrivial (Fin n) :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
        intro h
        have := congrArg Fin.val h
        simp at this⟩
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hconn.preconnected v w
    cases p with
    | nil => exact absurd rfl (Ne.symm hw)
    | cons hadj p' => exact mDeg_pos_of_edge m _ _ hadj.2.1
  obtain ⟨cycles, ha, hb, hcost⟩ := decompose c hc.1 (∑ u, ∑ v, m u v) m rfl
    hsym hdiag heven
  rcases cycles with _ | ⟨r0, rest⟩
  · exfalso
    have h0 : mDeg m ⟨0, by omega⟩ = 0 := by
      unfold mDeg
      apply Finset.sum_eq_zero
      intro u _
      have := ha ⟨0, by omega⟩ u
      simpa using this
    have := hdegall ⟨0, by omega⟩
    omega
  · have hr0 := hb r0 List.mem_cons_self
    have hedge_mem : ∀ v u, 0 < m v u →
        (∃ i, i < r0.1 ∧ r0.2 i = v) ∧ (∃ i, i < r0.1 ∧ r0.2 i = u) ∨
        ∃ cyc ∈ rest, (∃ i, i < cyc.1 ∧ cyc.2 i = v) ∧ (∃ i, i < cyc.1 ∧ cyc.2 i = u) := by
      intro v u hvu
      have hsum := ha v u
      have hex : ∃ cyc ∈ (r0 :: rest), 0 < cycEdge cyc.1 cyc.2 v u := by
        by_contra hcon
        push_neg at hcon
        have hz : (((r0 :: rest)).map (fun cyc => cycEdge cyc.1 cyc.2 v u)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨cyc, hcyc, rfl⟩ := hx
          have := hcon cyc hcyc
          omega
        omega
      obtain ⟨cyc, hcyc, hpos⟩ := hex
      have hmem := cycEdge_pos_mem cyc.1 cyc.2 v u hpos
      rcases List.mem_cons.mp hcyc with heq | htail
      · subst heq
        exact Or.inl hmem
      · exact Or.inr ⟨cyc, htail, hmem⟩
    have hi : ∀ v, 0 < mDeg m v → (∃ i, i < r0.1 ∧ r0.2 i = v) ∨
        ∃ cyc ∈ rest, ∃ i, i < cyc.1 ∧ cyc.2 i = v := by
      intro v hv
      obtain ⟨u, hu⟩ := mDeg_pos_witness m v hv
      rcases hedge_mem v u hu with ⟨h1, _⟩ | ⟨cyc, htail, h1, _⟩
      · exact Or.inl h1
      · exact Or.inr ⟨cyc, htail, h1⟩
    have hii : ∀ u v, u ≠ v → 0 < m u v →
        ((∃ i, i < r0.1 ∧ r0.2 i = u) ∧ (∃ i, i < r0.1 ∧ r0.2 i = v)) ∨
        (∃ cyc ∈ rest, (∃ i, i < cyc.1 ∧ cyc.2 i = u) ∧ (∃ i, i < cyc.1 ∧ cyc.2 i = v)) := by
      intro u v _ huv
      exact hedge_mem u v huv
    obtain ⟨L', W', hL', hcost', hcov'⟩ := absorb c m hconn rest.length rest le_rfl
      r0.1 r0.2 (by omega) (fun cyc hcyc => by
        have := hb cyc (List.mem_cons_of_mem r0 hcyc)
        omega) hi hii
    have hcovers : ∀ v : Fin n, ∃ i, i < L' ∧ W' i = v :=
      fun v => hcov' v (Or.inr (hdegall v))
    obtain ⟨π, hπ⟩ := tour_of_walk c hn hc L' hL' W' hcovers
    refine ⟨π, ?_⟩
    rw [hcost, List.map_cons, List.sum_cons]
    calc tourCost c π ≤ walkCost c L' W' := hπ
      _ = _ := hcost'

lemma pairCost_mk' (c : Fin n → Fin n → ℝ) (u v : Fin n) :
    pairCost c s(u, v) = (c u v + c v u) / 2 := rfl

/-- The edge-set cost of a graph as half the full adjacency double sum, stated
with an abstract indicator to stay independent of decidability instances. -/
lemma graphCost_double_sum (c : Fin n → Fin n → ℝ) (hcsym : ∀ u v, c u v = c v u)
    (G : SimpleGraph (Fin n)) (χ : Fin n → Fin n → ℝ)
    (hχ1 : ∀ u v, G.Adj u v → χ u v = 1) (hχ0 : ∀ u v, ¬ G.Adj u v → χ u v = 0) :
    graphCost c G = (1 / 2) * ∑ u, ∑ v, χ u v * c u v := by
  classical
  have hstep1 : (∑ u, ∑ v, χ u v * c u v)
      = ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
          (fun p : Fin n × Fin n => G.Adj p.1 p.2), c p.1 p.2 := by
    rw [Finset.sum_filter, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : G.Adj p.1 p.2
    · rw [if_pos h, hχ1 _ _ h, one_mul]
    · rw [if_neg h, hχ0 _ _ h, zero_mul]
  have hsplit : ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => G.Adj p.1 p.2))
      = ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 < p.2))
        ∪ ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.2 < p.1)) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      have hne := G.ne_of_adj h
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨h, hgt⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 < p.2))
      ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    exact absurd (hp1.2.2.trans hp2.2.2) (lt_irrefl _)
  have hswap : (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.2 < p.1), c p.1 p.2)
      = ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 < p.2), c p.1 p.2 := by
    apply Finset.sum_nbij' (fun p : Fin n × Fin n => (p.2, p.1))
      (fun p : Fin n × Fin n => (p.2, p.1))
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, hp.2.1.symm, hp.2.2⟩
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, hp.2.1.symm, hp.2.2⟩
    · intro p _
      rfl
    · intro p _
      rfl
    · intro p _
      exact hcsym p.1 p.2
  have hedge : graphCost c G = ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 < p.2), c p.1 p.2 := by
    unfold graphCost
    symm
    apply Finset.sum_nbij (i := fun p : Fin n × Fin n => s(p.1, p.2))
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      exact Set.mem_toFinset.mpr hp.2.1
    · intro p hp q hq heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        have hlt1 := hp.2.2
        have hlt2 := hq.2.2
        rw [h1, h2] at hlt1
        exact absurd (hlt1.trans hlt2) (lt_irrefl _)
    · intro e
      induction e using Sym2.ind with
      | _ x y =>
        intro he
        have he2 : s(x, y) ∈ G.edgeSet.toFinset := he
        have he' : G.Adj x y := (Set.mem_toFinset (s := G.edgeSet)).mp he2
        have hne := G.ne_of_adj he'
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · refine ⟨(x, y), ?_, rfl⟩
          refine Finset.mem_coe.mpr ?_
          rw [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, he', hlt⟩
        · refine ⟨(y, x), ?_, Sym2.eq_swap⟩
          refine Finset.mem_coe.mpr ?_
          rw [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, he'.symm, hgt⟩
    · intro p _
      rw [pairCost_mk', hcsym p.2 p.1]
      ring
  rw [hstep1, hsplit, Finset.sum_union hdisj, hswap, hedge]
  ring

/-- **The Christofides glue**: a connected graph plus a pairing of exactly its
odd-degree vertices supports a tour of cost at most the graph cost plus the
matching cost. -/
theorem tour_of_parity_join_thm (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.Connected) (f : Fin n → Fin n) (hinv : ∀ v, f (f v) = v)
    (hodd : ∀ v, f v ≠ v ↔ Odd (G.degree v)) :
    ∃ π : Equiv.Perm (Fin n),
      tourCost c π ≤ graphCost c G + (1 / 2) * ∑ v, c v (f v) := by
  set m : Fin n → Fin n → ℕ := fun u v =>
    (if G.Adj u v then 1 else 0) + (if f u = v ∧ u ≠ v then 1 else 0) with hm
  have hpairiff : ∀ u v : Fin n, (f u = v ∧ u ≠ v) ↔ (f v = u ∧ v ≠ u) := by
    intro u v
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← h1]; exact hinv u, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← h1]; exact hinv v, h2.symm⟩
  have hsym : ∀ u v, m u v = m v u := by
    intro u v
    show (if G.Adj u v then 1 else 0) + (if f u = v ∧ u ≠ v then 1 else 0)
      = (if G.Adj v u then 1 else 0) + (if f v = u ∧ v ≠ u then 1 else 0)
    congr 1
    · rw [if_congr (G.adj_comm u v) rfl rfl]
    · rw [if_congr (hpairiff u v) rfl rfl]
  have hdiag : ∀ v, m v v = 0 := by
    intro v
    show (if G.Adj v v then 1 else 0) + (if f v = v ∧ v ≠ v then 1 else 0) = 0
    rw [if_neg (G.irrefl), if_neg (fun h => h.2 rfl)]
  have hdegsplit : ∀ v, mDeg m v = G.degree v + (if f v ≠ v then 1 else 0) := by
    intro v
    unfold mDeg
    show (∑ u, ((if G.Adj v u then 1 else 0) + (if f v = u ∧ v ≠ u then 1 else 0))) = _
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.card_filter]
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    · by_cases hfv : f v = v
      · rw [if_neg (by simpa using hfv)]
        apply Finset.sum_eq_zero
        intro u _
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact h2 (hfv.symm.trans h1)
      · rw [if_pos hfv]
        have hcong : ∀ u : Fin n, (f v = u ∧ v ≠ u) ↔ u = f v := by
          intro u
          constructor
          · rintro ⟨h1, _⟩
            exact h1.symm
          · rintro rfl
            exact ⟨rfl, fun heq => hfv heq.symm⟩
        rw [Finset.sum_congr rfl (fun u _ => if_congr (hcong u) rfl rfl)]
        rw [Finset.sum_ite_eq' Finset.univ (f v) (fun _ => (1 : ℕ))]
        rw [if_pos (Finset.mem_univ _)]
  have heven : ∀ v, Even (mDeg m v) := by
    intro v
    rw [hdegsplit v]
    by_cases hfv : f v ≠ v
    · rw [if_pos hfv]
      obtain ⟨k, hk⟩ := (hodd v).mp hfv
      exact ⟨k + 1, by omega⟩
    · rw [if_neg hfv]
      have hnodd : ¬ Odd (G.degree v) := fun ho => hfv ((hodd v).mpr ho)
      rw [Nat.not_odd_iff_even] at hnodd
      simpa using hnodd
  have hle : G ≤ mSupport m := by
    intro u v hadj
    refine ⟨G.ne_of_adj hadj, ?_, ?_⟩
    · show 0 < (if G.Adj u v then 1 else 0) + (if f u = v ∧ u ≠ v then 1 else 0)
      rw [if_pos hadj]
      omega
    · show 0 < (if G.Adj v u then 1 else 0) + (if f v = u ∧ v ≠ u then 1 else 0)
      rw [if_pos hadj.symm]
      omega
  have hconn : (mSupport m).Connected := SimpleGraph.Connected.mono hle hG
  have hcost : mCost c m = graphCost c G + (1 / 2) * ∑ v, c v (f v) := by
    unfold mCost
    have hsplit : ∀ u v : Fin n, ((m u v : ℝ)) * c u v
        = (if G.Adj u v then (1 : ℝ) else 0) * c u v
          + (if f u = v ∧ u ≠ v then (1 : ℝ) else 0) * c u v := by
      intro u v
      show (((if G.Adj u v then (1 : ℕ) else 0)
          + (if f u = v ∧ u ≠ v then (1 : ℕ) else 0) : ℕ) : ℝ) * c u v = _
      by_cases h1 : G.Adj u v <;> by_cases h2 : f u = v ∧ u ≠ v
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
        push_cast
        ring
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        push_cast
        ring
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        push_cast
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        push_cast
        ring
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => Finset.sum_congr rfl
      (fun v (_ : v ∈ Finset.univ) => hsplit u v))]
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => Finset.sum_add_distrib)]
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    · exact (graphCost_double_sum c hc.1 G (fun u v => if G.Adj u v then 1 else 0)
        (fun u v h => if_pos h) (fun u v h => if_neg h)).symm
    · congr 1
      apply Finset.sum_congr rfl
      intro u _
      by_cases hfu : f u = u
      · rw [Finset.sum_eq_zero, hfu, hc.2.1 u]
        intro v _
        rw [if_neg]
        · ring
        · rintro ⟨h1, h2⟩
          exact h2 ((hfu.symm.trans h1).symm ▸ rfl)
      · have hcong : ∀ v : Fin n, (f u = v ∧ u ≠ v) ↔ v = f u := by
          intro v
          constructor
          · rintro ⟨h1, _⟩
            exact h1.symm
          · rintro rfl
            exact ⟨rfl, fun heq => hfu heq.symm⟩
        have hpt : ∀ v : Fin n, (if f u = v ∧ u ≠ v then (1 : ℝ) else 0) * c u v
            = (if v = f u then c u v else 0) := by
          intro v
          by_cases hv : v = f u
          · rw [if_pos ((hcong v).mpr hv), if_pos hv, one_mul]
          · rw [if_neg (fun h => hv ((hcong v).mp h)), if_neg hv, zero_mul]
        rw [Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hpt v)]
        rw [Finset.sum_ite_eq' Finset.univ (f u) (fun v => c u v)]
        rw [if_pos (Finset.mem_univ _)]
  obtain ⟨π, hπ⟩ := euler_tour c hn hc m hsym hdiag heven hconn
  refine ⟨π, ?_⟩
  rw [← hcost]
  exact hπ

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.Connected) (f : Fin n → Fin n) (hinv : ∀ v, f (f v) = v)
    (hodd : ∀ v, f v ≠ v ↔ Odd (G.degree v)) :
    ∃ π : Equiv.Perm (Fin n),
      tourCost c π ≤ graphCost c G + (1 / 2) * ∑ v, c v (f v) :=
  MetricTSP.tour_of_parity_join_thm n hn c hc G hG f hinv hodd
