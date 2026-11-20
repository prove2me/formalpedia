-- Prove2me | solution 1 for ManipPotential.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T20:24:12.861169+00:00
-- url     : https://prove2.me/submissions/3bed4a09-c365-4d25-bfc5-54e0d63d836d

import Mathlib
import Definitions.Def_ManipPotential_Anonymous
import Definitions.Def_ManipPotential_Onto
import Definitions.Def_ManipPotential_manipPotentialAt
import Definitions.Def_ManipPotential_GAxioms

open ManipPotential Filter

namespace Lemma62Aux

variable {m : ℕ}

/-- The integer profile `j! • P` (coordinates rounded down; exact for large `j`). -/
noncomputable def ip (j : ℕ) (P : Ranking m → ℚ) : Multiset (Ranking m) :=
  ∑ r, Multiset.replicate ⌊(j.factorial : ℚ) * P r⌋₊ r

lemma fact_mul_nat (q : ℚ) (hq : 0 ≤ q) :
    ∀ᶠ j : ℕ in atTop, ∃ N : ℕ, (j.factorial : ℚ) * q = N := by
  filter_upwards [Filter.eventually_ge_atTop q.den] with j hj
  obtain ⟨k, hk⟩ := Nat.dvd_factorial q.den_pos hj
  have hnum : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  refine ⟨k * q.num.toNat, ?_⟩
  have hq' : (q.den : ℚ) * q = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
  have hcast : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  rw [hk]
  push_cast
  rw [hcast, ← hq']
  ring

lemma ip_zero (j : ℕ) : ip j (0 : Ranking m → ℚ) = 0 := by
  simp [ip]

lemma ip_add (j : ℕ) (P : Ranking m → ℚ) (r : Ranking m) (a : ℚ)
    (hP : ∀ r', ∃ N : ℕ, (j.factorial : ℚ) * P r' = N) (A : ℕ) (hA : (j.factorial : ℚ) * a = A) :
    ip j (P + a • unitVec r) = ip j P + Multiset.replicate A r := by
  classical
  have hfl : ∀ r', ⌊(j.factorial : ℚ) * (P + a • (unitVec r : Ranking m → ℚ)) r'⌋₊ =
      ⌊(j.factorial : ℚ) * P r'⌋₊ + if r' = r then A else 0 := by
    intro r'
    obtain ⟨N, hN⟩ := hP r'
    have : (j.factorial : ℚ) * (P + a • (unitVec r : Ranking m → ℚ)) r' =
        ((N + if r' = r then A else 0 : ℕ) : ℚ) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec, Pi.single_apply]
      split_ifs with h
      · push_cast; rw [mul_add, hN, mul_one, hA]
      · push_cast; rw [mul_zero, add_zero, hN, add_zero]
    rw [this, hN, Nat.floor_natCast, Nat.floor_natCast]
  unfold ip
  simp_rw [hfl, Multiset.replicate_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ r) h

end Lemma62Aux

open Lemma62Aux in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (f : List (Ranking m) → Fin m)
    (hA : Anonymous f) (hO : Onto f) (K : ℕ) (hK : ∀ n : ℕ, manipPotentialAt f n ≤ K) :
    ∃ g : (Ranking m → ℚ) → Fin m, GAxioms K g := by
  classical
  -- Step 1: `k`-augmentation strategyproofness for every `k ≥ K`.
  have hKASP : ∀ n k', K ≤ k' → IsKASPAt f n k' := by
    intro n k' hk'
    have h := hK n
    unfold manipPotentialAt at h
    have hlt : sInf {x : ℕ∞ | ∃ k : ℕ, x = k ∧ ∀ k' : ℕ, k ≤ k' → IsKASPAt f n k'} <
        ((K + 1 : ℕ) : ℕ∞) :=
      lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self K)
    obtain ⟨x, ⟨k, rfl, hk⟩, hxlt⟩ := sInf_lt_iff.mp hlt
    have : k < K + 1 := by exact_mod_cast hxlt
    exact hk k' (by omega)
  -- Step 2: profiles as multisets.
  let F : Multiset (Ranking m) → Fin m := fun M => f M.toList
  have hAF : ∀ L : List (Ranking m), f L = F (L : Multiset (Ranking m)) := by
    intro L
    apply hA
    have : (((L : Multiset (Ranking m)).toList : List (Ranking m)) : Multiset (Ranking m)) =
        (L : Multiset (Ranking m)) := Multiset.coe_toList _
    exact (Multiset.coe_eq_coe.mp this).symm
  have htop : ∀ (r : Ranking m) (x : Fin m), Ranking.WeaklyPrefers r x (Ranking.top r) →
      x = Ranking.top r := by
    intro r x h
    unfold Ranking.WeaklyPrefers Ranking.top at h
    rw [Equiv.apply_symm_apply] at h
    have h0 : r x = 0 := le_antisymm h (Fin.zero_le _)
    unfold Ranking.top
    rw [← h0, Equiv.symm_apply_apply]
  -- (6)
  have h6 : ∀ (M : Multiset (Ranking m)) (r s : Ranking m) (t : ℕ), K + 1 ≤ t →
      Ranking.WeaklyPrefers r (F (M + Multiset.replicate t r)) (F (M + {s})) := by
    intro M r s t ht
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    have hk := hKASP (M.toList ++ [r]).length u (by omega)
    have hi : M.toList.length < (M.toList ++ [r]).length := by simp
    have := hk (M.toList ++ [r]) rfl ⟨M.toList.length, hi⟩ s
    have hget : (M.toList ++ [r]).get ⟨M.toList.length, hi⟩ = r := by simp
    rw [hget] at this
    have hset : (M.toList ++ [r]).set M.toList.length s = M.toList ++ [s] := by simp
    simp only [Fin.val_mk] at this
    rw [hset, hAF, hAF] at this
    have e1 : ((M.toList ++ [r] ++ List.replicate u r : List (Ranking m)) : Multiset (Ranking m)) =
        M + Multiset.replicate (u + 1) r := by
      rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_singleton,
        Multiset.coe_replicate, add_assoc, Multiset.singleton_add, ← Multiset.replicate_succ]
    have e2 : ((M.toList ++ [s] : List (Ranking m)) : Multiset (Ranking m)) = M + {s} := by
      rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_singleton]
    rwa [e1, e2] at this
  -- (7)
  have h7 : ∀ (r s : Ranking m) (b : ℕ), 1 ≤ b → ∀ (M : Multiset (Ranking m)) (a : ℕ),
      (K + 1) * b ≤ a →
      Ranking.WeaklyPrefers r (F (M + Multiset.replicate a r)) (F (M + Multiset.replicate b s)) := by
    intro r s b hb
    induction b, hb using Nat.le_induction with
    | base =>
      intro M a ha
      have := h6 M r s a (by simpa using ha)
      simpa [Multiset.replicate_one] using this
    | succ b hb ih =>
      intro M a ha
      have hab : (K + 1) * b ≤ a - (K + 1) := by
        have : (K + 1) * b + (K + 1) ≤ a := by rw [← Nat.mul_succ]; exact ha
        exact Nat.le_sub_of_add_le this
      have step1 := h6 (M + Multiset.replicate b s) r s (K + 1) le_rfl
      have step2 := ih (M + Multiset.replicate (K + 1) r) (a - (K + 1)) hab
      have hle : K + 1 ≤ a := le_trans (Nat.le_mul_of_pos_right _ (by omega)) ha
      have e1 : M + Multiset.replicate (K + 1) r + Multiset.replicate (a - (K + 1)) r =
          M + Multiset.replicate a r := by
        rw [add_assoc, ← Multiset.replicate_add]
        congr 2
        omega
      have e2 : M + Multiset.replicate (K + 1) r + Multiset.replicate b s =
          M + Multiset.replicate b s + Multiset.replicate (K + 1) r := by
        rw [add_assoc, add_assoc, add_comm (Multiset.replicate (K + 1) r)]
      have e3 : M + Multiset.replicate b s + {s} = M + Multiset.replicate (b + 1) s := by
        rw [add_assoc, Multiset.replicate_add, Multiset.replicate_one]
      rw [e1, e2] at step2
      rw [e3] at step1
      unfold Ranking.WeaklyPrefers at step1 step2 ⊢
      exact le_trans step2 step1
  -- Unanimity threshold
  have hthr : ∀ (r : Ranking m) (k : ℕ) (M : Multiset (Ranking m)), M ≠ 0 →
      Multiset.card (M.filter (· ≠ r)) = k → F M = Ranking.top r →
      ∃ N0, ∀ N, N0 ≤ N → F (Multiset.replicate N r) = Ranking.top r := by
    intro r k
    induction k with
    | zero =>
      intro M hM hk hF
      have hall : ∀ x ∈ M, x = r := by
        intro x hx
        by_contra hne
        have hmem : x ∈ M.filter (· ≠ r) := Multiset.mem_filter.mpr ⟨hx, hne⟩
        rw [Multiset.card_eq_zero.mp hk] at hmem
        simp at hmem
      have hMrep : M = Multiset.replicate (Multiset.card M) r :=
        Multiset.eq_replicate.mpr ⟨rfl, hall⟩
      have hj : 1 ≤ Multiset.card M := Multiset.card_pos.mpr hM
      refine ⟨Multiset.card M - 1 + (K + 1), fun N hN => ?_⟩
      have := h6 (Multiset.replicate (Multiset.card M - 1) r) r r (N - (Multiset.card M - 1))
        (by omega)
      have e1 : Multiset.replicate (Multiset.card M - 1) r +
          Multiset.replicate (N - (Multiset.card M - 1)) r = Multiset.replicate N r := by
        rw [← Multiset.replicate_add]; congr 1; omega
      have e2 : Multiset.replicate (Multiset.card M - 1) r + {r} = M := by
        conv_rhs => rw [hMrep]
        rw [← Multiset.replicate_one, ← Multiset.replicate_add]
        congr 1
        omega
      rw [e1, e2, hF] at this
      exact htop r _ this
    | succ k ih =>
      intro M hM hk hF
      obtain ⟨s, hsM, hsr⟩ : ∃ s ∈ M, s ≠ r := by
        by_contra h
        push Not at h
        have : M.filter (· ≠ r) = 0 :=
          Multiset.filter_eq_nil.mpr (fun x hx => not_not.mpr (h x hx))
        rw [this] at hk
        simp at hk
      obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hsM
      have step := h6 M' r s (K + 1) le_rfl
      have e : M' + {s} = s ::ₘ M' := by rw [add_comm, Multiset.singleton_add]
      rw [e, hF] at step
      have hF' := htop r _ step
      apply ih (M' + Multiset.replicate (K + 1) r) (by simp) _ hF'
      rw [Multiset.filter_cons_of_pos (p := fun x => x ≠ r) M' hsr, Multiset.card_cons] at hk
      rw [Multiset.filter_add]
      have : (Multiset.replicate (K + 1) r).filter (· ≠ r) = 0 :=
        Multiset.filter_eq_nil.mpr (fun x hx => by
          rw [Multiset.eq_of_mem_replicate hx]; simp)
      rw [this, add_zero]
      omega
  have hunan : ∀ r : Ranking m, ∃ N0, ∀ N, N0 ≤ N →
      F (Multiset.replicate N r) = Ranking.top r := by
    intro r
    obtain ⟨L, hL, hfL⟩ := hO (Ranking.top r)
    have hM : (L : Multiset (Ranking m)) ≠ 0 := by
      intro h; apply hL; simpa using h
    exact hthr r _ _ hM rfl (by rw [← hAF]; exact hfL)
  -- Step 3: the limit rule on rational profiles.
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hUev : ∀ p : ℕ → Prop, (∀ᶠ j in atTop, p j) → ∀ᶠ j in (U : Filter ℕ), p j := by
    intro p hp
    rw [← Nat.cofinite_eq_atTop] at hp
    exact Filter.hyperfilter_le_cofinite hp
  have hex : ∀ P : Ranking m → ℚ, ∃ c : Fin m, ∀ᶠ j in (U : Filter ℕ), F (ip j P) = c := by
    intro P
    obtain ⟨c, hc⟩ := Ultrafilter.eq_pure_of_finite (U.map (fun j => F (ip j P)))
    refine ⟨c, ?_⟩
    have hmem : ({c} : Set (Fin m)) ∈ U.map (fun j => F (ip j P)) := by
      rw [hc]; exact Ultrafilter.mem_pure.mpr rfl
    exact Ultrafilter.mem_map.mp hmem
  choose g hg using hex
  have hBMP : BoundedMP K g := by
    intro P hP r s a b ha hb hab
    have e1 : ∀ᶠ j : ℕ in atTop, ∀ r', ∃ N : ℕ, (j.factorial : ℚ) * P r' = N :=
      Filter.eventually_all.mpr (fun r' => fact_mul_nat _ (hP r'))
    have e2 := fact_mul_nat a ha.le
    have e3 := fact_mul_nat b hb.le
    have hev : ∀ᶠ j in (U : Filter ℕ), Ranking.WeaklyPrefers r (F (ip j (P + a • unitVec r)))
        (F (ip j (P + b • unitVec s))) := by
      apply hUev
      filter_upwards [e1, e2, e3] with j h1 h2 h3
      obtain ⟨A, hA'⟩ := h2
      obtain ⟨B, hB'⟩ := h3
      rw [ip_add j P r a h1 A hA', ip_add j P s b h1 B hB']
      have hfpos : (0 : ℚ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
      apply h7 r s B _ _ A _
      · have : (0 : ℚ) < B := by rw [← hB']; positivity
        exact_mod_cast this
      · have : ((K + 1 : ℕ) : ℚ) * B ≤ A := by
          rw [← hA', ← hB']
          push_cast
          nlinarith
        exact_mod_cast this
    obtain ⟨j, hj1, hj2, hj3⟩ :=
      ((hg (P + a • unitVec r)).and ((hg (P + b • unitVec s)).and hev)).exists
    rw [← hj1, ← hj2]
    exact hj3
  have hFaith : Faithful g := by
    intro r a ha
    obtain ⟨N0, hN0⟩ := hunan r
    have e2 := fact_mul_nat a ha.le
    have e4 : ∀ᶠ j : ℕ in atTop, (N0 : ℚ) ≤ (j.factorial : ℚ) * a := by
      filter_upwards [Filter.eventually_ge_atTop ⌈(N0 : ℚ) / a⌉₊] with j hj
      have h1 : ((N0 : ℚ) / a) ≤ j := le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
      have h2 : (j : ℚ) ≤ j.factorial := by exact_mod_cast Nat.self_le_factorial j
      rw [div_le_iff₀ ha] at h1
      nlinarith
    have hev : ∀ᶠ j in (U : Filter ℕ), F (ip j (a • unitVec r)) = Ranking.top r := by
      apply hUev
      filter_upwards [e2, e4] with j h2 h4
      obtain ⟨A, hA'⟩ := h2
      have h0 : ∀ r', ∃ N : ℕ, (j.factorial : ℚ) * (0 : Ranking m → ℚ) r' = N :=
        fun r' => ⟨0, by simp⟩
      have := ip_add j (0 : Ranking m → ℚ) r a h0 A hA'
      rw [zero_add, ip_zero, zero_add] at this
      rw [this]
      apply hN0
      have : (N0 : ℚ) ≤ A := by rw [← hA']; exact h4
      exact_mod_cast this
    obtain ⟨j, hj1, hj2⟩ := ((hg (a • unitVec r)).and hev).exists
    rw [← hj1]
    exact hj2
  have hCP : CondParticipation g := by
    intro P hP r a ha hPr
    set b : ℚ := min (P r) (a / (K + 1)) with hbdef
    have hK1 : (0 : ℚ) < K + 1 := by positivity
    have hb : 0 < b := lt_min hPr (div_pos ha hK1)
    have hbP : b ≤ P r := min_le_left _ _
    have hba : b ≤ a / (K + 1) := min_le_right _ _
    have hP' : 0 ≤ P - b • unitVec r := by
      intro r'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVec, Pi.single_apply, Pi.zero_apply]
      split_ifs with h
      · subst h; linarith
      · have := hP r'; simp only [Pi.zero_apply] at this; linarith
    have hab : ((K : ℚ) + 1) * b ≤ a + b := by
      rw [le_div_iff₀ hK1] at hba
      nlinarith
    have := hBMP (P - b • unitVec r) hP' r r (a + b) b (by linarith) hb hab
    have e1 : P - b • unitVec r + (a + b) • unitVec r = P + a • unitVec r := by
      funext r'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : P - b • unitVec r + b • unitVec r = P := by
      funext r'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [e1, e2] at this
  exact ⟨g, hFaith, hBMP, hCP⟩
