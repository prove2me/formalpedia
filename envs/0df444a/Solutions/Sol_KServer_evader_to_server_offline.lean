-- Prove2me | solution 1 for KServer.evader_to_server_offline
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:53:29.281725+00:00
-- url     : https://prove2.me/submissions/6554ba86-4bbc-42b0-91da-35e1504ac788

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_encoding
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_lipschitz
import Theorems.Thm_KServer_offlineCost_le_workFn

open KServer

/-- Serving a stretch of requests all covered by the endpoint is free. -/
private theorem workFn_covered_list (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (L L₂ : List M) (X : Config k M)
    (hX : ∀ r ∈ L₂, ∃ i, X i = r) :
    workFn C₀ (L ++ L₂) X = workFn C₀ L X := by
  induction L₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton L₂ r ih =>
    have h1 : workFn C₀ ((L ++ L₂) ++ [r]) X = workFn C₀ (L ++ L₂) X :=
      workFn_covered k hk M C₀ (L ++ L₂) r X (hX r (by simp))
    rw [show L ++ (L₂ ++ [r]) = (L ++ L₂) ++ [r] from (List.append_assoc L L₂ [r]).symm, h1]
    exact ih fun r' hr' => hX r' (by simp [hr'])

/-- **The offline direction of the k-server/evader reduction** on `k + 1` points:
the optimal server cost of the encoded sequence is at most the optimal evader cost,
because the servers can shadow the complement of the evader. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (hcard : Fintype.card M = k + 1) (R : ℕ)
    (C₀ : Config k M) (hinj : Function.Injective C₀)
    (x₀ : M) (hx₀ : x₀ ∉ Set.range C₀)
    (σ : List (Set M)) (hσ : ∀ S ∈ σ, S.Nonempty) :
    offlineCost C₀ (encSeq M R σ) ≤ evaderOfflineCost x₀ σ := by
  classical
  -- the evader's offline cost set is nonempty (greedy feasible path)
  have hne : {c : ℝ | ∃ P : ℕ → M, EvaderServes x₀ σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}.Nonempty := by
    have hQ : ∀ j : ℕ, ∃ y : M, ∀ hj : j < σ.length,
        (σ.get ⟨j, hj⟩).Nonempty → y ∈ σ.get ⟨j, hj⟩ := by
      intro j
      by_cases hj : j < σ.length
      · by_cases hne' : (σ.get ⟨j, hj⟩).Nonempty
        · exact ⟨hne'.some, fun _ _ => hne'.some_mem⟩
        · exact ⟨x₀, fun _ hne'' => absurd hne'' hne'⟩
      · exact ⟨x₀, fun hj' _ => absurd hj' hj⟩
    choose Q hQspec using hQ
    refine ⟨_, fun j => match j with | 0 => x₀ | (m + 1) => Q m, ⟨rfl, ?_⟩, rfl⟩
    intro j hjne
    exact hQspec (j : ℕ) j.2 hjne
  refine le_csInf hne ?_
  rintro c ⟨P, hP, rfl⟩
  have hP0 : P 0 = x₀ := hP.1
  -- the complement schedule: `D j` covers everything except `P j`
  set D : ℕ → Config k M := fun j =>
    Nat.rec C₀ (fun j prev =>
      if h : ∃ i, prev i = P (j + 1) then Function.update prev h.choose (P j) else prev) j
    with hDdef
  have hD0 : D 0 = C₀ := rfl
  have hDsucc : ∀ j : ℕ, D (j + 1)
      = if h : ∃ i, D j i = P (j + 1) then Function.update (D j) h.choose (P j)
        else D j := fun j => rfl
  -- invariant: `D j` is injective and covers exactly the complement of `P j`
  have hinv : ∀ j : ℕ, Function.Injective (D j)
      ∧ ∀ y : M, (∃ i, D j i = y) ↔ y ≠ P j := by
    intro j
    induction j with
    | zero =>
      refine ⟨hinj, fun y => ⟨?_, ?_⟩⟩
      · rintro ⟨i, hi⟩ hy
        rw [hP0] at hy
        exact hx₀ ⟨i, hi.trans hy⟩
      · intro hy
        by_contra hc
        have hcardim : (Finset.univ.image C₀).card = k := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        have hcompl : ((Finset.univ.image C₀)ᶜ : Finset M).card = 1 := by
          rw [Finset.card_compl, hcardim, hcard]; omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcompl
        have hy' : y ∈ (Finset.univ.image C₀)ᶜ := by
          rw [Finset.mem_compl, Finset.mem_image]
          rintro ⟨i, -, hi⟩
          exact hc ⟨i, hi⟩
        have hx' : x₀ ∈ (Finset.univ.image C₀)ᶜ := by
          rw [Finset.mem_compl, Finset.mem_image]
          rintro ⟨i, -, hi⟩
          exact hx₀ ⟨i, hi⟩
        rw [ha, Finset.mem_singleton] at hy' hx'
        rw [hP0] at hy
        exact hy (hy'.trans hx'.symm)
    | succ j ih =>
      obtain ⟨hinj', hrange⟩ := ih
      rw [hDsucc j]
      by_cases h : ∃ i, D j i = P (j + 1)
      · rw [dif_pos h]
        have hival : D j h.choose = P (j + 1) := h.choose_spec
        have hPj : P j ≠ P (j + 1) := by
          intro hc
          exact (hrange (P (j + 1))).mp h hc.symm
        have hPjnot : ¬∃ i, D j i = P j := by
          intro hc
          exact (hrange (P j)).mp hc rfl
        constructor
        · intro x y hxy
          by_cases hx : x = h.choose <;> by_cases hy : y = h.choose
          · rw [hx, hy]
          · exfalso
            rw [hx, Function.update_self, Function.update_of_ne hy] at hxy
            exact hPjnot ⟨y, hxy.symm⟩
          · exfalso
            rw [hy, Function.update_self, Function.update_of_ne hx] at hxy
            exact hPjnot ⟨x, hxy⟩
          · rw [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
            exact hinj' hxy
        · intro y
          constructor
          · rintro ⟨i, hi⟩ hy
            by_cases hii : i = h.choose
            · rw [hii, Function.update_self] at hi
              rw [← hi] at hy
              exact hPj hy
            · rw [Function.update_of_ne hii] at hi
              rw [hy] at hi
              exact hii (hinj' (hi.trans hival.symm))
          · intro hy
            by_cases hyPj : y = P j
            · exact ⟨h.choose, by rw [Function.update_self, hyPj]⟩
            · obtain ⟨i, hi⟩ := (hrange y).mpr hyPj
              have hii : i ≠ h.choose := by
                intro hc
                rw [hc, hival] at hi
                exact hy hi.symm
              exact ⟨i, by rw [Function.update_of_ne hii]; exact hi⟩
      · rw [dif_neg h]
        have hPeq : P (j + 1) = P j := by
          by_contra hc
          exact h ((hrange (P (j + 1))).mpr hc)
        refine ⟨hinj', fun y => ?_⟩
        rw [hPeq]
        exact hrange y
  -- one step of the complement schedule costs at most the evader's step
  have hmove : ∀ j : ℕ, moveCost (D j) (D (j + 1)) ≤ dist (P j) (P (j + 1)) := by
    intro j
    rw [hDsucc j]
    by_cases h : ∃ i, D j i = P (j + 1)
    · rw [dif_pos h]
      have hival : D j h.choose = P (j + 1) := h.choose_spec
      unfold moveCost
      rw [Finset.sum_eq_single h.choose
        (fun i _ hii => by rw [Function.update_of_ne hii, dist_self])
        (fun hn => absurd (Finset.mem_univ h.choose) hn)]
      rw [Function.update_self, hival, dist_comm]
    · rw [dif_neg h]
      have hz : moveCost (D j) (D j) = 0 := by unfold moveCost; simp
      rw [hz]
      exact dist_nonneg
  -- main induction: the work function ending at `D n` is dominated
  have main : ∀ τ : List (Set M), (∀ S ∈ τ, S.Nonempty) →
      (∀ (j : ℕ) (hj : j < τ.length),
        (τ.get ⟨j, hj⟩).Nonempty → P (j + 1) ∈ τ.get ⟨j, hj⟩) →
      workFn C₀ (encSeq M R τ) (D τ.length)
        ≤ ∑ j ∈ Finset.range τ.length, dist (P j) (P (j + 1)) := by
    intro τ
    induction τ using List.reverseRecOn with
    | nil =>
      intro _ _
      show workFn C₀ (encSeq M R []) (D 0)
        ≤ ∑ j ∈ Finset.range (0 : ℕ), dist (P j) (P (j + 1))
      have h1 : workFn C₀ (encSeq M R []) (D 0) = workFn C₀ [] C₀ := rfl
      rw [h1, workFn_nil k hk M C₀ C₀]
      have hz : moveCost C₀ C₀ = 0 := by unfold moveCost; simp
      rw [hz]
      simp
    | append_singleton τ S ih =>
      intro hτne hfeas
      set n := τ.length with hn
      have hlen : (τ ++ [S]).length = n + 1 := by simp [hn]
      have hSlast : (τ ++ [S]).get ⟨n, by rw [hlen]; omega⟩ = S := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (by omega)]
        simp [hn]
      have hSne : S.Nonempty := hτne S (by simp)
      have hPin : P (n + 1) ∈ S := by
        have := hfeas n (by rw [hlen]; omega)
        rw [hSlast] at this
        exact this hSne
      have henc : encSeq M R (τ ++ [S])
          = encSeq M R τ ++ (List.replicate R (encBlock M S)).flatten := by
        rw [encSeq_append, encSeq_singleton]
      have hcov : ∀ r ∈ (List.replicate R (encBlock M S)).flatten, ∃ i, D (n + 1) i = r := by
        intro r hr
        obtain ⟨l', hl', hrl'⟩ := List.mem_flatten.mp hr
        have : l' = encBlock M S := (List.eq_of_mem_replicate hl')
        rw [this] at hrl'
        have hrS : r ∉ S := (mem_encBlock S r).mp hrl'
        refine ((hinv (n + 1)).2 r).mpr ?_
        intro hc
        rw [hc] at hrS
        exact hrS hPin
      rw [henc, hlen]
      rw [workFn_covered_list k hk M C₀ (encSeq M R τ)
        ((List.replicate R (encBlock M S)).flatten) (D (n + 1)) hcov]
      have hlip := workFn_lipschitz k hk M C₀ (encSeq M R τ) (D (n + 1)) (D n)
      have hih := ih (fun S' hS' => hτne S' (by simp [hS']))
        (fun j hj hne' => by
          have hj' : j < (τ ++ [S]).length := by rw [hlen]; omega
          have hget : (τ ++ [S]).get ⟨j, hj'⟩ = τ.get ⟨j, hj⟩ := by
            simp only [List.get_eq_getElem]
            rw [List.getElem_append_left hj]
          have := hfeas j hj'
          rw [hget] at this
          exact this hne')
      have hm := hmove n
      rw [Finset.sum_range_succ]
      calc workFn C₀ (encSeq M R τ) (D (n + 1))
          ≤ workFn C₀ (encSeq M R τ) (D n) + moveCost (D n) (D (n + 1)) := hlip
        _ ≤ (∑ j ∈ Finset.range n, dist (P j) (P (j + 1))) + dist (P n) (P (n + 1)) := by
            have := hih
            linarith
  have hfeas0 : ∀ (j : ℕ) (hj : j < σ.length),
      (σ.get ⟨j, hj⟩).Nonempty → P (j + 1) ∈ σ.get ⟨j, hj⟩ := by
    intro j hj hne'
    exact hP.2 ⟨j, hj⟩ hne'
  calc offlineCost C₀ (encSeq M R σ)
      ≤ workFn C₀ (encSeq M R σ) (D σ.length) :=
        offlineCost_le_workFn k hk M C₀ (encSeq M R σ) (D σ.length)
    _ ≤ ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)) := main σ hσ hfeas0
