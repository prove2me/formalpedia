-- Prove2me | solution 1 for ImpulseGames.Verification.remark3_6_player_two
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:14:03.952347+00:00
-- url     : https://prove2.me/submissions/a721c3f8-c4e6-4813-86c4-0c388639c8b4

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification

namespace ImpulseL23

variable {d : ℕ}

lemma le_exitAfter (p : ℝ≥0 → State d) (t₀ : ℝ≥0∞) (O : Set (State d)) :
    t₀ ≤ exitAfter p t₀ O := by
  unfold exitAfter
  exact le_iInf₂ fun s hs => hs.1.le

lemma exitAfter_le {p : ℝ≥0 → State d} {t₀ : ℝ≥0∞} {O : Set (State d)} {s : ℝ≥0}
    (h1 : t₀ < s) (h2 : p s ∉ O) : exitAfter p t₀ O ≤ s :=
  iInf₂_le (f := fun (s : ℝ≥0) (_ : t₀ < (s : ℝ≥0∞) ∧ p s ∉ O) => (s : ℝ≥0∞)) s ⟨h1, h2⟩

lemma mem_of_lt_exitAfter {p : ℝ≥0 → State d} {t₀ : ℝ≥0∞} {O : Set (State d)} {s : ℝ≥0}
    (h1 : t₀ < s) (h2 : (s : ℝ≥0∞) < exitAfter p t₀ O) : p s ∈ O := by
  by_contra h
  exact absurd (exitAfter_le h1 h) (not_le.2 h2)

lemma not_mem_exitAfter {p : ℝ≥0 → State d} {t₀ : ℝ≥0∞} {O : Set (State d)}
    (hO : IsOpen O) (hp : ContinuousOn p {s | t₀ ≤ (s : ℝ≥0∞)})
    (hfin : exitAfter p t₀ O < ⊤) : p (exitAfter p t₀ O).toNNReal ∉ O := by
  set a := exitAfter p t₀ O with ha_def
  set a' := a.toNNReal
  have ha : (a' : ℝ≥0∞) = a := ENNReal.coe_toNNReal hfin.ne
  intro hin
  have hle : t₀ ≤ (a' : ℝ≥0∞) := by rw [ha]; exact le_exitAfter _ _ _
  have hcont : ContinuousWithinAt p (Set.Ici a') a' :=
    (hp a' hle).mono (fun s hs => le_trans hle (by exact_mod_cast hs))
  have hev : p ⁻¹' O ∈ 𝓝[Set.Ici a'] a' := hcont (hO.mem_nhds hin)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  have hau : a < (u : ℝ≥0∞) := by rw [← ha]; exact_mod_cast hu
  rw [ha_def] at hau
  unfold exitAfter at hau
  obtain ⟨s, hs⟩ := iInf_lt_iff.1 hau
  obtain ⟨hs1, hs2⟩ := iInf_lt_iff.1 hs
  have has : a ≤ (s : ℝ≥0∞) := exitAfter_le hs1.1 hs1.2
  have : a' ≤ s := by
    have : (a' : ℝ≥0∞) ≤ s := by rw [ha]; exact has
    exact_mod_cast this
  exact hs1.2 (hsub ⟨this, by exact_mod_cast hs2⟩)

variable {k : ℕ} (G : Game d k) (x : State d) (π : Profile G) (y : ℕ → ℝ≥0 → State d)

lemma time_zero : (stage G x π y 0).time = 0 := rfl

lemma time_succ (n : ℕ) : (stage G x π y (n + 1)).time =
    min (exitAfter (stage G x π y n).path (stage G x π y n).time (π.C .one))
      (exitAfter (stage G x π y n).path (stage G x π y n).time (π.C .two)) := rfl

lemma path_succ (n : ℕ) (s : ℝ≥0) : (stage G x π y (n + 1)).path s =
    if (s : ℝ≥0∞) < (stage G x π y (n + 1)).time then (stage G x π y n).path s
    else y (n + 1) s := rfl

lemma exitS_succ (n : ℕ) : (stage G x π y (n + 1)).exitS =
    exitAfter (stage G x π y n).path (stage G x π y n).time G.S := rfl

lemma mover_succ (n : ℕ) : (stage G x π y (n + 1)).mover =
    if exitAfter (stage G x π y n).path (stage G x π y n).time (π.C .one) ≤
      exitAfter (stage G x π y n).path (stage G x π y n).time (π.C .two) then .one else .two :=
  rfl

lemma pre_succ (n : ℕ) : (stage G x π y (n + 1)).pre =
    (stage G x π y n).path (stage G x π y (n + 1)).time.toNNReal := rfl

lemma post_succ (n : ℕ) : (stage G x π y (n + 1)).post =
    if (stage G x π y (n + 1)).time < ⊤ then
      G.Γ (stage G x π y (n + 1)).mover (stage G x π y (n + 1)).pre
        (π.ξ (stage G x π y (n + 1)).mover (stage G x π y (n + 1)).pre) else 0 := rfl

lemma time_le_succ (n : ℕ) : (stage G x π y n).time ≤ (stage G x π y (n + 1)).time := by
  rw [time_succ]; exact le_min (le_exitAfter _ _ _) (le_exitAfter _ _ _)

lemma time_mono : Monotone (fun n => (stage G x π y n).time) :=
  monotone_nat_of_le_succ (time_le_succ G x π y)

lemma time_succ_of_mover (n : ℕ) (i : Player) (h : (stage G x π y (n + 1)).mover = i) :
    (stage G x π y (n + 1)).time =
      exitAfter (stage G x π y n).path (stage G x π y n).time (π.C i) := by
  rw [mover_succ] at h
  rw [time_succ]
  split_ifs at h with h1
  · subst h; exact min_eq_left h1
  · subst h; exact min_eq_right (le_of_lt (not_le.1 h1))

lemma path_eq_y (n : ℕ) (s : ℝ≥0) (h : (stage G x π y n).time ≤ s) :
    (stage G x π y n).path s = y n s := by
  cases n with
  | zero => rfl
  | succ n => rw [path_succ, if_neg (not_lt.2 h)]

lemma path_stable (n m : ℕ) (hnm : n ≤ m) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) < (stage G x π y (n + 1)).time) :
    (stage G x π y m).path s = (stage G x π y n).path s := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [path_succ, if_pos (lt_of_lt_of_le hs (time_mono G x π y (by omega)))]
    exact ih

lemma alive_zero : alive G x π y 0 := by
  intro h hh
  obtain rfl : h = 0 := by omega
  simp [stage]

lemma alive_mono {n m : ℕ} (h : m ≤ n) (hn : alive G x π y n) : alive G x π y m :=
  fun j hj => hn j (le_trans hj h)

lemma alive_iff (n : ℕ) : alive G x π y n ↔ (n : ℕ∞) ≤ kbar G x π y := by
  constructor
  · intro h
    exact le_iSup₂ (f := fun (n : ℕ) (_ : alive G x π y n) => (n : ℕ∞)) n h
  · intro h
    by_contra hn
    have hn0 : n ≠ 0 := by rintro rfl; exact hn (alive_zero G x π y)
    have : kbar G x π y ≤ ((n - 1 : ℕ) : ℕ∞) := by
      unfold kbar
      refine iSup₂_le fun m hm => ?_
      have : m < n := by
        by_contra hmn; exact hn (alive_mono G x π y (not_lt.1 hmn) hm)
      exact_mod_cast (by omega : m ≤ n - 1)
    have := le_trans h this
    have : n ≤ n - 1 := by exact_mod_cast this
    omega

lemma not_alive_succ_kbar (hk : kbar G x π y ≠ ⊤) :
    alive G x π y (kbar G x π y).toNat ∧ ¬ alive G x π y ((kbar G x π y).toNat + 1) := by
  constructor
  · rw [alive_iff, ENat.coe_toNat hk]
  · rw [alive_iff]
    intro h
    have h2 : (((kbar G x π y).toNat + 1 : ℕ) : ℕ∞) ≤ ((kbar G x π y).toNat : ℕ∞) := by
      rwa [ENat.coe_toNat hk]
    have : (kbar G x π y).toNat + 1 ≤ (kbar G x π y).toNat := by exact_mod_cast h2
    omega

lemma exitS_le_time_of_not_alive (n : ℕ) (hn : alive G x π y n)
    (hn1 : ¬ alive G x π y (n + 1)) :
    (stage G x π y (n + 1)).exitS ≤ (stage G x π y (n + 1)).time := by
  by_contra hlt
  apply hn1
  intro j hj
  rcases Nat.lt_or_ge j (n + 1) with h | h
  · exact hn j (by omega)
  · obtain rfl : j = n + 1 := by omega
    exact not_le.1 hlt

/-- (2.4) -/
lemma ctrl_eq (n : ℕ) (s : ℝ≥0) (hn : (n : ℕ∞) ≤ kbar G x π y)
    (h1 : (stage G x π y n).time ≤ (s : ℝ≥0∞))
    (h2 : (n : ℕ∞) < kbar G x π y → (s : ℝ≥0∞) < (stage G x π y (n + 1)).time) :
    ctrl G x π y s = y n s := by
  unfold ctrl
  split_ifs with hk
  · have hlt : (n : ℕ∞) < kbar G x π y := by rw [hk]; exact ENat.coe_lt_top n
    have hconst : ∀ m ≥ n, (stage G x π y m).path s = y n s := by
      intro m hm
      rw [path_stable G x π y n m hm s (h2 hlt), path_eq_y G x π y n s h1]
    have ht : Tendsto (fun m => (stage G x π y m).path s) atTop (𝓝 (y n s)) :=
      tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun m hm => (hconst m hm).symm⟩)
    exact ht.limUnder_eq
  · have hK : n ≤ (kbar G x π y).toNat := by
      have : (n : ℕ∞) ≤ ((kbar G x π y).toNat : ℕ∞) := by rwa [ENat.coe_toNat hk]
      exact_mod_cast this
    rcases Nat.lt_or_ge n (kbar G x π y).toNat with hlt | hge
    · have hlt' : (n : ℕ∞) < kbar G x π y := by
        rw [← ENat.coe_toNat hk]; exact_mod_cast hlt
      rw [path_stable G x π y n _ hK s (h2 hlt'), path_eq_y G x π y n s h1]
    · obtain heq : (kbar G x π y).toNat = n := by omega
      rw [heq, path_eq_y G x π y n s h1]

lemma exists_index (s : ℝ≥0)
    (hlim : kbar G x π y = ⊤ → Tendsto (fun n => (stage G x π y n).time) atTop
      (𝓝 (⨆ n, (stage G x π y n).exitS)))
    (hs : (s : ℝ≥0∞) < exitTime G x π y) :
    ∃ n : ℕ, (n : ℕ∞) ≤ kbar G x π y ∧ (stage G x π y n).time ≤ (s : ℝ≥0∞) ∧
      ((n : ℕ∞) < kbar G x π y → (s : ℝ≥0∞) < (stage G x π y (n + 1)).time) := by
  classical
  by_cases hex : ∃ m : ℕ, (m : ℕ∞) ≤ kbar G x π y ∧ (s : ℝ≥0∞) < (stage G x π y m).time
  · set m := Nat.find hex with hm_def
    have hm := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h0
      have := hm.2
      rw [← hm_def, h0, time_zero] at this
      exact absurd this (by simp)
    refine ⟨m - 1, ?_, ?_, ?_⟩
    · exact le_trans (by exact_mod_cast (Nat.sub_le m 1)) hm.1
    · have hmin := Nat.find_min hex (show m - 1 < m by omega)
      push_neg at hmin
      exact hmin (le_trans (by exact_mod_cast (Nat.sub_le m 1)) hm.1)
    · intro _
      have : m - 1 + 1 = m := by omega
      rw [this]; exact hm.2
  · push_neg at hex
    by_cases hk : kbar G x π y = ⊤
    · exfalso
      have hle : (⨆ n, (stage G x π y n).exitS) ≤ (s : ℝ≥0∞) :=
        le_of_tendsto' (hlim hk) (fun n => hex n (by rw [hk]; exact le_top))
      unfold exitTime at hs
      rw [if_pos hk] at hs
      exact absurd hs (not_lt.2 hle)
    · refine ⟨(kbar G x π y).toNat, by rw [ENat.coe_toNat hk], ?_, ?_⟩
      · exact hex _ (by rw [ENat.coe_toNat hk])
      · intro h; rw [ENat.coe_toNat hk] at h; exact absurd h (lt_irrefl _)

lemma count_zero (i : Player) : count G x π y i 0 = 0 := by
  simp [count]

lemma count_succ (i : Player) (l : ℕ) : count G x π y i (l + 1) =
    count G x π y i l + if (stage G x π y (l + 1)).mover = i then 1 else 0 := by
  classical
  unfold count
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Icc_succ_top (by omega)]

lemma count_mono (i : Player) : Monotone (count G x π y i) := by
  apply monotone_nat_of_le_succ
  intro l; rw [count_succ]; omega

lemma eta_eq (i : Player) (n : ℕ) (hm : (stage G x π y n).mover = i) (hn : 1 ≤ n) :
    eta G x π y i (count G x π y i n) = n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hc : count G x π y i (n' + 1) = count G x π y i n' + 1 := by
    rw [count_succ, if_pos hm]
  unfold eta
  apply le_antisymm
  · exact Nat.sInf_le rfl
  · apply le_csInf (s := {l | count G x π y i l = count G x π y i (n' + 1)}) ⟨n' + 1, rfl⟩
    intro l hl
    simp only [Set.mem_setOf_eq] at hl
    by_contra hlt
    have := count_mono G x π y i (show l ≤ n' by omega)
    omega

lemma count_pos (i : Player) (n : ℕ) (hm : (stage G x π y n).mover = i) (hn : 1 ≤ n) :
    1 ≤ count G x π y i n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [count_succ, if_pos hm]; omega

lemma mem_interventionTimes (n : ℕ) (hn : 1 ≤ n) (hk : (n : ℕ∞) ≤ kbar G x π y)
    (hlt : (stage G x π y n).time < exitTime G x π y) :
    (stage G x π y n).time ∈ interventionTimes G x π y := by
  set i := (stage G x π y n).mover with hi
  have hc : ((count G x π y i n : ℕ) : ℕ∞) ≤ kbarI G x π y i :=
    le_iSup₂ (f := fun (l : ℕ) (_ : (l : ℕ∞) ≤ kbar G x π y) => (count G x π y i l : ℕ∞)) n hk
  have hT : interTime G x π y i (count G x π y i n) = (stage G x π y n).time := by
    unfold interTime; rw [if_pos hc, eta_eq G x π y i n hi.symm hn]
  exact ⟨i, count G x π y i n, count_pos G x π y i n hi.symm hn, by rw [hT]; exact hlt,
    hT.symm⟩

/-- Analysis of the `c`-th intervention of player `i` before the exit. -/
lemma eta_spec (i : Player) (c : ℕ) (hc : 1 ≤ c)
    (hlt : interTime G x π y i c < exitTime G x π y) :
    (c : ℕ∞) ≤ kbarI G x π y i ∧ 1 ≤ eta G x π y i c ∧
      ((eta G x π y i c : ℕ) : ℕ∞) ≤ kbar G x π y ∧
      (stage G x π y (eta G x π y i c)).mover = i ∧
      interTime G x π y i c = (stage G x π y (eta G x π y i c)).time := by
  classical
  have hcI : (c : ℕ∞) ≤ kbarI G x π y i := by
    by_contra h
    unfold interTime at hlt
    rw [if_neg h] at hlt
    exact lt_irrefl _ hlt
  -- some l ≤ kbar with c ≤ count l
  have hl : ∃ l : ℕ, (l : ℕ∞) ≤ kbar G x π y ∧ c ≤ count G x π y i l := by
    by_contra hno
    push_neg at hno
    have : kbarI G x π y i ≤ ((c - 1 : ℕ) : ℕ∞) := by
      unfold kbarI
      refine iSup₂_le fun l hl => ?_
      have := hno l hl
      exact_mod_cast (by omega : count G x π y i l ≤ c - 1)
    have := le_trans hcI this
    have : c ≤ c - 1 := by exact_mod_cast this
    omega
  obtain ⟨l, hlk, hcl⟩ := hl
  have hex : ∃ l', c ≤ count G x π y i l' := ⟨l, hcl⟩
  set l' := Nat.find hex with hl'
  have hl'spec : c ≤ count G x π y i l' := Nat.find_spec hex
  have hl'le : l' ≤ l := Nat.find_min' hex hcl
  have hl'0 : l' ≠ 0 := by
    intro h0; rw [h0, count_zero] at hl'spec; omega
  have hl'eq : count G x π y i l' = c := by
    have hmin := Nat.find_min hex (show l' - 1 < l' by omega)
    push_neg at hmin
    have := count_succ G x π y i (l' - 1)
    rw [show l' - 1 + 1 = l' by omega] at this
    split_ifs at this <;> omega
  have hne : {j | count G x π y i j = c}.Nonempty := ⟨l', hl'eq⟩
  have hmem : count G x π y i (eta G x π y i c) = c := Nat.sInf_mem hne
  have hetale : eta G x π y i c ≤ l' := Nat.sInf_le hl'eq
  have heta0 : 1 ≤ eta G x π y i c := by
    by_contra h0
    have : eta G x π y i c = 0 := by omega
    rw [this, count_zero] at hmem; omega
  have hmover : (stage G x π y (eta G x π y i c)).mover = i := by
    have hprev : count G x π y i (eta G x π y i c - 1) ≠ c :=
      Nat.notMem_of_lt_sInf (s := {j | count G x π y i j = c})
        (show eta G x π y i c - 1 < eta G x π y i c by omega)
    have := count_succ G x π y i (eta G x π y i c - 1)
    rw [show eta G x π y i c - 1 + 1 = eta G x π y i c by omega] at this
    by_contra hm
    rw [if_neg hm] at this
    omega
  refine ⟨hcI, heta0, le_trans (by exact_mod_cast (le_trans hetale hl'le)) hlk, hmover, ?_⟩
  unfold interTime; rw [if_pos hcI]

lemma nhds_ev (n : ℕ) (s : ℝ≥0)
    (h2 : (n : ℕ∞) < kbar G x π y → (s : ℝ≥0∞) < (stage G x π y (n + 1)).time) :
    {s' : ℝ≥0 | (n : ℕ∞) < kbar G x π y → (s' : ℝ≥0∞) < (stage G x π y (n + 1)).time}
      ∈ 𝓝 s := by
  by_cases h : (n : ℕ∞) < kbar G x π y
  · have hopen : IsOpen {s' : ℝ≥0 | (s' : ℝ≥0∞) < (stage G x π y (n + 1)).time} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    filter_upwards [hopen.mem_nhds (h2 h)] with s' hs' _ using hs'
  · exact Filter.univ_mem' (fun s' h' => absurd h' h)

section Main

variable
    (hcont : ∀ n, alive G x π y n →
      ContinuousOn (y n) {s | (stage G x π y n).time ≤ (s : ℝ≥0∞)})
    (hpost : ∀ n, alive G x π y n → (stage G x π y n).time < ⊤ →
      y n (stage G x π y n).time.toNNReal = (stage G x π y n).post)
    (hlim : kbar G x π y = ⊤ → Tendsto (fun n => (stage G x π y n).time) atTop
      (𝓝 (⨆ n, (stage G x π y n).exitS)))

include hcont hlim in
lemma rcont (s : ℝ≥0) (hs : (s : ℝ≥0∞) < exitTime G x π y) :
    ContinuousWithinAt (ctrl G x π y) (Set.Ici s) s := by
  obtain ⟨n, hn, h1, h2⟩ := exists_index G x π y s hlim hs
  have hyc : ContinuousWithinAt (y n) (Set.Ici s) s :=
    ((hcont n ((alive_iff G x π y n).2 hn)) s h1).mono
      (fun s' hs' => le_trans h1 (by exact_mod_cast hs'))
  refine hyc.congr_of_eventuallyEq ?_ (ctrl_eq G x π y n s hn h1 h2)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (nhds_ev G x π y n s h2)]
    with s' hs' hs''
  exact ctrl_eq G x π y n s' hn (le_trans h1 (by exact_mod_cast hs')) hs''

include hcont hlim in
lemma ccont (s : ℝ≥0) (hs : (s : ℝ≥0∞) < exitTime G x π y)
    (hnot : (s : ℝ≥0∞) ∉ interventionTimes G x π y) :
    ContinuousAt (ctrl G x π y) s := by
  obtain ⟨n, hn, h1, h2⟩ := exists_index G x π y s hlim hs
  have hgood : {s' : ℝ≥0 | (stage G x π y n).time ≤ (s' : ℝ≥0∞)} ∈ 𝓝 s := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact Filter.univ_mem' (fun s' => by simp [time_zero])
    · have hne : (stage G x π y n).time ≠ s := by
        intro heq; apply hnot; rw [← heq]
        exact mem_interventionTimes G x π y n hpos hn (by rw [heq]; exact hs)
      have hlt : (stage G x π y n).time < s := lt_of_le_of_ne h1 hne
      filter_upwards [(isOpen_lt continuous_const ENNReal.continuous_coe).mem_nhds hlt]
        with s' hs' using le_of_lt hs'
  have hyc : ContinuousAt (y n) s :=
    (hcont n ((alive_iff G x π y n).2 hn)).continuousAt hgood
  refine hyc.congr ?_
  filter_upwards [hgood, nhds_ev G x π y n s h2] with s' a b
  exact (ctrl_eq G x π y n s' hn a b).symm

include hcont hpost in
lemma jump (hπ : ∀ i, IsOpen (π.C i)) (i : Player) (c : ℕ) (hc : 1 ≤ c)
    (hlt : interTime G x π y i c < exitTime G x π y) :
    impulse G x π y i c = π.ξ i (preState G x π y i c) ∧
      preState G x π y i c ∉ π.C i ∧
      ((stage G x π y (eta G x π y i c)).time <
          (stage G x π y (eta G x π y i c + 1)).time →
        ctrl G x π y (interTime G x π y i c).toNNReal =
          G.Γ i (preState G x π y i c) (impulse G x π y i c)) := by
  obtain ⟨hcI, he1, hek, hmov, hIT⟩ := eta_spec G x π y i c hc hlt
  have himp : impulse G x π y i c = π.ξ i (preState G x π y i c) := by
    unfold impulse; rw [if_pos hcI]
  refine ⟨himp, ?_, ?_⟩
  · unfold preState
    obtain ⟨e', he'⟩ : ∃ e', eta G x π y i c = e' + 1 := ⟨eta G x π y i c - 1, by omega⟩
    rw [he'] at hmov hek hIT ⊢
    rw [pre_succ, time_succ_of_mover G x π y e' i hmov]
    apply not_mem_exitAfter (hπ i)
    · have ha : alive G x π y e' :=
        (alive_iff G x π y e').2 (le_trans (by exact_mod_cast (Nat.le_succ e')) hek)
      exact (hcont e' ha).congr (fun s hs => path_eq_y G x π y e' s hs)
    · rw [← time_succ_of_mover G x π y e' i hmov, ← hIT]; exact lt_of_lt_of_le hlt le_top
  · intro hlt2
    rw [himp]
    unfold preState
    obtain ⟨e', he'⟩ : ∃ e', eta G x π y i c = e' + 1 := ⟨eta G x π y i c - 1, by omega⟩
    rw [he'] at hmov hek hIT hlt2 ⊢
    have hfin : (stage G x π y (e' + 1)).time < ⊤ := by
      rw [← hIT]; exact lt_of_lt_of_le hlt le_top
    have hco : (((stage G x π y (e' + 1)).time.toNNReal : ℝ≥0) : ℝ≥0∞) =
        (stage G x π y (e' + 1)).time := ENNReal.coe_toNNReal hfin.ne
    rw [hIT, ctrl_eq G x π y (e' + 1) _ hek (by rw [hco]) (fun _ => by rw [hco]; exact hlt2),
      hpost (e' + 1) ((alive_iff G x π y _).2 hek) hfin, post_succ, if_pos hfin, hmov]

include hlim in
lemma stays (s : ℝ≥0) (hs0 : 0 < s) (hs : (s : ℝ≥0∞) < exitTime G x π y)
    (hnot : (s : ℝ≥0∞) ∉ interventionTimes G x π y) :
    ctrl G x π y s ∈ π.C .one ∩ π.C .two := by
  obtain ⟨n, hn, h1, h2⟩ := exists_index G x π y s hlim hs
  have hlt1 : (stage G x π y n).time < s := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [time_zero]; exact_mod_cast hs0
    · refine lt_of_le_of_ne h1 (fun heq => hnot ?_)
      rw [← heq]
      exact mem_interventionTimes G x π y n hpos hn (by rw [heq]; exact hs)
  have hlt2 : (s : ℝ≥0∞) < (stage G x π y (n + 1)).time := by
    by_cases hk : (n : ℕ∞) < kbar G x π y
    · exact h2 hk
    · have hkn : kbar G x π y = n := le_antisymm (not_lt.1 hk) hn
      have hkt : kbar G x π y ≠ ⊤ := by rw [hkn]; exact ENat.coe_ne_top n
      have htn : (kbar G x π y).toNat = n := by rw [hkn]; rfl
      obtain ⟨ha, hna⟩ := not_alive_succ_kbar G x π y hkt
      rw [htn] at ha hna
      have := exitS_le_time_of_not_alive G x π y n ha hna
      have hE : exitTime G x π y = (stage G x π y (n + 1)).exitS := by
        unfold exitTime; rw [if_neg hkt, htn]
      rw [hE] at hs; exact lt_of_lt_of_le hs this
  rw [ctrl_eq G x π y n s hn h1 h2, ← path_eq_y G x π y n s h1]
  rw [time_succ] at hlt2
  exact ⟨mem_of_lt_exitAfter hlt1 (lt_of_lt_of_le hlt2 (min_le_left _ _)),
    mem_of_lt_exitAfter hlt1 (lt_of_lt_of_le hlt2 (min_le_right _ _))⟩

end Main

section Real

variable {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
  (W : ℝ≥0 → Ω → (Fin k → ℝ))

lemma real_cont {Y : ℕ → ℝ≥0 → Ω → State d} (hY : IsRealization P 𝔽 W G x π Y) (ω : Ω)
    (n : ℕ) (ha : alive G x π (pathOf Y ω) n) :
    ContinuousOn (pathOf Y ω n) {s | (stage G x π (pathOf Y ω) n).time ≤ (s : ℝ≥0∞)} := by
  have h := (hY.1 n).1 ω
  simp only [if_pos ha] at h
  exact h

lemma real_post {Y : ℕ → ℝ≥0 → Ω → State d} (hY : IsRealization P 𝔽 W G x π Y) (ω : Ω)
    (n : ℕ) (ha : alive G x π (pathOf Y ω) n) (hf : (stage G x π (pathOf Y ω) n).time < ⊤) :
    pathOf Y ω n (stage G x π (pathOf Y ω) n).time.toNNReal =
      (stage G x π (pathOf Y ω) n).post := by
  have h := (hY.1 n).2.2.1 ω
  simp only [if_pos ha] at h
  exact h hf

end Real


section Mem

variable (hpost : ∀ n, alive G x π y n → (stage G x π y n).time < ⊤ →
      y n (stage G x π y n).time.toNNReal = (stage G x π y n).post)

include hpost in
lemma post_pre_mem (hG : G.Standing) (hx : x ∈ G.S) (hπ : ∀ i, ∀ z ∈ G.S, π.ξ i z ∈ G.Z i) :
    ∀ n, alive G x π y n → (stage G x π y n).post ∈ G.S ∧
      (1 ≤ n → (stage G x π y n).pre ∈ G.S) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hx, fun h => absurd h (by omega)⟩
  | succ n ih =>
    intro ha
    have han : alive G x π y n := alive_mono G x π y (Nat.le_succ n) ha
    have hlt : (stage G x π y (n + 1)).time < (stage G x π y (n + 1)).exitS := ha (n + 1) le_rfl
    have hfin : (stage G x π y (n + 1)).time < ⊤ := lt_of_lt_of_le hlt le_top
    have hco : (((stage G x π y (n + 1)).time.toNNReal : ℝ≥0) : ℝ≥0∞) =
        (stage G x π y (n + 1)).time := ENNReal.coe_toNNReal hfin.ne
    have hpre : (stage G x π y (n + 1)).pre ∈ G.S := by
      rw [pre_succ]
      rcases lt_or_eq_of_le (time_le_succ G x π y n) with h | h
      · apply mem_of_lt_exitAfter (t₀ := (stage G x π y n).time)
        · rw [hco]; exact h
        · rw [hco, ← exitS_succ]; exact hlt
      · have hfn : (stage G x π y n).time < ⊤ := by rw [h]; exact hfin
        have : (stage G x π y (n + 1)).time.toNNReal = (stage G x π y n).time.toNNReal := by
          rw [h]
        rw [this, path_eq_y G x π y n _ (by rw [ENNReal.coe_toNNReal hfn.ne]),
          hpost n han hfn]
        exact (ih han).1
    refine ⟨?_, fun _ => hpre⟩
    rw [post_succ, if_pos hfin]
    exact hG.2.2.2.2.1 _ _ hpre _ (hπ _ _ hpre)

end Mem

end ImpulseL23

open ImpulseL23 in
theorem solution {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (C1 : Set (State d)) (ξ1 : State d → G.Imp .one) (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsAdmissible P 𝔽 W G x ((starProfile G V δ).update .one C1 ξ1) Y) (ω : Ω) :
    (∀ s : ℝ≥0, 0 < s →
      (s : ℝ≥0∞) < exitTime G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) →
      (s : ℝ≥0∞) ∉ interventionTimes G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) →
      interventionOp G V δ .two
          (ctrl G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) s)
        - V .two (ctrl G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) s) < 0) ∧
    (∀ n : ℕ, 1 ≤ n →
      interTime G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n <
        exitTime G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) →
      impulse G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n =
          δ .two (preState G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n) ∧
        interventionOp G V δ .two
            (preState G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n)
          - V .two (preState G x ((starProfile G V δ).update .one C1 ξ1) (pathOf Y ω) .two n)
          = 0) := by
  set π := (starProfile G V δ).update .one C1 ξ1 with hπdef
  have hC2 : π.C .two = contRegion G V δ .two := by
    simp [hπdef, Profile.update, starProfile]
  have hξ2 : π.ξ .two = δ .two := by
    simp [hπdef, Profile.update, starProfile]
  have hR : IsRealization P 𝔽 W G x π Y := hY.2.1
  have hstrat := hY.1
  have hcont := real_cont G x π P 𝔽 W hR ω
  have hpost := real_post G x π P 𝔽 W hR ω
  have hlim := hR.2 ω
  refine ⟨fun s hs0 hs hnot => ?_, fun n hn hlt => ?_⟩
  · have h := (stays G x π (pathOf Y ω) hlim s hs0 hs hnot).2
    rw [hC2] at h
    exact h.2
  · obtain ⟨himp, hnotin, -⟩ :=
      jump G x π (pathOf Y ω) hcont hpost (fun i => (hstrat i).1) .two n hn hlt
    obtain ⟨hcI, he1, hek, hmov, hIT⟩ := eta_spec G x π (pathOf Y ω) .two n hn hlt
    have hmemS : preState G x π (pathOf Y ω) .two n ∈ G.S := by
      unfold preState
      exact (post_pre_mem G x π (pathOf Y ω) hpost hG hx (fun i => (hstrat i).2.2.1) _
        ((alive_iff G x π (pathOf Y ω) _).2 hek)).2 he1
    rw [hξ2] at himp
    refine ⟨himp, ?_⟩
    rw [hC2] at hnotin
    have hle := (hV .one).2.2.1.2.1 _ hmemS
    have hnlt : ¬ (interventionOp G V δ .two (preState G x π (pathOf Y ω) .two n)
        - V .two (preState G x π (pathOf Y ω) .two n) < 0) := fun h => hnotin ⟨hmemS, h⟩
    exact le_antisymm hle (not_lt.1 hnlt)
