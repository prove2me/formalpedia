-- Prove2me | solution 1 for ImpulseNMFG.Verification.eq_2_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:18:28.445503+00:00
-- url     : https://prove2.me/submissions/f8b362b4-a61a-4165-ac69-fb3cc2f7a799

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis SolvesFrom exitAfter disc before InL1)
open ImpulseNMFG.Verification

namespace ImpPathDev
variable {N d M : ℕ} [NeZero N]

lemma le_exitAfter (p : ℝ≥0 → State d) (t₀ : ℝ≥0∞) (O : Set (State d)) :
    t₀ ≤ exitAfter p t₀ O :=
  le_iInf fun _ => le_iInf fun h => h.1.le

lemma exitAfter_le (p : ℝ≥0 → State d) (t₀ : ℝ≥0∞) (O : Set (State d)) (s : ℝ≥0)
    (h1 : t₀ < s) (h2 : p s ∉ O) : exitAfter p t₀ O ≤ s :=
  iInf₂_le s ⟨h1, h2⟩

lemma mem_of_lt_exitAfter (p : ℝ≥0 → State d) (t₀ : ℝ≥0∞) (O : Set (State d)) (s : ℝ≥0)
    (h1 : t₀ < s) (h2 : (s : ℝ≥0∞) < exitAfter p t₀ O) : p s ∈ O := by
  by_contra h
  exact absurd (exitAfter_le p t₀ O s h1 h) (not_le.mpr h2)

lemma lt_exitAfter (p : ℝ≥0 → State d) (t₀ : ℝ≥0) (O : Set (State d)) (hO : IsOpen O)
    (hc : ContinuousWithinAt p (Set.Ici t₀) t₀) (hm : p t₀ ∈ O) :
    (t₀ : ℝ≥0∞) < exitAfter p t₀ O := by
  have hev : ∀ᶠ s in 𝓝[Set.Ici t₀] t₀, p s ∈ O := hc (hO.mem_nhds hm)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp hev
  have : ((u : ℝ≥0∞)) ≤ exitAfter p t₀ O := by
    refine le_iInf fun s => le_iInf fun hs => ?_
    by_contra hlt
    push Not at hlt
    have hs1 : t₀ < s := by exact_mod_cast hs.1
    have hs2 : s < u := by exact_mod_cast hlt
    exact hs.2 (hsub ⟨hs1.le, hs2⟩)
  exact lt_of_lt_of_le (by exact_mod_cast hu) this

lemma mem_at_exitAfter_compl (p : ℝ≥0 → State d) (t₀ : ℝ≥0∞) (A : Set (State d))
    (hA : IsClosed A) (hc : ContinuousOn p {s : ℝ≥0 | t₀ ≤ (s : ℝ≥0∞)})
    (hlt : exitAfter p t₀ Aᶜ < ⊤) : p (exitAfter p t₀ Aᶜ).toNNReal ∈ A := by
  set T : Set ℝ≥0 := {s | t₀ < (s : ℝ≥0∞) ∧ p s ∈ A} with hT
  have hne : T.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply (ne_of_lt hlt)
    refine le_antisymm le_top (le_iInf fun s => le_iInf fun hs => ?_)
    have : s ∈ T := ⟨hs.1, by simpa using hs.2⟩
    rw [hne] at this; exact this.elim
  have heq : exitAfter p t₀ Aᶜ = ((sInf T : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_sInf hne]
    unfold exitAfter
    apply le_antisymm
    · refine le_iInf₂ fun s hs => iInf₂_le s ⟨hs.1, by simpa using hs.2⟩
    · refine le_iInf₂ fun s hs => iInf₂_le s ⟨hs.1, by simpa using hs.2⟩
  rw [heq, ENNReal.toNNReal_coe]
  have hmem : sInf T ∈ closure T := csInf_mem_closure hne (OrderBot.bddBelow T)
  have hclosed : IsClosed {s : ℝ≥0 | t₀ ≤ (s : ℝ≥0∞)} :=
    isClosed_le continuous_const ENNReal.continuous_coe
  have hTsub : T ⊆ {s : ℝ≥0 | t₀ ≤ (s : ℝ≥0∞)} := fun s hs => hs.1.le
  have hcl : closure T ⊆ {s : ℝ≥0 | t₀ ≤ (s : ℝ≥0∞)} := hclosed.closure_subset_iff.mpr hTsub
  have : p (sInf T) ∈ closure (p '' T) :=
    ((hc _ (hcl hmem)).mono hTsub).mem_closure_image hmem
  have hsub : p '' T ⊆ A := by rintro _ ⟨s, hs, rfl⟩; exact hs.2
  exact hA.closure_subset_iff.mpr hsub this

section Path
variable (G : Game N d M) (x : State d) (π : Profile G) (y : ℕ → ℝ≥0 → State d)


lemma time_succ (n : ℕ) : (stage G x π y (n+1)).time = ⨅ i : Fin N,
    exitAfter (stage G x π y n).path (stage G x π y n).time (π.A i)ᶜ := rfl

lemma time_le_succ (n : ℕ) : (stage G x π y n).time ≤ (stage G x π y (n+1)).time := by
  rw [time_succ]; exact le_iInf fun i => le_exitAfter _ _ _

lemma time_mono : Monotone (fun n => (stage G x π y n).time) :=
  monotone_nat_of_le_succ (time_le_succ G x π y)

lemma time_zero : (stage G x π y 0).time = 0 := rfl

lemma path_eq_of_le (n : ℕ) (s : ℝ≥0) (hs : (s : ℝ≥0∞) < (stage G x π y (n+1)).time) :
    ∀ m, n ≤ m → (stage G x π y m).path s = (stage G x π y n).path s := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have : (s : ℝ≥0∞) < (stage G x π y (m+1)).time :=
      lt_of_lt_of_le hs (time_mono G x π y (by omega))
    show (if (s : ℝ≥0∞) < (stage G x π y (m+1)).time then (stage G x π y m).path s else y (m + 1) s) = _
    rw [if_pos this, ih]

lemma path_eq_y (n : ℕ) (s : ℝ≥0) (hs : (stage G x π y n).time ≤ (s : ℝ≥0∞)) : (stage G x π y n).path s = y n s := by
  cases n with
  | zero => rfl
  | succ n =>
    show (if (s : ℝ≥0∞) < (stage G x π y (n+1)).time then (stage G x π y n).path s else y (n + 1) s) = _
    rw [if_neg (not_lt.mpr hs)]

lemma alive_mono {n m : ℕ} (h : m ≤ n) (hn : alive G x π y n) : alive G x π y m :=
  fun k hk => hn k (le_trans hk h)

lemma alive_zero : alive G x π y 0 := by
  intro h hh
  have : h = 0 := by omega
  subst this
  show (0 : ℝ≥0∞) < ⊤
  exact ENNReal.zero_lt_top

lemma kbar_top_iff : kbar G x π y = ⊤ ↔ ∀ n, alive G x π y n := by
  constructor
  · intro h n
    by_contra hn
    have : kbar G x π y ≤ n := by
      refine iSup₂_le fun m hm => ?_
      by_contra hlt
      push Not at hlt
      exact hn (alive_mono G x π y (by exact_mod_cast hlt.le) hm)
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    exact ENat.eq_top_iff_forall_ge.mpr fun n => le_iSup₂_of_le n (h n) le_rfl

lemma kbar_fin (h : kbar G x π y ≠ ⊤) :
    ∃ K : ℕ, kbar G x π y = K ∧ alive G x π y K ∧ ¬ alive G x π y (K+1) := by
  have hex : ∃ n, ¬ alive G x π y n := by
    by_contra hc; push Not at hc
    exact h ((kbar_top_iff G x π y).mpr hc)
  classical
  let K0 := Nat.find hex
  have hK0 : ¬ alive G x π y K0 := Nat.find_spec hex
  have hK0pos : K0 ≠ 0 := by
    intro h0; rw [h0] at hK0; exact hK0 (alive_zero G x π y)
  have hbelow : ∀ m < K0, alive G x π y m := fun m hm => by
    have := Nat.find_min hex hm; push Not at this; exact this
  refine ⟨K0 - 1, ?_, hbelow _ (by omega), by rw [show K0 - 1 + 1 = K0 by omega]; exact hK0⟩
  apply le_antisymm
  · refine iSup₂_le fun m hm => ?_
    have : m < K0 := by
      by_contra hc; push Not at hc
      exact hK0 (alive_mono G x π y hc hm)
    exact_mod_cast (by omega : m ≤ K0 - 1)
  · exact le_iSup₂_of_le (K0 - 1) (hbelow _ (by omega)) le_rfl

lemma alive_le_kbar (k : ℕ) (hk : alive G x π y k) : (k : ℕ∞) ≤ kbar G x π y :=
  le_iSup₂_of_le k hk le_rfl

lemma alive_of_le_kbar (k : ℕ) (hk : (k : ℕ∞) ≤ kbar G x π y) : alive G x π y k := by
  by_cases h : kbar G x π y = ⊤
  · exact (kbar_top_iff G x π y).mp h k
  · obtain ⟨K, hK, hKa, -⟩ := kbar_fin G x π y h
    rw [hK] at hk
    exact alive_mono G x π y (by exact_mod_cast hk) hKa

/-- ctrl agrees with the k-th stage path before time (stage G x π y (k+1)).time, when k is alive. -/
lemma ctrl_eq_path (k : ℕ) (hk : alive G x π y k) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) < (stage G x π y (k+1)).time) : ctrl G x π y s = (stage G x π y k).path s := by
  unfold ctrl
  split_ifs with h
  · apply Filter.Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with m hm
    exact (path_eq_of_le G x π y k s hs m hm).symm
  · obtain ⟨K, hK, hKa, -⟩ := kbar_fin G x π y h
    rw [hK, ENat.toNat_natCast]
    have : k ≤ K := by
      have := alive_le_kbar G x π y k hk; rw [hK] at this; exact_mod_cast this
    exact path_eq_of_le G x π y k s hs K this

lemma ctrl_eq_path_last (K : ℕ) (hK : kbar G x π y = K) (s : ℝ≥0) :
    ctrl G x π y s = (stage G x π y K).path s := by
  unfold ctrl
  rw [if_neg (by rw [hK]; exact ENat.natCast_ne_top K), hK, ENat.toNat_natCast]


lemma alive_succ_lt (k : ℕ) (hk : alive G x π y (k+1)) :
    (stage G x π y (k+1)).time < (stage G x π y (k+1)).exitS := hk (k+1) le_rfl

lemma exitTime_fin (K : ℕ) (hK : kbar G x π y = K) :
    exitTime G x π y = (stage G x π y (K+1)).exitS := by
  unfold exitTime; rw [if_neg (by rw [hK]; exact ENat.natCast_ne_top K), hK, ENat.toNat_natCast]

lemma exitTime_top (h : kbar G x π y = ⊤) :
    exitTime G x π y = ⨆ n, (stage G x π y n).exitS := by
  unfold exitTime; rw [if_pos h]

lemma seg_aux (s : ℝ≥0) : ∀ n, (s : ℝ≥0∞) < (stage G x π y n).time →
    ∃ k, k + 1 ≤ n ∧ (stage G x π y k).time ≤ s ∧ (s : ℝ≥0∞) < (stage G x π y (k+1)).time := by
  intro n
  induction n with
  | zero => intro h; rw [time_zero] at h; exact absurd h (not_lt.mpr bot_le)
  | succ n ih =>
    intro h
    by_cases hn : (stage G x π y n).time ≤ s
    · exact ⟨n, le_rfl, hn, h⟩
    · obtain ⟨k, hk1, hk2, hk3⟩ := ih (lt_of_not_ge hn)
      exact ⟨k, by omega, hk2, hk3⟩

/-- Every time before exit lies in a live segment. -/
lemma segment_exists
    (hlim : kbar G x π y = ⊤ → Tendsto (fun n => (stage G x π y n).time) atTop
      (𝓝 (⨆ n, (stage G x π y n).exitS)))
    (s : ℝ≥0) (hs : (s : ℝ≥0∞) < exitTime G x π y) :
    ∃ k, alive G x π y k ∧ (stage G x π y k).time ≤ s ∧
      (s : ℝ≥0∞) < (stage G x π y (k+1)).time ∧
      (s : ℝ≥0∞) < (stage G x π y (k+1)).exitS := by
  by_cases h : kbar G x π y = ⊤
  · have hall := (kbar_top_iff G x π y).mp h
    rw [exitTime_top G x π y h] at hs
    obtain ⟨n, hn⟩ := ((hlim h).eventually (eventually_gt_nhds hs)).exists
    obtain ⟨k, -, hk2, hk3⟩ := seg_aux G x π y s n hn
    exact ⟨k, hall k, hk2, hk3, lt_trans hk3 (alive_succ_lt G x π y k (hall _))⟩
  · obtain ⟨K, hK, hKa, hKn⟩ := kbar_fin G x π y h
    rw [exitTime_fin G x π y K hK] at hs
    by_cases hsK : (stage G x π y K).time ≤ s
    · refine ⟨K, hKa, hsK, ?_, hs⟩
      have : ¬ ((stage G x π y (K+1)).time < (stage G x π y (K+1)).exitS) := by
        intro hlt; apply hKn
        intro j hj
        rcases Nat.lt_or_ge j (K+1) with hj' | hj'
        · exact hKa j (by omega)
        · have : j = K + 1 := by omega
          subst this; exact hlt
      exact lt_of_lt_of_le hs (not_lt.mp this)
    · obtain ⟨k, hk1, hk2, hk3⟩ := seg_aux G x π y s K (lt_of_not_ge hsK)
      have hak : alive G x π y (k+1) := alive_mono G x π y hk1 hKa
      exact ⟨k, alive_mono G x π y (by omega) hak, hk2, hk3,
        lt_trans hk3 (alive_succ_lt G x π y k hak)⟩

lemma ctrl_eq_y (k : ℕ) (hk : alive G x π y k) (s : ℝ≥0) (h1 : (stage G x π y k).time ≤ s)
    (h2 : (s : ℝ≥0∞) < (stage G x π y (k+1)).time) : ctrl G x π y s = y k s := by
  rw [ctrl_eq_path G x π y k hk s h2, path_eq_y G x π y k s h1]

lemma path_not_mem (k : ℕ) (s : ℝ≥0) (h1 : (stage G x π y k).time < s)
    (h2 : (s : ℝ≥0∞) < (stage G x π y (k+1)).time) (i : Fin N) :
    (stage G x π y k).path s ∉ π.A i := by
  have : (s : ℝ≥0∞) < exitAfter (stage G x π y k).path (stage G x π y k).time (π.A i)ᶜ :=
    lt_of_lt_of_le h2 (by rw [time_succ]; exact iInf_le _ i)
  exact mem_of_lt_exitAfter _ _ _ s h1 this

lemma path_mem_S (k : ℕ) (s : ℝ≥0) (h1 : (stage G x π y k).time < s)
    (h2 : (s : ℝ≥0∞) < (stage G x π y (k+1)).exitS) :
    (stage G x π y k).path s ∈ G.S :=
  mem_of_lt_exitAfter _ _ _ s h1 h2

lemma ctrl_rcont (hcont : ∀ n, alive G x π y n →
      ContinuousOn (y n) {s : ℝ≥0 | (stage G x π y n).time ≤ (s : ℝ≥0∞)})
    (k : ℕ) (hk : alive G x π y k) (s : ℝ≥0) (h1 : (stage G x π y k).time ≤ s)
    (h2 : (s : ℝ≥0∞) < (stage G x π y (k+1)).time) :
    ContinuousWithinAt (ctrl G x π y) (Set.Ici s) s := by
  have hy : ContinuousWithinAt (y k) (Set.Ici s) s :=
    (hcont k hk s h1).mono (fun t ht => le_trans h1 (by exact_mod_cast ht))
  refine hy.congr_of_eventuallyEq ?_ (ctrl_eq_y G x π y k hk s h1 h2)
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < (stage G x π y (k+1)).time} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds h2)] with t ht1 ht2
  exact ctrl_eq_y G x π y k hk t (le_trans h1 (by exact_mod_cast ht1)) ht2

lemma ctrl_cont (hcont : ∀ n, alive G x π y n →
      ContinuousOn (y n) {s : ℝ≥0 | (stage G x π y n).time ≤ (s : ℝ≥0∞)})
    (k : ℕ) (hk : alive G x π y k) (s : ℝ≥0) (h1 : (stage G x π y k).time < s)
    (h2 : (s : ℝ≥0∞) < (stage G x π y (k+1)).time) :
    ContinuousAt (ctrl G x π y) s := by
  have hopen1 : IsOpen {t : ℝ≥0 | (stage G x π y k).time < (t : ℝ≥0∞)} :=
    isOpen_lt continuous_const ENNReal.continuous_coe
  have hopen2 : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < (stage G x π y (k+1)).time} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hy : ContinuousAt (y k) s :=
    (hcont k hk).continuousAt (Filter.mem_of_superset (hopen1.mem_nhds h1)
      (fun t (ht : (stage G x π y k).time < (t : ℝ≥0∞)) =>
        (le_of_lt ht : (stage G x π y k).time ≤ (t : ℝ≥0∞))))
  refine hy.congr ?_
  filter_upwards [hopen1.mem_nhds h1, hopen2.mem_nhds h2] with t ht1 ht2
  exact (ctrl_eq_y G x π y k hk t (le_of_lt ht1) ht2).symm

/-! counting -/

lemma Icc_succ (l : ℕ) : Finset.Icc 1 (l+1) = insert (l+1) (Finset.Icc 1 l) := by
  ext a; simp; omega

lemma count_zero (i : Fin N) : count G x π y i 0 = 0 := by
  simp [count]

lemma count_succ (i : Fin N) (l : ℕ) : count G x π y i (l+1) =
    count G x π y i l + (if (stage G x π y (l+1)).mover = i then 1 else 0) := by
  unfold count
  rw [Icc_succ, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma count_mono (i : Fin N) : Monotone (count G x π y i) := by
  apply monotone_nat_of_le_succ
  intro l; rw [count_succ]; omega

lemma count_ivt (i : Fin N) (n : ℕ) : ∀ l, n ≤ count G x π y i l →
    ∃ l' ≤ l, count G x π y i l' = n := by
  intro l
  induction l with
  | zero => intro h; rw [count_zero] at h; exact ⟨0, le_rfl, by rw [count_zero]; omega⟩
  | succ l ih =>
    intro h
    by_cases h' : n ≤ count G x π y i l
    · obtain ⟨l', hl', e⟩ := ih h'; exact ⟨l', by omega, e⟩
    · refine ⟨l+1, le_rfl, ?_⟩
      have := count_succ G x π y i l
      split_ifs at this <;> omega

/-- The k-th stage time (k ≥ 1 alive) is the count-th intervention time of its mover. -/
lemma eta_count (k : ℕ) (i : Fin N) (hm : (stage G x π y (k+1)).mover = i) :
    eta G x π y i (count G x π y i (k+1)) = k + 1 := by
  unfold eta
  apply le_antisymm
  · exact Nat.sInf_le rfl
  · refine le_csInf ⟨k+1, rfl⟩ fun l hl => ?_
    by_contra hlt; push Not at hlt
    have h1 := count_mono G x π y i (show l ≤ k by omega)
    have h2 := count_succ G x π y i k
    rw [if_pos hm] at h2
    simp only [Set.mem_ofPred_eq] at hl
    omega

lemma interTime_alive (k : ℕ) (hk : alive G x π y (k+1)) :
    let i := (stage G x π y (k+1)).mover
    1 ≤ count G x π y i (k+1) ∧
    interTime G x π y i (count G x π y i (k+1)) = (stage G x π y (k+1)).time := by
  intro i
  have h2 := count_succ G x π y i k
  rw [if_pos rfl] at h2
  refine ⟨by omega, ?_⟩
  unfold interTime
  rw [if_pos, eta_count G x π y k i rfl]
  exact le_iSup₂_of_le (k+1) (alive_le_kbar G x π y _ hk) le_rfl

lemma time_mem_interventionTimes (k : ℕ) (hk : alive G x π y (k+1))
    (hlt : (stage G x π y (k+1)).time < exitTime G x π y) :
    (stage G x π y (k+1)).time ∈ interventionTimes G x π y := by
  obtain ⟨h1, h2⟩ := interTime_alive G x π y k hk
  exact ⟨_, _, h1, by rw [h2]; exact hlt, h2.symm⟩

/-- Decoding an intervention time before exit. -/
lemma interTime_decode (i : Fin N) (n : ℕ) (hn : 1 ≤ n)
    (hlt : interTime G x π y i n < exitTime G x π y) :
    ∃ k, eta G x π y i n = k + 1 ∧ alive G x π y (k+1) ∧
      (stage G x π y (k+1)).mover = i ∧ count G x π y i (k+1) = n ∧
      (n : ℕ∞) ≤ kbarI G x π y i ∧
      interTime G x π y i n = (stage G x π y (k+1)).time := by
  have hle : (n : ℕ∞) ≤ kbarI G x π y i := by
    by_contra hc
    unfold interTime at hlt; rw [if_neg hc] at hlt; exact lt_irrefl _ hlt
  have : ((n - 1 : ℕ) : ℕ∞) < kbarI G x π y i :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : n - 1 < n)) hle
  unfold kbarI at this
  obtain ⟨l, hl⟩ := lt_iSup_iff.mp this
  obtain ⟨hlk, hl2⟩ := lt_iSup_iff.mp hl
  have hnl : n ≤ count G x π y i l := by
    have h3 : n - 1 < count G x π y i l := by exact_mod_cast hl2
    omega
  obtain ⟨l', hl'l, hl'⟩ := count_ivt G x π y i n l hnl
  have hne : {l | count G x π y i l = n}.Nonempty := ⟨l', hl'⟩
  set k0 := eta G x π y i n with hk0
  have hk0mem : count G x π y i k0 = n := Nat.sInf_mem hne
  have hk0le : k0 ≤ l' := Nat.sInf_le hl'
  have hk0pos : k0 ≠ 0 := by
    intro h; rw [h, count_zero] at hk0mem; omega
  obtain ⟨k, hk⟩ : ∃ k, k0 = k + 1 := ⟨k0 - 1, by omega⟩
  have hmin : count G x π y i k ≠ n := by
    intro h
    have : k0 ≤ k := Nat.sInf_le h
    omega
  have halive : alive G x π y (k+1) := by
    apply alive_of_le_kbar
    exact le_trans (by exact_mod_cast (by omega : k + 1 ≤ l)) hlk
  have hc := count_succ G x π y i k
  have hk0mem' : count G x π y i (k+1) = n := by rw [← hk]; exact hk0mem
  rw [hk0mem'] at hc
  have hmov : (stage G x π y (k+1)).mover = i := by
    by_contra hm; rw [if_neg hm] at hc; omega
  refine ⟨k, hk, halive, hmov, by rw [← hk]; exact hk0mem, hle, ?_⟩
  unfold interTime; rw [if_pos hle, ← hk0, hk]

lemma mover_spec (Q : Stage N d) :
    exitAfter Q.path Q.time (π.A (mover G π Q))ᶜ =
      ⨅ j : Fin N, exitAfter Q.path Q.time (π.A j)ᶜ := by
  have hne : {i : Fin N | exitAfter Q.path Q.time (π.A i)ᶜ =
      ⨅ j : Fin N, exitAfter Q.path Q.time (π.A j)ᶜ}.Nonempty := by
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
      (f := fun j : Fin N => exitAfter Q.path Q.time (π.A j)ᶜ)
    exact ⟨i, hi⟩
  exact csInf_mem hne


lemma path_repr (s : ℝ≥0) : ∀ n, (stage G x π y n).path s =
    (∑ k ∈ Finset.range n, if (stage G x π y k).time ≤ (s : ℝ≥0∞) ∧
        (s : ℝ≥0∞) < (stage G x π y (k + 1)).time then y k s else 0) +
      (if (stage G x π y n).time ≤ (s : ℝ≥0∞) then y n s else 0) := by
  intro n
  induction n with
  | zero => simp [time_zero]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hs : (s : ℝ≥0∞) < (stage G x π y (n+1)).time
    · show (if (s : ℝ≥0∞) < (stage G x π y (n+1)).time then (stage G x π y n).path s
        else y (n + 1) s) = _
      rw [if_pos hs, ih, if_neg (not_le.mpr hs)]
      by_cases h2 : (stage G x π y n).time ≤ (s : ℝ≥0∞)
      · simp [h2, hs]
      · simp [h2]
    · show (if (s : ℝ≥0∞) < (stage G x π y (n+1)).time then (stage G x π y n).path s
        else y (n + 1) s) = _
      rw [if_neg hs, if_pos (not_lt.mp hs)]
      have hz : (∑ k ∈ Finset.range n, if (stage G x π y k).time ≤ (s : ℝ≥0∞) ∧
          (s : ℝ≥0∞) < (stage G x π y (k + 1)).time then y k s else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_range] at hk
        rw [if_neg]
        rintro ⟨-, h⟩
        apply hs
        exact lt_of_lt_of_le h (time_mono G x π y (by omega))
      rw [hz, if_neg (fun h => hs h.2)]
      simp

lemma jump (hinit : ∀ n, alive G x π y n → (stage G x π y n).time < ⊤ →
      y n (stage G x π y n).time.toNNReal = (stage G x π y n).post)
    (j : ℕ) (hj : alive G x π y j) (hlt : (stage G x π y j).time < ⊤)
    (hnext : alive G x π y (j+1) → (stage G x π y j).time < (stage G x π y (j+1)).time) :
    ctrl G x π y (stage G x π y j).time.toNNReal = (stage G x π y j).post := by
  have hc : (((stage G x π y j).time.toNNReal : ℝ≥0) : ℝ≥0∞) = (stage G x π y j).time :=
    ENNReal.coe_toNNReal hlt.ne
  have hpe : (stage G x π y j).path (stage G x π y j).time.toNNReal = (stage G x π y j).post := by
    rw [path_eq_y G x π y j _ (by rw [hc]), hinit j hj hlt]
  by_cases ha : alive G x π y (j+1)
  · rw [ctrl_eq_path G x π y j hj _ (by rw [hc]; exact hnext ha), hpe]
  · have hne : kbar G x π y ≠ ⊤ := fun h => ha ((kbar_top_iff G x π y).mp h _)
    obtain ⟨K, hK, hKa, hKn⟩ := kbar_fin G x π y hne
    have : K = j := by
      have h1 : j ≤ K := by
        have := alive_le_kbar G x π y j hj; rw [hK] at this; exact_mod_cast this
      have h2 : ¬ (j + 1 ≤ K) := fun h => ha (alive_mono G x π y h hKa)
      omega
    subst this
    rw [ctrl_eq_path_last G x π y K hK, hpe]

lemma pre_mem (hcont : ∀ n, alive G x π y n →
      ContinuousOn (y n) {s : ℝ≥0 | (stage G x π y n).time ≤ (s : ℝ≥0∞)})
    (hclosed : ∀ i, IsClosed (π.A i))
    (k : ℕ) (hk : alive G x π y (k+1)) (hlt : (stage G x π y (k+1)).time < ⊤) :
    (stage G x π y (k+1)).pre ∈ π.A (stage G x π y (k+1)).mover := by
  have hak : alive G x π y k := alive_mono G x π y (by omega) hk
  have hT : (stage G x π y (k+1)).time = exitAfter (stage G x π y k).path
      (stage G x π y k).time (π.A (stage G x π y (k+1)).mover)ᶜ := by
    rw [time_succ]; exact (mover_spec G π (stage G x π y k)).symm
  have hcp : ContinuousOn (stage G x π y k).path
      {s : ℝ≥0 | (stage G x π y k).time ≤ (s : ℝ≥0∞)} :=
    (hcont k hak).congr fun s hs => path_eq_y G x π y k s hs
  show (stage G x π y k).path (stage G x π y (k+1)).time.toNNReal ∈ _
  rw [hT] at hlt ⊢
  exact mem_at_exitAfter_compl _ _ _ (hclosed _) hcp hlt

end Path
end ImpPathDev

open ImpPathDev in
theorem solution {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (G : Game N d M) (V : Fin N → State d → ℝ)
    (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i)
    (x : State d) (hx : x ∈ G.S) (i : Fin N)
    (A : Set (State d)) (ξ' : State d → G.Imp i)
    (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsAdmissible P 𝔽 W G x ((starProfile G V ξ).update i A ξ') Y) :
    ∀ ω, ∀ j : Fin N, j ≠ i →
      (∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) <
          exitTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) →
          (s : ℝ≥0∞) ∉
            interventionTimes G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) →
          0 < ownOp G V ξ j
            (ctrl G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) s) -
            V j (ctrl G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) s)) ∧
      (∀ n : ℕ, 1 ≤ n →
        interTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n <
          exitTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) →
        ownOp G V ξ j
          (preState G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n) -
          V j (preState G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n) = 0 ∧
        impulse G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n =
          ξ j (preState G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n)) := by
  intro ω j hji
  set π := (starProfile G V ξ).update i A ξ' with hπ
  have hπA : π.A j = starAction G V ξ j := by
    show Function.update (starProfile G V ξ).A i A j = _
    rw [Function.update_of_ne hji]; rfl
  have hπξ : π.ξ j = ξ j := by
    show Function.update (starProfile G V ξ).ξ i ξ' j = _
    rw [Function.update_of_ne hji]; rfl
  have hR := hY.2.2.1
  have hcont : ∀ n, alive G x π (pathOf Y ω) n →
      ContinuousOn ((pathOf Y ω) n)
        {s : ℝ≥0 | (stage G x π (pathOf Y ω) n).time ≤ (s : ℝ≥0∞)} := by
    intro n hn
    have := (hR.1 n).1 ω
    simp only [if_pos hn] at this
    exact this
  have hlim := hR.2 ω
  have hclosed : ∀ i, IsClosed (π.A i) := fun i => (hY.1 i).1
  set y := pathOf Y ω with hy
  refine ⟨?_, ?_⟩
  · intro s hs0 hs hnot
    obtain ⟨k, hk, h1, h2, h3⟩ := segment_exists G x π y hlim s hs
    have hstrict : (stage G x π y k).time < s := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [time_zero]; exact_mod_cast hs0
      · obtain ⟨j', rfl⟩ : ∃ j', k = j' + 1 := ⟨k - 1, by omega⟩
        refine lt_of_le_of_ne h1 ?_
        intro heq
        apply hnot
        rw [← heq]
        exact time_mem_interventionTimes G x π y j' hk (by rw [heq]; exact hs)
    rw [ctrl_eq_path G x π y k hk s h2]
    have hS := path_mem_S G x π y k s hstrict h3
    have hA := path_not_mem G x π y k s hstrict h2 j
    rw [hπA] at hA
    have hge := (hi j).2.1 j _ hS
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exact absurd ⟨hS, h.symm⟩ hA
  · intro n hn hlt
    obtain ⟨k, hk, halive, hmov, hcount, hle, hIT⟩ := interTime_decode G x π y j n hn hlt
    have htop : (stage G x π y (k+1)).time < ⊤ := by
      rw [← hIT]; exact lt_of_lt_of_le hlt le_top
    have hpre : preState G x π y j n = (stage G x π y (k+1)).pre := by
      unfold preState; rw [hk]
    have hmem : preState G x π y j n ∈ π.A j := by
      rw [hpre, ← hmov]; exact pre_mem G x π y hcont hclosed k halive htop
    rw [hπA] at hmem
    refine ⟨hmem.2, ?_⟩
    unfold impulse; rw [if_pos hle, hπξ]
