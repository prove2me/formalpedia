-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedCompoundPoissonCylinderMarkov
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T12:01:49.945811+00:00
-- url     : https://prove2.me/submissions/82f216ad-8379-49ed-9b6f-e0e8e597da52

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace CylM

abbrev W := (ℕ → ℝ) × (ℕ → ℝ)
def τc : ℕ → W → ℝ := fun m w => w.1 m
def ξc : ℕ → W → ℝ := fun m w => w.2 m

noncomputable def T (w : W) (m : ℕ) : ℝ := arrival τc m w
noncomputable def jc (w : W) (t : ℝ) : ℕ := jumpCount (fun m => arrival τc m w) t
noncomputable def S (w : W) (n : ℕ) : ℝ := ∑ m ∈ Finset.range n, w.2 m

def Good (w : W) : Prop :=
  (∀ m, 0 < w.1 m) ∧ (∀ m, ∃ j : ℕ, w.2 m = (j : ℝ) - 1) ∧ (∀ L : ℝ, ∃ m, L < T w m)

noncomputable def G (y : ℕ) (n : ℕ) (w : W) : ℕ := by
  classical
  exact if ∃ m ≤ n, ⌊(y : ℝ) + S w m⌋ ≤ 0 then 0 else (⌊(y : ℝ) + S w n⌋).toNat

noncomputable def Φh (y : ℕ) (t : ℝ) (w : W) : ℕ := G y (jc w t) w

lemma T_zero (w : W) : T w 0 = w.1 0 := by simp [T, arrival, τc]
lemma T_succ (w : W) (m : ℕ) : T w (m + 1) = T w m + w.1 (m + 1) := by
  simp only [T, arrival, τc]; rw [Finset.sum_range_succ]

lemma T_strictMono (w : W) (hw : ∀ m, 0 < w.1 m) : StrictMono (T w) :=
  strictMono_nat_of_lt_succ (fun m => by rw [T_succ]; linarith [hw (m + 1)])

lemma T_pos (w : W) (hw : ∀ m, 0 < w.1 m) (m : ℕ) : 0 < T w m := by
  induction m with
  | zero => rw [T_zero]; exact hw 0
  | succ m ih => rw [T_succ]; linarith [hw (m + 1)]

lemma nat_sInf_eq_iff (A : Set ℕ) (hA : A.Nonempty) (n : ℕ) :
    sInf A = n ↔ n ∈ A ∧ ∀ m < n, m ∉ A := by
  constructor
  · rintro rfl; exact ⟨Nat.sInf_mem hA, fun m hm => Nat.notMem_of_lt_sInf hm⟩
  · rintro ⟨hn, hlt⟩
    apply le_antisymm (Nat.sInf_le hn)
    by_contra h
    exact hlt _ (not_le.1 h) (Nat.sInf_mem hA)

lemma jc_spec (w : W) (hw : Good w) (t : ℝ) (n : ℕ) :
    jc w t = n ↔ (∀ m < n, T w m ≤ t) ∧ t < T w n := by
  obtain ⟨m0, hm0⟩ := hw.2.2 t
  have hne : ({m | t < arrival τc m w} : Set ℕ).Nonempty := ⟨m0, hm0⟩
  unfold jc jumpCount
  rw [nat_sInf_eq_iff _ hne]
  simp only [Set.mem_ofPred_eq, not_lt]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

lemma jc_lt (w : W) (hw : Good w) (t : ℝ) : t < T w (jc w t) := ((jc_spec w hw t _).1 rfl).2
lemma jc_le (w : W) (hw : Good w) (t : ℝ) {m : ℕ} (hm : m < jc w t) : T w m ≤ t :=
  ((jc_spec w hw t _).1 rfl).1 m hm

lemma jc_le_of_lt (w : W) (t : ℝ) {m : ℕ} (h : t < T w m) : jc w t ≤ m :=
  Nat.sInf_le (show m ∈ {m | t < arrival τc m w} from h)

lemma jc_mono (w : W) (hw : Good w) {t t' : ℝ} (h : t ≤ t') : jc w t ≤ jc w t' :=
  jc_le_of_lt w t (lt_of_le_of_lt h (jc_lt w hw t'))

lemma jc_zero (w : W) (hw : Good w) : jc w 0 = 0 :=
  Nat.le_zero.1 (jc_le_of_lt w 0 (T_pos w hw.1 0))

lemma icp_eq (y : ℕ) (w : W) (t : ℝ≥0) :
    integerCompoundPoisson y τc ξc t w = ⌊(y : ℝ) + S w (jc w t)⌋ := by
  simp [integerCompoundPoisson, compoundPoisson, piecewisePath, S, jc, ξc]

lemma S_int (w : W) (hw : Good w) (n : ℕ) : ∃ K : ℤ, S w n = K := by
  induction n with
  | zero => exact ⟨0, by simp [S]⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨j, hj⟩ := hw.2.1 n
    refine ⟨K + j - 1, ?_⟩
    simp only [S, Finset.sum_range_succ] at hK ⊢
    rw [hK, hj]; push_cast; ring

/-- On good sequences, the stopping rule fires by `t` iff some pre-`t` partial sum is nonpositive. -/
lemma hit_iff (y : ℕ) (w : W) (hw : Good w) (t : ℝ≥0) :
    firstNonpositiveLattice (integerCompoundPoisson y τc ξc) w ≤ (t : WithTop ℝ≥0) ↔
      ∃ m ≤ jc w t, ⌊(y : ℝ) + S w m⌋ ≤ 0 := by
  classical
  constructor
  · intro h
    unfold firstNonpositiveLattice at h
    split_ifs at h with hex
    swap; · exact absurd h (not_le.2 (WithTop.coe_lt_top t))
    rw [WithTop.coe_le_coe] at h
    obtain ⟨s0, hs0⟩ := hex
    have hP : ∃ m, ⌊(y : ℝ) + S w m⌋ ≤ 0 := ⟨jc w s0, by rw [← icp_eq]; exact hs0⟩
    refine ⟨Nat.find hP, ?_, Nat.find_spec hP⟩
    by_contra hlt
    rw [not_le] at hlt
    set m := Nat.find hP with hm
    have hm1 : jc w t ≤ m - 1 := by omega
    have htm : (t : ℝ) < T w (m - 1) :=
      lt_of_lt_of_le (jc_lt w hw t) ((T_strictMono w hw.1).monotone hm1)
    have hlb : (T w (m - 1)).toNNReal ≤ sInf {s : ℝ≥0 | integerCompoundPoisson y τc ξc s w ≤ 0} := by
      apply le_csInf ⟨s0, hs0⟩
      intro u hu
      have hu' : ⌊(y : ℝ) + S w (jc w u)⌋ ≤ 0 := by rw [← icp_eq]; exact hu
      have hge : m ≤ jc w u := Nat.find_min' hP hu'
      have := jc_le w hw u (show m - 1 < jc w u by omega)
      exact Real.toNNReal_le_iff_le_coe.2 this
    have : t < (T w (m - 1)).toNNReal := Real.lt_toNNReal_iff_coe_lt.2 htm
    exact absurd (lt_of_lt_of_le this hlb) (not_lt.2 h)
  · rintro ⟨m, hm, hP⟩
    -- a time `u ≤ t` with `jc u = m`
    obtain ⟨u, hu, hju⟩ : ∃ u : ℝ≥0, u ≤ t ∧ jc w u = m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exact ⟨0, zero_le, by rw [h0]; exact jc_zero w hw⟩
      · refine ⟨(T w (m - 1)).toNNReal, ?_, ?_⟩
        · exact Real.toNNReal_le_iff_le_coe.2 (jc_le w hw t (by omega))
        · rw [Real.coe_toNNReal _ (T_pos w hw.1 _).le, jc_spec w hw]
          refine ⟨fun m' hm' => (T_strictMono w hw.1).monotone (by omega), ?_⟩
          exact (T_strictMono w hw.1) (by omega)
    have hX : integerCompoundPoisson y τc ξc u w ≤ 0 := by rw [icp_eq, hju]; exact hP
    unfold firstNonpositiveLattice
    rw [if_pos ⟨u, hX⟩, WithTop.coe_le_coe]
    exact (csInf_le (OrderBot.bddBelow _) (show u ∈ {s : ℝ≥0 | integerCompoundPoisson y τc ξc s w ≤ 0} from hX)).trans hu

lemma stopped_eq (y : ℕ) (w : W) (hw : Good w) (t : ℝ≥0) :
    (stoppedIntegerCompoundPoisson y τc ξc t w).toNat = Φh y t w := by
  classical
  unfold stoppedIntegerCompoundPoisson Φh G
  simp only
  by_cases h : ∃ m ≤ jc w t, ⌊(y : ℝ) + S w m⌋ ≤ 0
  · rw [if_pos ((hit_iff y w hw t).2 h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((hit_iff y w hw t).1 h')), if_neg h, icp_eq]

/-- The driver restarted at time `s`. -/
noncomputable def R (s : ℝ) (w : W) : W :=
  (fun i => if i = 0 then T w (jc w s) - s else w.1 (jc w s + i), fun i => w.2 (jc w s + i))

lemma T_R (s : ℝ) (w : W) (i : ℕ) : T (R s w) i = T w (jc w s + i) - s := by
  induction i with
  | zero => rw [T_zero]; simp [R]
  | succ i ih =>
    rw [T_succ, ih, show jc w s + (i + 1) = (jc w s + i) + 1 from rfl, T_succ]
    have : (R s w).1 (i + 1) = w.1 (jc w s + i + 1) := by simp [R]; rfl
    rw [this]; ring

lemma S_R (s : ℝ) (w : W) (i : ℕ) : S w (jc w s + i) = S w (jc w s) + S (R s w) i := by
  simp only [S, R]; rw [Finset.sum_range_add]

lemma good_R (s : ℝ) (w : W) (hw : Good w) : Good (R s w) := by
  refine ⟨fun i => ?_, fun i => hw.2.1 _, fun L => ?_⟩
  · by_cases hi : i = 0
    · simp only [R, hi, if_true]; linarith [jc_lt w hw s]
    · simp only [R, hi, if_false]; exact hw.1 _
  · obtain ⟨m, hm⟩ := hw.2.2 (L + s)
    refine ⟨m, ?_⟩
    rw [T_R]
    have := (T_strictMono w hw.1).monotone (show m ≤ jc w s + m by omega)
    linarith

lemma jc_R (s : ℝ) (w : W) (hw : Good w) {v : ℝ} (hv : 0 ≤ v) :
    jc w (s + v) = jc w s + jc (R s w) v := by
  have hR := (jc_spec (R s w) (good_R s w hw) v _).1 rfl
  rw [jc_spec w hw]
  refine ⟨fun m hm => ?_, ?_⟩
  · by_cases hmn : m < jc w s
    · linarith [jc_le w hw s hmn]
    · have h := hR.1 (m - jc w s) (by omega)
      rw [T_R, show jc w s + (m - jc w s) = m by omega] at h
      linarith
  · have h := hR.2; rw [T_R] at h; linarith

lemma Φh_restart (y : ℕ) (s : ℝ) (w : W) (hw : Good w) {v : ℝ} (hv : 0 ≤ v) :
    Φh y (s + v) w = Φh (Φh y s w) v (R s w) := by
  classical
  have hjc := jc_R s w hw hv
  unfold Φh G
  rw [hjc]
  set n := jc w s
  set j := jc (R s w) v
  by_cases h1 : ∃ m ≤ n, ⌊(y : ℝ) + S w m⌋ ≤ 0
  · obtain ⟨m, hm, hP⟩ := h1
    rw [if_pos (show ∃ m ≤ n, ⌊(y : ℝ) + S w m⌋ ≤ 0 from ⟨m, hm, hP⟩),
      if_pos (show ∃ m' ≤ n + j, ⌊(y : ℝ) + S w m'⌋ ≤ 0 from ⟨m, by omega, hP⟩),
      if_pos (show ∃ i ≤ j, ⌊((0 : ℕ) : ℝ) + S (R s w) i⌋ ≤ 0 from ⟨0, zero_le, by simp [S]⟩)]
  · rw [if_neg h1]
    obtain ⟨K, hK⟩ := S_int w hw n
    have hfl : ⌊(y : ℝ) + S w n⌋ = (y : ℤ) + K := by
      rw [hK, show (y : ℝ) + (K : ℝ) = (((y : ℤ) + K : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    have hK1 : 1 ≤ (y : ℤ) + K := by
      have hn : ¬ (⌊(y : ℝ) + S w n⌋ ≤ 0) := fun h => h1 ⟨n, le_rfl, h⟩
      rw [hfl] at hn; omega
    set z := (⌊(y : ℝ) + S w n⌋).toNat with hz
    have hzR : (z : ℝ) = (y : ℝ) + S w n := by
      rw [hz, hfl, hK]
      have : (((y : ℤ) + K).toNat : ℤ) = (y : ℤ) + K := Int.toNat_of_nonneg (by omega)
      have h2 : (((y : ℤ) + K).toNat : ℝ) = (((y : ℤ) + K : ℤ) : ℝ) := by exact_mod_cast this
      rw [h2]; push_cast; ring
    have key : ∀ i, (y : ℝ) + S w (n + i) = (z : ℝ) + S (R s w) i := by
      intro i; rw [S_R, hzR]; ring
    have hcond : (∃ m ≤ n + j, ⌊(y : ℝ) + S w m⌋ ≤ 0) ↔
        (∃ i ≤ j, ⌊(z : ℝ) + S (R s w) i⌋ ≤ 0) := by
      constructor
      · rintro ⟨m, hm, hP⟩
        by_cases hmn : m ≤ n
        · exact absurd ⟨m, hmn, hP⟩ h1
        · refine ⟨m - n, by omega, ?_⟩
          rw [← key, show n + (m - n) = m by omega]; exact hP
      · rintro ⟨i, hi, hP⟩
        exact ⟨n + i, by omega, by rw [key]; exact hP⟩
    by_cases hc : ∃ i ≤ j, ⌊(z : ℝ) + S (R s w) i⌋ ≤ 0
    · rw [if_pos (hcond.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hcond.1 h)), if_neg hc, key]

/-- The first `n` interarrivals and marks. -/
def past (n : ℕ) (w : W) : (Fin n → ℝ) × (Fin n → ℝ) := (fun i => w.1 i, fun i => w.2 i)

/-- Extend a finite past by inert interarrivals `s + 1` and zero marks. -/
noncomputable def trunc (n : ℕ) (s : ℝ) (v : (Fin n → ℝ) × (Fin n → ℝ)) : W :=
  (fun m => if h : m < n then v.1 ⟨m, h⟩ else s + 1, fun m => if h : m < n then v.2 ⟨m, h⟩ else 0)

lemma sInf_agree (A B : Set ℕ) (n : ℕ) (hA : n ∈ A) (hB : n ∈ B)
    (h : ∀ m < n, m ∈ A ↔ m ∈ B) : sInf A = sInf B := by
  have ha : sInf A ≤ n := Nat.sInf_le hA
  symm
  rw [nat_sInf_eq_iff B ⟨n, hB⟩]
  refine ⟨?_, fun m hm => ?_⟩
  · rcases lt_or_eq_of_le ha with hlt | heq
    · exact (h _ hlt).1 (Nat.sInf_mem ⟨n, hA⟩)
    · rw [heq]; exact hB
  · rw [← h m (by omega)]; exact Nat.notMem_of_lt_sInf hm

lemma Φh_trunc (y : ℕ) (s : ℝ) (w : W) (hw : Good w) {u : ℝ} (hu : u ≤ s) :
    Φh y u w = Φh y u (trunc (jc w s) s (past (jc w s) w)) := by
  classical
  set n := jc w s
  set w' := trunc n s (past n w)
  have h1 : ∀ m < n, w'.1 m = w.1 m := fun m hm => by simp [w', trunc, past, hm]
  have h2 : ∀ m < n, w'.2 m = w.2 m := fun m hm => by simp [w', trunc, past, hm]
  have hT : ∀ m < n, T w' m = T w m := by
    intro m hm
    simp only [T, arrival, τc]
    exact Finset.sum_congr rfl (fun i hi => h1 i (by simp at hi; omega))
  have hTn : s < T w' n := by
    simp only [T, arrival, τc]
    rw [Finset.sum_range_succ]
    have hlast : w'.1 n = s + 1 := by simp [w', trunc]
    rw [hlast]
    have : 0 ≤ ∑ i ∈ Finset.range n, w'.1 i := by
      apply Finset.sum_nonneg
      intro i hi; rw [h1 i (by simpa using hi)]; exact (hw.1 i).le
    linarith
  have hS : ∀ m ≤ n, S w' m = S w m := by
    intro m hm
    simp only [S]
    exact Finset.sum_congr rfl (fun i hi => h2 i (by simp at hi; omega))
  have hjc : jc w' u = jc w u := by
    unfold jc jumpCount
    apply sInf_agree _ _ n
    · show u < T w' n; linarith
    · show u < T w n; linarith [jc_lt w hw s]
    · intro m hm
      show u < T w' m ↔ u < T w m
      rw [hT m hm]
  have hJ : jc w u ≤ n := jc_mono w hw hu
  unfold Φh G
  rw [hjc]
  have hcond : (∃ m ≤ jc w u, ⌊(y : ℝ) + S w' m⌋ ≤ 0) ↔ (∃ m ≤ jc w u, ⌊(y : ℝ) + S w m⌋ ≤ 0) := by
    constructor
    · rintro ⟨m, hm, hP⟩; exact ⟨m, hm, by rw [← hS m (by omega)]; exact hP⟩
    · rintro ⟨m, hm, hP⟩; exact ⟨m, hm, by rw [hS m (by omega)]; exact hP⟩
  by_cases hc : ∃ m ≤ jc w u, ⌊(y : ℝ) + S w m⌋ ≤ 0
  · rw [if_pos hc, if_pos (hcond.2 hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hcond.1 h)), hS _ hJ]

lemma meas_T (m : ℕ) : Measurable (fun w : W => T w m) := by
  simp only [T, arrival, τc]
  exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_fst)

lemma meas_S (n : ℕ) : Measurable (fun w : W => S w n) := by
  simp only [S]
  exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_snd)

lemma nat_sInf_eq_iff' (A : Set ℕ) (n : ℕ) :
    sInf A = n ↔ (n ∈ A ∧ ∀ m < n, m ∉ A) ∨ ((∀ m, m ∉ A) ∧ n = 0) := by
  rcases A.eq_empty_or_nonempty with h | h
  · subst h; simp [eq_comm]
  · rw [nat_sInf_eq_iff A h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨h', -⟩)
      · exact h'
      · obtain ⟨m, hm⟩ := h; exact absurd hm (h' m)

lemma meas_jc (t : ℝ) : Measurable (fun w : W => jc w t) := by
  apply measurable_to_countable'
  intro n
  have : (fun w : W => jc w t) ⁻¹' {n} =
      ({w | t < T w n} ∩ {w | ∀ m, m < n → ¬ t < T w m}) ∪
        ({w | ∀ m, ¬ t < T w m} ∩ {_w | n = 0}) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    unfold jc jumpCount
    rw [nat_sInf_eq_iff']
    rfl
  rw [this]
  have hlt : ∀ m, MeasurableSet {w : W | t < T w m} := fun m => measurableSet_lt measurable_const (meas_T m)
  refine ((hlt n).inter ?_).union (MeasurableSet.inter ?_ (MeasurableSet.const _))
  · have : {w : W | ∀ m, m < n → ¬ t < T w m} = ⋂ m, {w | m < n → ¬ t < T w m} := by ext; simp
    rw [this]
    refine MeasurableSet.iInter (fun m => ?_)
    by_cases hm : m < n
    · simp only [hm, true_implies]; exact (hlt m).compl
    · simp [hm]
  · have : {w : W | ∀ m, ¬ t < T w m} = ⋂ m, {w | t < T w m}ᶜ := by ext; simp
    rw [this]; exact MeasurableSet.iInter (fun m => (hlt m).compl)

lemma meas_G (y n : ℕ) : Measurable (G y n) := by
  classical
  have hfl : ∀ m, Measurable (fun w : W => ⌊(y : ℝ) + S w m⌋) :=
    fun m => Int.measurable_floor.comp (measurable_const.add (meas_S m))
  have hset : MeasurableSet {w : W | ∃ m ≤ n, ⌊(y : ℝ) + S w m⌋ ≤ 0} := by
    have : {w : W | ∃ m ≤ n, ⌊(y : ℝ) + S w m⌋ ≤ 0} =
        ⋃ m ∈ Finset.range (n + 1), {w | ⌊(y : ℝ) + S w m⌋ ≤ 0} := by
      ext w; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ (fun m _ => measurableSet_le (hfl m) measurable_const)
  unfold G
  exact Measurable.ite hset measurable_const
    ((measurable_from_top (f := Int.toNat)).comp (hfl n))

lemma meas_Φh (y : ℕ) (t : ℝ) : Measurable (Φh y t) := by
  apply measurable_to_countable'
  intro k
  have : Φh y t ⁻¹' {k} = ⋃ n, ((fun w : W => jc w t) ⁻¹' {n} ∩ G y n ⁻¹' {k}) := by
    ext w; simp [Φh]
  rw [this]
  exact MeasurableSet.iUnion (fun n =>
    (meas_jc t (measurableSet_singleton n)).inter (meas_G y n (measurableSet_singleton k)))

lemma meas_trunc (n : ℕ) (s : ℝ) : Measurable (trunc n s) := by
  unfold trunc
  refine Measurable.prodMk (measurable_pi_lambda _ (fun m => ?_)) (measurable_pi_lambda _ (fun m => ?_))
  · by_cases h : m < n
    · simp only [h, dif_pos]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
  · by_cases h : m < n
    · simp only [h, dif_pos]; exact (measurable_pi_apply _).comp measurable_snd
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma meas_R_on (s : ℝ) (n : ℕ) :
    Measurable (fun w : W => (((fun i => if i = 0 then T w n - s else w.1 (n + i)),
      (fun i => w.2 (n + i))) : W)) := by
  refine Measurable.prodMk (measurable_pi_lambda _ (fun i => ?_)) (measurable_pi_lambda _ (fun i => ?_))
  · by_cases h : i = 0
    · simp only [h, if_true]; exact (meas_T n).sub measurable_const
    · simp only [h, if_false]; exact (measurable_pi_apply _).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

section Prob
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {rate : ℝ≥0} (hRate : 0 < rate) {τ ξ : ℕ → Ω → ℝ}
  {jumpLaw : Measure ℝ} [IsProbabilityMeasure jumpLaw]
  (hD : IsCompoundPoissonDriver τ ξ rate jumpLaw Q)

def seq (τ ξ : ℕ → Ω → ℝ) (ω : Ω) : W := (fun m => τ m ω, fun m => ξ m ω)

include hD in
lemma meas_seq : Measurable (seq τ ξ) :=
  Measurable.prodMk (measurable_pi_lambda _ hD.measurable_interarrival)
    (measurable_pi_lambda _ hD.measurable_mark)

include hRate hD in
lemma prob_le_N (m : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Q {ω | τ m ω ≤ N} = ENNReal.ofReal (1 - Real.exp (-((rate : ℝ) * N))) := by
  have hr : (0 : ℝ) < rate := hRate
  have := isProbabilityMeasure_expMeasure hr
  rw [(hD.law_interarrival m).measure_eq (p := fun x => x ≤ N) measurableSet_Iic,
    show {x : ℝ | x ≤ N} = Set.Iic N from rfl, ← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hN]

include hRate hD in
lemma ae_pos_all : ∀ᵐ ω ∂Q, ∀ m, 0 < τ m ω := by
  rw [ae_all_iff]
  intro m
  rw [ae_iff]
  have : {ω | ¬ 0 < τ m ω} = {ω | τ m ω ≤ 0} := by ext; simp
  rw [this, prob_le_N Q hRate hD m le_rfl]; simp

include hD in
lemma ae_mark_all (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1) :
    ∀ᵐ ω ∂Q, ∀ m, ∃ j : ℕ, ξ m ω = (j : ℝ) - 1 := by
  have hS : MeasurableSet {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} := by
    have : {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = Set.range (fun k : ℕ => (k : ℝ) - 1) := by
      ext x; simp [eq_comm]
    rw [this]; exact (Set.countable_range _).measurableSet
  have h1 : ∀ᵐ x ∂jumpLaw, ∃ k : ℕ, x = (k : ℝ) - 1 := by
    rw [ae_iff]
    have : {a : ℝ | ¬∃ k : ℕ, a = (k : ℝ) - 1} = {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1}ᶜ := rfl
    rw [this, prob_compl_eq_zero_iff hS]; exact hSupport
  rw [ae_all_iff]
  intro m
  exact ((hD.law_mark m).ae_iff (p := fun x => ∃ k : ℕ, x = (k : ℝ) - 1) (measurable_mem.2 hS)).2 h1

lemma single_le_T (w : W) (hw : ∀ m, 0 < w.1 m) (i : ℕ) : w.1 i ≤ T w i := by
  simp only [T, arrival, τc]
  exact Finset.single_le_sum (f := fun j => w.1 j) (fun j _ => (hw j).le)
    (Finset.mem_range.2 (Nat.lt_succ_self i))

include hRate hD in
lemma ae_div : ∀ᵐ ω ∂Q, ∀ L : ℝ, ∃ m, L < T (seq τ ξ ω) m := by
  have hr : (0 : ℝ) < rate := hRate
  suffices h : ∀ N : ℕ, ∀ᵐ ω ∂Q, ∃ m, (N : ℝ) < T (seq τ ξ ω) m by
    filter_upwards [ae_all_iff.2 h] with ω hω L
    obtain ⟨N, hN⟩ := exists_nat_ge L
    obtain ⟨m, hm⟩ := hω N
    exact ⟨m, lt_of_le_of_lt hN hm⟩
  intro N
  rw [ae_iff]
  set p : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-((rate : ℝ) * N))) with hp
  have hp1 : p < 1 := by
    rw [hp, ENNReal.ofReal_lt_one]; linarith [Real.exp_pos (-((rate : ℝ) * N))]
  have hpos := ae_pos_all Q hRate hD
  have hbound : ∀ M : ℕ, Q {ω | ¬∃ m, (N : ℝ) < T (seq τ ξ ω) m} ≤ p ^ M := by
    intro M
    have hsub : {ω | ¬∃ m, (N : ℝ) < T (seq τ ξ ω) m} ∩ {ω | ∀ m, 0 < τ m ω} ⊆
        ⋂ i ∈ Finset.range M, τ i ⁻¹' Set.Iic (N : ℝ) := by
      intro ω ⟨h1, h2⟩
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
      intro i _
      have := single_le_T (seq τ ξ ω) h2 i
      push Not at h1
      exact this.trans (h1 i)
    have hprod : Q (⋂ i ∈ Finset.range M, τ i ⁻¹' Set.Iic (N : ℝ)) = p ^ M := by
      have := hD.indep.measure_inter_preimage_eq_mul ((Finset.range M).image Sum.inl)
        (sets := fun _ => Set.Iic (N : ℝ)) (fun _ _ => measurableSet_Iic)
      rw [Finset.set_biInter_finset_image] at this
      simp only [Sum.elim_inl] at this
      rw [this, Finset.prod_image (fun a _ b _ h => Sum.inl_injective h)]
      simp only [Sum.elim_inl]
      rw [Finset.prod_congr rfl (fun i _ => (show Q (τ i ⁻¹' Set.Iic (N : ℝ)) = p from
          prob_le_N Q hRate hD i (Nat.cast_nonneg N))), Finset.prod_const, Finset.card_range]
    have hnull : Q {ω | ∀ m, 0 < τ m ω}ᶜ = 0 := hpos
    calc Q {ω | ¬∃ m, (N : ℝ) < T (seq τ ξ ω) m}
        ≤ Q ({ω | ¬∃ m, (N : ℝ) < T (seq τ ξ ω) m} ∩ {ω | ∀ m, 0 < τ m ω}) +
          Q {ω | ∀ m, 0 < τ m ω}ᶜ := by
          conv_lhs => rw [← Set.inter_union_compl {ω | ¬∃ m, (N : ℝ) < T (seq τ ξ ω) m}
            {ω | ∀ m, 0 < τ m ω}]
          exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_mono Set.inter_subset_right))
      _ ≤ p ^ M := by rw [hnull, add_zero, ← hprod]; exact measure_mono hsub
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp1) hbound)
    bot_le

include hRate hD in
lemma ae_good (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1) :
    ∀ᵐ ω ∂Q, Good (seq τ ξ ω) := by
  filter_upwards [ae_pos_all Q hRate hD, ae_mark_all Q hD hSupport, ae_div Q hRate hD]
    with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

lemma stopped_eq' (y : ℕ) (ω : Ω) (hω : Good (seq τ ξ ω)) (t : ℝ≥0) :
    (stoppedIntegerCompoundPoisson y τ ξ t ω).toNat = Φh y t (seq τ ξ ω) :=
  stopped_eq y (seq τ ξ ω) hω t

lemma tsum_partition {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℕ) (hg : Measurable g)
    (A : Set α) (hA : MeasurableSet A) : ∑' n, μ (A ∩ {a | g a = n}) = μ A := by
  rw [← measure_iUnion]
  · congr 1; ext a; simp
  · intro i j hij
    exact Set.disjoint_left.2 (fun a ha hb => hij (ha.2.symm.trans hb.2))
  · exact fun n => hA.inter (hg (measurableSet_singleton n))

end Prob

section Regen

/-- Independence of two functions measurable with respect to disjoint blocks of an
independent family. -/
lemma indepFun_blocks {Ω ι β γ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [MeasurableSpace β] [MeasurableSpace γ]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i)) (hind : iIndepFun G μ)
    {S₁ S₂ : Set ι} (hST : Disjoint S₁ S₂) (f : Ω → β) (g : Ω → γ)
    (hf : Measurable[⨆ i ∈ S₁, MeasurableSpace.comap (G i) inferInstance] f)
    (hg : Measurable[⨆ i ∈ S₂, MeasurableSpace.comap (G i) inferInstance] g) :
    IndepFun f g μ := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint (fun i => (hG i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 hind) hST
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h hf.comap_le) hg.comap_le

lemma coord_meas {Ω ι : Type*} [MeasurableSpace Ω] (G : ι → Ω → ℝ) (S₁ : Set ι) {i : ι}
    (hi : i ∈ S₁) : Measurable[⨆ i ∈ S₁, MeasurableSpace.comap (G i) inferInstance] (G i) :=
  (comap_measurable (G i)).mono (le_iSup₂ (f := fun i (_ : i ∈ S₁) =>
    MeasurableSpace.comap (G i) inferInstance) i hi) le_rfl

/-- Memorylessness of the exponential law. -/
lemma exp_shift {r : ℝ≥0} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a) :
    ((expMeasure r).restrict (Set.Ioi a)).map (fun x => x - a) =
      ENNReal.ofReal (Real.exp (-((r : ℝ) * a))) • expMeasure r := by
  have hr' : (0 : ℝ) < r := hr
  have := isProbabilityMeasure_expMeasure hr'
  have hfin : IsFiniteMeasure (((expMeasure r).restrict (Set.Ioi a)).map (fun x => x - a)) := by
    infer_instance
  have hm : Measurable (fun x : ℝ => x - a) := (continuous_sub_right a).measurable
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hm measurableSet_Iic,
    Measure.restrict_apply (hm measurableSet_Iic), Measure.smul_apply,
    smul_eq_mul]
  have hset : (fun x => x - a) ⁻¹' Set.Iic t ∩ Set.Ioi a = Set.Ioc a (a + t) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, ← measure_cdf (expMeasure r), StieltjesFunction.measure_Ioc, measure_cdf,
    ← ofReal_cdf, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    cdf_expMeasure_eq hr', cdf_expMeasure_eq hr', cdf_expMeasure_eq hr']
  by_cases ht : 0 ≤ t
  · congr 1
    rw [if_pos (by linarith), if_pos ha, if_pos ht]
    rw [show -((r : ℝ) * (a + t)) = -((r : ℝ) * a) + -((r : ℝ) * t) by ring, Real.exp_add]
    ring
  · rw [if_neg ht, mul_zero, ENNReal.ofReal_zero]
    apply ENNReal.ofReal_of_nonpos
    rw [if_pos ha]
    have h1 : Real.exp (-((r : ℝ) * a)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    split_ifs with hat
    · have : Real.exp (-((r : ℝ) * a)) ≤ Real.exp (-((r : ℝ) * (a + t))) :=
        Real.exp_le_exp.2 (by nlinarith)
      linarith
    · linarith

lemma memoryless_prod {β : Type*} [MeasurableSpace β] {r : ℝ≥0} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a)
    (μR : Measure β) [IsProbabilityMeasure μR] (D : Set (ℝ × β)) (hD : MeasurableSet D) :
    ((expMeasure r).prod μR) {p | a < p.1 ∧ (p.1 - a, p.2) ∈ D} =
      ENNReal.ofReal (Real.exp (-((r : ℝ) * a))) * ((expMeasure r).prod μR) D := by
  have hr' : (0 : ℝ) < r := hr
  have := isProbabilityMeasure_expMeasure hr'
  have hm : Measurable (fun x : ℝ => x - a) := (continuous_sub_right a).measurable
  have hf : Measurable (Prod.map (fun x : ℝ => x - a) (id : β → β)) :=
    hm.prodMap measurable_id
  have hset : {p : ℝ × β | a < p.1 ∧ (p.1 - a, p.2) ∈ D} =
      Prod.map (fun x : ℝ => x - a) id ⁻¹' D ∩ (Set.Ioi a ×ˢ Set.univ) := by
    ext p; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Prod.map,
      Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true, id]
    exact and_comm
  rw [hset, ← Measure.restrict_apply (hf hD), ← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.map_apply hf hD, ← Measure.map_prod_map _ _ hm measurable_id,
    Measure.map_id, exp_shift hr ha, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]

end Regen

section RegenMain
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {rate : ℝ≥0} (hRate : 0 < rate) {τ ξ : ℕ → Ω → ℝ}
  {jumpLaw : Measure ℝ} [IsProbabilityMeasure jumpLaw]
  (hD : IsCompoundPoissonDriver τ ξ rate jumpLaw Q)
include hD

lemma law_shift (n : ℕ) :
    Q.map (fun ω => (((fun i => τ (n + i) ω), (fun i => ξ (n + i) ω)) : W)) =
      Q.map (fun ω => (((fun i => τ i ω), (fun i => ξ i ω)) : W)) := by
  set Gf : ℕ ⊕ ℕ → Ω → ℝ := Sum.elim τ ξ
  have hGm : ∀ j, Measurable (Gf j) := by
    rintro (i | i)
    exacts [hD.measurable_interarrival i, hD.measurable_mark i]
  set sh : ℕ ⊕ ℕ → ℕ ⊕ ℕ := Sum.map (n + ·) (n + ·)
  have hsh : Function.Injective sh :=
    Sum.map_injective.2 ⟨fun a b h => by simpa using h, fun a b h => by simpa using h⟩
  have m1 := iIndepFun.map_fun_eq_infinitePi_map hGm hD.indep
  have m2 := iIndepFun.map_fun_eq_infinitePi_map (fun j => hGm (sh j)) (hD.indep.precomp hsh)
  have marg : (fun j => Q.map (Gf (sh j))) = (fun j => Q.map (Gf j)) := by
    funext j
    rcases j with i | i
    · exact (hD.law_interarrival (n + i)).map_eq.trans (hD.law_interarrival i).map_eq.symm
    · exact (hD.law_mark (n + i)).map_eq.trans (hD.law_mark i).map_eq.symm
  set e : (ℕ ⊕ ℕ → ℝ) → W := fun g => (fun i => g (Sum.inl i), fun i => g (Sum.inr i))
  have he : Measurable e :=
    Measurable.prodMk (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
      (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hv1 : Measurable (fun ω j => Gf j ω) := measurable_pi_lambda _ hGm
  have hv2 : Measurable (fun ω j => Gf (sh j) ω) := measurable_pi_lambda _ (fun j => hGm (sh j))
  have c1 : (fun ω => (((fun i => τ (n + i) ω), (fun i => ξ (n + i) ω)) : W)) =
      e ∘ (fun ω j => Gf (sh j) ω) := rfl
  have c2 : (fun ω => (((fun i => τ i ω), (fun i => ξ i ω)) : W)) = e ∘ (fun ω j => Gf j ω) := rfl
  rw [c1, c2, ← Measure.map_map he hv2, ← Measure.map_map he hv1, m1, m2, marg]

include hRate

theorem regen (s : ℝ) (hs : 0 ≤ s) (n : ℕ)
    (P : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hP : MeasurableSet P)
    (B : Set ((ℕ → ℝ) × (ℕ → ℝ))) (hB : MeasurableSet B) :
    Q ({ω | jumpCount (fun m => arrival τ m ω) s = n} ∩
        {ω | ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω)) ∈ P} ∩
        {ω | ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω),
              (fun i : ℕ => ξ (n + i) ω)) ∈ B}) =
      Q ({ω | jumpCount (fun m => arrival τ m ω) s = n} ∩
        {ω | ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω)) ∈ P}) *
      Q {ω | ((fun i : ℕ => τ i ω), (fun i : ℕ => ξ i ω)) ∈ B} := by
  classical
  have hr : (0 : ℝ) < rate := hRate
  have hexp := isProbabilityMeasure_expMeasure hr
  set Gf : ℕ ⊕ ℕ → Ω → ℝ := Sum.elim τ ξ with hGf
  have hGm : ∀ j, Measurable (Gf j) := by
    rintro (i | i)
    exacts [hD.measurable_interarrival i, hD.measurable_mark i]
  -- the three blocks
  set Vp : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω => ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω))
  set X : Ω → ℝ := fun ω => τ n ω
  set Rst : Ω → W := fun ω => ((fun j => τ (n + 1 + j) ω), (fun j => ξ (n + j) ω))
  set Sp : Set (ℕ ⊕ ℕ) := {j | ∃ i < n, j = Sum.inl i ∨ j = Sum.inr i}
  set Sx : Set (ℕ ⊕ ℕ) := {Sum.inl n}
  set Sr : Set (ℕ ⊕ ℕ) := {j | (∃ i, n < i ∧ j = Sum.inl i) ∨ (∃ i, n ≤ i ∧ j = Sum.inr i)}
  have hVpM : Measurable[⨆ j ∈ Sp, MeasurableSpace.comap (Gf j) inferInstance] Vp := by
    let _ : MeasurableSpace Ω := ⨆ j ∈ Sp, MeasurableSpace.comap (Gf j) inferInstance
    exact Measurable.prodMk
      (measurable_pi_lambda _ (fun i => coord_meas Gf Sp (i := Sum.inl i) ⟨i, i.2, Or.inl rfl⟩))
      (measurable_pi_lambda _ (fun i => coord_meas Gf Sp (i := Sum.inr i) ⟨i, i.2, Or.inr rfl⟩))
  have hXM : Measurable[⨆ j ∈ Sx, MeasurableSpace.comap (Gf j) inferInstance] X :=
    coord_meas Gf Sx (i := Sum.inl n) rfl
  have hRM : Measurable[⨆ j ∈ Sr, MeasurableSpace.comap (Gf j) inferInstance] Rst := by
    let _ : MeasurableSpace Ω := ⨆ j ∈ Sr, MeasurableSpace.comap (Gf j) inferInstance
    exact Measurable.prodMk
      (measurable_pi_lambda _ (fun j => coord_meas Gf Sr (i := Sum.inl (n + 1 + j))
        (Or.inl ⟨n + 1 + j, by omega, rfl⟩)))
      (measurable_pi_lambda _ (fun j => coord_meas Gf Sr (i := Sum.inr (n + j))
        (Or.inr ⟨n + j, by omega, rfl⟩)))
  have hXRM : Measurable[⨆ j ∈ Sx ∪ Sr, MeasurableSpace.comap (Gf j) inferInstance]
      (fun ω => (X ω, Rst ω)) := by
    let _ : MeasurableSpace Ω := ⨆ j ∈ Sx ∪ Sr, MeasurableSpace.comap (Gf j) inferInstance
    refine Measurable.prodMk ?_ ?_
    · exact hXM.mono (iSup₂_mono' (fun j hj => ⟨j, Or.inl hj, le_rfl⟩)) le_rfl
    · exact hRM.mono (iSup₂_mono' (fun j hj => ⟨j, Or.inr hj, le_rfl⟩)) le_rfl
  have hd1 : Disjoint Sp (Sx ∪ Sr) := by
    rw [Set.disjoint_left]
    rintro j ⟨i, hi, h | h⟩ h2 <;> subst h <;>
      rcases h2 with h2 | ⟨i', hi', h2⟩ | ⟨i', hi', h2⟩ <;> simp_all [Sx] <;> omega
  have hd2 : Disjoint Sx Sr := by
    rw [Set.disjoint_left]
    rintro j hj h2
    simp only [Sx, Set.mem_singleton_iff] at hj
    subst hj
    rcases h2 with ⟨i', hi', h2⟩ | ⟨i', hi', h2⟩ <;> simp_all <;> omega
  have hI1 := indepFun_blocks Gf hGm hD.indep hd1 Vp (fun ω => (X ω, Rst ω)) hVpM hXRM
  have hI2 := indepFun_blocks Gf hGm hD.indep hd2 X Rst hXM hRM
  -- global measurability
  have mVp : Measurable Vp := Measurable.prodMk
    (measurable_pi_lambda _ (fun i => hD.measurable_interarrival _))
    (measurable_pi_lambda _ (fun i => hD.measurable_mark _))
  have mX : Measurable X := hD.measurable_interarrival n
  have mR : Measurable Rst := Measurable.prodMk
    (measurable_pi_lambda _ (fun i => hD.measurable_interarrival _))
    (measurable_pi_lambda _ (fun i => hD.measurable_mark _))
  have mXR : Measurable (fun ω => (X ω, Rst ω)) := mX.prodMk mR
  set μV := Q.map Vp
  set μR := Q.map Rst
  have hμV : IsProbabilityMeasure μV := Measure.isProbabilityMeasure_map mVp.aemeasurable
  have hμR : IsProbabilityMeasure μR := Measure.isProbabilityMeasure_map mR.aemeasurable
  have hlawXR : Q.map (fun ω => (X ω, Rst ω)) = (expMeasure rate).prod μR := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map mX.aemeasurable mR.aemeasurable).1 hI2,
      (hD.law_interarrival n).map_eq]
  have hjoint : Q.map (fun ω => (Vp ω, (X ω, Rst ω))) = μV.prod ((expMeasure rate).prod μR) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map mVp.aemeasurable mXR.aemeasurable).1 hI1, hlawXR]
  -- deterministic functionals of the blocks
  set Tv : (Fin n → ℝ) × (Fin n → ℝ) → ℕ → ℝ := fun v m =>
    ∑ i ∈ Finset.range (m + 1), (if h : i < n then v.1 ⟨i, h⟩ else 0)
  set Wv : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun v =>
    ∑ i ∈ Finset.range n, (if h : i < n then v.1 ⟨i, h⟩ else 0)
  set av : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun v => s - Wv v
  set Φ : ℝ × W → W := fun p => ((fun i => if i = 0 then p.1 else p.2.1 (i - 1)), p.2.2)
  set P' : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {v | v ∈ P ∧ ∀ m < n, Tv v m ≤ s}
  have mcoord : ∀ i, Measurable (fun v : (Fin n → ℝ) × (Fin n → ℝ) =>
      (if h : i < n then v.1 ⟨i, h⟩ else 0)) := by
    intro i
    by_cases h : i < n
    · simp only [h, dif_pos]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
  have mTv : ∀ m, Measurable (fun v => Tv v m) := fun m =>
    Finset.measurable_sum _ (fun i _ => mcoord i)
  have mWv : Measurable Wv := Finset.measurable_sum _ (fun i _ => mcoord i)
  have mav : Measurable av := measurable_const.sub mWv
  have mΦ : Measurable Φ := by
    refine Measurable.prodMk (measurable_pi_lambda _ (fun i => ?_)) ((measurable_snd).comp measurable_snd)
    by_cases hi : i = 0
    · simp only [Φ, hi, if_true]; exact measurable_fst
    · simp only [Φ, hi, if_false]
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  have mP' : MeasurableSet P' := by
    have : P' = P ∩ ⋂ m, {v | m < n → Tv v m ≤ s} := by ext v; simp [P']
    rw [this]
    refine hP.inter (MeasurableSet.iInter (fun m => ?_))
    by_cases hm : m < n
    · simp only [hm, true_implies]; exact measurableSet_le (mTv m) measurable_const
    · simp [hm]
  set E : Set W → Set (((Fin n → ℝ) × (Fin n → ℝ)) × (ℝ × W)) := fun B' =>
    {q | q.1 ∈ P' ∧ av q.1 < q.2.1 ∧ Φ (q.2.1 - av q.1, q.2.2) ∈ B'}
  have mE : ∀ B', MeasurableSet B' → MeasurableSet (E B') := by
    intro B' hB'
    have : E B' = (Prod.fst ⁻¹' P') ∩ {q | av q.1 < q.2.1} ∩
        (fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (ℝ × W) => Φ (q.2.1 - av q.1, q.2.2)) ⁻¹' B' := by
      ext q; simp [E, and_assoc]
    rw [this]
    refine ((measurable_fst mP').inter (measurableSet_lt (mav.comp measurable_fst)
      (measurable_fst.comp measurable_snd))).inter ?_
    exact (mΦ.comp (((measurable_fst.comp measurable_snd).sub (mav.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_snd))) hB'
  -- pointwise identities
  have hTv : ∀ ω, ∀ m < n, Tv (Vp ω) m = arrival τ m ω := by
    intro ω m hm
    simp only [Tv, arrival]
    exact Finset.sum_congr rfl (fun i hi => by
      have : i < n := by simp at hi; omega
      simp [Vp, this])
  have hTn : ∀ ω, arrival τ n ω = Wv (Vp ω) + X ω := by
    intro ω
    simp only [arrival, Wv, X]
    rw [Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => by
      have : i < n := by simpa using hi
      simp [Vp, this])
  have hΦfut : ∀ ω, Φ (X ω - av (Vp ω), Rst ω) =
      ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω), (fun i : ℕ => ξ (n + i) ω)) := by
    intro ω
    simp only [Φ, av, Rst, hTn ω]
    refine Prod.ext (funext (fun i => ?_)) rfl
    by_cases hi : i = 0
    · simp only [hi, if_true]; ring
    · simp only [hi, if_false]; congr 1; omega
  have hΦshift : ∀ ω, Φ (X ω, Rst ω) = (((fun i => τ (n + i) ω), (fun i => ξ (n + i) ω)) : W) := by
    intro ω
    refine Prod.ext (funext (fun i => ?_)) rfl
    by_cases hi : i = 0
    · simp [Φ, hi, X]
    · simp only [Φ, hi, if_false, Rst]; congr 1; omega
  -- the a.e. identification of the events
  have hdiv := ae_div Q hRate hD
  have hJ : ∀ ω, (∃ m, s < arrival τ m ω) →
      (jumpCount (fun m => arrival τ m ω) s = n ↔ (∀ m < n, arrival τ m ω ≤ s) ∧ s < arrival τ n ω) := by
    intro ω hne
    obtain ⟨m0, hm0⟩ := hne
    unfold jumpCount
    show sInf {m | s < arrival τ m ω} = n ↔ _
    rw [nat_sInf_eq_iff {m | s < arrival τ m ω} ⟨m0, hm0⟩]
    simp only [Set.mem_ofPred_eq, not_lt]
    exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  have hev : ∀ B', ({ω | jumpCount (fun m => arrival τ m ω) s = n} ∩
        {ω | ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω)) ∈ P} ∩
        {ω | ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω),
              (fun i : ℕ => ξ (n + i) ω)) ∈ B'} : Set Ω) =ᵐ[Q]
      ((fun ω => (Vp ω, (X ω, Rst ω))) ⁻¹' E B' : Set Ω) := by
    intro B'
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [hdiv] with ω hω
    have hne : ∃ m, s < arrival τ m ω := hω s
    show ((jumpCount (fun m => arrival τ m ω) s = n ∧ Vp ω ∈ P) ∧
        ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω), (fun i : ℕ => ξ (n + i) ω)) ∈ B') ↔
      ((Vp ω ∈ P ∧ ∀ m < n, Tv (Vp ω) m ≤ s) ∧ av (Vp ω) < X ω ∧ Φ (X ω - av (Vp ω), Rst ω) ∈ B')
    rw [hJ ω hne, hΦfut ω, hTn ω]
    have h2 : (∀ m < n, arrival τ m ω ≤ s) ↔ (∀ m < n, Tv (Vp ω) m ≤ s) :=
      ⟨fun h m hm => by rw [hTv ω m hm]; exact h m hm, fun h m hm => by rw [← hTv ω m hm]; exact h m hm⟩
    rw [h2]
    have h3 : s < Wv (Vp ω) + X ω ↔ av (Vp ω) < X ω := by simp only [av]; constructor <;> intro h <;> linarith
    rw [h3]
    tauto
  -- measure of the product-space events
  have hav0 : ∀ v ∈ P', 0 ≤ av v := by
    intro v hv
    simp only [av, sub_nonneg]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [Wv, h0, hs]
    · have := hv.2 (n - 1) (by omega)
      simpa [Tv, Wv, show n - 1 + 1 = n by omega] using this
  set ν := (expMeasure rate).prod μR
  have hνprob : IsProbabilityMeasure ν := by infer_instance
  have hcomp : ∀ B', MeasurableSet B' →
      Q ((fun ω => (Vp ω, (X ω, Rst ω))) ⁻¹' E B') =
        (∫⁻ v, P'.indicator (fun v => ENNReal.ofReal (Real.exp (-((rate : ℝ) * av v)))) v ∂μV) *
          ν (Φ ⁻¹' B') := by
    intro B' hB'
    have hf0 : Measurable (fun v => ENNReal.ofReal (Real.exp (-((rate : ℝ) * av v)))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_const.mul mav).neg))
    rw [← Measure.map_apply (mVp.prodMk mXR) (mE B' hB'), hjoint, Measure.prod_apply (mE B' hB'),
      ← lintegral_mul_const _ (hf0.indicator mP')]
    refine lintegral_congr (fun v => ?_)
    by_cases hv : v ∈ P'
    · rw [Set.indicator_of_mem hv]
      have hsec : Prod.mk v ⁻¹' E B' = {p : ℝ × W | av v < p.1 ∧ (p.1 - av v, p.2) ∈ Φ ⁻¹' B'} := by
        ext p; simp [E, hv]
      rw [hsec, memoryless_prod hRate (hav0 v hv) μR _ (mΦ hB')]
    · rw [Set.indicator_of_notMem hv, zero_mul]
      have hsec : Prod.mk v ⁻¹' E B' = ∅ := by ext p; simp [E, hv]
      rw [hsec, measure_empty]
  have hB1 : ν (Φ ⁻¹' B) = Q {ω | ((fun i : ℕ => τ i ω), (fun i : ℕ => ξ i ω)) ∈ B} := by
    rw [← hlawXR, Measure.map_apply mXR (mΦ hB)]
    have : (fun ω => (X ω, Rst ω)) ⁻¹' (Φ ⁻¹' B) =
        (fun ω => (((fun i => τ (n + i) ω), (fun i => ξ (n + i) ω)) : W)) ⁻¹' B := by
      ext ω; simp only [Set.mem_preimage, hΦshift ω]
    rw [this, ← Measure.map_apply _ hB, law_shift Q hD n, Measure.map_apply _ hB]
    · rfl
    · exact (meas_seq Q hD)
    · exact Measurable.prodMk (measurable_pi_lambda _ (fun i => hD.measurable_interarrival _))
        (measurable_pi_lambda _ (fun i => hD.measurable_mark _))
  have hev0 : ({ω | jumpCount (fun m => arrival τ m ω) s = n} ∩
        {ω | ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω)) ∈ P} : Set Ω) =ᵐ[Q]
      ((fun ω => (Vp ω, (X ω, Rst ω))) ⁻¹' E Set.univ : Set Ω) := by
    refine (Filter.EventuallyEq.trans ?_ (hev Set.univ))
    refine Filter.eventuallyEq_set.2 (Eventually.of_forall (fun ω => ?_))
    simp
  rw [measure_congr (hev B), measure_congr hev0, hcomp B hB, hcomp Set.univ MeasurableSet.univ,
    Set.preimage_univ, measure_univ, mul_one, hB1]

end RegenMain

section Glue
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {rate : ℝ≥0} (hRate : 0 < rate) {τ ξ : ℕ → Ω → ℝ}
  {jumpLaw : Measure ℝ} [IsProbabilityMeasure jumpLaw]
  (hD : IsCompoundPoissonDriver τ ξ rate jumpLaw Q)
include hRate hD

lemma markov_Φh (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (y m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ) (hu : ∀ i, u i ≤ s) :
    Q ({ω | ∀ i, Φh y (u i) (seq τ ξ ω) = v i} ∩ {ω | Φh y ((s : ℝ) + t) (seq τ ξ ω) = k}) =
      ∑' z : ℕ, Q ({ω | ∀ i, Φh y (u i) (seq τ ξ ω) = v i} ∩ {ω | Φh y s (seq τ ξ ω) = z}) *
        Q {ω | Φh z t (seq τ ξ ω) = k} := by
  classical
  set f := seq τ ξ with hf
  have mf : Measurable f := meas_seq Q hD
  have hgood := ae_good Q hRate hD hSupport
  set Ev := {ω | ∀ i, Φh y (u i) (f ω) = v i} with hEv
  have mEv : MeasurableSet Ev := by
    have : Ev = ⋂ i, (fun ω => Φh y (u i) (f ω)) ⁻¹' {v i} := by ext; simp [Ev]
    rw [this]
    exact MeasurableSet.iInter (fun i => ((meas_Φh y _).comp mf) (measurableSet_singleton _))
  have mpre : ∀ (z : ℕ) (r : ℝ), MeasurableSet {ω | Φh z r (f ω) = k} := fun z r =>
    ((meas_Φh z r).comp mf) (measurableSet_singleton _)
  have mpre' : ∀ (z : ℕ) (r : ℝ) (a : ℕ), MeasurableSet {ω | Φh z r (f ω) = a} := fun z r a =>
    ((meas_Φh z r).comp mf) (measurableSet_singleton _)
  have mjc : Measurable (fun ω => jc (f ω) s) := (meas_jc s).comp mf
  rw [← tsum_partition Q (fun ω => Φh y s (f ω)) ((meas_Φh y s).comp mf) _ (mEv.inter (mpre y _))]
  congr 1; funext z
  rw [← tsum_partition Q (fun ω => jc (f ω) s) mjc _ ((mEv.inter (mpre y _)).inter (mpre' y s z)),
    ← tsum_partition Q (fun ω => jc (f ω) s) mjc _ (mEv.inter (mpre' y s z)), ← ENNReal.tsum_mul_right]
  congr 1; funext n
  set P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | (∀ i, Φh y (u i) (trunc n s p) = v i) ∧ Φh y s (trunc n s p) = z} with hP
  have mP : MeasurableSet P := by
    have : P = (⋂ i, (fun p => Φh y (u i) (trunc n s p)) ⁻¹' {v i}) ∩
        (fun p => Φh y s (trunc n s p)) ⁻¹' {z} := by ext; simp [P]
    rw [this]
    exact (MeasurableSet.iInter (fun i => ((meas_Φh y _).comp (meas_trunc n s))
      (measurableSet_singleton _))).inter (((meas_Φh y _).comp (meas_trunc n s)) (measurableSet_singleton _))
  set B : Set W := {w | Φh z t w = k} with hB
  have mB : MeasurableSet B := (meas_Φh z t) (measurableSet_singleton k)
  have hreg := regen Q hRate hD s (NNReal.coe_nonneg s) n P mP B mB
  -- pathwise facts on the good set with `jc = n`
  have hpath : ∀ ω, Good (f ω) → jc (f ω) s = n →
      (∀ r : ℝ, r ≤ s → Φh y r (f ω) = Φh y r (trunc n s (past n (f ω)))) ∧
      Φh y ((s : ℝ) + t) (f ω) = Φh (Φh y s (f ω)) t
        ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω),
          (fun i : ℕ => ξ (n + i) ω)) := by
    intro ω hω hn
    refine ⟨fun r hr => ?_, ?_⟩
    · have := Φh_trunc y s (f ω) hω hr
      rw [hn] at this; exact this
    · rw [Φh_restart y s (f ω) hω (NNReal.coe_nonneg t)]
      congr 1
      simp only [R, hn]
      rfl
  have E1 : ((Ev ∩ {ω | Φh y ((s : ℝ) + t) (f ω) = k}) ∩ {ω | Φh y s (f ω) = z} ∩
        {ω | jc (f ω) s = n} : Set Ω) =ᵐ[Q]
      ({ω | jumpCount (fun m => arrival τ m ω) s = n} ∩
        {ω | ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω)) ∈ P} ∩
        {ω | ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω),
              (fun i : ℕ => ξ (n + i) ω)) ∈ B} : Set Ω) := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [hgood] with ω hω
    show ((((∀ i, Φh y (u i) (f ω) = v i) ∧ Φh y ((s : ℝ) + t) (f ω) = k) ∧ Φh y s (f ω) = z) ∧
        jc (f ω) s = n) ↔ ((jc (f ω) s = n ∧
          ((∀ i, Φh y (u i) (trunc n s (past n (f ω))) = v i) ∧
            Φh y s (trunc n s (past n (f ω))) = z)) ∧
          Φh z t ((fun i : ℕ => if i = 0 then arrival τ n ω - s else τ (n + i) ω),
            (fun i : ℕ => ξ (n + i) ω)) = k)
    constructor
    · rintro ⟨⟨⟨hA, hk⟩, hz⟩, hn⟩
      obtain ⟨htr, hrs⟩ := hpath ω hω hn
      refine ⟨⟨hn, fun i => ?_, ?_⟩, ?_⟩
      · rw [← htr _ (by exact_mod_cast hu i)]; exact hA i
      · rw [← htr _ le_rfl]; exact hz
      · rw [← hz, ← hrs]; exact hk
    · rintro ⟨⟨hn, hA, hz⟩, hk⟩
      obtain ⟨htr, hrs⟩ := hpath ω hω hn
      have hz' : Φh y s (f ω) = z := by rw [htr _ le_rfl]; exact hz
      refine ⟨⟨⟨fun i => ?_, ?_⟩, hz'⟩, hn⟩
      · rw [htr _ (by exact_mod_cast hu i)]; exact hA i
      · rw [hrs, hz']; exact hk
  have E2 : ((Ev ∩ {ω | Φh y s (f ω) = z}) ∩ {ω | jc (f ω) s = n} : Set Ω) =ᵐ[Q]
      ({ω | jumpCount (fun m => arrival τ m ω) s = n} ∩
        {ω | ((fun i : Fin n => τ i ω), (fun i : Fin n => ξ i ω)) ∈ P} : Set Ω) := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [hgood] with ω hω
    show (((∀ i, Φh y (u i) (f ω) = v i) ∧ Φh y s (f ω) = z) ∧ jc (f ω) s = n) ↔
        (jc (f ω) s = n ∧ ((∀ i, Φh y (u i) (trunc n s (past n (f ω))) = v i) ∧
            Φh y s (trunc n s (past n (f ω))) = z))
    constructor
    · rintro ⟨⟨hA, hz⟩, hn⟩
      obtain ⟨htr, -⟩ := hpath ω hω hn
      exact ⟨hn, fun i => by rw [← htr _ (by exact_mod_cast hu i)]; exact hA i,
        by rw [← htr _ le_rfl]; exact hz⟩
    · rintro ⟨hn, hA, hz⟩
      obtain ⟨htr, -⟩ := hpath ω hω hn
      exact ⟨⟨fun i => by rw [htr _ (by exact_mod_cast hu i)]; exact hA i,
        by rw [htr _ le_rfl]; exact hz⟩, hn⟩
  rw [measure_congr E1, hreg, ← measure_congr E2]
  rfl

end Glue

lemma stopped_nonneg {Ω : Type*} (y : ℕ) (τ ξ : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ stoppedIntegerCompoundPoisson y τ ξ t ω := by
  unfold stoppedIntegerCompoundPoisson
  simp only
  split_ifs with h
  · exact le_rfl
  · by_contra hneg
    rw [not_le] at hneg
    apply h
    unfold firstNonpositiveLattice
    rw [if_pos ⟨t, hneg.le⟩, WithTop.coe_le_coe]
    exact csInf_le (OrderBot.bddBelow _)
      (show t ∈ {s : ℝ≥0 | integerCompoundPoisson y τ ξ s ω ≤ 0} from hneg.le)

lemma Φh_zero (y : ℕ) (w : W) (hw : Good w) : Φh y 0 w = y := by
  classical
  unfold Φh G
  rw [jc_zero w hw]
  have hS0 : S w 0 = 0 := by simp [S]
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; rw [if_pos ⟨0, le_rfl, by simp [hS0]⟩]
  · rw [if_neg]
    · simp [hS0]
    · rintro ⟨m, hm, hP⟩
      rw [Nat.le_zero.1 hm, hS0, add_zero, Int.floor_natCast] at hP
      omega

end CylM

theorem solution
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1) :
    ∀ y : ℕ,
      (∀ t : ℝ≥0, ∀ᵐ ω ∂Q,
        0 ≤ stoppedIntegerCompoundPoisson y arrival marks t ω) ∧
      (∀ t : ℝ≥0, AEMeasurable
        (fun ω => (stoppedIntegerCompoundPoisson y arrival marks t ω).toNat) Q) ∧
      Q {ω | (stoppedIntegerCompoundPoisson y arrival marks 0 ω).toNat = y} = 1 ∧
      ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
        (∀ i, u i ≤ s) →
        Q ({ω | ∀ i,
              (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
            {ω | (stoppedIntegerCompoundPoisson y arrival marks (s + t) ω).toNat = k}) =
          ∑' z : ℕ, Q ({ω | ∀ i,
              (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
            {ω | (stoppedIntegerCompoundPoisson y arrival marks s ω).toNat = z}) *
            Q {ω | (stoppedIntegerCompoundPoisson z arrival marks t ω).toNat = k}  := by
  intro y
  have hgood := CylM.ae_good Q hRate hDriver hSupport
  have mf := CylM.meas_seq Q hDriver
  have hst : ∀ (z : ℕ) (r : ℝ≥0), ∀ᵐ ω ∂Q,
      (stoppedIntegerCompoundPoisson z arrival marks r ω).toNat =
        CylM.Φh z r (CylM.seq arrival marks ω) := fun z r => by
    filter_upwards [hgood] with ω hω
    exact CylM.stopped_eq' z ω hω r
  refine ⟨fun t => Eventually.of_forall (fun ω => CylM.stopped_nonneg y arrival marks t ω),
    fun t => ?_, ?_, ?_⟩
  · exact ((CylM.meas_Φh y t).comp mf).aemeasurable.congr
      (by filter_upwards [hst y t] with ω h; exact h.symm)
  · have : {ω | (stoppedIntegerCompoundPoisson y arrival marks 0 ω).toNat = y} =ᵐ[Q]
        (Set.univ : Set Ω') := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [hgood] with ω hω
      show (stoppedIntegerCompoundPoisson y arrival marks 0 ω).toNat = y ↔ ω ∈ Set.univ
      rw [CylM.stopped_eq' y ω hω 0, NNReal.coe_zero, CylM.Φh_zero y _ hω]
      simp
    rw [measure_congr this, measure_univ]
  · intro m u v s t k hu
    have hL : ({ω | ∀ i, (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
        {ω | (stoppedIntegerCompoundPoisson y arrival marks (s + t) ω).toNat = k} : Set Ω') =ᵐ[Q]
        ({ω | ∀ i, CylM.Φh y (u i) (CylM.seq arrival marks ω) = v i} ∩
          {ω | CylM.Φh y ((s : ℝ) + t) (CylM.seq arrival marks ω) = k} : Set Ω') := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [hgood] with ω hω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, CylM.stopped_eq' y ω hω, NNReal.coe_add]
    have hR : ∀ z : ℕ,
        ({ω | ∀ i, (stoppedIntegerCompoundPoisson y arrival marks (u i) ω).toNat = v i} ∩
          {ω | (stoppedIntegerCompoundPoisson y arrival marks s ω).toNat = z} : Set Ω') =ᵐ[Q]
        ({ω | ∀ i, CylM.Φh y (u i) (CylM.seq arrival marks ω) = v i} ∩
          {ω | CylM.Φh y s (CylM.seq arrival marks ω) = z} : Set Ω') := by
      intro z
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [hgood] with ω hω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, CylM.stopped_eq' y ω hω]
    have hK : ∀ z : ℕ,
        ({ω | (stoppedIntegerCompoundPoisson z arrival marks t ω).toNat = k} : Set Ω') =ᵐ[Q]
        ({ω | CylM.Φh z t (CylM.seq arrival marks ω) = k} : Set Ω') := by
      intro z
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [hgood] with ω hω
      simp only [CylM.stopped_eq' z ω hω]
    rw [measure_congr hL, CylM.markov_Φh Q hRate hDriver hSupport y m u v s t k hu]
    congr 1; funext z
    rw [measure_congr (hR z), measure_congr (hK z)]
