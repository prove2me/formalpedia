-- Prove2me | solution 1 for NondomArb.Superhedge.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:56:49.314367+00:00
-- url     : https://prove2.me/submissions/f215088e-34d4-4389-a0b9-799752a29d6d

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_General
open MeasureTheory Filter Topology NondomArb.Superhedge.General
open NondomArb.Superhedge

namespace Thm22Aux

open Classical

/-! ### Measurable random subsequences (Kabanov–Stricker, Lemma 2) -/

section Select
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma meas_comp_nat {β : Type*} [MeasurableSpace β] {σ : Ω → ℕ} (hσ : Measurable σ)
    {g : ℕ → Ω → β} (hg : ∀ n, Measurable (g n)) : Measurable fun ω => g (σ ω) ω := by
  intro B hB
  have : (fun ω => g (σ ω) ω) ⁻¹' B = ⋃ n, ({ω | σ ω = n} ∩ g n ⁻¹' B) := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun n => (hσ (measurableSet_singleton n)).inter (hg n hB)

lemma exists_after (p : ℕ → ℕ → Ω → Prop) (hp : ∀ k ω, ∃ᶠ n in atTop, p k n ω) (k t : ℕ)
    (ω : Ω) : ∃ n, t < n ∧ p k n ω := by
  obtain ⟨b, hb, hpb⟩ := frequently_atTop.mp (hp k ω) (t+1)
  exact ⟨b, by omega, hpb⟩

/-- The `k`-th selected index: the first index after the previous one satisfying `p k`. -/
noncomputable def subseq (p : ℕ → ℕ → Ω → Prop) (hp : ∀ k ω, ∃ᶠ n in atTop, p k n ω) :
    ℕ → Ω → ℕ
  | 0, ω => Nat.find (exists_after p hp 0 0 ω)
  | k+1, ω => Nat.find (exists_after p hp (k+1) (subseq p hp k ω) ω)

lemma subseq_spec (p : ℕ → ℕ → Ω → Prop) (hp : ∀ k ω, ∃ᶠ n in atTop, p k n ω) (k : ℕ)
    (ω : Ω) : p k (subseq p hp k ω) ω := by
  cases k with
  | zero => exact (Nat.find_spec (exists_after p hp 0 0 ω)).2
  | succ k => exact (Nat.find_spec (exists_after p hp (k+1) (subseq p hp k ω) ω)).2

lemma subseq_strictMono (p : ℕ → ℕ → Ω → Prop) (hp : ∀ k ω, ∃ᶠ n in atTop, p k n ω)
    (ω : Ω) : StrictMono (fun k => subseq p hp k ω) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  exact (Nat.find_spec (exists_after p hp (k+1) (subseq p hp k ω) ω)).1

lemma subseq_meas (p : ℕ → ℕ → Ω → Prop) (hp : ∀ k ω, ∃ᶠ n in atTop, p k n ω)
    (hm : ∀ k n, MeasurableSet {ω | p k n ω}) : ∀ k, Measurable (subseq p hp k) := by
  intro k
  induction k with
  | zero =>
    show Measurable fun ω => Nat.find (exists_after p hp 0 0 ω)
    refine measurable_find (p := fun ω n => 0 < n ∧ p 0 n ω) _ fun n => ?_
    exact (MeasurableSet.const _).inter (hm 0 n)
  | succ k ih =>
    show Measurable fun ω => Nat.find (exists_after p hp (k+1) (subseq p hp k ω) ω)
    refine measurable_find (p := fun ω n => subseq p hp k ω < n ∧ p (k+1) n ω) _ fun n => ?_
    exact (ih (measurableSet_Iio (a := n))).inter (hm (k+1) n)

lemma select_real (x : ℕ → Ω → ℝ) (hx : ∀ n, Measurable (x n)) (B : Ω → ℝ)
    (hB : ∀ n ω, |x n ω| ≤ B ω) :
    ∃ τ : ℕ → Ω → ℕ, (∀ k, Measurable (τ k)) ∧ (∀ ω, StrictMono (fun k => τ k ω)) ∧
      ∃ ℓ : Ω → ℝ, Measurable ℓ ∧ ∀ ω, Tendsto (fun k => x (τ k ω) ω) atTop (𝓝 (ℓ ω)) := by
  let ℓ : Ω → ℝ := fun ω => liminf (fun n => x n ω) atTop
  have hℓ : Measurable ℓ := Measurable.liminf hx
  have hbd1 : ∀ ω, IsBoundedUnder (· ≥ ·) atTop (fun n => x n ω) := fun ω =>
    ⟨-B ω, eventually_map.mpr (Eventually.of_forall fun n => (abs_le.mp (hB n ω)).1)⟩
  have hbd2 : ∀ ω, IsCoboundedUnder (· ≥ ·) atTop (fun n => x n ω) := fun ω =>
    IsBoundedUnder.isCoboundedUnder_flip
      (⟨B ω, eventually_map.mpr (Eventually.of_forall fun n => (abs_le.mp (hB n ω)).2)⟩ :
        IsBoundedUnder (· ≤ ·) atTop (fun n => x n ω))
  let p : ℕ → ℕ → Ω → Prop := fun k n ω => |x n ω - ℓ ω| < 1 / ((k:ℝ)+1)
  have hp : ∀ k ω, ∃ᶠ n in atTop, p k n ω := by
    intro k ω
    have hε : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
    have h1 : ∀ᶠ n in atTop, ℓ ω - 1/((k:ℝ)+1) < x n ω :=
      eventually_lt_of_lt_liminf (by simp only [ℓ]; linarith) (hbd1 ω)
    have h2 : ∃ᶠ n in atTop, x n ω < ℓ ω + 1/((k:ℝ)+1) :=
      frequently_lt_of_liminf_lt (hbd2 ω) (by simp only [ℓ]; linarith)
    refine (h2.and_eventually h1).mono fun n hn => ?_
    simp only [p, abs_lt]; constructor <;> linarith [hn.1, hn.2]
  have hm : ∀ k n, MeasurableSet {ω | p k n ω} := fun k n =>
    measurableSet_lt ((hx n).sub hℓ).abs measurable_const
  refine ⟨subseq p hp, subseq_meas p hp hm, subseq_strictMono p hp, ℓ, hℓ, fun ω => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => (subseq_spec p hp k ω).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

lemma select_vec {d : ℕ} (η : ℕ → Ω → Fin d → ℝ) (hη : ∀ n, Measurable (η n)) (B : Ω → ℝ)
    (hB : ∀ n ω, ‖η n ω‖ ≤ B ω) :
    ∃ τ : ℕ → Ω → ℕ, (∀ k, Measurable (τ k)) ∧ (∀ ω, StrictMono (fun k => τ k ω)) ∧
      ∃ ℓ : Ω → Fin d → ℝ, Measurable ℓ ∧
        ∀ ω, Tendsto (fun k => η (τ k ω) ω) atTop (𝓝 (ℓ ω)) := by
  have key : ∀ c ≤ d, ∃ τ : ℕ → Ω → ℕ, (∀ k, Measurable (τ k)) ∧
      (∀ ω, StrictMono (fun k => τ k ω)) ∧ ∀ j : Fin d, (j:ℕ) < c → ∃ ℓ : Ω → ℝ,
        Measurable ℓ ∧ ∀ ω, Tendsto (fun k => η (τ k ω) ω j) atTop (𝓝 (ℓ ω)) := by
    intro c
    induction c with
    | zero =>
      intro _
      exact ⟨fun k _ => k, fun k => measurable_const, fun ω => strictMono_id,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ c ih =>
      intro hc
      obtain ⟨τ, hτm, hτs, hτc⟩ := ih (by omega)
      let jc : Fin d := ⟨c, by omega⟩
      let x : ℕ → Ω → ℝ := fun k ω => η (τ k ω) ω jc
      have hxm : ∀ k, Measurable (x k) := fun k =>
        meas_comp_nat (g := fun n ω => η n ω jc) (hτm k)
          (fun n => (measurable_pi_apply jc).comp (hη n))
      have hxB : ∀ k ω, |x k ω| ≤ B ω := fun k ω =>
        (norm_le_pi_norm (η (τ k ω) ω) jc).trans (hB _ ω)
      obtain ⟨τ', hτ'm, hτ's, ℓ, hℓm, hℓ⟩ := select_real x hxm B hxB
      refine ⟨fun k ω => τ (τ' k ω) ω, fun k => meas_comp_nat (hτ'm k) hτm,
        fun ω => (hτs ω).comp (hτ's ω), fun j hj => ?_⟩
      by_cases hjc : (j:ℕ) < c
      · obtain ⟨ℓj, hℓjm, hℓj⟩ := hτc j hjc
        exact ⟨ℓj, hℓjm, fun ω => (hℓj ω).comp (hτ's ω).tendsto_atTop⟩
      · have : j = jc := Fin.ext (by simp [jc]; omega)
        subst this
        exact ⟨ℓ, hℓm, hℓ⟩
  obtain ⟨τ, hτm, hτs, hτc⟩ := key d le_rfl
  choose ℓ hℓm hℓ using fun j : Fin d => hτc j j.isLt
  refine ⟨τ, hτm, hτs, fun ω j => ℓ j ω, measurable_pi_lambda _ hℓm, fun ω => ?_⟩
  exact tendsto_pi_nhds.mpr fun j => hℓ j ω

/-- The set where `‖η n‖` does not tend to infinity. -/
def boundedSet {d : ℕ} (η : ℕ → Ω → Fin d → ℝ) : Set Ω :=
  {ω | ∃ C : ℕ, ∃ᶠ n in atTop, ‖η n ω‖ ≤ C}

lemma measurableSet_boundedSet {d : ℕ} (η : ℕ → Ω → Fin d → ℝ) (hη : ∀ n, Measurable (η n)) :
    MeasurableSet (boundedSet η) := by
  have : boundedSet η = ⋃ C : ℕ, ⋂ a : ℕ, ⋃ b : ℕ, ({_ω | a ≤ b} ∩ {ω | ‖η b ω‖ ≤ C}) := by
    ext ω; simp [boundedSet, frequently_atTop]
  rw [this]
  exact MeasurableSet.iUnion fun C => MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
    (MeasurableSet.const _).inter (measurableSet_le (hη b).norm measurable_const)

lemma select {d : ℕ} (η : ℕ → Ω → Fin d → ℝ) (hη : ∀ n, Measurable (η n)) :
    ∃ τ : ℕ → Ω → ℕ, (∀ k, Measurable (τ k)) ∧ (∀ ω, StrictMono (fun k => τ k ω)) ∧
      ∃ ℓ : Ω → Fin d → ℝ, Measurable ℓ ∧
        ∀ ω ∈ boundedSet η, Tendsto (fun k => η (τ k ω) ω) atTop (𝓝 (ℓ ω)) := by
  set A := boundedSet η with hAdef
  have hA : MeasurableSet A := measurableSet_boundedSet η hη
  have hq : ∀ ω, ∃ C : ℕ, ω ∉ A ∨ ∃ᶠ n in atTop, ‖η n ω‖ ≤ C := by
    intro ω
    by_cases h : ω ∈ A
    · obtain ⟨C, hC⟩ := h; exact ⟨C, Or.inr hC⟩
    · exact ⟨0, Or.inl h⟩
  let Cω : Ω → ℕ := fun ω => Nat.find (hq ω)
  have hCm : Measurable Cω := by
    refine measurable_find (p := fun ω C => ω ∉ A ∨ ∃ᶠ n in atTop, ‖η n ω‖ ≤ C) _ fun C => ?_
    have : {ω | ω ∉ A ∨ ∃ᶠ n in atTop, ‖η n ω‖ ≤ (C:ℝ)} =
        Aᶜ ∪ ⋂ a : ℕ, ⋃ b : ℕ, ({_ω | a ≤ b} ∩ {ω | ‖η b ω‖ ≤ C}) := by
      ext ω; simp [frequently_atTop]
    rw [this]
    exact hA.compl.union (MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
      (MeasurableSet.const _).inter (measurableSet_le (hη b).norm measurable_const))
  let p0 : ℕ → ℕ → Ω → Prop := fun _ n ω => ω ∉ A ∨ ‖η n ω‖ ≤ Cω ω
  have hp0 : ∀ k ω, ∃ᶠ n in atTop, p0 k n ω := by
    intro k ω
    by_cases h : ω ∈ A
    · have hs := Nat.find_spec (hq ω)
      rcases hs with hs | hs
      · exact absurd h hs
      · exact hs.mono fun n hn => Or.inr hn
    · exact Frequently.of_forall fun n => Or.inl h
  have hp0m : ∀ k n, MeasurableSet {ω | p0 k n ω} := fun k n =>
    hA.compl.union (measurableSet_le (hη n).norm ((measurable_from_nat (f := fun n : ℕ => (n:ℝ))).comp hCm))
  let σ0 := subseq p0 hp0
  have hσ0m := subseq_meas p0 hp0 hp0m
  let y : ℕ → Ω → Fin d → ℝ := fun k ω => if ω ∈ A then η (σ0 k ω) ω else 0
  have hym : ∀ k, Measurable (y k) := fun k =>
    Measurable.ite hA (meas_comp_nat (hσ0m k) hη) measurable_const
  have hyB : ∀ k ω, ‖y k ω‖ ≤ (Cω ω : ℝ) := by
    intro k ω
    by_cases h : ω ∈ A
    · simp only [y, if_pos h]
      rcases subseq_spec p0 hp0 k ω with hs | hs
      · exact absurd h hs
      · exact hs
    · simp only [y, if_neg h, norm_zero]; exact Nat.cast_nonneg _
  obtain ⟨τ, hτm, hτs, ℓ, hℓm, hℓ⟩ := select_vec y hym (fun ω => (Cω ω : ℝ)) hyB
  refine ⟨fun k ω => σ0 (τ k ω) ω, fun k => meas_comp_nat (hτm k) hσ0m,
    fun ω => (subseq_strictMono p0 hp0 ω).comp (hτs ω), ℓ, hℓm, fun ω hω => ?_⟩
  refine (hℓ ω).congr fun k => ?_
  simp only [y, if_pos hω]

end Select

/-! ### Quasi-sure bookkeeping -/

section QS
variable {Ω : Type*} [MeasurableSpace Ω] {Pset : Set (Measure Ω)}

lemma qs_mono {p q : Ω → Prop} (hp : QS Pset p) (h : ∀ ω, p ω → q ω) : QS Pset q := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  exact ⟨A, hA, fun ω hω => hsub (fun hp => hω (h ω hp)), h0⟩

lemma qs_and {p q : Ω → Prop} (hp : QS Pset p) (hq : QS Pset q) :
    QS Pset (fun ω => p ω ∧ q ω) := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  obtain ⟨B, hB, hsubB, h0B⟩ := hq
  refine ⟨A ∪ B, hA.union hB, fun ω hω => ?_,
    fun P hP => measure_union_null (h0 P hP) (h0B P hP)⟩
  by_cases h1 : p ω
  · exact Or.inr (hsubB fun h2 => hω ⟨h1, h2⟩)
  · exact Or.inl (hsub h1)

lemma qs_always (p : Ω → Prop) (h : ∀ ω, p ω) : QS Pset p :=
  ⟨∅, MeasurableSet.empty, fun ω hω => (hω (h ω)).elim, fun _ _ => measure_empty⟩

lemma qs_forall {p : ℕ → Ω → Prop} (hp : ∀ n, QS Pset (p n)) : QS Pset (fun ω => ∀ n, p n ω) := by
  choose A hA hsub h0 using hp
  refine ⟨⋃ n, A n, MeasurableSet.iUnion hA, fun ω hω => ?_,
    fun P hP => measure_iUnion_null fun n => h0 n P hP⟩
  simp only [Set.mem_setOf_eq, not_forall] at hω
  obtain ⟨n, hn⟩ := hω
  exact Set.mem_iUnion.mpr ⟨n, hsub n hn⟩

end QS

/-! ### Tail wealth -/

section Tail
variable {Ω : Type*} {d : ℕ}

/-- `Σ_{u = s}^{T-1} H_u ΔS_{u+1}`. -/
def tw (T : ℕ) (S : ℕ → Ω → Fin d → ℝ) (s : ℕ) (H : ℕ → Ω → Fin d → ℝ) (ω : Ω) : ℝ :=
  ∑ u ∈ Finset.Ico s T, H u ω ⬝ᵥ (S (u+1) ω - S u ω)

lemma tw_succ {T s : ℕ} (hs : s < T) (S : ℕ → Ω → Fin d → ℝ) (H : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    tw T S s H ω = H s ω ⬝ᵥ (S (s+1) ω - S s ω) + tw T S (s+1) H ω :=
  Finset.sum_eq_sum_Ico_succ_bot hs _

lemma tw_top (T : ℕ) (S : ℕ → Ω → Fin d → ℝ) (H : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    tw T S T H ω = 0 := by simp [tw]

lemma tw_congr {T s : ℕ} (S : ℕ → Ω → Fin d → ℝ) {H H' : ℕ → Ω → Fin d → ℝ} {ω ω' : Ω}
    (hS : ∀ u, S u ω = S u ω') (h : ∀ u, s ≤ u → H u ω = H' u ω') :
    tw T S s H ω = tw T S s H' ω' := by
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [h u (Finset.mem_Ico.mp hu).1, hS u, hS (u+1)]

lemma tw_smul (T s : ℕ) (S : ℕ → Ω → Fin d → ℝ) (H : ℕ → Ω → Fin d → ℝ) (c : ℝ) (ω : Ω) :
    tw T S s (fun u ω' => c • H u ω') ω = c * tw T S s H ω := by
  unfold tw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_dotProduct, smul_eq_mul]

lemma tw_sub (T s : ℕ) (S : ℕ → Ω → Fin d → ℝ) (H D : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    tw T S s (fun u ω' => H u ω' - D u ω') ω = tw T S s H ω - tw T S s D ω := by
  unfold tw
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sub_dotProduct]

lemma tw_zero (T s : ℕ) (S : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    tw T S s (fun _ _ => (0 : Fin d → ℝ)) ω = 0 := by simp [tw]

lemma wealth_eq_tw {T : ℕ} (S : ℕ → Ω → Fin d → ℝ) (H : ℕ → Ω → Fin d → ℝ) (s : ℕ)
    (hs : s ≤ T) (h0 : ∀ u < s, ∀ ω, H u ω = 0) (ω : Ω) : wealth T S H ω = tw T S s H ω := by
  unfold wealth tw
  rw [← Finset.sum_range_add_sum_Ico _ hs]
  have : ∑ u ∈ Finset.range s, H u ω ⬝ᵥ (S (u + 1) ω - S u ω) = 0 :=
    Finset.sum_eq_zero fun u hu => by rw [h0 u (Finset.mem_range.mp hu) ω]; simp
  rw [this, zero_add]

lemma wealth_eq_tw0 {T : ℕ} (S : ℕ → Ω → Fin d → ℝ) (H : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    wealth T S H ω = tw T S 0 H ω := by
  unfold wealth tw; rw [Finset.range_eq_Ico]

end Tail

section Defs
variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- Predictability on `{s, …, T-1}`. -/
def PredFrom (ℱ : Filtration ℕ m) (T s : ℕ) (H : ℕ → Ω → Fin d → ℝ) : Prop :=
  ∀ u, s ≤ u → u < T → Measurable[ℱ u] (H u)

/-- `W = H • S_{s,T} − K` quasi-surely. -/
def Rep (ℱ : Filtration ℕ m) (Pset : Set (Measure Ω)) (T : ℕ) (S : ℕ → Ω → Fin d → ℝ) (s : ℕ)
    (W : Ω → ℝ) : Prop :=
  ∃ H : ℕ → Ω → Fin d → ℝ, PredFrom ℱ T s H ∧ ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 0 ≤ K ω) ∧
    QS Pset (fun ω => W ω = tw T S s H ω - K ω)

/-- The number of rows of the random matrix `(H^n_s)_n` that vanish identically. -/
noncomputable def idx (s : ℕ) (H : ℕ → ℕ → Ω → Fin d → ℝ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j : Fin d => ∀ n, H n s ω j = 0)).card

/-- The closedness claim on `{s, …, T}` for sequences whose index at `s` is at least `i`. -/
def ClosedSeq (ℱ : Filtration ℕ m) (Pset : Set (Measure Ω)) (T : ℕ) (S : ℕ → Ω → Fin d → ℝ)
    (s i : ℕ) : Prop :=
  ∀ (H : ℕ → ℕ → Ω → Fin d → ℝ) (K : ℕ → Ω → ℝ) (Wl : Ω → ℝ),
    (∀ n, PredFrom ℱ T s (H n)) → (∀ n, Measurable (K n)) → (∀ n ω, 0 ≤ K n ω) →
    Measurable Wl →
    QS Pset (fun ω => Tendsto (fun n => tw T S s (H n) ω - K n ω) atTop (𝓝 (Wl ω))) →
    QS Pset (fun ω => i ≤ idx s H ω) → Rep ℱ Pset T S s Wl

lemma tw_meas (ℱ : Filtration ℕ m) {T s : ℕ} {S : ℕ → Ω → Fin d → ℝ}
    (hS : ∀ t ≤ T, Measurable (S t)) {H : ℕ → Ω → Fin d → ℝ} (hH : PredFrom ℱ T s H) :
    Measurable (tw T S s H) := by
  unfold tw
  refine Finset.measurable_sum _ fun u hu => ?_
  obtain ⟨hsu, huT⟩ := Finset.mem_Ico.mp hu
  have hHm : Measurable (H u) := (hH u hsu huT).mono (ℱ.le u) le_rfl
  have hY : Measurable fun ω => S (u+1) ω - S u ω := (hS (u+1) huT).sub (hS u huT.le)
  show Measurable fun ω => ∑ i, H u ω i * (S (u+1) ω - S u ω) i
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hHm).mul ((measurable_pi_apply i).comp hY)

lemma dot_meas {m0 : MeasurableSpace Ω} {A B : Ω → Fin d → ℝ} (hA : Measurable[m0] A)
    (hB : Measurable[m0] B) : Measurable[m0] (fun ω => A ω ⬝ᵥ B ω) := by
  show Measurable[m0] fun ω => ∑ i, A ω i * B ω i
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hA).mul ((measurable_pi_apply i).comp hB)

end Defs

section Steps
variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ} (ℱ : Filtration ℕ m)
  (Pset : Set (Measure Ω)) {T : ℕ} {S : ℕ → Ω → Fin d → ℝ}

lemma tendsto_dot {a : ℕ → Fin d → ℝ} {a0 : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 a0))
    (c : Fin d → ℝ) : Tendsto (fun k => a k ⬝ᵥ c) atTop (𝓝 (a0 ⬝ᵥ c)) := by
  have hc : Continuous fun x : Fin d → ℝ => x ⬝ᵥ c := by
    show Continuous fun x : Fin d → ℝ => ∑ i, x i * c i
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  exact (hc.tendsto a0).comp ha


lemma closed_top : ClosedSeq ℱ Pset T S T 0 := by
  intro H K Wl hH hKm hK0 hWl hconv _
  refine ⟨fun _ _ => 0, fun u _ _ => measurable_const, fun ω => max (-Wl ω) 0,
    hWl.neg.max measurable_const, fun ω => le_max_right _ _, ?_⟩
  refine qs_mono hconv fun ω h => ?_
  simp only [tw_top, zero_sub] at h ⊢
  have : Wl ω ≤ 0 := le_of_tendsto' h fun n => by linarith [hK0 n ω]
  rw [max_eq_left (by linarith)]; ring

lemma closed_full {s : ℕ} (hs : s < T) (hnext : ClosedSeq ℱ Pset T S (s+1) 0) :
    ClosedSeq ℱ Pset T S s d := by
  intro H K Wl hH hKm hK0 hWl hconv hidx
  have hz : QS Pset (fun ω => ∀ n, H n s ω = 0) := qs_mono hidx fun ω h n => by
    funext j
    have hc : (Finset.univ.filter (fun j : Fin d => ∀ n, H n s ω j = 0)).card =
        Fintype.card (Fin d) := le_antisymm (Finset.card_le_univ _) (by simpa [idx] using h)
    have hfull := Finset.eq_univ_of_card _ hc
    have : j ∈ Finset.univ.filter (fun j : Fin d => ∀ n, H n s ω j = 0) := by
      rw [hfull]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp this).2 n
  have hconv' : QS Pset (fun ω => Tendsto (fun n => tw T S (s+1) (H n) ω - K n ω) atTop
      (𝓝 (Wl ω))) := by
    refine qs_mono (qs_and hconv hz) fun ω h => ?_
    refine h.1.congr fun n => ?_
    rw [tw_succ hs, h.2 n]; simp
  obtain ⟨H', hH', K', hK'm, hK'0, hq⟩ := hnext H K Wl
    (fun n u hu huT => hH n u (by omega) huT) hKm hK0 hWl hconv'
    (qs_always _ fun _ => Nat.zero_le _)
  refine ⟨fun u ω => if u = s then 0 else H' u ω, fun u hu huT => ?_, K', hK'm, hK'0,
    qs_mono hq fun ω h => ?_⟩
  · by_cases hus : u = s
    · simp only [if_pos hus]; exact measurable_const
    · simp only [if_neg hus]; exact hH' u (by omega) huT
  · rw [h, tw_succ hs]
    simp only [if_true, zero_dotProduct, zero_add]
    congr 1
    exact tw_congr S (fun _ => rfl) fun u hu => by simp [show u ≠ s by omega]

lemma omega1 {s : ℕ} (hs : s < T) (hS : ∀ t ≤ T, Measurable (S t))
    (hnext : ClosedSeq ℱ Pset T S (s+1) 0)
    (H : ℕ → ℕ → Ω → Fin d → ℝ) (K : ℕ → Ω → ℝ) (Wl : Ω → ℝ)
    (hH : ∀ n, PredFrom ℱ T s (H n)) (hKm : ∀ n, Measurable (K n)) (hK0 : ∀ n ω, 0 ≤ K n ω)
    (hWl : Measurable Wl)
    (hconv : QS Pset (fun ω => Tendsto (fun n => tw T S s (H n) ω - K n ω) atTop (𝓝 (Wl ω)))) :
    ∃ H1 : ℕ → Ω → Fin d → ℝ, PredFrom ℱ T s H1 ∧ ∃ K1 : Ω → ℝ, Measurable K1 ∧
      (∀ ω, 0 ≤ K1 ω) ∧
      QS Pset (fun ω => ω ∈ boundedSet (fun n => H n s) → Wl ω = tw T S s H1 ω - K1 ω) := by
  have hHs : ∀ n, Measurable[ℱ s] (H n s) := fun n => hH n s le_rfl hs
  obtain ⟨τ, hτm, hτs, Hs, hHsm, hHsc⟩ := select (mΩ := ℱ s) (fun n => H n s) hHs
  set A := boundedSet (fun n => H n s) with hA
  have hAm : MeasurableSet[ℱ s] A := measurableSet_boundedSet (mΩ := ℱ s) _ hHs
  have hdS : Measurable fun ω => S (s+1) ω - S s ω := (hS _ hs).sub (hS _ hs.le)
  let H' : ℕ → ℕ → Ω → Fin d → ℝ := fun k u ω => if ω ∈ A then H (τ k ω) u ω else 0
  let K' : ℕ → Ω → ℝ := fun k ω => if ω ∈ A then K (τ k ω) ω else 0
  let W' : Ω → ℝ := fun ω => if ω ∈ A then Wl ω - Hs ω ⬝ᵥ (S (s+1) ω - S s ω) else 0
  have hH' : ∀ k, PredFrom ℱ T (s+1) (H' k) := by
    intro k u hu huT
    have hle : ℱ s ≤ ℱ u := ℱ.mono (by omega)
    exact Measurable.ite (hle _ hAm) (meas_comp_nat (mΩ := ℱ u) (g := fun n ω => H n u ω)
      ((hτm k).mono hle le_rfl) (fun n => hH n u (by omega) huT)) measurable_const
  have hK'm : ∀ k, Measurable (K' k) := fun k =>
    Measurable.ite (ℱ.le s _ hAm) (meas_comp_nat ((hτm k).mono (ℱ.le s) le_rfl) hKm)
      measurable_const
  have hK'0 : ∀ k ω, 0 ≤ K' k ω := fun k ω => by
    simp only [K']; split_ifs
    · exact hK0 _ _
    · exact le_rfl
  have hW'm : Measurable W' :=
    Measurable.ite (ℱ.le s _ hAm) (hWl.sub (dot_meas (hHsm.mono (ℱ.le s) le_rfl) hdS))
      measurable_const
  have hconv' : QS Pset (fun ω => Tendsto (fun k => tw T S (s+1) (H' k) ω - K' k ω) atTop
      (𝓝 (W' ω))) := by
    refine qs_mono hconv fun ω h => ?_
    by_cases hω : ω ∈ A
    · have e : ∀ k, tw T S (s+1) (H' k) ω - K' k ω =
          (tw T S s (H (τ k ω)) ω - K (τ k ω) ω) - H (τ k ω) s ω ⬝ᵥ (S (s+1) ω - S s ω) := by
        intro k
        rw [tw_succ hs]
        have : tw T S (s+1) (H' k) ω = tw T S (s+1) (H (τ k ω)) ω :=
          tw_congr S (fun _ => rfl) fun u _ => by simp [H', hω]
        simp only [this, K', if_pos hω]; ring
      simp only [e, W', if_pos hω]
      exact (h.comp (hτs ω).tendsto_atTop).sub (tendsto_dot (hHsc ω hω) _)
    · have e : ∀ k, tw T S (s+1) (H' k) ω - K' k ω = 0 := by
        intro k
        have : tw T S (s+1) (H' k) ω = tw T S (s+1) (fun _ _ => (0 : Fin d → ℝ)) ω :=
          tw_congr S (fun _ => rfl) fun u _ => by simp [H', hω]
        simp only [this, tw_zero, K', if_neg hω, sub_zero]
      simp only [e, W', if_neg hω]
      exact tendsto_const_nhds
  obtain ⟨H1', hH1', K1, hK1m, hK10, hq⟩ := hnext H' K' W' hH' hK'm hK'0 hW'm hconv'
    (qs_always _ fun _ => Nat.zero_le _)
  refine ⟨fun u ω => if u = s then Hs ω else H1' u ω, fun u hu huT => ?_, K1, hK1m, hK10,
    qs_mono hq fun ω h hω => ?_⟩
  · by_cases hus : u = s
    · simp only [if_pos hus]; subst hus; exact hHsm
    · simp only [if_neg hus]; exact hH1' u (by omega) huT
  · simp only [W', if_pos hω] at h
    rw [tw_succ hs]
    simp only [if_true]
    have : tw T S (s+1) (fun u ω => if u = s then Hs ω else H1' u ω) ω = tw T S (s+1) H1' ω :=
      tw_congr S (fun _ => rfl) fun u hu => by simp [show u ≠ s by omega]
    rw [this]; linarith

lemma omega2 {s i : ℕ} (hs : s < T) (hi : i < d) (hS : ∀ t ≤ T, Measurable (S t))
    (hNA : NA Pset ℱ T S)
    (hnext : ClosedSeq ℱ Pset T S (s+1) 0) (hself : ClosedSeq ℱ Pset T S s (i+1))
    (H : ℕ → ℕ → Ω → Fin d → ℝ) (K : ℕ → Ω → ℝ) (Wl : Ω → ℝ)
    (hH : ∀ n, PredFrom ℱ T s (H n)) (hKm : ∀ n, Measurable (K n)) (hK0 : ∀ n ω, 0 ≤ K n ω)
    (hWl : Measurable Wl)
    (hconv : QS Pset (fun ω => Tendsto (fun n => tw T S s (H n) ω - K n ω) atTop (𝓝 (Wl ω))))
    (hidx : QS Pset (fun ω => i ≤ idx s H ω)) :
    ∃ H2 : ℕ → Ω → Fin d → ℝ, PredFrom ℱ T s H2 ∧ ∃ K2 : Ω → ℝ, Measurable K2 ∧
      (∀ ω, 0 ≤ K2 ω) ∧
      QS Pset (fun ω => ω ∉ boundedSet (fun n => H n s) → Wl ω = tw T S s H2 ω - K2 ω) := by
  have hHs : ∀ n, Measurable[ℱ s] (H n s) := fun n => hH n s le_rfl hs
  set A := boundedSet (fun n => H n s) with hA
  have hAm : MeasurableSet[ℱ s] A := measurableSet_boundedSet (mΩ := ℱ s) _ hHs
  have hdS : Measurable fun ω => S (s+1) ω - S s ω := (hS _ hs).sub (hS _ hs.le)
  -- normalised positions `G^n = H^n_s / (1 + |H^n_s|)`
  let c : ℕ → Ω → ℝ := fun n ω => (1 + ‖H n s ω‖)⁻¹
  let G : ℕ → Ω → Fin d → ℝ := fun n ω => c n ω • H n s ω
  have hfc : Continuous fun x : Fin d → ℝ => (1 + ‖x‖)⁻¹ :=
    (continuous_const.add continuous_norm).inv₀ fun x => (by positivity : (0:ℝ) < 1 + ‖x‖).ne'
  have hcm : ∀ n, Measurable[ℱ s] (c n) := fun n => hfc.measurable.comp (hHs n)
  have hGm : ∀ n, Measurable[ℱ s] (G n) := fun n =>
    (hfc.smul continuous_id).measurable.comp (hHs n)
  have hcpos : ∀ n ω, 0 < c n ω := fun n ω => inv_pos.mpr (by positivity)
  have hcG : ∀ n ω, ‖G n ω‖ = 1 - c n ω := by
    intro n ω
    have h1 : (0:ℝ) < 1 + ‖H n s ω‖ := by positivity
    simp only [G, c, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h1]
    field_simp
    ring
  have hGb : ∀ n ω, ‖G n ω‖ ≤ 1 := fun n ω => by rw [hcG]; linarith [hcpos n ω]
  obtain ⟨τ, hτm, hτs, Gl, hGlm, hGlc'⟩ := select (mΩ := ℱ s) G hGm
  have hGlc : ∀ ω, Tendsto (fun k => G (τ k ω) ω) atTop (𝓝 (Gl ω)) := fun ω =>
    hGlc' ω ⟨1, Frequently.of_forall fun n => by exact_mod_cast hGb n ω⟩
  have hinf : ∀ ω, ω ∉ A → Tendsto (fun n => ‖H n s ω‖) atTop atTop := by
    intro ω hω
    rw [tendsto_atTop]
    intro b
    obtain ⟨C, hC⟩ := exists_nat_ge b
    have : ¬ ∃ᶠ n in atTop, ‖H n s ω‖ ≤ ((C+1 : ℕ) : ℝ) := fun hf => hω ⟨C+1, hf⟩
    rw [not_frequently] at this
    exact this.mono fun n hn => by push_cast at hn; linarith [not_le.mp hn]
  have hc0 : ∀ ω, ω ∉ A → Tendsto (fun n => c n ω) atTop (𝓝 0) := fun ω hω =>
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 (hinf ω hω))
  have hGl1 : ∀ ω, ω ∉ A → Gl ω ≠ 0 := by
    intro ω hω h0
    have h1 : Tendsto (fun k => ‖G (τ k ω) ω‖) atTop (𝓝 ‖Gl ω‖) := (hGlc ω).norm
    have h2 : Tendsto (fun k => ‖G (τ k ω) ω‖) atTop (𝓝 (1 - 0)) := by
      simp only [hcG]
      exact tendsto_const_nhds.sub ((hc0 ω hω).comp (hτs ω).tendsto_atTop)
    have := tendsto_nhds_unique h1 h2
    rw [h0, norm_zero] at this; norm_num at this
  have hGlrow : ∀ ω (l : Fin d), (∀ n, H n s ω l = 0) → Gl ω l = 0 := by
    intro ω l hl
    have h1 : Tendsto (fun k => G (τ k ω) ω l) atTop (𝓝 (Gl ω l)) :=
      tendsto_pi_nhds.mp (hGlc ω) l
    have h2 : (fun k => G (τ k ω) ω l) = fun _ => 0 := by
      funext k; simp [G, hl]
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  -- the rescaled sequence on `Ω₂ = Aᶜ`
  let H'' : ℕ → ℕ → Ω → Fin d → ℝ := fun k u ω =>
    if ω ∈ A then 0 else c (τ k ω) ω • H (τ k ω) u ω
  let K'' : ℕ → Ω → ℝ := fun k ω => if ω ∈ A then 0 else c (τ k ω) ω * K (τ k ω) ω
  let W'' : Ω → ℝ := fun ω => if ω ∈ A then 0 else -(Gl ω ⬝ᵥ (S (s+1) ω - S s ω))
  have hH'' : ∀ k, PredFrom ℱ T (s+1) (H'' k) := by
    intro k u hu huT
    have hle : ℱ s ≤ ℱ u := ℱ.mono (by omega)
    refine Measurable.ite (hle _ hAm) measurable_const ?_
    exact (meas_comp_nat (mΩ := ℱ u) (g := c) ((hτm k).mono hle le_rfl)
      (fun n => (hcm n).mono hle le_rfl)).smul
      (meas_comp_nat (mΩ := ℱ u) (g := fun n ω => H n u ω) ((hτm k).mono hle le_rfl)
        (fun n => hH n u (by omega) huT))
  have hK''m : ∀ k, Measurable (K'' k) := fun k =>
    Measurable.ite (ℱ.le s _ hAm) measurable_const
      ((meas_comp_nat (g := c) ((hτm k).mono (ℱ.le s) le_rfl)
        (fun n => (hcm n).mono (ℱ.le s) le_rfl)).mul
        (meas_comp_nat ((hτm k).mono (ℱ.le s) le_rfl) hKm))
  have hK''0 : ∀ k ω, 0 ≤ K'' k ω := fun k ω => by
    simp only [K'']; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hcpos _ _).le (hK0 _ _)
  have hW''m : Measurable W'' :=
    Measurable.ite (ℱ.le s _ hAm) measurable_const
      (dot_meas (hGlm.mono (ℱ.le s) le_rfl) hdS).neg
  have hconv'' : QS Pset (fun ω => Tendsto (fun k => tw T S (s+1) (H'' k) ω - K'' k ω) atTop
      (𝓝 (W'' ω))) := by
    refine qs_mono hconv fun ω h => ?_
    by_cases hω : ω ∈ A
    · have e : ∀ k, tw T S (s+1) (H'' k) ω - K'' k ω = 0 := by
        intro k
        have : tw T S (s+1) (H'' k) ω = tw T S (s+1) (fun _ _ => (0 : Fin d → ℝ)) ω :=
          tw_congr S (fun _ => rfl) fun u _ => by simp [H'', hω]
        simp only [this, tw_zero, K'', if_pos hω, sub_zero]
      simp only [e, W'', if_pos hω]
      exact tendsto_const_nhds
    · have e : ∀ k, tw T S (s+1) (H'' k) ω - K'' k ω =
          c (τ k ω) ω * (tw T S s (H (τ k ω)) ω - K (τ k ω) ω) -
            G (τ k ω) ω ⬝ᵥ (S (s+1) ω - S s ω) := by
        intro k
        have : tw T S (s+1) (H'' k) ω =
            tw T S (s+1) (fun u ω' => c (τ k ω) ω • H (τ k ω) u ω') ω :=
          tw_congr S (fun _ => rfl) fun u _ => by simp [H'', hω]
        rw [this, tw_smul, tw_succ hs]
        simp only [K'', if_neg hω, G, smul_dotProduct, smul_eq_mul]
        ring
      simp only [e, W'', if_neg hω]
      have h1 : Tendsto (fun k => c (τ k ω) ω * (tw T S s (H (τ k ω)) ω - K (τ k ω) ω))
          atTop (𝓝 (0 * Wl ω)) :=
        ((hc0 ω hω).comp (hτs ω).tendsto_atTop).mul (h.comp (hτs ω).tendsto_atTop)
      rw [zero_mul] at h1
      have := h1.sub (tendsto_dot (hGlc ω) (S (s+1) ω - S s ω))
      simpa using this
  obtain ⟨Ht, hHt, Kt, hKtm, hKt0, hqt⟩ := hnext H'' K'' W'' hH'' hK''m hK''0 hW''m hconv''
    (qs_always _ fun _ => Nat.zero_le _)
  -- NA yields (2.1)
  let L : ℕ → Ω → Fin d → ℝ := fun u ω =>
    if u < s then 0 else if ω ∈ A then 0 else if u = s then Gl ω else Ht u ω
  have hL : IsPredictable ℱ T L := by
    intro u huT
    by_cases h1 : u < s
    · simp only [L, if_pos h1]; exact measurable_const
    · simp only [L, if_neg h1]
      have hle : ℱ s ≤ ℱ u := ℱ.mono (by omega)
      refine Measurable.ite (hle _ hAm) measurable_const ?_
      by_cases h2 : u = s
      · simp only [if_pos h2]; subst h2; exact hGlm
      · simp only [if_neg h2]; exact hHt u (by omega) huT
  have hLtw : ∀ ω, wealth T S L ω =
      if ω ∈ A then 0 else Gl ω ⬝ᵥ (S (s+1) ω - S s ω) + tw T S (s+1) Ht ω := by
    intro ω
    rw [wealth_eq_tw S L s hs.le (fun u hu ω => by simp [L, hu]), tw_succ hs]
    by_cases hω : ω ∈ A
    · rw [if_pos hω]
      have : tw T S (s+1) L ω = tw T S (s+1) (fun _ _ => (0 : Fin d → ℝ)) ω :=
        tw_congr S (fun _ => rfl) fun u hu => by simp [L, hω, show ¬ u < s by omega]
      rw [this, tw_zero]; simp [L, hω]
    · rw [if_neg hω]
      have : tw T S (s+1) L ω = tw T S (s+1) Ht ω :=
        tw_congr S (fun _ => rfl) fun u hu => by
          simp [L, hω, show ¬ u < s by omega, show u ≠ s by omega]
      rw [this]; simp [L, hω]
  have hge : QS Pset (fun ω => 0 ≤ wealth T S L ω) := by
    refine qs_mono hqt fun ω h => ?_
    rw [hLtw]
    by_cases hω : ω ∈ A
    · rw [if_pos hω]
    · rw [if_neg hω]
      simp only [W'', if_neg hω] at h
      linarith [hKt0 ω]
  have hzero : QS Pset (fun ω => ω ∉ A →
      Gl ω ⬝ᵥ (S (s+1) ω - S s ω) + tw T S (s+1) Ht ω = 0) := by
    refine qs_mono (hNA L hL hge) fun ω h hω => ?_
    rw [hLtw, if_neg hω] at h; exact h
  -- the partition `Λ_j` of `Ω₂` and the coefficients `φ^n`
  let Λ : Fin d → Set Ω := fun j => {ω | ω ∉ A ∧ Gl ω j ≠ 0 ∧ ∀ l : Fin d, l < j → Gl ω l = 0}
  have hΛm : ∀ j, MeasurableSet[ℱ s] (Λ j) := by
    intro j
    have : Λ j = Aᶜ ∩ ((fun ω => Gl ω j) ⁻¹' {0}ᶜ ∩
        ⋂ l : Fin d, ⋂ (_ : l < j), (fun ω => Gl ω l) ⁻¹' {0}) := by
      ext ω; simp [Λ]
    rw [this]
    have hGj : ∀ l : Fin d, Measurable[ℱ s] (fun ω => Gl ω l) := fun l =>
      (measurable_pi_apply l).comp hGlm
    exact hAm.compl.inter (((hGj j) (measurableSet_singleton 0).compl).inter
      (MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
        (hGj l) (measurableSet_singleton 0)))
  have hΛex : ∀ ω, ω ∉ A → ∃ j, ω ∈ Λ j ∧ ∀ j', ω ∈ Λ j' → j' = j := by
    intro ω hω
    have hne : (Finset.univ.filter (fun j : Fin d => Gl ω j ≠ 0)).Nonempty := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp (hGl1 ω hω)
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    set j0 := (Finset.univ.filter (fun j : Fin d => Gl ω j ≠ 0)).min' hne
    have hj0 : Gl ω j0 ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hlt : ∀ l : Fin d, l < j0 → Gl ω l = 0 := by
      intro l hl
      by_contra hcon
      have hmem : l ∈ Finset.univ.filter (fun j : Fin d => Gl ω j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩
      have := Finset.min'_le _ l hmem
      exact absurd hl (not_lt.mpr this)
    refine ⟨j0, ⟨hω, hj0, hlt⟩, fun j' hj' => ?_⟩
    rcases lt_trichotomy j' j0 with h | h | h
    · exact absurd (hlt j' h) hj'.2.1
    · exact h
    · exact absurd (hj'.2.2 j0 h) hj0
  let φ : ℕ → Ω → ℝ := fun n ω => ∑ j, (Λ j).indicator (fun ω => H n s ω j / Gl ω j) ω
  have hφm : ∀ n, Measurable[ℱ s] (φ n) := by
    intro n
    refine Finset.measurable_sum _ fun j _ => Measurable.indicator ?_ (hΛm j)
    exact ((measurable_pi_apply j).comp (hHs n)).div ((measurable_pi_apply j).comp hGlm)
  have hφA : ∀ n ω, ω ∈ A → φ n ω = 0 := by
    intro n ω hω
    refine Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (fun h => h.1 hω) _
  have hφΛ : ∀ n ω j, ω ∈ Λ j → (∀ j', ω ∈ Λ j' → j' = j) →
      φ n ω = H n s ω j / Gl ω j := by
    intro n ω j hj huniq
    simp only [φ]
    rw [Finset.sum_eq_single j]
    · exact Set.indicator_of_mem hj _
    · intro j' _ hj'
      exact Set.indicator_of_notMem (fun h => hj' (huniq j' h)) _
    · intro h; exact absurd (Finset.mem_univ j) h
  -- the modified strategies `H̄^n`
  let D : ℕ → Ω → Fin d → ℝ := fun u ω => if u = s then Gl ω else Ht u ω
  let Hb : ℕ → ℕ → Ω → Fin d → ℝ := fun n u ω => H n u ω - φ n ω • D u ω
  have hHb : ∀ n, PredFrom ℱ T s (Hb n) := by
    intro n u hu huT
    have hle : ℱ s ≤ ℱ u := ℱ.mono hu
    refine (hH n u hu huT).sub (((hφm n).mono hle le_rfl).smul ?_)
    by_cases h : u = s
    · simp only [D, if_pos h]; subst h; exact hGlm
    · simp only [D, if_neg h]; exact hHt u (by omega) huT
  have hDtw : ∀ ω, tw T S s D ω = Gl ω ⬝ᵥ (S (s+1) ω - S s ω) + tw T S (s+1) Ht ω := by
    intro ω
    rw [tw_succ hs]
    simp only [D, if_true]
    congr 1
    exact tw_congr S (fun _ => rfl) fun u hu => by simp [show u ≠ s by omega]
  have hHbtw : ∀ n ω, tw T S s (Hb n) ω = tw T S s (H n) ω - φ n ω * tw T S s D ω := by
    intro n ω
    have : tw T S s (Hb n) ω = tw T S s (fun u ω' => H n u ω' - φ n ω • D u ω') ω :=
      tw_congr S (fun _ => rfl) fun u _ => rfl
    rw [this, tw_sub, tw_smul]
  have hsame : QS Pset (fun ω => ∀ n, tw T S s (Hb n) ω = tw T S s (H n) ω) := by
    refine qs_mono hzero fun ω h n => ?_
    rw [hHbtw]
    by_cases hω : ω ∈ A
    · rw [hφA n ω hω]; ring
    · rw [hDtw, h hω]; ring
  -- the index increases on `Ω₂`
  have hidxb : ∀ ω, ω ∉ A → i ≤ idx s H ω → i + 1 ≤ idx s Hb ω := by
    intro ω hω hiω
    obtain ⟨j0, hj0, huniq⟩ := hΛex ω hω
    set V := Finset.univ.filter (fun j : Fin d => ∀ n, H n s ω j = 0) with hV
    have hsub : insert j0 V ⊆ Finset.univ.filter (fun j : Fin d => ∀ n, Hb n s ω j = 0) := by
      intro l hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun n => ?_⟩
      simp only [Hb, D, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases Finset.mem_insert.mp hl with h | h
      · subst h
        rw [hφΛ n ω l hj0 huniq]
        field_simp [hj0.2.1]
        ring
      · have hl0 := (Finset.mem_filter.mp h).2
        rw [hl0 n, hGlrow ω l hl0]; ring
    have hnot : j0 ∉ V := fun h => hj0.2.1 (hGlrow ω j0 (Finset.mem_filter.mp h).2)
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at this
    simp only [idx] at hiω ⊢
    rw [← hV] at hiω
    omega
  -- localise to `Ω₂` and apply the induction hypothesis on the index
  let H3 : ℕ → ℕ → Ω → Fin d → ℝ := fun n u ω => if ω ∈ A then 0 else Hb n u ω
  let K3 : ℕ → Ω → ℝ := fun n ω => if ω ∈ A then 0 else K n ω
  let W3 : Ω → ℝ := fun ω => if ω ∈ A then 0 else Wl ω
  have hH3 : ∀ n, PredFrom ℱ T s (H3 n) := fun n u hu huT =>
    Measurable.ite (ℱ.mono hu _ hAm) measurable_const (hHb n u hu huT)
  have hK3m : ∀ n, Measurable (K3 n) := fun n =>
    Measurable.ite (ℱ.le s _ hAm) measurable_const (hKm n)
  have hK30 : ∀ n ω, 0 ≤ K3 n ω := fun n ω => by
    simp only [K3]; split_ifs
    · exact le_rfl
    · exact hK0 n ω
  have hW3m : Measurable W3 := Measurable.ite (ℱ.le s _ hAm) measurable_const hWl
  have hconv3 : QS Pset (fun ω => Tendsto (fun n => tw T S s (H3 n) ω - K3 n ω) atTop
      (𝓝 (W3 ω))) := by
    refine qs_mono (qs_and hconv hsame) fun ω h => ?_
    by_cases hω : ω ∈ A
    · have e : ∀ n, tw T S s (H3 n) ω - K3 n ω = 0 := by
        intro n
        have : tw T S s (H3 n) ω = tw T S s (fun _ _ => (0 : Fin d → ℝ)) ω :=
          tw_congr S (fun _ => rfl) fun u _ => by simp [H3, hω]
        simp only [this, tw_zero, K3, if_pos hω, sub_zero]
      simp only [e, W3, if_pos hω]
      exact tendsto_const_nhds
    · have e : ∀ n, tw T S s (H3 n) ω - K3 n ω = tw T S s (H n) ω - K n ω := by
        intro n
        have : tw T S s (H3 n) ω = tw T S s (Hb n) ω :=
          tw_congr S (fun _ => rfl) fun u _ => by simp [H3, hω]
        simp only [this, h.2 n, K3, if_neg hω]
      simp only [e, W3, if_neg hω]
      exact h.1
  have hidx3 : QS Pset (fun ω => i + 1 ≤ idx s H3 ω) := by
    refine qs_mono hidx fun ω h => ?_
    by_cases hω : ω ∈ A
    · have : Finset.univ.filter (fun j : Fin d => ∀ n, H3 n s ω j = 0) = Finset.univ := by
        ext j; simp [H3, hω]
      simp only [idx, this, Finset.card_univ, Fintype.card_fin]
      omega
    · have : idx s H3 ω = idx s Hb ω := by
        simp only [idx, H3, if_neg hω]
      rw [this]
      exact hidxb ω hω h
  obtain ⟨H2, hH2, K2, hK2m, hK20, hq2⟩ := hself H3 K3 W3 hH3 hK3m hK30 hW3m hconv3 hidx3
  refine ⟨H2, hH2, K2, hK2m, hK20, qs_mono hq2 fun ω h hω => ?_⟩
  simp only [W3, if_neg hω] at h
  exact h

lemma closed_step {s i : ℕ} (hs : s < T) (hi : i < d) (hS : ∀ t ≤ T, Measurable (S t))
    (hNA : NA Pset ℱ T S)
    (hnext : ClosedSeq ℱ Pset T S (s+1) 0) (hself : ClosedSeq ℱ Pset T S s (i+1)) :
    ClosedSeq ℱ Pset T S s i := by
  intro H K Wl hH hKm hK0 hWl hconv hidx
  obtain ⟨H1, hH1, K1, hK1m, hK10, hq1⟩ :=
    omega1 ℱ Pset hs hS hnext H K Wl hH hKm hK0 hWl hconv
  obtain ⟨H2, hH2, K2, hK2m, hK20, hq2⟩ :=
    omega2 ℱ Pset hs hi hS hNA hnext hself H K Wl hH hKm hK0 hWl hconv hidx
  have hHs : ∀ n, Measurable[ℱ s] (H n s) := fun n => hH n s le_rfl hs
  set A := boundedSet (fun n => H n s) with hA
  have hAm : MeasurableSet[ℱ s] A := measurableSet_boundedSet (mΩ := ℱ s) _ hHs
  refine ⟨fun u ω => if ω ∈ A then H1 u ω else H2 u ω, fun u hu huT =>
    Measurable.ite (ℱ.mono hu _ hAm) (hH1 u hu huT) (hH2 u hu huT),
    fun ω => if ω ∈ A then K1 ω else K2 ω, Measurable.ite (ℱ.le s _ hAm) hK1m hK2m,
    fun ω => ?_, qs_mono (qs_and hq1 hq2) fun ω h => ?_⟩
  · by_cases hω : ω ∈ A
    · simp only [if_pos hω]; exact hK10 ω
    · simp only [if_neg hω]; exact hK20 ω
  · by_cases hω : ω ∈ A
    · have : tw T S s (fun u ω => if ω ∈ A then H1 u ω else H2 u ω) ω = tw T S s H1 ω :=
        tw_congr S (fun _ => rfl) fun u _ => by simp [hω]
      rw [this]; simp only [if_pos hω]; exact h.1 hω
    · have : tw T S s (fun u ω => if ω ∈ A then H1 u ω else H2 u ω) ω = tw T S s H2 ω :=
        tw_congr S (fun _ => rfl) fun u _ => by simp [hω]
      rw [this]; simp only [if_neg hω]; exact h.2 hω

lemma closed_all (hS : ∀ t ≤ T, Measurable (S t)) (hNA : NA Pset ℱ T S) :
    ∀ k ≤ T, ClosedSeq ℱ Pset T S (T - k) 0 := by
  intro k
  induction k with
  | zero => intro _; simpa using closed_top ℱ Pset (T := T) (S := S)
  | succ k ih =>
    intro hk
    have hs : T - (k+1) < T := by omega
    have hnext : ClosedSeq ℱ Pset T S (T - (k+1) + 1) 0 := by
      have := ih (by omega); rwa [show T - (k+1) + 1 = T - k by omega]
    have hinner : ∀ j ≤ d, ClosedSeq ℱ Pset T S (T - (k+1)) (d - j) := by
      intro j
      induction j with
      | zero => intro _; simpa using closed_full ℱ Pset hs hnext
      | succ j ihj =>
        intro hj
        have := ihj (by omega)
        exact closed_step ℱ Pset hs (by omega) hS hNA hnext
          (by rwa [show d - (j+1) + 1 = d - j by omega])
    simpa using hinner d le_rfl

end Steps

end Thm22Aux

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Pset : Set (Measure Ω)) (hPne : Pset.Nonempty) (hPprob : ∀ P ∈ Pset, IsProbabilityMeasure P)
    {T d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable (S t))
    (hNA : NA Pset ℱ T S)
    (W : ℕ → Ω → ℝ) (hWmeas : ∀ n, Measurable (W n)) (hWC : ∀ n, InCone Pset ℱ T S (W n))
    (Wlim : Ω → ℝ) (hWlim : Measurable Wlim)
    (hconv : QS Pset (fun ω => Tendsto (fun n => W n ω) atTop (𝓝 (Wlim ω)))) :
    InCone Pset ℱ T S Wlim := by
  choose H hH K hKm hK0 hq using hWC
  have hcl := Thm22Aux.closed_all ℱ Pset hS hNA T le_rfl
  rw [Nat.sub_self] at hcl
  have hconv' : QS Pset (fun ω => Tendsto (fun n => Thm22Aux.tw T S 0 (H n) ω - K n ω) atTop
      (𝓝 (Wlim ω))) := by
    refine Thm22Aux.qs_mono (Thm22Aux.qs_and hconv (Thm22Aux.qs_forall hq)) fun ω h => ?_
    refine h.1.congr fun n => ?_
    rw [h.2 n, Thm22Aux.wealth_eq_tw0]
  obtain ⟨H', hH', K', hK'm, hK'0, hq'⟩ := hcl H K Wlim (fun n u _ huT => hH n u huT) hKm hK0
    hWlim hconv' (Thm22Aux.qs_always _ fun _ => Nat.zero_le _)
  exact ⟨H', fun u hu => hH' u (Nat.zero_le u) hu, K', hK'm, hK'0,
    Thm22Aux.qs_mono hq' fun ω h => by rw [h, Thm22Aux.wealth_eq_tw0]⟩
