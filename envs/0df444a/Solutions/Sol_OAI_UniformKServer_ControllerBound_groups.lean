-- Prove2me | solution 1 for OAI.UniformKServer.ControllerBound.groups
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:59:41.292832+00:00
-- url     : https://prove2.me/submissions/f45f6b34-cd58-4a26-ae10-c208f0f1245f

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk007
import Definitions.Def_Q220Uk008

section
-- module Solutions.Q220_UK.UniformKServer_BitSampling
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

theorem exact_row_proof {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  let e : (Fin b → Bool) ≃ ((j : Fin k) × Fin (N j)) :=
    (bitsEquiv b).trans ((finCongr hN).symm.trans finSigmaFinEquiv.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro coins
    exact Nat.zero_lt_of_lt (e coins).2.isLt
  · intro coins
    have he := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply
      ((finCongr hN).symm (bitsEquiv b coins)))
    rw [finSigmaFinEquiv_apply] at he
    change cumulative N (row N hN coins) + (e coins).2.val = (bitsEquiv b coins).val at he
    have ht := (e coins).2.isLt
    change (e coins).2.val < N (row N hN coins) at ht
    omega
  · intro f
    have hs : (∑ coins : Fin b → Bool, f (row N hN coins)) =
        ∑ j, (N j : ℝ) * f j := by
      calc
        _ = ∑ v : (j : Fin k) × Fin (N j), f v.1 :=
          e.sum_comp (fun v => f v.1)
        _ = _ := by simp [Fintype.sum_sigma]
    rw [hs, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring

                                                                            
theorem exact_row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  exact exact_row_proof N hN

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BitPaths
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

theorem mean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (v : B → ℝ) : mean (fun a => v (e a)) = mean v := by
  unfold mean
  rw [e.sum_comp, Fintype.card_congr e]

theorem mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    mean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α:=A))
  simp [mean, hc]

theorem mean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a,b))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [mul_comm (Fintype.card A : ℝ), div_mul_eq_div_div, Finset.sum_div]

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BoundedFilter
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.lazyPath_nil_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

private theorem distance_nonneg {n : ℕ} (d : RationalMetric n) (x y : Fin n) :
    (0 : ℝ) ≤ d.distance x y := by exact_mod_cast d.nonneg x y

private theorem distance_triangle {n : ℕ} (d : RationalMetric n) (x y z : Fin n) :
    (d.distance x z : ℝ) ≤ d.distance x y + d.distance y z := by
  exact_mod_cast d.triangle x y z

private theorem distance_self {n : ℕ} (d : RationalMetric n) (x : Fin n) :
    (d.distance x x : ℝ) = 0 := by
  exact_mod_cast (d.eq_zero x x).2 rfl

private theorem mismatch_nonneg {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) : 0 ≤ mismatch d u s :=
  Finset.sum_nonneg (fun _ _ => distance_nonneg d _ _)

private theorem mismatch_le_diameter {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) (D : ℝ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D) : mismatch d u s ≤ k * D := by
  calc
    mismatch d u s ≤ ∑ _j : Fin k, D := Finset.sum_le_sum (fun j _ => hdiam (u j) (s j))
    _ = k * D := by simp

private theorem mismatch_skip {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) (r : Fin n) (j : Fin k) :
    mismatch d u (serve s r j) ≤ mismatch d u s + (d.distance (s j) r : ℝ) := by
  classical
  unfold mismatch
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j, (d.distance (u i) (serve s r j i) : ℝ)) =
      ∑ i ∈ Finset.univ.erase j, (d.distance (u i) (s i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [serve, Finset.ne_of_mem_erase hi]
  rw [he]
  simp only [serve, Function.update_self]
  have hs := Finset.sum_erase_add Finset.univ (fun i => (d.distance (u i) (s i) : ℝ))
    (Finset.mem_univ j)
  have ht := distance_triangle d (u j) (s j) r
  linarith

private theorem mismatch_keep {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) (r : Fin n) (j : Fin k) :
    (d.distance (u j) r : ℝ) + mismatch d (serve u r j) (serve s r j) ≤
      (d.distance (s j) r : ℝ) + mismatch d u s := by
  classical
  unfold mismatch
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j,
      (d.distance (serve u r j i) (serve s r j i) : ℝ)) =
      ∑ i ∈ Finset.univ.erase j, (d.distance (u i) (s i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [serve, Finset.ne_of_mem_erase hi]
  rw [he]
  simp only [serve, Function.update_self, distance_self, add_zero]
  have hs := Finset.sum_erase_add Finset.univ (fun i => (d.distance (u i) (s i) : ℝ))
    (Finset.mem_univ j)
  have ht := distance_triangle d (u j) (s j) r
  linarith

/-- Skipped virtual visits are paid by triangle inequality; retained visits
synchronize the relevant actual and virtual labels. -/
theorem sublist_potential {n k : ℕ} (d : RationalMetric n)
    {g h : History n k} (hsub : g.Sublist h) (u s : Configuration n k) :
    costAlong d u g + mismatch d (finish u g) (finish s h) ≤
      costAlong d s h + mismatch d u s := by
  induction hsub generalizing u s with
  | slnil => simp [costAlong, finish]
  | cons a hsub ih =>
    rcases a with ⟨r,j⟩
    have hi := ih u (serve s r j)
    have ht := mismatch_skip d u s r j
    simp only [costAlong, finish]
    linarith
  | cons_cons a hsub ih =>
    rcases a with ⟨r,j⟩
    have hi := ih (serve u r j) (serve s r j)
    have ht := mismatch_keep d u s r j
    simp only [costAlong, finish]
    linarith

theorem costAlong_nonneg {n k : ℕ} (d : RationalMetric n)
    (s : Configuration n k) (h : History n k) : 0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    exact add_nonneg (distance_nonneg d _ _) (ih _)

/-- The infimum definition of OPT is bounded below even before selecting a
minimizer. Every explicit legal label history gives an upper bound. -/
theorem offlineCost_le_history {n k : ℕ} (d : RationalMetric n)
    (s : Configuration n k) (h : History n k) :
    offlineCost d s (h.map Prod.fst) ≤ costAlong d s h := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨g, _, rfl⟩
    exact costAlong_nonneg d s g
  · exact ⟨h, rfl, rfl⟩

end UniformKServer

/-- Exact pathwise transfer needed at every restart and for deleting requests.
Source: Section 03, equations actual-virtual and subsequence-comparison. -/
theorem subsequence_cost_transfer {n k : ℕ} (d : UniformKServer.RationalMetric n)
    (u s : UniformKServer.Configuration n k) (g h : UniformKServer.History n k)
    (hsub : g.Sublist h) (D : ℝ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D) :
    UniformKServer.costAlong d u g +
      UniformKServer.mismatch d (UniformKServer.finish u g) (UniformKServer.finish s h) ≤
      UniformKServer.costAlong d s h + UniformKServer.mismatch d u s ∧
    UniformKServer.costAlong d u g ≤ UniformKServer.costAlong d s h + k * D ∧
    UniformKServer.offlineCost d u (g.map Prod.fst) ≤
      UniformKServer.costAlong d s h + k * D := by
  have hp := UniformKServer.sublist_potential d hsub u s
  have hn := UniformKServer.mismatch_nonneg d (UniformKServer.finish u g)
    (UniformKServer.finish s h)
  have hu := UniformKServer.mismatch_le_diameter d u s D hdiam
  have hb : UniformKServer.costAlong d u g ≤ UniformKServer.costAlong d s h + k * D :=
    by linarith
  exact ⟨hp, hb, (UniformKServer.offlineCost_le_history d u g).trans hb⟩



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Epochs
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFilter.allCover_state _root_.OAI.UniformKServer.RawFilter.births_entry _root_.OAI.UniformKServer.RawFilter.cover_entry _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

/-- Source Lemma `lem:filter`: all created entries, the live list, and the kept
word are bounded by H, for every raw finite prefix, even when the list empties.
The deterministic filter and bound do not inspect any random online trajectory. -/
theorem filter_bounds {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (raw : List (Fin n)) :
    let s := runFilter M u raw
    s.created ≤ horizon k M ∧ s.live.length ≤ horizon k M ∧
      s.kept.length ≤ horizon k M := by
  dsimp
  obtain ⟨_, hb, hf⟩ := runFilter_good M u raw
  have hl := length_le_mass M (runFilter M u raw).live
  rw [treeBudget_eq_horizon] at hb hf
  omega

theorem lazyPath_snoc_iff {n k : ℕ} (u : Configuration n k)
    (w : List (Fin n)) (r : Fin n) (e' : Entry n k) :
    LazyPath u (w ++ [r]) e' ↔ ∃ e, LazyPath u w e ∧ LazyStep e r e' := by
  constructor
  · intro h
    generalize hw : w ++ [r] = wr at h
    cases h with
    | nil => simp at hw
    | @snoc w' e e' r' hp hs =>
      have hw' : w = w' ∧ r = r' := by simpa using hw
      rcases hw' with ⟨rfl, rfl⟩
      exact ⟨_, hp, hs⟩
  · rintro ⟨e, hp, hs⟩
    exact LazyPath.snoc hp hs

theorem lazyStep_moves_mono {n k : ℕ} {e e' : Entry n k} {r : Fin n}
    (h : LazyStep e r e') : e.moves ≤ e'.moves := by
  unfold LazyStep at h
  split_ifs at h with hc
  · subst e'; exact le_rfl
  · obtain ⟨j, rfl⟩ := h
    exact Nat.le_succ _

theorem mem_expand_iff {n k : ℕ} (M : ℕ) (r : Fin n) (e e' : Entry n k)
    (he : e.moves ≤ M) :
    e' ∈ expand M r e ↔ LazyStep e r e' ∧ e'.moves ≤ M := by
  by_cases hc : Covers e r
  · simp only [expand, LazyStep, hc, ↓reduceIte, List.mem_singleton]
    exact ⟨fun h => ⟨h, h ▸ he⟩, And.left⟩
  · by_cases hm : e.moves < M
    · simp only [expand, hc, ↓reduceIte, hm, List.mem_map, List.mem_finRange,
        true_and, LazyStep]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j, rfl⟩, by dsimp; omega⟩
      · rintro ⟨⟨j, rfl⟩, _⟩
        exact ⟨j, rfl⟩
    · simp only [expand, hc, ↓reduceIte, hm, List.not_mem_nil, LazyStep,
        false_iff, not_and]
      rintro ⟨j, rfl⟩
      dsimp
      omega

theorem initial_represents {n k : ℕ} (M : ℕ) (u : Configuration n k) :
    Represents M u (initial u) := by
  intro e
  simp only [initial, List.mem_singleton, lazyPath_nil_iff]
  exact ⟨fun h => ⟨h, by rw [h]; exact Nat.zero_le _⟩, And.left⟩

theorem step_represents {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (s : FilterState n k) (r : Fin n) (hs : Represents M u s) :
    Represents M u (step M s r) := by
  unfold step
  split_ifs with hc
  · exact hs
  · intro e'
    dsimp
    rw [List.mem_flatMap, lazyPath_snoc_iff]
    constructor
    · rintro ⟨e, he, he'⟩
      obtain ⟨hp, hm⟩ := (hs e).mp he
      obtain ⟨hstep, hm'⟩ := (mem_expand_iff M r e e' hm).mp he'
      exact ⟨⟨e, hp, hstep⟩, hm'⟩
    · rintro ⟨⟨e, hp, hstep⟩, hm'⟩
      have hm : e.moves ≤ M := (lazyStep_moves_mono hstep).trans hm'
      exact ⟨e, (hs e).mpr ⟨hp, hm⟩,
        (mem_expand_iff M r e e' hm).mpr ⟨hstep, hm'⟩⟩

theorem lazyStep_injective {n k : ℕ} {e e' : Entry n k} {r : Fin n}
    (hi : Function.Injective e.position) (hs : LazyStep e r e') :
    Function.Injective e'.position := by
  unfold LazyStep at hs
  split_ifs at hs with hc
  · subst e'; exact hi
  · obtain ⟨j, rfl⟩ := hs
    intro a b hab
    dsimp at hab
    by_cases ha : a = j
    · subst a
      by_cases hb : b = j
      · exact hb.symm
      · have heq : r = e.position b := by simpa [Function.update, hb] using hab
        exact False.elim (hc ⟨b, heq.symm⟩)
    · by_cases hb : b = j
      · subst b
        have heq : e.position a = r := by simpa [Function.update, ha] using hab
        exact False.elim (hc ⟨a, heq⟩)
      · apply hi
        simpa [Function.update, ha, hb] using hab

theorem lazyPath_injective {n k : ℕ} {u : Configuration n k}
    (hu : Function.Injective u) {w : List (Fin n)} {e : Entry n k}
    (hp : LazyPath u w e) : Function.Injective e.position := by
  induction hp with
  | nil => exact hu
  | snoc hp hs ih => exact lazyStep_injective ih hs

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Fallback
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.lazyPath_nil_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer
namespace Fallback


theorem pick_mem {k : ℕ} (hk : 0 < k) (A : Finset (Fin k)) (hA : A.Nonempty) :
    pick hk A ∈ A := by
  simp only [pick, hA, ↓reduceDIte]
  exact A.min'_mem hA

theorem misses_card_lt {n k : ℕ} (s : State n k) (S : Finset (Fin n))
    (hv : Valid s S) (r : Fin n) (hr : r ∈ S)
    (hn : ¬(coverers s.position r).Nonempty) : s.marked.card < k := by
  have hs : r ∉ s.marked.image s.position := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact hn ⟨j, by simpa using hj⟩
  have hb : insert r (s.marked.image s.position) ⊆ S :=
    Finset.insert_subset hr hv.2.1
  have hc := Finset.card_le_card hb
  rw [Finset.card_insert_of_notMem hs,
    Finset.card_image_of_injective _ hv.1] at hc
  exact lt_of_lt_of_le (by omega) hv.2.2

theorem free_nonempty {k : ℕ} (m : Finset (Fin k)) (h : m.card < k) :
    (Finset.univ \ m).Nonempty := by
  apply Finset.nonempty_of_ne_empty
  intro he
  have hm : m = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    have : j ∈ Finset.univ \ m := by simp [hj]
    simp [he] at this
  simp [hm] at h

theorem choice_hit_or_free {n k : ℕ} (hk : 0 < k) (s : State n k)
    (S : Finset (Fin n)) (hv : Valid s S) (r : Fin n) (hr : r ∈ S) :
    s.position (choose hk s r) = r ∨ choose hk s r ∉ s.marked := by
  unfold choose
  split_ifs with hc
  · exact Or.inl ((mem_coverers _ _ _).1 (pick_mem hk _ hc))
  · right
    have hf := free_nonempty s.marked (misses_card_lt s S hv r hr hc)
    exact (Finset.mem_sdiff.mp (pick_mem hk _ hf)).2

theorem updated_injective {n k : ℕ} (hk : 0 < k) (s : State n k)
    (r : Fin n) (hs : Function.Injective s.position) :
    Function.Injective (step hk s r).position := by
  by_cases hc : (coverers s.position r).Nonempty
  · have hh : s.position (choose hk s r) = r := by
      simpa [choose, hc] using (mem_coverers _ _ _).1 (pick_mem hk _ hc)
    have he : (step hk s r).position = s.position := by
      dsimp [step, serve]
      conv_lhs => arg 3; rw [← hh]
      exact Function.update_eq_self _ _
    simpa [he] using hs
  · have hn : ∀ j, s.position j ≠ r := by
      intro j hj
      exact hc ⟨j, (mem_coverers _ _ _).2 hj⟩
    intro i j hij
    change Function.update s.position (choose hk s r) r i =
      Function.update s.position (choose hk s r) r j at hij
    by_cases hi : i = choose hk s r
    · subst i
      by_cases hj : j = choose hk s r
      · exact hj.symm
      · simp only [Function.update_self, Function.update_of_ne hj] at hij
        exact False.elim (hn j hij.symm)
    · by_cases hj : j = choose hk s r
      · subst j
        simp only [Function.update_self, Function.update_of_ne hi] at hij
        exact False.elim (hn i hij)
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj] at hij
        exact hs hij

/-- Source Lemma fallback: the exact nonendpoint marking rule is feasible. -/
theorem step_guarantee {n k : ℕ} (hk : 0 < k) (s : State n k)
    (S : Finset (Fin n)) (hv : Valid s S) (r : Fin n) (hr : r ∈ S) :
    Valid (step hk s r) S ∧
    (∀ j ∈ s.marked, (step hk s r).position j = s.position j) := by
  have hh := choice_hit_or_free hk s S hv r hr
  have hp : ∀ j ∈ s.marked, (step hk s r).position j = s.position j := by
    intro j hj
    dsimp [step, serve]
    by_cases he : j = choose hk s r
    · subst j
      rw [Function.update_self]
      exact (hh.resolve_right (not_not.mpr hj)).symm
    · exact Function.update_of_ne he _ _
  refine ⟨⟨updated_injective hk s r hv.1, ?_, hv.2.2⟩, hp⟩
  intro p hp'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp'
  change j ∈ insert (choose hk s r) s.marked at hj
  rcases Finset.mem_insert.mp hj with he | hj
  · subst j
    simpa [step, serve] using hr
  · rw [hp j hj]
    exact hv.2.1 (Finset.mem_image.mpr ⟨j,hj,rfl⟩)

theorem step_cost {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : State n k) (S : Finset (Fin n)) (hv : Valid s S)
    (r : Fin n) (hr : r ∈ S) :
    (d.distance (s.position (choose hk s r)) r : ℝ) + s.marked.card * D ≤
      (step hk s r).marked.card * D := by
  by_cases hm : choose hk s r ∈ s.marked
  · have hh := (choice_hit_or_free hk s S hv r hr).resolve_right (not_not.mpr hm)
    have hz : (d.distance r r : ℝ) = 0 := by exact_mod_cast (d.eq_zero r r).2 rfl
    simp [step, Finset.insert_eq_of_mem hm, hh, hz]
  · have hc : (step hk s r).marked.card = s.marked.card + 1 := by
      exact Finset.card_insert_of_notMem hm
    rw [hc, Nat.cast_add, Nat.cast_one]
    have hd := hdiam (s.position (choose hk s r)) r
    nlinarith

end Fallback


namespace Fallback


theorem endpoint_injective {n k : ℕ} (hk : 0 < k) (c : Configuration n k)
    (hc : Function.Injective c) (r : Fin n) :
    Function.Injective (serve c r (pick hk (coverers c r))) := by
  by_cases hcov : (coverers c r).Nonempty
  · have hh : c (pick hk (coverers c r)) = r :=
      (mem_coverers _ _ _).1 (pick_mem hk _ hcov)
    have he : serve c r (pick hk (coverers c r)) = c := by
      unfold serve
      conv_lhs => arg 3; rw [← hh]
      exact Function.update_eq_self _ _
    simpa [he] using hc
  · have hf : ∀ j, c j ≠ r := fun j hj => hcov ⟨j, by simpa using hj⟩
    intro i j hij
    change Function.update c (pick hk (coverers c r)) r i =
      Function.update c (pick hk (coverers c r)) r j at hij
    by_cases hi : i = pick hk (coverers c r)
    · subst i
      by_cases hj : j = pick hk (coverers c r)
      · exact hj.symm
      · simp only [Function.update_self, Function.update_of_ne hj] at hij
        exact (hf j hij.symm).elim
    · by_cases hj : j = pick hk (coverers c r)
      · subst j
        simp only [Function.update_self, Function.update_of_ne hi] at hij
        exact (hf i hij).elim
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj] at hij
        exact hc hij

theorem raw_step_valid {n k : ℕ} (hk : 0 < k) (s : RawState n k)
    (hv : Valid s.marking s.seen) (r : Fin n) :
    Valid (rawStep hk s r).marking (rawStep hk s r).seen := by
  by_cases he : isEndpoint s r
  · simp only [rawStep, he, ↓reduceIte, rawChoice]
    exact ⟨endpoint_injective hk _ hv.1 r, by simp, by simp⟩
  · have hn : (insert r s.seen).card ≤ k := le_of_not_gt he
    have hv' : Valid s.marking (insert r s.seen) :=
      ⟨hv.1, hv.2.1.trans (Finset.subset_insert _ _), hn⟩
    simpa [rawStep, he] using
      (step_guarantee hk s.marking (insert r s.seen) hv' r (by simp)).1

theorem raw_step_position {n k : ℕ} (hk : 0 < k) (s : RawState n k) (r : Fin n) :
    (rawStep hk s r).marking.position = serve s.marking.position r (rawChoice hk s r) := by
  by_cases he : isEndpoint s r <;> simp [rawStep, rawChoice, step, he]

theorem raw_step_cost {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : RawState n k) (hv : Valid s.marking s.seen) (r : Fin n) :
    (d.distance (s.marking.position (rawChoice hk s r)) r : ℝ) + ledger D s ≤
      ledger D (rawStep hk s r) := by
  by_cases he : isEndpoint s r
  · have hcard : s.marking.marked.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ s.marking.marked)
    have hcard' : (s.marking.marked.card : ℝ) ≤ k := by exact_mod_cast hcard
    have hh := hdiam (s.marking.position (rawChoice hk s r)) r
    simp only [ledger, rawStep, he, ↓reduceIte, Finset.card_empty, Nat.cast_zero,
      zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hcard' hD]
  · have hv' : Valid s.marking (insert r s.seen) :=
      ⟨hv.1, hv.2.1.trans (Finset.subset_insert _ _), le_of_not_gt he⟩
    have hb := step_cost hk d D hdiam s.marking (insert r s.seen) hv' r (by simp)
    simpa [rawChoice, rawStep, he, ledger, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hb (s.completed * (k+1) * D)

theorem raw_run_ledger {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : RawState n k) (hv : Valid s.marking s.seen) (w : List (Fin n)) :
    Valid (rawRun hk s w).marking (rawRun hk s w).seen ∧
    (rawTrace hk s w).map Prod.fst = w ∧
    costAlong d s.marking.position (rawTrace hk s w) + ledger D s ≤
      ledger D (rawRun hk s w) := by
  induction w generalizing s with
  | nil => exact ⟨hv, rfl, by simp [rawTrace, rawRun, costAlong]⟩
  | cons r w ih =>
    have hv' := raw_step_valid hk s hv r
    have hi := ih (rawStep hk s r) hv'
    have hs := raw_step_cost hk d D hD hdiam s hv r
    refine ⟨hi.1, ?_, ?_⟩
    · simpa [rawTrace] using congrArg (List.cons r) hi.2.1
    · simp only [rawTrace, costAlong, rawRun]
      rw [← raw_step_position]
      linarith [hi.2.2]

theorem ledger_le_portions {n k : ℕ} (D : ℝ) (hD : 0 ≤ D) (s : RawState n k)
    (hv : Valid s.marking s.seen) : ledger D s ≤ portions s * (k+1) * D := by
  by_cases he : s.seen.Nonempty
  · have hcard : s.marking.marked.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ s.marking.marked)
    have hcard' : (s.marking.marked.card : ℝ) ≤ k+1 := by exact_mod_cast (by omega : s.marking.marked.card ≤ k+1)
    have hm := mul_le_mul_of_nonneg_right hcard' hD
    simp only [ledger, portions, he, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    nlinarith
  · have hem : s.seen = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hmarks : s.marking.marked = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have h := hv.2.1 (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
      simp [hem] at h
    simp [ledger, portions, he, hmarks]

/-- The literal marking fallback of Section 03, including raw block endpoints,
an inherited pre-switch raw block, and any finite truncation. -/
theorem raw_fallback_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (c : Configuration n k) (hc : Function.Injective c)
    (seen : Finset (Fin n)) (hs : seen.card ≤ k)
    (w : List (Fin n)) (R : ℕ)
    (hR : portions (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R) :
    Valid (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w).marking
      (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w).seen ∧
    (rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w).map Prod.fst = w ∧
    costAlong d c (rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R * (k+1) * D := by
  have hv : Valid (⟨c,∅⟩ : State n k) seen := ⟨hc, by simp, hs⟩
  have hr := raw_run_ledger hk d D hD hdiam ⟨⟨c,∅⟩,seen,0⟩ hv w
  have hb := ledger_le_portions D hD (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) hr.1
  have hR' : ((portions (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) : ℕ) : ℝ) ≤ R := by
    exact_mod_cast hR
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hR' (by positivity : (0:ℝ) ≤ k+1)) hD
  refine ⟨hr.1, hr.2.1, ?_⟩
  have hl : ledger D (⟨⟨c,∅⟩,seen,0⟩ : RawState n k) = 0 := by simp [ledger]
  rw [hl, add_zero] at hr
  exact hr.2.2.trans (hb.trans hm)

end Fallback
end UniformKServer


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochShadow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.nextSeen_bits _root_.OAI.UniformKServer.RawFilter.allCover_state _root_.OAI.UniformKServer.RawFilter.births_entry _root_.OAI.UniformKServer.RawFilter.cover_entry _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochShadow



theorem raw_count {n k : ℕ} (hk : 0 < k) (s : Fallback.RawState n k)
    (w : List (Fin n)) :
    Fallback.portions (Fallback.rawRun hk s w) = s.completed + blockCount (k:=k) s.seen w := by
  induction w generalizing s with
  | nil => rfl
  | cons r w ih =>
    rw [Fallback.rawRun, ih]
    by_cases he : k < (insert r s.seen).card <;>
      simp [Fallback.rawStep, Fallback.isEndpoint, he, blockCount, bookStep, Nat.add_assoc]

theorem book_card {n k : ℕ} (seen : Finset (Fin n)) (r : Fin n) :
    (bookStep (k:=k) seen r).card ≤ k := by
  unfold bookStep
  split_ifs with h
  · simp
  · exact le_of_not_gt h

theorem block_tail_le {n k : ℕ} (seen : Finset (Fin n)) (r : Fin n) (w : List (Fin n)) :
    blockCount (k:=k) (bookStep (k:=k) seen r) w ≤ blockCount (k:=k) seen (r::w) := by
  simp only [blockCount]
  omega

theorem kept_tail_snoc {n k : ℕ} (M : ℕ) (f : FilterState n k) (w : List (Fin n)) :
    (w.foldl (UniformKServer.step M) f).kept = f.kept ++ keptTail M f w := by
  induction w generalizing f with
  | nil => simp [keptTail]
  | cons r w ih =>
    rw [List.foldl_cons, ih]
    by_cases h : ∀ e ∈ f.live, Covers e r
    · simp only [keptTail, UniformKServer.step, ite_eq_left h]
    · simp only [keptTail, UniformKServer.step, ite_eq_right h, List.append_assoc, List.singleton_append]

theorem kept_tail_full {n k : ℕ} (M : ℕ) (u : Configuration n k) (raw : List (Fin n)) :
    keptTail M (initial u) raw = (runFilter M u raw).kept := by
  simpa [runFilter, initial] using (kept_tail_snoc M (initial u) raw).symm

theorem next_lazy {n k : ℕ} (T : Selector n k) (hT : StronglyLazy T)
    (p : List (Fin n)) (e : Entry n k) (r : Fin n) :
    LazyStep e r (nextEntry e r (T p e.position r)) := by
  unfold LazyStep
  split_ifs with h
  · have hj := hT p e.position r h
    have hc : serve e.position r (T p e.position r) = e.position := by
      unfold serve
      conv_lhs => arg 3; rw [← hj]
      exact Function.update_eq_self _ _
    cases e
    simp_all [nextEntry]
  · have hj : e.position (T p e.position r) ≠ r := fun hh => h ⟨_,hh⟩
    exact ⟨T p e.position r, by simp [nextEntry, hj, serve]⟩

theorem next_cost {n k : ℕ} (d : RationalMetric n) (δ : ℝ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (e : Entry n k) (r : Fin n) (j : Fin k) (paid : ℝ)
    (hp : e.moves * δ ≤ paid) :
    (nextEntry e r j).moves * δ ≤ paid + (d.distance (e.position j) r : ℝ) := by
  by_cases h : e.position j = r
  · simp only [nextEntry, ite_eq_left h, Nat.add_zero]
    exact hp.trans (le_add_of_nonneg_right (by exact_mod_cast d.nonneg _ _))
  · simp only [nextEntry, ite_eq_right h, Nat.cast_add, Nat.cast_one]
    nlinarith [hsep _ _ h]

theorem fallback_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (c : Configuration n k) (hc : Function.Injective c)
    (seen : Finset (Fin n)) (hs : seen.card ≤ k)
    (w : List (Fin n)) (R : ℕ) (hR : blockCount (k:=k) seen w ≤ R) :
    (Fallback.rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w).map Prod.fst = w ∧
    costAlong d c (Fallback.rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R * (k+1) * D := by
  have hR' : Fallback.portions (Fallback.rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R := by
    simpa [raw_count] using hR
  exact (Fallback.raw_fallback_bound hk d D hD hdiam c hc seen hs w R hR').2


/-- Paying for fallback by an already accumulated *unconditioned* shadow
prefix; the comparison never conditions on the event of reaching the cap. -/
theorem trace_ledger {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (T : Selector n k) (hT : StronglyLazy T) (u : Configuration n k)
    (hu : Function.Injective u) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (raw : List (Fin n)) (f : FilterState n k) (e : Entry n k)
    (seen : Finset (Fin n)) (paid : ℝ)
    (hf : Represents M u f) (hp : LazyPath u f.kept e) (hm : e.moves ≤ M)
    (hs : seen.card ≤ k) (hR : blockCount (k:=k) seen raw ≤ R)
    (hpaid : e.moves * δ ≤ paid) :
    (trace hk M T f e seen raw).map Prod.fst = raw ∧
    costAlong d e.position (trace hk M T f e seen raw) ≤
      paid + 2 * costAlong d e.position (shadowTrace T f.kept e.position (keptTail M f raw)) := by
  induction raw generalizing f e seen paid with
  | nil =>
    have hn : 0 ≤ paid := (mul_nonneg (Nat.cast_nonneg _) hδ).trans hpaid
    simpa only [trace, List.map_nil, keptTail, shadowTrace, costAlong, mul_zero, add_zero,
      true_and] using hn
  | cons r w ih =>
    have hs' := book_card (k:=k) seen r
    have hR' := (block_tail_le (k:=k) seen r w).trans hR
    by_cases hdrop : ∀ z ∈ f.live, Covers z r
    · have hc := hdrop e ((hf e).mpr ⟨hp,hm⟩)
      let j := Fallback.pick hk (Fallback.coverers e.position r)
      have hj : e.position j = r := by
        apply (Fallback.mem_coverers _ _ _).mp
        apply Fallback.pick_mem
        rcases hc with ⟨l,hl⟩
        exact ⟨l,(Fallback.mem_coverers _ _ _).mpr hl⟩
      have heq : serve e.position r j = e.position := by
        unfold serve
        conv_lhs => arg 3; rw [← hj]
        exact Function.update_eq_self _ _
      have hz : (d.distance (e.position j) r : ℝ) = 0 := by
        rw [hj, (d.eq_zero r r).mpr rfl, Rat.cast_zero]
      have hi := ih f e (bookStep (k:=k) seen r) paid hf hp hm hs' hR' hpaid
      dsimp only [j] at heq hz
      simpa only [trace, ite_eq_left hdrop, keptTail, List.map_cons, costAlong,
        heq, hz, zero_add, List.cons.injEq, true_and] using hi
    · let j := T f.kept e.position r
      let e' := nextEntry e r j
      let f' := UniformKServer.step M f r
      let q : ℝ := (d.distance (e.position j) r : ℝ)
      have hq : 0 ≤ q := by
        dsimp [q]
        exact_mod_cast d.nonneg (e.position j) r
      have hnew : e'.moves * δ ≤ paid+q := next_cost d δ hsep e r j paid hpaid
      have hls : LazyStep e r e' := next_lazy T hT f.kept e r
      have hfp : f'.kept = f.kept ++ [r] := by
        simp only [f', UniformKServer.step, ite_eq_right hdrop]
      have hpath : LazyPath u f'.kept e' := hfp ▸ LazyPath.snoc hp hls
      have hf' : Represents M u f' := step_represents M u f r hf
      by_cases hcont : e'.moves ≤ M
      · dsimp only [e', j] at hcont
        have hi := ih f' e' (bookStep (k:=k) seen r) (paid+q)
          hf' hpath hcont hs' hR' hnew
        constructor
        · simpa only [trace, ite_eq_right hdrop, ite_eq_left hcont, List.map_cons,
            List.cons.injEq, true_and] using hi.1
        · simp only [trace, ite_eq_right hdrop, ite_eq_left hcont, keptTail, shadowTrace,
            costAlong]
          change q + costAlong d e'.position (trace hk M T f' e' (bookStep seen r) w) ≤
            paid+2*(q + costAlong d e'.position
              (shadowTrace T (f.kept++[r]) e'.position (keptTail M f' w)))
          rw [hfp] at hi
          linarith [hi.2]
      · dsimp only [e', j] at hcont
        have hc : (M+1 : ℝ)*δ ≤ paid+q := by
          have hm' : M+1 ≤ e'.moves := Nat.succ_le_of_lt (lt_of_not_ge hcont)
          have hm'' : (M+1 : ℝ) ≤ e'.moves := by exact_mod_cast hm'
          exact (mul_le_mul_of_nonneg_right hm'' hδ).trans hnew
        have hb := fallback_bound hk d D hD hdiam e'.position
          (lazyPath_injective hu hpath) (bookStep (k:=k) seen r) hs' w R hR'
        constructor
        · simpa only [trace, ite_eq_right hdrop, ite_eq_right hcont, List.map_cons,
            List.cons.injEq, true_and] using hb.1
        · simp only [trace, ite_eq_right hdrop, ite_eq_right hcont, keptTail, shadowTrace,
            costAlong]
          change q + costAlong d e'.position
            (Fallback.rawTrace hk ⟨⟨e'.position,∅⟩,bookStep seen r,0⟩ w) ≤
            paid + 2*(q + costAlong d e'.position
              (shadowTrace T (f.kept++[r]) e'.position (keptTail M f' w)))
          have hn := costAlong_nonneg d e'.position
            (shadowTrace T (f.kept++[r]) e'.position (keptTail M f' w))
          linarith [hb.2]

theorem epoch_virtual_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (T : Selector n k) (hT : StronglyLazy T) (u : Configuration n k)
    (hu : Function.Injective u) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R) :
    (trace hk M T (initial u) ⟨u,0⟩ ∅ raw).map Prod.fst = raw ∧
    costAlong d u (trace hk M T (initial u) ⟨u,0⟩ ∅ raw) ≤
      2 * costAlong d u (shadowTrace T [] u (keptTail M (initial u) raw)) := by
  have h := trace_ledger hk d T hT u hu M R D δ hD hδ hdiam hsep hcap raw
    (initial u) ⟨u,0⟩ ∅ 0 (initial_represents M u) LazyPath.nil
    (Nat.zero_le _) (by simp) hR (by simp)
  simpa only [initial, zero_add] using h

theorem epoch_actual_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (T : Selector n k) (hT : StronglyLazy T) (u s : Configuration n k)
    (hu : Function.Injective u) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R) :
    costAlong d s (trace hk M T (initial u) ⟨u,0⟩ ∅ raw) ≤
      2 * costAlong d u (shadowTrace T [] u (keptTail M (initial u) raw)) + k*D := by
  have hv := epoch_virtual_bound hk d T hT u hu M R D δ hD hδ hdiam hsep hcap raw hR
  have ht := subsequence_cost_transfer d s u
    (trace hk M T (initial u) ⟨u,0⟩ ∅ raw)
    (trace hk M T (initial u) ⟨u,0⟩ ∅ raw) (List.Sublist.refl _) D hdiam
  linarith [ht.2.1, hv.2]


end UniformKServer.EpochShadow

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBlockCharge
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.RawBlockCharge

theorem split_history {n k : ℕ} (h : History n k) (w v : List (Fin n))
    (hw : h.map Prod.fst = w++v) :
    ∃ g t, h = g++t ∧ g.map Prod.fst = w ∧ t.map Prod.fst = v := by
  refine ⟨h.take w.length, h.drop w.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.map_take, hw, List.take_left]
  · rw [List.map_drop, hw, List.drop_left]

end UniformKServer.RawBlockCharge


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochExpectation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochExpectation
open EpochShadow

theorem selector_lazy {n k b : ℕ} (N : BState n k → Fin n → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (hLazy : ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → N s r j = 0)
    (coins : ℕ → Fin b → Bool) : StronglyLazy (selector N hN coins) := by
  intro p c r hc
  by_contra hn
  have hz := hLazy (p,c) r (selector N hN coins p c r) hc hn
  have hp := (BitSampling.exact_row (N (p,c) r) (hN (p,c) r)).1 (coins p.length)
  change 0 < N (p,c) r (selector N hN coins p c r) at hp
  omega

theorem shadow_cost {n k b : ℕ} (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (coins : ℕ → Fin b → Bool) (p : List (Fin n)) (c : Configuration n k)
    (w : List (Fin n)) :
    costAlong d c (shadowTrace (selector N hN coins) p c w) =
      BitSampling.runCost N hN next (charge d) (p,c) w
        (fun i => coins (p.length + i.val)) := by
  induction w generalizing p c with
  | nil => rfl
  | cons r w ih =>
    simp only [shadowTrace, costAlong, BitSampling.runCost, selector, Fin.val_zero,
      add_zero, next, charge, ih]
    congr 1
    congr 1
    funext i
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      Fin.tail, Fin.val_succ]
    congr 1
    omega

theorem shadow_full {n k b : ℕ} (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (c : Configuration n k) (w : List (Fin n)) (coins : Fin w.length → Fin b → Bool) :
    costAlong d c (shadowTrace (selector N hN (extend coins)) [] c w) =
      BitSampling.runCost N hN next (charge d) ([],c) w coins := by
  rw [shadow_cost]
  congr 1
  funext i
  simp [extend, i.isLt]

theorem kept_sublist {n k : ℕ} (M : ℕ) (f : FilterState n k) (w : List (Fin n)) :
    (keptTail M f w).Sublist w := by
  induction w generalizing f with
  | nil => exact List.Sublist.refl _
  | cons r w ih =>
    unfold keptTail
    split_ifs
    · exact (ih f).cons r
    · exact (ih _).cons_cons r

theorem mean_mono {A : Type*} [Fintype A] (f g : A → ℝ) (h : ∀ a, f a ≤ g a) :
    BitSampling.mean f ≤ BitSampling.mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem mean_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    BitSampling.mean (fun a => c * f a) = c * BitSampling.mean f := by
  simp only [BitSampling.mean, ← Finset.mul_sum, mul_div_assoc]




end UniformKServer.EpochExpectation



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochControl
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.nextSeen_bits _root_.OAI.UniformKServer.RawFilter.allCover_state _root_.OAI.UniformKServer.RawFilter.births_entry _root_.OAI.UniformKServer.RawFilter.cover_entry _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.EpochControl
open EpochShadow

theorem rawChoice_congr {n k : ℕ} (hk : 0 < k) (s t : Fallback.RawState n k)
    (hm : s.marking=t.marking) (hs : s.seen=t.seen) (r : Fin n) :
    Fallback.rawChoice hk s r=Fallback.rawChoice hk t r := by
  simp [Fallback.rawChoice,Fallback.isEndpoint,hm,hs]
  rfl

theorem rawStep_congr {n k : ℕ} (hk : 0 < k) (s t : Fallback.RawState n k)
    (hm : s.marking=t.marking) (hs : s.seen=t.seen) (r : Fin n) :
    (Fallback.rawStep hk s r).marking=(Fallback.rawStep hk t r).marking ∧
    (Fallback.rawStep hk s r).seen=(Fallback.rawStep hk t r).seen := by
  have hc := rawChoice_congr hk s t hm hs r
  by_cases he : k < (insert r t.seen).card <;>
    simp [Fallback.rawStep,Fallback.isEndpoint,hm,hs,hc,he]

theorem fallbackTrace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (hs : s.fallback=true) (raw : Fallback.RawState n k)
    (hm : (asRaw s).marking=raw.marking) (hseen : s.seen=raw.seen) (w : List (Fin n)) :
    runTrace hk M T s w = Fallback.rawTrace hk raw w := by
  induction w generalizing s raw with
  | nil => rfl
  | cons r w ih =>
    have hchoice := rawChoice_congr hk (asRaw s) raw hm hseen r
    have hstep := rawStep_congr hk (asRaw s) raw hm hseen r
    simp only [runTrace,label,hs,ite_true, if_true,Fallback.rawTrace,hchoice]
    congr 1
    apply ih
    · simp [step,hs]
    · simpa [step,hs,asRaw] using hstep.1
    · simpa [step,hs] using hstep.2

theorem normalTrace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (hs : s.fallback=false) (w : List (Fin n)) :
    runTrace hk M T s w = trace hk M T s.filter s.virtual s.seen w := by
  induction w generalizing s with
  | nil => rfl
  | cons r w ih =>
    by_cases hit : ∀z ∈ s.filter.live,Covers z r
    · simp only [runTrace,label,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_left hit,trace]
      congr 1
      simpa only [step,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_left hit] using
        ih {s with seen := bookStep (k:=k) s.seen r} hs
    · let e := nextEntry s.virtual r (T s.filter.kept s.virtual.position r)
      by_cases hc : e.moves ≤ M
      · have he : ¬ M < e.moves := by omega
        simp only [runTrace,label,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_right hit,trace]
        simp only [show (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M from hc,
          ite_true, if_true]
        change _::_ = _::_
        congr 1
        simpa only [step,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_right hit,show ¬M<e.moves from he,
          decide_false,e] using ih (step hk M T s r) (by
            simp only [step,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_right hit]
            exact decide_eq_false he)
      · have he : M < e.moves := by omega
        simp only [runTrace,label,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_right hit,trace]
        simp only [show ¬(nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M from hc,
          ite_false, if_false]
        congr 1
        apply fallbackTrace
        · simp only [step,hs,Bool.false_eq_true,ite_false, if_false,ite_eq_right hit]
          exact decide_eq_true he
        · simp [asRaw,step,hs,hit]
        · simp [step,hs,hit]

theorem initial_trace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (u : Configuration n k) (w : List (Fin n)) :
    runTrace hk M T (initial u) w = trace hk M T (UniformKServer.initial u) ⟨u,0⟩ ∅ w :=
  normalTrace hk M T (initial u) rfl w

end UniformKServer.EpochControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFilter.allCover_state _root_.OAI.UniformKServer.RawFilter.births_entry _root_.OAI.UniformKServer.RawFilter.cover_entry _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.EpochTape
open EpochShadow EpochExpectation

theorem mean_restrict {m H : ℕ} (h : m ≤ H) {A : Type*} [Fintype A] [Nonempty A]
    (f : (Fin m → A) → ℝ) :
    BitSampling.mean (fun g : Fin H → A => f (fun i => g (Fin.castLE h i))) =
      BitSampling.mean f := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  have he := BitSampling.mean_equiv (Fin.appendEquiv (α:=A) m d)
    (fun g : Fin (m+d) → A => f (fun i => g (Fin.castLE (by omega) i)))
  have hh : (fun p : (Fin m → A) × (Fin d → A) =>
      f (fun i => Fin.append p.1 p.2 (Fin.castLE (by omega) i))) = fun p => f p.1 := by
    funext p
    congr 1
    funext i
    change Fin.append p.1 p.2 (Fin.castAdd d i) = p.1 i
    simp
  change BitSampling.mean (fun p : (Fin m → A) × (Fin d → A) =>
    f (fun i => Fin.append p.1 p.2 (Fin.castLE (by omega) i))) = _ at he
  rw [hh] at he
  rw [← he, BitSampling.mean_prod]
  simp only [BitSampling.mean_const]

theorem trace_congr {n k : ℕ} (hk : 0 < k) (M m : ℕ)
    (T U : Selector n k) (hTU : ∀p c r,p.length < m → T p c r=U p c r)
    (f : FilterState n k) (e : Entry n k) (seen : Finset (Fin n))
    (w : List (Fin n)) (hb : f.kept.length+(keptTail M f w).length ≤ m) :
    trace hk M T f e seen w = trace hk M U f e seen w := by
  induction w generalizing f e seen with
  | nil => rfl
  | cons r w ih =>
    by_cases hs : ∀ z ∈ f.live,Covers z r
    · simp only [trace,ite_eq_left hs]
      congr 1
      apply ih
      simpa only [keptTail,ite_eq_left hs] using hb
    · have hl : f.kept.length < m := by
        simp only [keptTail,ite_eq_right hs,List.length_cons] at hb
        omega
      have ht := hTU f.kept e.position r hl
      simp only [trace,ite_eq_right hs,ht]
      congr 1
      split_ifs
      · apply ih
        simp only [keptTail,ite_eq_right hs] at hb
        simpa only [UniformKServer.step,ite_eq_right hs,List.length_append,
          List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
      · rfl

theorem fullTrace_restrict {n k b H : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (u : Configuration n k) (w : List (Fin n))
    (hb : (keptTail M (initial u) w).length ≤ H) (coins : Fin H → Fin b → Bool) :
    fullTrace hk M N hN u w coins =
      epochTrace hk M N hN u w (fun i => coins (Fin.castLE hb i)) := by
  apply trace_congr hk M (keptTail M (initial u) w).length
  · intro p c r hp
    have hpH : p.length < H := hp.trans_le hb
    simp only [selector,extend,dite_eq_left hp,dite_eq_left hpH]
    rfl
  · simp [initial]

theorem kept_bound {n k : ℕ} (M : ℕ) (u : Configuration n k) (w : List (Fin n)) :
    (keptTail M (initial u) w).length ≤ horizon k M := by
  rw [kept_tail_full]
  exact (filter_bounds M u w).2.2

theorem full_mean {n k b : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (u : Configuration n k) (w : List (Fin n)) (f : History n k → ℝ) :
    BitSampling.mean (fun coins : Fin (horizon k M) → Fin b → Bool =>
      f (fullTrace hk M N hN u w coins)) =
    BitSampling.mean (fun coins => f (epochTrace hk M N hN u w coins)) := by
  simp_rw [fullTrace_restrict hk M N hN u w (kept_bound M u w)]
  exact mean_restrict (kept_bound M u w) (fun coins => f (epochTrace hk M N hN u w coins))

end UniformKServer.EpochTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetComparison
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                       
section

namespace UniformKServer.OffsetComparison
open EpochExpectation EpochShadow BitSampling
theorem comparison {n k b : ℕ} (hk : 0 < k) (hk2 : 2 ≤ k) (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (hLazy : ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → N s r j = 0)
    (u s c : Configuration n k) (hu : Function.Injective u) (M R : ℕ)
    (D δ a E : ℝ) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (hTable : ∀ w : List (Fin n), w.length ≤ horizon k M →
      BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w) ≤
        a * offlineCost d u w + E + D)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R)
    (g : History n k) (hg : g.map Prod.fst = raw) :
    (∀ coins, (epochTrace hk M N hN u raw coins).map Prod.fst = raw) ∧
    BitSampling.mean (fun coins => costAlong d s (epochTrace hk M N hN u raw coins)) ≤
      2*a*costAlong d c g + (2*a+1)*k*D+2*E+2*D := by
  have hl := selector_lazy N hN hLazy
  refine ⟨fun coins => (epoch_virtual_bound hk d _ (hl _) u hu M R D δ hD hδ
    hdiam hsep hcap raw hR).1, ?_⟩
  let w := keptTail M (initial u) raw
  have hw : w.length ≤ horizon k M := by
    simpa only [w, kept_tail_full] using (filter_bounds M u raw).2.2
  have hsub : w.Sublist (g.map Prod.fst) := by
    rw [hg]; exact kept_sublist M (initial u) raw
  obtain ⟨g',hgg',hew⟩ := List.sublist_map_iff.mp hsub
  have hopt : offlineCost d u w ≤ costAlong d c g + k*D := by
    rw [hew]
    exact (subsequence_cost_transfer d u c g' g hgg' D hdiam).2.2
  have ht := hTable w hw
  have hb := mean_mono
    (fun coins => costAlong d s (epochTrace hk M N hN u raw coins))
    (fun coins => 2 * BitSampling.runCost N hN next (charge d) ([],u) w coins + k*D)
    (fun coins => by
      have hh := epoch_actual_bound hk d _ (hl (extend coins)) u s hu M R D δ hD hδ
        hdiam hsep hcap raw hR
      simpa only [epochTrace, shadow_full] using hh)
  rw [BitSampling.mean_add, mean_mul, BitSampling.mean_const] at hb
  have hmul := mul_le_mul_of_nonneg_left hopt ha
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hKD := mul_le_mul_of_nonneg_right hk' hD
  nlinarith


end UniformKServer.OffsetComparison

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ControllerBound
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.ControllerBound
open EpochShadow EpochExpectation EpochPartition TapeController
variable {n k b M R : ℕ} [NeZero k] (hk2 : 2≤k) (d : RationalMetric n)
  (u : Configuration n k) (hu : Function.Injective u)
  (N : BState n k→Fin n→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
  (hLazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0)
  (D δ A E : ℝ) (hD : 0≤D) (hδ : 0≤δ) (hA : 0≤A)
  (hdiam : ∀x y,(d.distance x y:ℝ)≤D)
  (hsep : ∀x y,x≠y→δ≤(d.distance x y:ℝ))
  (hcap : R*(k+1)*D≤(M+1)*δ)
  (hTable : ∀w : List (Fin n),w.length≤horizon k M→
    BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w)≤
      A*offlineCost d u w+E+D)

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem epoch (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw≤R)
    (s c : Configuration n k) (g : History n k) (hg : g.map Prod.fst=raw) :
    BitSampling.mean (fun coins : Tape k M b=>costAlong d s
      (EpochControl.runTrace (NeZero.pos k) M (selector N hN (extend coins)) (EpochControl.initial u) raw))≤
      2*A*costAlong d c g+(2*A+1)*k*D+2*E+2*D := by
  simp_rw [EpochControl.initial_trace]
  change BitSampling.mean (fun coins : Tape k M b=>
    costAlong d s (EpochTape.fullTrace (NeZero.pos k) M N hN u raw coins))≤_
  rw [EpochTape.full_mean]
  exact (OffsetComparison.comparison (NeZero.pos k) hk2 d N hN hLazy u s c hu M R
    D δ A E hD hδ hA hdiam hsep hcap hTable raw hR g hg).2

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem groups_oai (es : List (List (Fin n))) (hR : ∀e∈es,blockCount (k:=k) ∅ e≤R)
    (s c : Configuration n k) (g : History n k) (hg : g.map Prod.fst=es.flatten) :
    groupExpected (M:=M) (NeZero.pos k) d u N hN s es≤
      2*A*costAlong d c g+((2*A+1)*k*D+2*E+2*D)*es.length := by
  induction es generalizing s c g with
  | nil=>
    have hgn : g=[] := List.map_eq_nil_iff.mp hg
    simp [groupExpected,hgn,costAlong]
  | cons e es ih=>
    obtain ⟨g₁,g₂,rfl,hg₁,hg₂⟩:=RawBlockCharge.split_history g e es.flatten hg
    have htail:=ih (fun e he=>hR e (by simp [he]))
    have hep:=epoch hk2 d u hu N hN hLazy D δ A E hD hδ hA hdiam hsep hcap hTable
      e (hR e (by simp)) s c g₁ hg₁
    let trace := fun coins : Tape k M b=>
      EpochControl.runTrace (NeZero.pos k) M (selector N hN (extend coins)) (EpochControl.initial u) e
    have hm:=EpochExpectation.mean_mono
      (fun coins : Tape k M b=>costAlong d s (trace coins)+
        groupExpected (M:=M) (NeZero.pos k) d u N hN (finish s (trace coins)) es)
      (fun coins : Tape k M b=>costAlong d s (trace coins)+
        (2*A*costAlong d (finish c g₁) g₂+((2*A+1)*k*D+2*E+2*D)*es.length))
      (fun coins=>add_le_add (le_refl _) (htail _ (finish c g₁) g₂ hg₂))
    simp only [BitSampling.mean_add,BitSampling.mean_const] at hm
    change BitSampling.mean _≤_
    change BitSampling.mean (fun coins=>costAlong d s (trace coins))≤_ at hep
    rw [BitSampling.mean_add,RawBlockCharge.cost_append]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

end UniformKServer.ControllerBound

end


end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.ControllerBound.groups_oai := @OAI.UniformKServer.ControllerBound.groups_oai
