-- Prove2me | solution 1 for OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:50:12.224996+00:00
-- url     : https://prove2.me/submissions/ac78aec7-ef55-480a-be40-dc79ae5e8d24

import Mathlib

section
-- module Solutions.OAIQW_SeparableQuotient.Compat
namespace OAI.SeparableQuotient
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434


end OAI.SeparableQuotient
end

section
-- module Solutions.OAIQW_SeparableQuotient.PrefixNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance prefixDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance prefixDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

/-- Finite prefix normers for a zero-based sequence. The existential formulation is equivalent to a maximum over the finite set. -/
structure PrefixNormers (f : ℕ → StrongDual 𝕜 X) where
  D : ℕ → Finset X
  unit : ∀ m, ∀ d ∈ D m, ‖d‖ ≤ 1
  norming : ∀ m, 0 < m → ∀ c : ℕ → 𝕜, ∃ d ∈ D m,
    ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖(∑ i ∈ Finset.range m, c i • f i) d‖
  vanish : ∀ m n, m ≤ n → ∀ d ∈ D m, f n d = 0

namespace PrefixNormers

variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

theorem prefix_evaluation (c : ℕ → 𝕜) {m N : ℕ} (hmN : m ≤ N)
    {d : X} (hd : d ∈ H.D m) :
    (∑ i ∈ Finset.range N, c i • f i) d = (∑ i ∈ Finset.range m, c i • f i) d := by
  simp only [sum_apply, smul_apply]
  symm
  apply Finset.sum_subset (Finset.range_mono hmN)
  intro i hiN him
  have hmi : m ≤ i := by simpa using him
  rw [H.vanish m i hmi d hd, smul_zero]

include H

theorem prefix_bound (c : ℕ → 𝕜) {m N : ℕ} (hmN : m ≤ N) :
    ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  by_cases hm : m = 0
  · subst m; simp
  obtain ⟨d, hd, hb⟩ := H.norming m (Nat.pos_of_ne_zero hm) c
  rw [← H.prefix_evaluation c hmN hd] at hb
  apply hb.trans
  gcongr
  exact ((∑ i ∈ Finset.range N, c i • f i).le_opNorm d).trans
    (by
      simpa using mul_le_mul_of_nonneg_left (H.unit m d hd)
        (norm_nonneg (∑ i ∈ Finset.range N, c i • f i)))

theorem term_bound (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n • f n‖ ≤ 4 * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  have hp := H.prefix_bound c (Nat.succ_le_of_lt hn)
  have hq := H.prefix_bound c hn.le
  have he : c n • f n =
      (∑ i ∈ Finset.range (n + 1), c i • f i) - (∑ i ∈ Finset.range n, c i • f i) := by
    rw [Finset.sum_range_succ, add_sub_cancel_left]
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem coefficient_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n‖ ≤ (4 / a) * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  have hb := H.term_bound c hn
  rw [norm_smul] at hb
  have hmul := mul_le_mul_of_nonneg_left (hf n) (norm_nonneg (c n))
  have he : 4 * ‖∑ i ∈ Finset.range N, c i • f i‖ / a =
      (4 / a) * ‖∑ i ∈ Finset.range N, c i • f i‖ := by ring
  rw [← he]
  exact (le_div_iff₀ ha).mpr (hmul.trans hb)

theorem finsupp_coefficient_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (c : ℕ →₀ 𝕜) (n : ℕ) :
    ‖c n‖ ≤ (4 / a) * ‖Finsupp.linearCombination 𝕜 f c‖ := by
  classical
  obtain ⟨N, hN⟩ := (insert n c.support).exists_nat_subset_range
  have hsum : (∑ i ∈ Finset.range N, c i • f i) =
      Finsupp.linearCombination 𝕜 f c := by
    change (∑ i ∈ Finset.range N, c i • f i) = ∑ i ∈ c.support, c i • f i
    symm
    apply Finset.sum_subset (fun i hi => hN (Finset.mem_insert_of_mem hi))
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
  rw [← hsum]
  exact H.coefficient_bound a ha hf c (Finset.mem_range.mp (hN (Finset.mem_insert_self _ _)))

theorem linearIndependent (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    LinearIndependent 𝕜 f := by
  rw [linearIndependent_iff]
  intro c hc
  ext n
  have h := H.finsupp_coefficient_bound a ha hf c n
  rw [hc, norm_zero, mul_zero] at h
  simpa using norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- The closed linear span of the sequence. -/
def closedSpan (f : ℕ → StrongDual 𝕜 X) : Submodule 𝕜 (StrongDual 𝕜 X) :=
  (Submodule.span 𝕜 (Set.range f)).topologicalClosure

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoherentClosures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient.CoherentClosures

open Set
universe u
variable {Γ : Type u} [LinearOrder Γ]

/-- Finite closures on the strict initial segment at β. -/
abbrev PreSystem (β : Γ) := Set.Iio β → ℕ → Finset Γ

/-- Coherence conditions below β. -/
structure PreGood (β : Γ) (G : PreSystem β) : Prop where
  lower : ∀ (a : Set.Iio β) n, ∀ x ∈ G a n, x ≤ a.val
  self : ∀ (a : Set.Iio β) n, a.val ∈ G a n
  mono : ∀ a : Set.Iio β, Monotone (G a)
  exhaust : ∀ (a : Set.Iio β) x, x ≤ a.val → ∃ n, x ∈ G a n
  coherent : ∀ (a b : Set.Iio β) n, b.val ∈ G a n →
    G b n = (G a n).filter (fun x => x ≤ b.val)

/-- The closure conditions at a new endpoint, relative to earlier closures. -/
structure ExtensionGood (β : Γ) (G : PreSystem β) (H : ℕ → Finset Γ) : Prop where
  lower : ∀ n, ∀ x ∈ H n, x ≤ β
  self : ∀ n, β ∈ H n
  mono : Monotone H
  exhaust : ∀ x, x ≤ β → ∃ n, x ∈ H n
  coherent : ∀ (a : Set.Iio β) n, a.val ∈ H n →
    G a n = (H n).filter (fun x => x ≤ a.val)

/-- A threshold beyond which two specified earlier coordinates are recorded. -/
lemma exists_next_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (a b : Set.Iio β) (p : ℕ) :
    ∃ q > p, a.val ∈ G (max a b) q ∧ b.val ∈ G (max a b) q := by
  obtain ⟨i, hi⟩ := hg.exhaust (max a b) a.val (le_max_left _ _)
  obtain ⟨j, hj⟩ := hg.exhaust (max a b) b.val (le_max_right _ _)
  refine ⟨max (max i j) (p + 1), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self p) (le_max_right _ _)
  · exact hg.mono (max a b) (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  · exact hg.mono (max a b) (le_trans (le_max_right _ _) (le_max_left _ _)) hj

/-- Each stage of the endpoint construction keeps one earlier endpoint and an
activation threshold. The next endpoint is the maximum of the old endpoint
and the next enumerated predecessor. -/
noncomputable def stage {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : ℕ → Set.Iio β × ℕ
  | 0 => (e 0, 0)
  | n+1 => let v := stage hg e n
    (max v.1 (e (n+1)), (exists_next_threshold hg v.1 (e (n+1)) v.2).choose)

lemma stage_zero {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : stage hg e 0 = (e 0, 0) := rfl

lemma stage_succ_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) :
    (stage hg e n).2 < (stage hg e (n+1)).2 ∧
    (stage hg e n).1.val ∈ G (stage hg e (n+1)).1 (stage hg e (n+1)).2 ∧
    (e (n+1)).val ∈ G (stage hg e (n+1)).1 (stage hg e (n+1)).2 := by
  exact (exists_next_threshold hg (stage hg e n).1 (e (n+1))
    (stage hg e n).2).choose_spec

lemma stage_threshold_strictMono {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : StrictMono (fun n => (stage hg e n).2) :=
  strictMono_nat_of_lt_succ fun n => (stage_succ_threshold hg e n).1

lemma stage_threshold_ge {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) : n ≤ (stage hg e n).2 :=
  (stage_threshold_strictMono hg e).id_le n

/-- The last activated stage at parameter p. -/
noncomputable def active {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : ℕ :=
  Nat.findGreatest (fun n => (stage hg e n).2 ≤ p) p

lemma active_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : (stage hg e (active hg e p)).2 ≤ p := by
  exact Nat.findGreatest_spec (P := fun n => (stage hg e n).2 ≤ p)
    (Nat.zero_le p) (show (stage hg e 0).2 ≤ p from Nat.zero_le p)

lemma stage_le_active {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) {n p : ℕ} (h : (stage hg e n).2 ≤ p) :
    n ≤ active hg e p :=
  Nat.le_findGreatest (le_trans (stage_threshold_ge hg e n) h) h

lemma active_mono {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : Monotone (active hg e) := by
  intro p q hpq
  exact stage_le_active hg e (le_trans (active_threshold hg e p) hpq)

lemma active_at_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) : active hg e (stage hg e n).2 = n := by
  apply le_antisymm
  · exact (stage_threshold_strictMono hg e).le_iff_le.mp (active_threshold hg e _)
  · exact stage_le_active hg e le_rfl

/-- Earlier stage closures embed in later ones once the later stage is active. -/
lemma stage_subset_succ {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n p : ℕ) (hp : (stage hg e (n+1)).2 ≤ p) :
    G (stage hg e n).1 p ⊆ G (stage hg e (n+1)).1 p := by
  have hm := hg.mono (stage hg e (n+1)).1 hp (stage_succ_threshold hg e n).2.1
  rw [hg.coherent (stage hg e (n+1)).1 (stage hg e n).1 p hm]
  exact Finset.filter_subset _ _

lemma stage_subset {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) {n m p : ℕ} (hnm : n ≤ m)
    (hp : (stage hg e m).2 ≤ p) : G (stage hg e n).1 p ⊆ G (stage hg e m).1 p := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    apply Finset.Subset.trans (ih ((stage_threshold_strictMono hg e).monotone
      (Nat.le_succ m) |>.trans hp))
    exact stage_subset_succ hg e m p hp

/-- The new closure: keep the activated earlier closure and append β. -/
noncomputable def extended {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : Finset Γ :=
  insert β (G (stage hg e (active hg e p)).1 p)

lemma extended_good {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (he : Function.Surjective e) :
    ExtensionGood β G (extended hg e) := by
  classical
  constructor
  · intro n x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hg.lower _ _ _ hx).trans (stage hg e (active hg e n)).1.property.le
  · intro n
    exact Finset.mem_insert_self _ _
  · intro p q hpq
    apply Finset.insert_subset_insert
    exact (hg.mono _ hpq).trans
      (stage_subset hg e (active_mono hg e hpq) (active_threshold hg e q))
  · intro x hx
    rcases lt_or_eq_of_le hx with hx | rfl
    · obtain ⟨i, hi⟩ := he ⟨x, hx⟩
      refine ⟨(stage hg e i).2, Finset.mem_insert_of_mem ?_⟩
      rw [active_at_threshold]
      cases i with
      | zero => simpa [stage_zero, hi] using hg.self (e 0) 0
      | succ i => simpa only [hi] using (stage_succ_threshold hg e i).2.2
    · exact ⟨0, Finset.mem_insert_self _ _⟩
  · intro a n ha
    have hab : a.val ≠ β := ne_of_lt a.property
    have ha' := (Finset.mem_insert.mp ha).resolve_left hab
    rw [hg.coherent _ a n ha']
    apply Finset.ext
    intro x
    simp only [extended, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxa⟩; exact ⟨Or.inr hx, hxa⟩
    · rintro ⟨rfl | hx, hxa⟩
      · exact (not_le_of_gt a.property hxa).elim
      · exact ⟨hx, hxa⟩

/-- Empty strict segments require no recursive information. -/
lemma singleton_good {β : Γ} {G : PreSystem β} (h : IsEmpty (Set.Iio β)) :
    ExtensionGood β G (fun _ => {β}) := by
  classical
  constructor
  · intro n x hx; exact (Finset.mem_singleton.mp hx).le
  · intro n; simp
  · intro p q hpq; exact le_rfl
  · intro x hx
    have he : x = β := (lt_or_eq_of_le hx).resolve_left fun hlt => h.false ⟨x, hlt⟩
    subst x; exact ⟨0, by simp⟩
  · intro a; exact h.false a |>.elim

/-- Countability of the strict segment suffices to extend the coherent system. -/
lemma exists_extension {β : Γ} [Countable (Set.Iio β)]
    {G : PreSystem β} (hg : PreGood β G) :
    ∃ H : ℕ → Finset Γ, ExtensionGood β G H := by
  classical
  cases isEmpty_or_nonempty (Set.Iio β) with
  | inl h => exact ⟨fun _ => {β}, singleton_good h⟩
  | inr h =>
    let := h
    obtain ⟨e, he⟩ := exists_surjective_nat (Set.Iio β)
    exact ⟨extended hg e, extended_good hg e he⟩

/-- Full endpoint property for a total system. -/
structure GoodAt (F : Γ → ℕ → Finset Γ) (β : Γ) : Prop where
  lower : ∀ n, ∀ x ∈ F β n, x ≤ β
  self : ∀ n, β ∈ F β n
  mono : Monotone (F β)
  exhaust : ∀ x, x ≤ β → ∃ n, x ∈ F β n
  coherent : ∀ α n, α ∈ F β n → F α n = (F β n).filter (fun x => x ≤ α)

variable [WellFoundedLT Γ] [∀ β : Γ, Countable (Set.Iio β)]

/-- The recursion step is defined even on bad predecessor data; the bad branch
is never used in the well-founded construction. -/
noncomputable def next (β : Γ) (G : PreSystem β) : ℕ → Finset Γ := by
  classical
  exact if h : PreGood β G then (exists_extension h).choose else fun _ => {β}

omit [WellFoundedLT Γ] in
lemma next_good (β : Γ) (G : PreSystem β) (h : PreGood β G) :
    ExtensionGood β G (next β G) := by
  classical
  rw [next, dite_eq_left h]
  exact (exists_extension h).choose_spec

/-- The actual coherently nested finite closures on the well-order. -/
noncomputable def system : Γ → ℕ → Finset Γ :=
  WellFounded.fix wellFounded_lt fun β rec => next β (fun a => rec a.val a.property)

lemma system_eq (β : Γ) : system β = next β (fun a => system a.val) := by
  rw [system, WellFounded.fix_eq]

/-- Transfinite induction establishes the coherent closure properties. -/
theorem system_goodAt (β : Γ) : GoodAt system β := by
  classical
  refine (wellFounded_lt : WellFounded ((· < ·) : Γ → Γ → Prop)).induction β ?_
  intro β ih
  have hg : PreGood β (fun a => system a.val) := by
    constructor
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).lower
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).self
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).mono
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).exhaust
    · intro a b n hb; exact (ih a.val (Set.mem_Iio.mp a.property)).coherent b.val n hb
  have he := next_good β (fun a => system a.val) hg
  rw [← system_eq] at he
  refine ⟨he.lower, he.self, he.mono, he.exhaust, ?_⟩
  intro α n hα
  rcases lt_or_eq_of_le (he.lower n α hα) with hlt | rfl
  · exact he.coherent ⟨α, hlt⟩ n hα
  · exact (Finset.filter_eq_self.mpr fun x hx => he.lower n x hx).symm

end SeparableQuotient.CoherentClosures

namespace SeparableQuotient.CoherentClosures

open Set

/-- The coordinate set of the negative construction is really ω₁. -/
abbrev OmegaOne := (Cardinal.aleph 1).ord.ToType

instance omegaOne_initialSegment_countable (β : OmegaOne) : Countable (Set.Iio β) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt β (by simp [OmegaOne])
  simpa [OmegaOne] using h

/-- Positive-indexed finite closures. -/
noncomputable def F (β : OmegaOne) (p : ℕ) : Finset OmegaOne :=
  system β (p - 1)

/-- The first positive parameter at which α enters the closure of β. The
irrelevant case α > β is set to zero. -/
noncomputable def rho (α β : OmegaOne) : ℕ := by
  classical
  exact if h : α ≤ β then Nat.find ((system_goodAt β).exhaust α h) + 1 else 0

end SeparableQuotient.CoherentClosures

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient.PathCoding

open CoherentClosures

section OrderedArray
variable {Γ : Type*} [LinearOrder Γ]

/-- Position of a coordinate in an ordered finite closure; no ordinal label is
stored in the code. -/
def position (s : Finset Γ) (x : Γ) : ℕ := (s.filter (· < x)).card

/-- A zero-filled rational array recorded by order positions, including zero values. -/
def arrayCode (s : Finset Γ) (f : Γ →₀ ℚ) : Finset (ℕ × ℚ) :=
  s.image (fun x => (position s x, f x))

end OrderedArray
end SeparableQuotient.PathCoding

namespace SeparableQuotient.PathCoding

open CoherentClosures

abbrev Code := List (ℕ × ℕ × Finset (ℕ × ℚ))

def codeBound : Code → ℕ
  | [] => 0
  | x :: xs => max x.2.1 (codeBound xs)

/-- An injective code greater than every entry of its final metadata. -/
noncomputable def sigma (c : Code) : ℕ := Nat.pair (Encodable.encode c) (codeBound c + 1)

/-- Raw infinite path data, retaining the actual rational pieces, declared
weights and metadata. Nonzero pieces are included here to define the prefix
endpoint without arbitrary defaults. Type-I membership is not needed for the
combinatorial rigidity theorem. -/
@[ext] structure RawPath where
  piece : ℕ → OmegaOne →₀ ℚ
  weight : ℕ → ℕ
  metadata : ℕ → ℕ
  nonzero : ∀ i, piece i ≠ 0

namespace RawPath

noncomputable def support (P : RawPath) (n : ℕ) : Finset OmegaOne :=
  (Finset.range (n+1)).biUnion (fun i => (P.piece i).support)

lemma mem_support_iff (P : RawPath) (n : ℕ) (a : OmegaOne) :
    a ∈ P.support n ↔ ∃ i ≤ n, a ∈ (P.piece i).support := by
  classical
  simp only [support, Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff]

lemma piece_support_subset (P : RawPath) {i n : ℕ} (hi : i ≤ n) :
    (P.piece i).support ⊆ P.support n := by
  intro a ha
  exact (P.mem_support_iff n a).mpr ⟨i, hi, ha⟩

lemma support_nonempty (P : RawPath) (n : ℕ) : (P.support n).Nonempty := by
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (P.nonzero n)
  exact ⟨a, P.piece_support_subset le_rfl ha⟩

noncomputable def endpoint (P : RawPath) (n : ℕ) : OmegaOne :=
  (P.support n).max' (P.support_nonempty n)

noncomputable def closure (P : RawPath) (n : ℕ) : Finset OmegaOne :=
  F (P.endpoint n) (P.metadata n)

noncomputable def code (P : RawPath) (n : ℕ) : Code :=
  List.ofFn (fun i : Fin (n+1) =>
    (P.weight i, P.metadata i, arrayCode (P.closure n) (P.piece i)))

/-- Exact support, succession, weight and metadata conditions of a path. The
Type-I construction contributes only additional restrictions, not needed below. -/
structure Admissible (P : RawPath) : Prop where
  successive : ∀ i j, i < j → ∀ a ∈ (P.piece i).support,
    ∀ b ∈ (P.piece j).support, a < b
  metadata_strict : StrictMono P.metadata
  metadata_pos : ∀ i, 1 ≤ P.metadata i
  weight_pos : ∀ i, 1 ≤ P.weight i
  weight_le_metadata : ∀ i, P.weight i ≤ P.metadata i
  rho_bound : ∀ n a b, a ∈ P.support n → b ∈ P.support n → a ≤ b →
    rho a b ≤ P.metadata n
  rule : ∀ n, P.weight (n+1) = sigma (P.code n)

end RawPath
end SeparableQuotient.PathCoding

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Admissible parameters for the pure s = k + 2 families and mixed s = 2 family, with q = (s + 1) / s. Integer powers avoid rounding noninteger powers. -/
namespace SeparableQuotient.Parameters

open Filter Topology

def d (n : ℕ) : ℕ := n+11

/-- State stores the exponent scale and twice the sum of all earlier lengths. -/
def state (s : ℕ) : ℕ → ℕ × ℕ
  | 0 => ((d 0 + 1) + 1 + d 0 + (d 0)^2, 0)
  | n+1 =>
    let old := state s n
    let B := old.2 + 2 * 2^(s*(s+1)*old.1)
    (old.1 + (B+1)*(d (n+1)+1) + 1 + d (n+1) + (d (n+1))^2, B)

def t (s n : ℕ) : ℕ := (state s n).1
def B (s n : ℕ) : ℕ := (state s n).2
def L (s n : ℕ) : ℕ := 2^(s*(s+1)*t s n)
def m (s n : ℕ) : ℕ := 2^((s-1)*(s+1)*t s n+d n)
def r (s : ℕ) : ℝ := (s:ℝ)/((s:ℝ)-1)
def q (s : ℕ) : ℝ := ((s:ℝ)+1)/(s:ℝ)
def theta (s n : ℕ) : ℝ := (L s n : ℝ) ^ (1/r s) / (m s n : ℝ)

lemma m_pos (s n : ℕ) : 0 < m s n := pow_pos (by omega) _

lemma theta_numerator {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (L s n : ℝ) ^ (1/r s) = (2:ℝ)^((s-1)*(s+1)*t s n) := by
  have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : 1 ≤ s := by omega
  simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  simp only [r, one_div_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hs1]
  field_simp

lemma theta_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) : theta s n = (1/2:ℝ)^(d n) := by
  rw [theta, theta_numerator hs]
  simp only [m]
  push_cast
  rw [pow_add, div_mul_eq_div_div, div_self (by positivity : (2:ℝ)^((s-1)*(s+1)*t s n) ≠ 0)]
  exact (one_div_pow _ _).symm

lemma hasSum_theta {s : ℕ} (hs : 2 ≤ s) :
    HasSum (theta s) (1/1024:ℝ) := by
  have hgeom : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) using 1; norm_num
  have h := hgeom.mul_left ((1/2:ℝ)^11)
  have h' : HasSum (theta s) ((1/2:ℝ)^11*2) := h.congr_fun (by
    intro n
    rw [theta_eq hs, d, pow_add, mul_comm])
  norm_num at h' ⊢
  exact h'

lemma theta_sum_small {s : ℕ} (hs : 2 ≤ s) : ∑' n, theta s n < (1/8:ℝ) := by
  rw [(hasSum_theta hs).tsum_eq]
  norm_num

lemma reciprocal_le_theta {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    1/(m s n:ℝ) ≤ theta s n := by
  rw [theta, theta_numerator hs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact one_le_pow₀ (by norm_num)

lemma reciprocal_sum_small {s : ℕ} (hs : 2 ≤ s) :
    ∑' n, 1/(m s n:ℝ) < (1/8:ℝ) := by
  have hsum := (hasSum_theta hs).summable
  have hrecip : Summable (fun n => 1/(m s n:ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) (reciprocal_le_theta hs) hsum
  exact (Summable.tsum_le_tsum (reciprocal_le_theta hs) hrecip hsum).trans_lt
    (theta_sum_small hs)

lemma q_bounds {s : ℕ} (hs : 2 ≤ s) :
    1 < q s ∧ q s < r s ∧ r s < (s:ℝ)+1 ∧ 1/((s:ℝ)+1) < 1/(s:ℝ) := by
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by linarith
  have hs1 : (0:ℝ) < (s:ℝ)-1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [q, lt_div_iff₀ hs0]; linarith
  · rw [q, r, div_lt_div_iff₀ hs0 hs1]; nlinarith
  · rw [r, div_lt_iff₀ hs1]; nlinarith
  · exact one_div_lt_one_div_of_lt hs0 (by linarith)

end SeparableQuotient.Parameters

namespace SeparableQuotient.Colors
open CoherentClosures

/-- A partition of ω₁ into countably many unbounded fibers. -/
def partitionEquiv : OmegaOne.{0} ≃ ℕ × OmegaOne.{0} :=
  Classical.choice (Cardinal.eq.mp (by
    simp only [OmegaOne, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_nat,
      Cardinal.mk_ord_toType, Cardinal.aleph0_mul_aleph]))

def color (a : OmegaOne.{0}) : ℕ := (partitionEquiv a).1

end SeparableQuotient.Colors

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open CoherentClosures PathCoding
open scoped ENNReal Classical
abbrev Γ := OmegaOne.{0}
abbrev Array := Γ →₀ ℚ

inductive Family where
  | pure : ℕ → Family
  | mixed : Family
  deriving DecidableEq

def Family.s : Family → ℕ
  | .pure k => k+2
  | .mixed => 2

lemma Family.s_ge_two (f : Family) : 2 ≤ f.s := by cases f <;> simp [Family.s]

def Family.q (f : Family) : ℝ := Parameters.q f.s

def Family.L (f : Family) (j : ℕ) : ℕ := Parameters.L f.s (j-1)
def Family.m (f : Family) (j : ℕ) : ℕ := Parameters.m f.s (j-1)

lemma Family.m_pos (f : Family) (j : ℕ) : 0 < f.m j := Parameters.m_pos _ _

/-- Succession refers to the full supports, in both orders in mixed mode. -/
def Successive (f : Family) (x y : Array) : Prop :=
  ∀ a ∈ x.support, ∀ b ∈ y.support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)

lemma Successive.disjoint {f : Family} {x y : Array} (h : Successive f x y) :
    Disjoint x.support y.support := by
  apply Finset.disjoint_left.mpr
  intro a hx hy
  exact (lt_irrefl a) (h a hx a hy).1

structure Crop where
  ordinal : Set Γ
  ordinal_convex : Set.OrdConnected ordinal
  colors : Set ℕ
  colors_convex : Set.OrdConnected colors

def Crop.set (A : Crop) : Family → Set Γ
  | .pure _ => A.ordinal
  | .mixed => A.ordinal ∩ Colors.color ⁻¹' A.colors

def restrict (A : Set Γ) (x : Array) : Array := x.filter (· ∈ A)

@[simp] lemma restrict_apply (A : Set Γ) (x : Array) (a : Γ) :
    restrict A x a = if a ∈ A then x a else 0 := Finsupp.filter_apply _ _ _

/-- A specified Type I expression. Child norming membership is imposed at its
construction stage, outside this data structure. -/
structure TypeI (f : Family) where
  weight : ℕ
  weight_pos : 1 ≤ weight
  length : ℕ
  length_pos : 1 ≤ length
  length_le : length ≤ f.L weight
  child : Fin length → Array
  child_nonzero : ∀ h, child h ≠ 0
  successive : ∀ h i, h < i → Successive f (child h) (child i)

def TypeI.value {f : Family} (e : TypeI f) : Array :=
  (1 / (f.m e.weight : ℚ)) • ∑ h, e.child h

/-- Exactly the finite prefix conditions, with unused raw entries ignored.
Padding raw data beyond length imposes no mathematical restriction. -/
structure PrefixValid (P : RawPath) (length : ℕ) : Prop where
  successive : ∀ i j, i < j → j < length → ∀ a ∈ (P.piece i).support,
    ∀ b ∈ (P.piece j).support, a < b
  metadata_strict : ∀ i j, i < j → j < length → P.metadata i < P.metadata j
  metadata_pos : ∀ i, i < length → 1 ≤ P.metadata i
  weight_pos : ∀ i, i < length → 1 ≤ P.weight i
  weight_le_metadata : ∀ i, i < length → P.weight i ≤ P.metadata i
  rho_bound : ∀ n, n < length → ∀ a b, a ∈ P.support n → b ∈ P.support n → a ≤ b →
    rho a b ≤ P.metadata n
  rule : ∀ n, n+1 < length → P.weight (n+1) = sigma (P.code n)

structure FinitePath (f : Family) where
  raw : RawPath
  length : ℕ
  length_pos : 1 ≤ length
  valid : PrefixValid raw length
  piece : Fin length → TypeI f
  value_eq : ∀ i, (piece i).value = raw.piece i
  weight_eq : ∀ i, (piece i).weight = raw.weight i
  mixed_successive : ∀ (i j : Fin length), i < j →
    Successive f (raw.piece i) (raw.piece j)

def FinitePath.value {f : Family} (P : FinitePath f) : Array := ∑ i : Fin P.length, P.raw.piece i

def FinitePath.active {f : Family} (P : FinitePath f) (A : Crop) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin P.length => restrict (A.set f) (P.raw.piece i) ≠ 0)).image
    (fun i : Fin P.length => P.raw.weight i)

structure TypeII (f : Family) where
  length : ℕ
  path : Fin length → FinitePath f
  crop : Fin length → Crop
  coefficient : Fin length → ℚ
  bound : ∑ b, |(coefficient b : ℝ)| ^ f.q ≤ 1
  disjoint_active : Pairwise (fun b c =>
    Disjoint ((path b).active (crop b)) ((path c).active (crop c)))

def TypeII.value {f : Family} (e : TypeII f) : Array :=
  ∑ b, e.coefficient b • restrict ((e.crop b).set f) (e.path b).value

/-- Each stage retains previous stages and adjoins expressions whose Type I children belong to previous stages, with uncropped path data. -/
def stage (base : Set Array) (f : Family) : ℕ → Set Array
  | 0 => base
  | n+1 => stage base f n ∪
      {x | ∃ e : TypeI f, e.value = x ∧ ∀ h, e.child h ∈ stage base f n} ∪
      {x | ∃ e : TypeII f, e.value = x ∧
        ∀ b i h, ((e.path b).piece i).child h ∈ stage base f n}

def pureBase (k : ℕ) : Set Array :=
  {x | x = 0 ∨ ∃ a, Colors.color a = k ∧
    (x = Finsupp.single a 1 ∨ x = Finsupp.single a (-1))}

def Pure (k : ℕ) : Set Array := ⋃ n, stage (pureBase k) (.pure k) n

def Full : Set Array := ⋃ n, stage (⋃ k, Pure k) .mixed n

lemma stage_mono (base : Set Array) (f : Family) : Monotone (stage base f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl (Or.inl hx)

lemma pure_subset_full (k : ℕ) : Pure k ⊆ Full := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨k, hx⟩⟩

lemma coordinate_mem (a : Γ) : Finsupp.single a 1 ∈ Full := by
  apply pure_subset_full (Colors.color a)
  exact Set.mem_iUnion.mpr ⟨0, Or.inr ⟨a, rfl, Or.inl rfl⟩⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open CoherentClosures PathCoding
open scoped Classical

lemma successive_coefficient_unique {f : Family} {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive f (v i) (v j)) {a : Γ} {i j : Fin n}
    (hi : v i a ≠ 0) (hj : v j a ≠ 0) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact Finset.disjoint_left.mp (h i j hij).disjoint
      (Finsupp.mem_support_iff.mpr hi) (Finsupp.mem_support_iff.mpr hj)
  · exact Finset.disjoint_left.mp (h j i hij).disjoint
      (Finsupp.mem_support_iff.mpr hj) (Finsupp.mem_support_iff.mpr hi)

lemma TypeI.coefficient_bound {f : Family} (e : TypeI f)
    (h : ∀ i a, |(e.child i a : ℝ)| ≤ 1) (a : Γ) :
    |(e.value a : ℝ)| ≤ 1 / (f.m e.weight : ℝ) := by
  classical
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos _
  have hsum : |∑ i, (e.child i a : ℝ)| ≤ 1 := by
    by_cases hex : ∃ i, e.child i a ≠ 0
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i]
      · exact h i a
      · intro j _ hji
        have hz : e.child j a = 0 := by
          by_contra hj
          exact hji (successive_coefficient_unique e.child e.successive hj hi)
        simp [hz]
      · simp
    · push Not at hex
      simp [hex]
  have heq : (e.value a : ℝ) = (1 / (f.m e.weight : ℝ)) * ∑ i, (e.child i a : ℝ) := by
    simp [TypeI.value, Finsupp.smul_apply, smul_eq_mul]
  rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hm)]
  simpa using mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hm))

/-- A coordinate meets at most one original path piece. -/
def FinitePath.hitIndex {f : Family} (P : FinitePath f) (a : Γ) : Fin P.length :=
  if h : ∃ i : Fin P.length, P.raw.piece i a ≠ 0 then h.choose
  else ⟨0, P.length_pos⟩

lemma FinitePath.value_at_hit {f : Family} (P : FinitePath f) (a : Γ) :
    P.value a = P.raw.piece (P.hitIndex a) a := by
  classical
  by_cases hex : ∃ i : Fin P.length, P.raw.piece i a ≠ 0
  · have hi : P.raw.piece (P.hitIndex a) a ≠ 0 := by
      simpa only [FinitePath.hitIndex, dite_eq_left hex] using hex.choose_spec
    change (∑ i : Fin P.length, P.raw.piece i) a = _
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (P.hitIndex a)]
    · intro j _ hj
      by_contra hne
      exact hj (successive_coefficient_unique (fun i : Fin P.length => P.raw.piece i)
        P.mixed_successive hne hi)
    · simp
  · push Not at hex
    simp [FinitePath.value, hex]

lemma FinitePath.hit_weight_active {f : Family} (P : FinitePath f) (A : Crop) (a : Γ)
    (ha : restrict (A.set f) P.value a ≠ 0) :
    P.raw.weight (P.hitIndex a) ∈ P.active A := by
  classical
  have hAc : a ∈ A.set f := by
    by_contra hn
    simp [hn] at ha
  have hv : P.raw.piece (P.hitIndex a) a ≠ 0 := by
    simpa [hAc, P.value_at_hit] using ha
  apply Finset.mem_image.mpr
  refine ⟨P.hitIndex a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro hz
  have hz' := congrArg (fun x : Array => x a) hz
  exact hv (by simpa [hAc] using hz')

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.reciprocal_summable (f : Family) :
    Summable (fun n => 1 / (Parameters.m f.s n : ℝ)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (Parameters.reciprocal_le_theta f.s_ge_two) (Parameters.hasSum_theta f.s_ge_two).summable

lemma TypeII.coefficient_le_one {f : Family} (e : TypeII f) (b : Fin e.length) :
    |(e.coefficient b : ℝ)| ≤ 1 := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  have hb : |(e.coefficient b : ℝ)| ^ f.q ≤ 1 :=
    (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (abs_nonneg (e.coefficient i : ℝ)) f.q)
      (Finset.mem_univ b)).trans e.bound
  by_contra h
  have ht := Real.one_lt_rpow (lt_of_not_ge h) hq
  exact (not_lt_of_ge hb) ht

lemma TypeII.hit_weight_injective {f : Family} (e : TypeII f) (a : Γ) :
    Set.InjOn (fun b : Fin e.length => (e.path b).raw.weight ((e.path b).hitIndex a))
      {b | restrict ((e.crop b).set f) (e.path b).value a ≠ 0} := by
  intro b hb c hc heq
  by_contra hbc
  have hb' := (e.path b).hit_weight_active (e.crop b) a hb
  have hc' := (e.path c).hit_weight_active (e.crop c) a hc
  dsimp only at heq
  rw [heq] at hb'
  exact Finset.disjoint_left.mp (e.disjoint_active hbc) hb' hc'

lemma TypeII.coefficient_bound {f : Family} (e : TypeII f)
    (h : ∀ b i j a, |(((e.path b).piece i).child j a : ℝ)| ≤ 1) (a : Γ) :
    |(e.value a : ℝ)| < 1/8 := by
  classical
  let active : Finset (Fin e.length) := Finset.univ.filter
    (fun b => restrict ((e.crop b).set f) (e.path b).value a ≠ 0)
  let j : Fin e.length → ℕ := fun b =>
    (e.path b).raw.weight ((e.path b).hitIndex a)
  have jpos : ∀ b, 1 ≤ j b := fun b => (e.path b).valid.weight_pos _
    ((e.path b).hitIndex a).isLt
  have jinj : Set.InjOn (fun b => j b - 1) active := by
    intro b hb c hc heq
    apply e.hit_weight_injective a (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
    change j b = j c
    dsimp only at heq
    have := jpos b
    have := jpos c
    omega
  have hterm : ∀ b ∈ active,
      |(e.coefficient b : ℝ) * (restrict ((e.crop b).set f) (e.path b).value a : ℝ)|
        ≤ 1 / (Parameters.m f.s (j b - 1) : ℝ) := by
    intro b hb
    have hAc : a ∈ (e.crop b).set f := by
      by_contra hn
      have := (Finset.mem_filter.mp hb).2
      simp [hn] at this
    have hv : |((e.path b).raw.piece ((e.path b).hitIndex a) a : ℝ)| ≤
        1 / (f.m (j b) : ℝ) := by
      rw [← (e.path b).value_eq]
      have hh := ((e.path b).piece ((e.path b).hitIndex a)).coefficient_bound
        (h b ((e.path b).hitIndex a)) a
      simpa only [(e.path b).weight_eq] using hh
    rw [restrict_apply, ite_eq_left hAc, (e.path b).value_at_hit, abs_mul]
    exact (mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (abs_nonneg _)).trans
      (by simpa only [one_mul, Family.m] using hv)
  have hsum : (e.value a : ℝ) = ∑ b ∈ active,
      (e.coefficient b : ℝ) * (restrict ((e.crop b).set f) (e.path b).value a : ℝ) := by
    simp only [TypeII.value, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Rat.cast_sum,
      Rat.cast_mul]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b _ hb
    have hz : restrict ((e.crop b).set f) (e.path b).value a = 0 := by
      simpa [active] using hb
    simp [hz]
  rw [hsum]
  calc
    |∑ b ∈ active, (e.coefficient b : ℝ) *
        (restrict ((e.crop b).set f) (e.path b).value a : ℝ)|
      ≤ ∑ b ∈ active, |(e.coefficient b : ℝ) *
        (restrict ((e.crop b).set f) (e.path b).value a : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ active, 1 / (Parameters.m f.s (j b - 1) : ℝ) := Finset.sum_le_sum hterm
    _ = ∑ n ∈ active.image (fun b => j b-1), 1 / (Parameters.m f.s n : ℝ) := by
      rw [Finset.sum_image]
      exact fun b hb c hc hbc => jinj hb hc hbc
    _ ≤ ∑' n, 1 / (Parameters.m f.s n : ℝ) :=
      f.reciprocal_summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ < 1/8 := Parameters.reciprocal_sum_small f.s_ge_two

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma stage_coefficient_bound {base : Set Array} (f : Family)
    (hbase : ∀ x ∈ base, ∀ a, |(x a : ℝ)| ≤ 1) :
    ∀ n x, x ∈ stage base f n → ∀ a, |(x a : ℝ)| ≤ 1 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx a
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx a
    · exact (e.coefficient_bound (fun i => ih _ (he i)) a).trans (by
        have hm : (1 : ℝ) ≤ f.m e.weight := by exact_mod_cast f.m_pos e.weight
        exact (div_le_one (lt_of_lt_of_le (by norm_num) hm)).mpr hm)
    · exact le_trans (le_of_lt (e.coefficient_bound
        (fun b i j => ih _ (he b i j)) a)) (by norm_num)

lemma pureBase_coefficient_bound (k : ℕ) (x : Array) (hx : x ∈ pureBase k) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  rcases hx with rfl | ⟨b, _, rfl | rfl⟩
  · simp
  all_goals by_cases hab : a = b <;> simp [hab]

lemma pure_coefficient_bound (k : ℕ) (x : Array) (hx : x ∈ Pure k) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact stage_coefficient_bound (.pure k) (pureBase_coefficient_bound k) n x hn a

lemma full_coefficient_bound (x : Array) (hx : x ∈ Full) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_coefficient_bound .mixed ?_ n x hn a
  intro y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact pure_coefficient_bound k y hk

lemma restrict_support_subset (A : Set Γ) (x : Array) :
    (restrict A x).support ⊆ x.support := Finset.filter_subset _ _

lemma restrict_zero (A : Set Γ) : restrict A 0 = 0 := by ext a; simp

lemma restrict_smul (A : Set Γ) (c : ℚ) (x : Array) :
    restrict A (c • x) = c • restrict A x := by
  ext a
  by_cases h : a ∈ A <;> simp [h]

lemma restrict_sum {ι : Type*} (A : Set Γ) (s : Finset ι) (x : ι → Array) :
    restrict A (∑ i ∈ s, x i) = ∑ i ∈ s, restrict A (x i) := Finsupp.filter_sum _ _

lemma restrict_restrict (A B : Set Γ) (x : Array) :
    restrict A (restrict B x) = restrict (A ∩ B) x := by
  ext a
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

def Crop.inter (A B : Crop) : Crop :=
  ⟨A.ordinal ∩ B.ordinal, A.ordinal_convex.inter B.ordinal_convex,
    A.colors ∩ B.colors, A.colors_convex.inter B.colors_convex⟩

@[simp] lemma Crop.inter_set (A B : Crop) (f : Family) :
    (A.inter B).set f = A.set f ∩ B.set f := by
  cases f <;> ext a <;> simp [Crop.set, Crop.inter, and_assoc, and_left_comm, and_comm]

lemma Successive.restrict {f : Family} {x y : Array} (h : Successive f x y) (A : Set Γ) :
    Successive f (restrict A x) (restrict A y) := by
  intro a ha b hb
  exact h a (restrict_support_subset A x ha) b (restrict_support_subset A y hb)

lemma TypeII.active_crop_subset {f : Family} (P : FinitePath f) (A B : Crop) :
    P.active (A.inter B) ⊆ P.active B := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro hz
  have hn := (Finset.mem_filter.mp hi).2
  apply hn
  rw [Crop.inter_set, ← restrict_restrict, hz, restrict_zero]

/-- Crops of Type II expressions retain the original paths and coding. -/
def TypeII.cropped {f : Family} (e : TypeII f) (A : Crop) : TypeII f where
  length := e.length
  path := e.path
  crop b := A.inter (e.crop b)
  coefficient := e.coefficient
  bound := e.bound
  disjoint_active := fun _b _c hbc => (e.disjoint_active hbc).mono
    (TypeII.active_crop_subset _ _ _) (TypeII.active_crop_subset _ _ _)

lemma TypeII.cropped_value {f : Family} (e : TypeII f) (A : Crop) :
    (e.cropped A).value = restrict (A.set f) e.value := by
  simp only [TypeII.value, TypeII.cropped, restrict_sum, restrict_smul,
    Crop.inter_set, restrict_restrict]
  rfl

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

/-- The crop operation discards zero children in order. -/
lemma TypeI.crop_cases {f : Family} (e : TypeI f) (A : Set Γ) :
    restrict A e.value = 0 ∨ ∃ d : TypeI f,
      d.weight = e.weight ∧ d.value = restrict A e.value ∧
      ∀ i, ∃ j, d.child i = restrict A (e.child j) := by
  let S : Finset (Fin e.length) := Finset.univ.filter (fun i => restrict A (e.child i) ≠ 0)
  have hsum : ∑ i ∈ S, restrict A (e.child i) = ∑ i, restrict A (e.child i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  by_cases hS : S.Nonempty
  · right
    let idx : Fin S.card → Fin e.length := fun i => (S.orderIsoOfFin rfl i).val
    have hidx : StrictMono idx := (S.orderEmbOfFin rfl).strictMono
    have hiS : ∀ i, idx i ∈ S := fun i => (S.orderIsoOfFin rfl i).property
    let d : TypeI f :=
      { weight := e.weight
        weight_pos := e.weight_pos
        length := S.card
        length_pos := Finset.card_pos.mpr hS
        length_le := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using e.length_le)
        child := fun i => restrict A (e.child (idx i))
        child_nonzero := fun i => (Finset.mem_filter.mp (hiS i)).2
        successive := fun i j hij => (e.successive _ _ (hidx hij)).restrict A }
    refine ⟨d, rfl, ?_, fun i => ⟨idx i, rfl⟩⟩
    have hsum' : ∑ i : Fin S.card, restrict A (e.child (idx i)) =
        ∑ i ∈ S, restrict A (e.child i) := by
      calc
        _ = ∑ i : S, restrict A (e.child i) :=
          (S.orderIsoOfFin rfl).toEquiv.sum_comp _
        _ = _ := (Finset.sum_subtype S (fun _ => Iff.rfl) (fun i => restrict A (e.child i))).symm
    simp only [d, TypeI.value, restrict_smul, restrict_sum, hsum', hsum]
  · left
    have hz : ∀ i, restrict A (e.child i) = 0 := by
      intro i
      by_contra hi
      exact hS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simp only [TypeI.value, restrict_smul, restrict_sum, hz, Finset.sum_const_zero, smul_zero]

lemma stage_zero {base : Set Array} (f : Family) (h0 : (0 : Array) ∈ base) (n : ℕ) :
    (0 : Array) ∈ stage base f n := stage_mono base f (Nat.zero_le n) h0

lemma stage_crop {base : Set Array} (f : Family) (h0 : (0 : Array) ∈ base)
    (hbase : ∀ (A : Crop) x, x ∈ base → restrict (A.set f) x ∈ base) :
    ∀ n (A : Crop) x, x ∈ stage base f n → restrict (A.set f) x ∈ stage base f n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro A x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact Or.inl (Or.inl (ih A x hx))
    · rcases e.crop_cases (A.set f) with hz | ⟨d, _, hd, hchild⟩
      · rw [hz]
        exact stage_zero f h0 (n+1)
      · apply Or.inl ∘ Or.inr
        refine ⟨d, hd, ?_⟩
        intro i
        obtain ⟨j, hj⟩ := hchild i
        rw [hj]
        exact ih A _ (he j)
    · right
      exact ⟨e.cropped A, e.cropped_value A, he⟩

lemma pureBase_zero (k : ℕ) : (0 : Array) ∈ pureBase k := Or.inl rfl

lemma pureBase_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ pureBase k) :
    restrict (A.set (.pure k)) x ∈ pureBase k := by
  rcases hx with rfl | ⟨a, ha, rfl | rfl⟩
  · exact Or.inl (restrict_zero _)
  all_goals
    by_cases hA : a ∈ A.set (.pure k)
    · rw [restrict, Finsupp.filter_single_of_pos _ hA]
      exact Or.inr ⟨a, ha, by first | exact Or.inl rfl | exact Or.inr rfl⟩
    · rw [restrict, Finsupp.filter_single_of_neg _ hA]
      exact pureBase_zero k

lemma pure_zero (k : ℕ) : (0 : Array) ∈ Pure k := Set.mem_iUnion.mpr ⟨0, pureBase_zero k⟩

lemma pure_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ Pure k) :
    restrict (A.set (.pure k)) x ∈ Pure k := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n,
    stage_crop (.pure k) (pureBase_zero k) (pureBase_crop k) n A x hn⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma TypeI.zero_at {f : Family} (e : TypeI f) (a : Γ)
    (h : ∀ i, e.child i a = 0) : e.value a = 0 := by
  simp [TypeI.value, h]

lemma FinitePath.zero_at {f : Family} (P : FinitePath f) (a : Γ)
    (h : ∀ i j, (P.piece i).child j a = 0) : P.value a = 0 := by
  rw [FinitePath.value, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [← P.value_eq]
  exact (P.piece i).zero_at a (h i)

lemma TypeII.zero_at {f : Family} (e : TypeII f) (a : Γ)
    (h : ∀ b i j, ((e.path b).piece i).child j a = 0) : e.value a = 0 := by
  simp only [TypeII.value, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    restrict_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [(e.path b).zero_at a (h b)]
  simp

lemma stage_vanish {base : Set Array} (f : Family) (a : Γ)
    (hbase : ∀ x ∈ base, x a = 0) :
    ∀ n x, x ∈ stage base f n → x a = 0 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · exact e.zero_at a (fun i => ih _ (he i))
    · exact e.zero_at a (fun b i j => ih _ (he b i j))

lemma pure_vanish (k : ℕ) (x : Array) (hx : x ∈ Pure k) (a : Γ)
    (ha : Colors.color a ≠ k) : x a = 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_vanish (.pure k) a ?_ n x hn
  intro y hy
  rcases hy with rfl | ⟨b, hb, rfl | rfl⟩
  · rfl
  all_goals
    have hab : a ≠ b := by intro h; subst b; exact ha hb
    simp [hab]

lemma pure_mixed_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ Pure k) :
    restrict (A.set .mixed) x =
      if k ∈ A.colors then restrict (A.set (.pure k)) x else 0 := by
  ext a
  by_cases hcol : Colors.color a = k
  · by_cases hk : k ∈ A.colors <;> simp [Crop.set, hcol, hk]
  · have hz := pure_vanish k x hx a hcol
    by_cases hk : k ∈ A.colors <;> simp [Crop.set, hk, hz]

lemma full_crop (A : Crop) (x : Array) (hx : x ∈ Full) :
    restrict (A.set .mixed) x ∈ Full := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨n, stage_crop .mixed ?_ ?_ n A x hn⟩
  · exact Set.mem_iUnion.mpr ⟨0, pure_zero 0⟩
  · intro B y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [pure_mixed_crop k B y hk]
    split_ifs
    · exact pure_crop k B y hk
    · exact pure_zero k

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.FiniteLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped ENNReal NNReal Classical

def Family.r (f : Family) : ℝ := Parameters.r f.s

def Family.exponent (f : Family) : ℝ≥0∞ := ENNReal.ofReal f.r

def Family.theta (f : Family) (j : ℕ) : ℝ := Parameters.theta f.s (j-1)

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ColorDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.all : Crop := ⟨Set.univ, Set.ordConnected_univ, Set.univ, Set.ordConnected_univ⟩

@[simp] lemma Crop.all_set (f : Family) : Crop.all.set f = Set.univ := by
  cases f <;> simp [Crop.all, Crop.set]

@[simp] lemma restrict_univ (x : Array) : restrict Set.univ x = x := by
  ext a
  simp

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- The completion of c₀₀ under a bounded rational norming set. -/
namespace SeparableQuotient.NormConstruction
open scoped Topology ENNReal
open Filter
universe u
variable {Γ : Type u}

structure NormingSet (Γ : Type u) where
  carrier : Set (Γ →₀ ℚ)
  coordinate_mem : ∀ a, Finsupp.single a 1 ∈ carrier
  coefficient_bound : ∀ f ∈ carrier, ∀ a, |(f a : ℝ)| ≤ 1

namespace NormingSet
variable (K : NormingSet Γ)
abbrev BoundedSpace := lp (fun _ : K.carrier => ℝ) ⊤

def coordinateVector (a : Γ) : K.BoundedSpace :=
  ⟨fun f => (f.val a : ℝ), memℓp_infty ⟨1, by
    rintro _ ⟨f, rfl⟩
    exact K.coefficient_bound f.val f.property a⟩⟩

@[simp] lemma coordinateVector_apply (a : Γ) (f : K.carrier) :
    K.coordinateVector a f = (f.val a : ℝ) := rfl

/-- Algebraic inclusion of the prescribed finitely supported vectors. -/
def finiteMap : (Γ →₀ ℝ) →ₗ[ℝ] K.BoundedSpace :=
  Finsupp.linearCombination ℝ K.coordinateVector

lemma finiteMap_apply (x : Γ →₀ ℝ) (f : K.carrier) :
    K.finiteMap x f = x.sum (fun a t => t * (f.val a : ℝ)) := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : K.carrier => ℝ) ⊤ f) (K.finiteMap x) = _
  simp only [finiteMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    map_smul, lp.evalₗ_apply, K.coordinateVector_apply, smul_eq_mul]

/-- The concrete Banach completion. Its norm is literally the supremum of
absolute evaluations over K. -/
def closedSpan : Submodule ℝ K.BoundedSpace := K.finiteMap.range.topologicalClosure
abbrev Space := K.closedSpan

def includeFinite : (Γ →₀ ℝ) →ₗ[ℝ] K.Space :=
  K.finiteMap.codRestrict K.closedSpan (fun x =>
    Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

lemma denseRange_includeFinite : DenseRange K.includeFinite := by
  have hd : DenseRange (Set.inclusion (show (K.finiteMap.range : Set K.BoundedSpace) ⊆
      K.closedSpan from Submodule.le_topologicalClosure _)) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact hd.comp (show Function.Surjective K.finiteMap.rangeRestrict from fun ⟨y, x, hx⟩ =>
      ⟨x, Subtype.ext hx⟩).denseRange
    (continuous_inclusion _)

def functional (f : K.carrier) : K.Space →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : K.carrier => ℝ) ⊤ f).comp K.closedSpan.subtypeL

def coordinate (a : Γ) : K.Space →L[ℝ] ℝ :=
  K.functional ⟨Finsupp.single a 1, K.coordinate_mem a⟩

@[simp] lemma functional_includeFinite (f : K.carrier) (x : Γ →₀ ℝ) :
    K.functional f (K.includeFinite x) = x.sum (fun a t => t * (f.val a : ℝ)) :=
  K.finiteMap_apply x f

lemma functional_bound (f : K.carrier) (x : K.Space) : |K.functional f x| ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x.val f

lemma norm_functional_le (f : K.carrier) : ‖K.functional f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa [Real.norm_eq_abs] using K.functional_bound f x

end NormingSet
end SeparableQuotient.NormConstruction

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology ENNReal Classical
open Filter
universe u
variable {Γ : Type u} (K : NormingSet Γ)

/-- Stability of a norming set under the specified coordinate crop. -/
def CropStable (A : Set Γ) : Prop := ∀ f ∈ K.carrier, f.filter (· ∈ A) ∈ K.carrier

variable (A : Set Γ) (hA : K.CropStable A)

def cropNormer (f : K.carrier) : K.carrier := ⟨f.val.filter (· ∈ A), hA _ f.property⟩

def cropAmbient : K.BoundedSpace →L[ℝ] K.BoundedSpace :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun f => x (K.cropNormer A hA f), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨f, rfl⟩
        exact lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x _⟩⟩
      map_add' := fun x y => by apply lp.ext; rfl
      map_smul' := fun c x => by apply lp.ext; rfl }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_le_of_forall_le (norm_nonneg x)
        (fun f => lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x
          (K.cropNormer A hA f)))

@[simp] lemma cropAmbient_apply (x : K.BoundedSpace) (f : K.carrier) :
    K.cropAmbient A hA x f = x (K.cropNormer A hA f) := rfl

lemma cropAmbient_finiteMap (x : Γ →₀ ℝ) :
    K.cropAmbient A hA (K.finiteMap x) = K.finiteMap (x.filter (· ∈ A)) := by
  apply lp.ext
  funext f
  rw [K.cropAmbient_apply, K.finiteMap_apply, K.finiteMap_apply]
  simp only [cropNormer, Finsupp.filter_apply, apply_ite, Rat.cast_zero,
    mul_zero]
  rw [Finsupp.sum_filter_index]
  simp only [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]

lemma cropAmbient_mem (x : K.Space) : K.cropAmbient A hA x.val ∈ K.closedSpan := by
  have hi : K.finiteMap.range ∈ Module.End.invtSubmodule (K.cropAmbient A hA) := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v.filter (· ∈ A), (K.cropAmbient_finiteMap A hA v).symm⟩
  have hc := Submodule.topologicalClosure_mem_invtSubmodule hi
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hc
  exact hc ⟨x.val, x.property, rfl⟩

/-- Contractive interval/rectangle projection on the actual Banach completion. -/
def projection : K.Space →L[ℝ] K.Space :=
  ((K.cropAmbient A hA).comp K.closedSpan.subtypeL).codRestrict K.closedSpan
    (K.cropAmbient_mem A hA)

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinateDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

@[reducible] local instance dualNormedGroup_r0e08f0_1 : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace_r0e08f0_1 : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance
/-- The coordinate predual. -/
def predual : Submodule ℝ (StrongDual ℝ K.Space) :=
  (Submodule.span ℝ (Set.range K.coordinate)).topologicalClosure

lemma coordinate_mem_predual (a : Γ) : K.coordinate a ∈ K.predual :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

@[reducible] local instance dualNormedGroup'_r0e08f0_1 : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace'_r0e08f0_1 : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance
/-- The coordinate functional regarded as an element of the actual predual. -/
def predualCoordinate (a : Γ) : K.predual := ⟨K.coordinate a, K.coordinate_mem_predual a⟩

def rationalPredual : (Γ →₀ ℚ) →ₗ[ℚ] K.predual :=
  Finsupp.linearCombination ℚ K.predualCoordinate

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

@[reducible] local instance dualNormedGroup''_r0e08f0_1 : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace''_r0e08f0_1 : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance
/-- Evaluation of any rational array, not only chosen normers. -/
def evaluateArray (x : K.Space) : (Γ →₀ ℚ) →ₗ[ℚ] ℝ where
  toFun := fun f => (K.rationalPredual f).val x
  map_add' := by intro f g; simp
  map_smul' := by intro q f; simp

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinatePredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

/-- The full norming set obtained from finite-stage pure and mixed operations. -/
def norming : NormingSet Γ where
  carrier := Full
  coordinate_mem := Norming.coordinate_mem
  coefficient_bound := full_coefficient_bound

/-- The actual real Banach space E of the CH construction. -/
abbrev E := norming.Space

@[reducible] instance EGroup : NormedAddCommGroup E := inferInstanceAs (NormedAddCommGroup norming.Space)
@[reducible] instance ESpace : NormedSpace ℝ E := inferInstanceAs (NormedSpace ℝ norming.Space)

lemma cropStable (A : Crop) : norming.CropStable (A.set .mixed) :=
  full_crop A

/-- Every ordinal/color rectangle projection is defined on the full completion. -/
def projection (A : Crop) : E →L[ℝ] E := norming.projection (A.set .mixed) (cropStable A)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.ordinalSet (I : Set Γ) (hI : Set.OrdConnected I) : Crop :=
  ⟨I, hI, Set.univ, Set.ordConnected_univ⟩

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.PathLimits
open Filter
open scoped Topology
universe u
variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma unit_bound (f : StrongDual ℝ Z) (hf : ‖f‖ ≤ 1) (x : Z) : ‖f x‖ ≤ ‖x‖ :=
  (f.le_opNorm x).trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hf (norm_nonneg x))

lemma cauchy_of_dense (f : ℕ → StrongDual ℝ Z) (hf : ∀ n, ‖f n‖ ≤ 1)
    (D : Set Z) (hD : Dense D) (h : ∀ x ∈ D, CauchySeq (fun n => f n x)) (x : Z) :
    CauchySeq (fun n => f n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hD x) (ε/4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h y hy) (ε/4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmxy : dist (f m x) (f m y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using unit_bound (f m) (hf m) (x-y)
  have hnxy : dist (f n y) (f n x) ≤ dist x y := by
    rw [dist_comm (f n y)]
    simpa only [dist_eq_norm, ← map_sub] using unit_bound (f n) (hf n) (x-y)
  have ht := calc
    dist (f m x) (f n x) ≤ dist (f m x) (f m y) + dist (f m y) (f n x) := dist_triangle _ _ _
    _ ≤ dist (f m x) (f m y) + (dist (f m y) (f n y) + dist (f n y) (f n x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
  have := hN m hm n hn
  have hd : dist x y < ε/4 := by simpa only [dist_comm] using hxy
  linarith

/-- Bounded pointwise convergence on a dense set determines an actual bounded
functional on the completed space; no weak-star sequential compactness is used. -/
lemma exists_limit_of_dense (f : ℕ → StrongDual ℝ Z) (hf : ∀ n, ‖f n‖ ≤ 1)
    (D : Set Z) (hD : Dense D) (h : ∀ x ∈ D, CauchySeq (fun n => f n x)) :
    ∃ P : StrongDual ℝ Z, ‖P‖ ≤ 1 ∧ ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (P x)) := by
  choose g hg using (fun x => cauchySeq_tendsto_of_complete (cauchy_of_dense f hf D hD h x))
  have hb : Bornology.IsBounded (Set.range f) := isBounded_iff_forall_norm_le.mpr
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hf n⟩
  let P : StrongDual ℝ Z := ContinuousLinearMap.ofTendstoOfBoundedRange g f
    (tendsto_pi_nhds.mpr hg) hb
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound P (by norm_num)
    intro x
    simpa only [P, ContinuousLinearMap.ofTendstoOfBoundedRange_apply, one_mul] using le_of_tendsto (hg x).norm
      (Filter.Eventually.of_forall (fun n => unit_bound (f n) (hf n) x))
  exact ⟨P, hP, hg⟩

end SeparableQuotient.PathLimits

namespace SeparableQuotient.Norming
open scoped Classical
open PathCoding

def Family.base : Family → Set Array
  | .pure k => pureBase k
  | .mixed => ⋃ k, Pure k

def Family.norming (f : Family) : Set Array := ⋃ n, stage f.base f n

lemma Family.norming_subset_full (f : Family) : f.norming ⊆ Full := by
  cases f with
  | pure k => exact pure_subset_full k
  | mixed => exact Set.Subset.rfl

lemma common_stage {f : Family} {ι : Type*} [Fintype ι] (x : ι → Array)
    (hx : ∀ i, x i ∈ f.norming) : ∃ n, ∀ i, x i ∈ stage f.base f n := by
  have hh : ∀ i, ∃ n, x i ∈ stage f.base f n := fun i => Set.mem_iUnion.mp (hx i)
  choose n hn using hh
  exact ⟨Finset.univ.sup n, fun i => stage_mono _ _ (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

lemma TypeII.mem_family {f : Family} (e : TypeII f)
    (h : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) : e.value ∈ f.norming := by
  let ι := Σ b : Fin e.length, Σ i : Fin (e.path b).length, Fin ((e.path b).piece i).length
  obtain ⟨n, hn⟩ := common_stage (fun a : ι => ((e.path a.1).piece a.2.1).child a.2.2)
    (fun a => h a.1 a.2.1 a.2.2)
  exact Set.mem_iUnion.mpr ⟨n+1, Or.inr ⟨e, rfl, fun b i j => hn ⟨b,i,j⟩⟩⟩

lemma admissible_prefix {P : RawPath} (h : P.Admissible) (n : ℕ) : PrefixValid P n where
  successive := fun i j hij _ => h.successive i j hij
  metadata_strict := fun _i _j hij _ => h.metadata_strict hij
  metadata_pos := fun i _ => h.metadata_pos i
  weight_pos := fun i _ => h.weight_pos i
  weight_le_metadata := fun i _ => h.weight_le_metadata i
  rho_bound := fun i _ => h.rho_bound i
  rule := fun i _ => h.rule i

/-- Actual infinite paths retain all original Type I expressions, weights, and
uncropped metadata. No completion of the coding tree is inserted as a path. -/
structure InfinitePath (f : Family) where
  raw : RawPath
  admissible : raw.Admissible
  piece : ℕ → TypeI f
  value_eq : ∀ i, (piece i).value = raw.piece i
  weight_eq : ∀ i, (piece i).weight = raw.weight i
  successive : ∀ i j, i < j → Successive f (raw.piece i) (raw.piece j)
  children_mem : ∀ i j, (piece i).child j ∈ f.norming

def InfinitePath.prefix {f : Family} (P : InfinitePath f) (n : ℕ) : FinitePath f where
  raw := P.raw
  length := n+1
  length_pos := by omega
  valid := admissible_prefix P.admissible (n+1)
  piece := fun i => P.piece i
  value_eq := fun i => P.value_eq i
  weight_eq := fun i => P.weight_eq i
  mixed_successive := fun i j hij => P.successive i j hij

def FinitePath.oneTerm {f : Family} (P : FinitePath f) (A : Crop) : TypeII f where
  length := 1
  path := fun _ => P
  crop := fun _ => A
  coefficient := fun _ => 1
  bound := by simp
  disjoint_active := fun b c hbc => (hbc (Subsingleton.elim _ _)).elim

@[simp] lemma FinitePath.oneTerm_value {f : Family} (P : FinitePath f) (A : Crop) :
    (P.oneTerm A).value = restrict (A.set f) P.value := by
  change (∑ _b : Fin 1, (1 : ℚ) • restrict (A.set f) P.value) = _
  simp

lemma InfinitePath.prefix_crop_mem {f : Family} (P : InfinitePath f) (n : ℕ) (A : Crop) :
    restrict (A.set f) (P.prefix n).value ∈ f.norming := by
  rw [← FinitePath.oneTerm_value]
  exact TypeII.mem_family _ (fun _ i j => P.children_mem i j)

lemma InfinitePath.prefix_mem {f : Family} (P : InfinitePath f) (n : ℕ) :
    (P.prefix n).value ∈ Full := by
  apply f.norming_subset_full
  simpa only [Crop.all_set, restrict_univ] using P.prefix_crop_mem n Crop.all

lemma InfinitePath.piece_coefficient_unique {f : Family} (P : InfinitePath f)
    {i j : ℕ} {a : Γ} (hi : P.raw.piece i a ≠ 0) (hj : P.raw.piece j a ≠ 0) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have := P.admissible.successive i j h a (Finsupp.mem_support_iff.mpr hi)
      a (Finsupp.mem_support_iff.mpr hj)
    exact (lt_irrefl a) this
  · have := P.admissible.successive j i h a (Finsupp.mem_support_iff.mpr hj)
      a (Finsupp.mem_support_iff.mpr hi)
    exact (lt_irrefl a) this

lemma InfinitePath.prefix_at_hit {f : Family} (P : InfinitePath f) (a : Γ) (i n : ℕ)
    (hi : P.raw.piece i a ≠ 0) (hin : i ≤ n) :
    (P.prefix n).value a = P.raw.piece i a := by
  change (∑ j : Fin (n+1), P.raw.piece j) a = _
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (n+1))]
  · intro j _ hji
    by_contra hn
    exact hji (Fin.ext (P.piece_coefficient_unique hn hi))
  · simp

lemma InfinitePath.prefix_coordinate_eventually_constant {f : Family} (P : InfinitePath f)
    (a : Γ) : ∃ q : ℚ, ∀ᶠ n in Filter.atTop, (P.prefix n).value a = q := by
  by_cases h : ∃ i, P.raw.piece i a ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact ⟨P.raw.piece i a, (Filter.eventually_ge_atTop i).mono (fun n hn => P.prefix_at_hit a i n hi hn)⟩
  · push Not at h
    refine ⟨0, Filter.Eventually.of_forall (fun n => ?_)⟩
    change (∑ j : Fin (n+1), P.raw.piece j) a = 0
    simp only [Finsupp.finsetSum_apply, h, Finset.sum_const_zero]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup8_r0e08f0_1 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace8_r0e08f0_1 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
def pathPartial {f : Family} (P : InfinitePath f) (n : ℕ) : StrongDual ℝ E :=
  norming.functional ⟨(P.prefix n).value, P.prefix_mem n⟩

lemma pathPartial_bound {f : Family} (P : InfinitePath f) (n : ℕ) : ‖pathPartial P n‖ ≤ 1 :=
  norming.norm_functional_le _

lemma pathPartial_finite_cauchy {f : Family} (P : InfinitePath f) (x : Γ →₀ ℝ) :
    CauchySeq (fun n => pathPartial P n (norming.includeFinite x)) := by
  choose q hq using P.prefix_coordinate_eventually_constant
  have he : ∀ᶠ n in atTop, pathPartial P n (norming.includeFinite x) =
      x.sum (fun a t => t * (q a : ℝ)) := by
    filter_upwards [(Filter.eventually_all_finset x.support).mpr (fun a _ => hq a)] with n hn
    rw [pathPartial, norming.functional_includeFinite]
    apply Finset.sum_congr rfl
    intro a ha
    change x a * ((P.prefix n).value a : ℝ) = x a * (q a : ℝ)
    rw [hn a ha]
  exact (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)).cauchySeq

lemma exists_pathFunctional {f : Family} (P : InfinitePath f) :
    ∃ F : StrongDual ℝ E, ‖F‖ ≤ 1 ∧ ∀ x, Tendsto (fun n => pathPartial P n x) atTop (𝓝 (F x)) := by
  apply PathLimits.exists_limit_of_dense _ (pathPartial_bound P) _ norming.denseRange_includeFinite
  rintro _ ⟨x, rfl⟩
  exact pathPartial_finite_cauchy P x

/-- Path partial sums are bounded and converge pointwise. -/
def pathFunctional {f : Family} (P : InfinitePath f) : StrongDual ℝ E :=
  (exists_pathFunctional P).choose

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup11_r0e08f0_1 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace11_r0e08f0_1 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
/-- Admissible block sequences with real coefficients. Pure mode requires one color, mixed mode both orders. -/
structure BlockSequence (f : Family) where
  vector : ℕ → Γ →₀ ℝ
  nonzero : ∀ n, vector n ≠ 0
  successive : ∀ i j, i < j → ∀ a ∈ (vector i).support, ∀ b ∈ (vector j).support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)
  pure_color : ∀ k, f = .pure k → ∀ n a, a ∈ (vector n).support → Colors.color a = k

def BlockSequence.embed {f : Family} (x : BlockSequence f) (n : ℕ) : E :=
  norming.includeFinite (x.vector n)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

def FinitePath.window {f : Family} (P : FinitePath f) (J T : ℕ) : Array :=
  ∑ i : Fin P.length, if J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T then P.raw.piece i else 0

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- A finite path with its original finite-stage children. -/
def LegalFinitePath (f : Family) := {P : FinitePath f // ∀ i j, (P.piece i).child j ∈ f.norming}

def WindowHit {f : Family} (P : LegalFinitePath f) (x : Γ →₀ ℝ) (J T : ℕ) (δ : ℝ) : Prop :=
  δ < |norming.evaluateArray (norming.includeFinite x) (P.val.window J T)|

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.SeriesTails
open Filter
open scoped Topology Classical

noncomputable def tail (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑' k, a (k+N)

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def vectorL1 (x : Γ →₀ ℝ) : ℝ := ∑ a ∈ x.support, |x a|

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PartitionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def intervalProjection (I : Set Γ) (hI : Set.OrdConnected I) : E →L[ℝ] E :=
  projection (Crop.ordinalSet I hI)

/-- An interval-partition inequality and its constant-16 difference-vector version. Intervals may be unbounded or singletons. -/
def PartitionBound (x : E) (N : ℕ) (A r : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ N → ∀ (I : Fin d → Set Γ) (hI : ∀ i, Set.OrdConnected (I i)),
    (∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) →
    ∑ i : Fin d, ‖intervalProjection (I i) (hI i) x‖ ≤ A * (d : ℝ)^(1/r)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

/-- Algebraic finite blocks in the specified tail, with no completion added. -/
noncomputable def BlockSequence.tailSpan {f : Family} (z : BlockSequence f) (a : ℕ) :
    Submodule ℝ (Γ →₀ ℝ) := Submodule.span ℝ (Set.range (fun n => z.vector (n+a)))

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Window blocks with partition estimates, pathwise nullity, and coherent support bounds. -/
structure WindowBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (a : ℕ) where
  blocks : BlockSequence f
  lower : ℕ → ℕ
  upper : ℕ → ℕ
  mem_tail : ∀ n, blocks.vector n ∈ z.tailSpan a
  lower_norm : ∀ n, 1 ≤ ‖blocks.embed n‖
  upper_norm : ∀ n, ‖blocks.embed n‖ ≤ 2
  prescribed : ∀ n, J < lower n
  order : ∀ n, lower n ≤ upper n
  separated : ∀ i j, i < j → upper i < lower j
  coherence : ∀ i j k, j < i → k < i → ∀ α ∈ (blocks.vector j).support,
    ∀ β ∈ (blocks.vector k).support, rho (min α β) (max α β) < lower i
  partition : ∀ n, PartitionBound (blocks.embed n) (f.L (lower n)) 16 f.r
  tail_small : ∀ n, vectorL1 (blocks.vector n) * tail (fun j => 1/(f.m j : ℝ)) (upper n+1) ≤ ε
  tail_vanish : Tendsto (fun n => vectorL1 (blocks.vector n) * tail (fun j => 1/(f.m j : ℝ)) (upper n+1)) atTop (𝓝 0)
  path_null : ∀ P : InfinitePath f, Tendsto (fun n => pathFunctional P (blocks.embed n)) atTop (𝓝 0)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Successively thinned windows. The threshold indexed by n is used strictly after n. -/
structure ThinnedWindows {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (a : ℕ)
    extends WindowBlocks z J ε a where
  threshold : ℕ → ℝ
  threshold_pos : ∀ n, 0 < threshold n
  threshold_charge_succ : ∀ n, (upper n+1 : ℝ) * threshold n = ε * (1/2 : ℝ)^(n+1)
  threshold_charge : ∀ n, (upper n : ℝ) * threshold n ≤ ε * (1/2 : ℝ)^(n+1)
  four_hits_after : ∀ n (S : Finset ℕ), (∀ i ∈ S, n < i) → S.card = 4 →
    ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S,
      WindowHit P (blocks.vector i) (lower i) (upper i) (threshold n)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.MarkedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u
variable {ι : Type u} [Fintype ι]

def vec (p : ℝ≥0∞) (v : ι → ℝ) : lp (fun _ : ι => ℝ) p := ⟨v, Memℓp.all v⟩

end SeparableQuotient.FiniteVectors

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

noncomputable def ThinnedWindows.evalVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (i : s) : ℝ :=
  if i ∈ I then |norming.evaluateArray (w.blocks.embed i) g| else 0

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def smallBudget (f : Family) (J d : ℕ) : ℝ :=
  (1552/7)*f.theta J+64*(1/8)^d
noncomputable def largeUnit (f : Family) (J : ℕ) (s : Finset ℕ) : ℝ :=
  16*(1+(Parameters.B f.s (J-1) : ℝ)+(s.card : ℝ)^(1-1/f.q))
noncomputable def largeBudget (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : ℝ :=
  largeUnit f J s*(1+(Parameters.B f.s (J-1) : ℝ))^d

structure DepthMajorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (d : ℕ) where
  small : s → ℝ
  large : s → ℝ
  small_nonneg : ∀ i, 0 ≤ small i
  large_nonneg : ∀ i, 0 ≤ large i
  small_support : ∀ i, i ∉ I → small i = 0
  large_support : ∀ i, i ∉ I → large i = 0
  majorizes : ∀ i, w.evalVector s I g i ≤ small i+large i
  norm_small : ‖vec f.exponent small‖ ≤ smallBudget f J d
  sum_large : (∑ i : s, large i) ≤ largeBudget f J s d

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.StrictSingularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set Metric
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A strictly singular operator is not bounded below on any closed infinite-dimensional subspace. -/
def StrictlySingular (T : Y →L[𝕜] Z) : Prop :=
  ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) → ¬ FiniteDimensional 𝕜 M →
    ∀ c : ℝ, 0 < c → ∃ x : M, ‖T x‖ < c*‖x‖

lemma finiteDimensional_of_ker [FiniteDimensional 𝕜 Z] (T : Y →ₗ[𝕜] Z)
    [FiniteDimensional 𝕜 T.ker] : FiniteDimensional 𝕜 Y := by
  have h : FiniteDimensional 𝕜 (Submodule.comap T (⊤ : Submodule 𝕜 Z)) := inferInstance
  rw [Submodule.comap_top] at h
  exact FiniteDimensional.of_injective (Submodule.topEquiv : (⊤ : Submodule 𝕜 Y) ≃ₗ[𝕜] Y).symm.toLinearMap
    (Submodule.topEquiv.symm.injective)

lemma exists_finite_vector_normers (F : Submodule 𝕜 Y) [FiniteDimensional 𝕜 F] :
    ∃ D : Finset (StrongDual 𝕜 Y), (∀ d ∈ D, ‖d‖ ≤ 1) ∧
      ∀ v : F, ∃ d ∈ D, ‖v‖ ≤ 2*‖d v‖ := by
  let U (d : closedBall (0 : StrongDual 𝕜 Y) 1) : Set F := {v | (1/2 : ℝ) < ‖d.1 v‖}
  have hU : ∀ d, IsOpen (U d) := fun d =>
    isOpen_lt continuous_const ((d.1.comp F.subtypeL).continuous.norm)
  have hc : sphere (0 : F) 1 ⊆ ⋃ d, U d := by
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    obtain ⟨d,hd,he⟩ := exists_dual_vector'' 𝕜 (v : Y)
    refine Set.mem_iUnion.mpr ⟨⟨d,by simpa only [mem_closedBall,dist_zero_right] using hd⟩,?_⟩
    change (1/2 : ℝ) < ‖d v‖
    rw [he,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    change (1/2 : ℝ) < ‖v‖
    rw [hn]; norm_num
  obtain ⟨t,ht⟩ := (isCompact_sphere (0 : F) 1).elim_finite_subcover U hU hc
  refine ⟨insert 0 (t.image Subtype.val),?_,?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hd
      simpa only [mem_closedBall,dist_zero_right] using d.property
  · intro v
    by_cases hv : v = 0
    · subst v; exact ⟨0,Finset.mem_insert_self _ _,by simp⟩
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : F := (↑‖v‖ : 𝕜)⁻¹ • v
    have hw : w ∈ sphere (0 : F) 1 := by
      simp only [w,mem_sphere,dist_zero_right,norm_smul,norm_inv,RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hp.ne']
    obtain ⟨d,hd,he⟩ := Set.mem_iUnion₂.mp (ht hw)
    refine ⟨d,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩),?_⟩
    change (1/2 : ℝ) < ‖d.1 ((↑‖v‖ : 𝕜)⁻¹ • (v : Y))‖ at he
    rw [map_smul,norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg v)] at he
    have hm := mul_lt_mul_of_pos_left he hp
    rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul] at hm
    linarith

/-- Finitely many exact annihilation conditions preserve infinite dimension. -/
lemma finite_annihilator (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y))
    (hI : ¬ FiniteDimensional 𝕜 M) (D : Finset (StrongDual 𝕜 Y)) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ x ∈ N, ∀ d ∈ D, d x = 0 := by
  let A : Y →L[𝕜] (D → 𝕜) := ContinuousLinearMap.pi (fun d => d.1)
  let N := M ⊓ A.ker
  refine ⟨N,inf_le_left,hM.inter A.isClosed_ker,?_,?_⟩
  · intro hn
    let : FiniteDimensional 𝕜 N := hn
    let B := A.comp M.subtypeL
    have hker : FiniteDimensional 𝕜 B.ker := by
      let L : B.ker →ₗ[𝕜] N := {
        toFun := fun x => ⟨x.1.1,⟨x.1.2,x.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      exact FiniteDimensional.of_injective L (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun y : N => (y : Y)) h)))
    exact hI (finiteDimensional_of_ker B.toLinearMap)
  · intro x hx d hd
    have he : A x = 0 := hx.2
    exact congrFun he ⟨d,hd⟩

lemma StrictlySingular.exists_unit_small (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) : ∃ x : M, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  obtain ⟨x,hx⟩ := hT M hM hI ε hε
  have hx0 : 0 < ‖x‖ := by
    by_contra hh
    have hz : ‖x‖ = 0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hz,mul_zero] at hx
    exact (not_lt_of_ge (norm_nonneg _)) hx
  refine ⟨(↑‖x‖ : 𝕜)⁻¹ • x,?_,?_⟩
  · simp only [norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hx0.ne']
  · change ‖T ((↑‖x‖ : 𝕜)⁻¹ • (x : Y))‖ < ε
    rw [map_smul,norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    exact (inv_mul_lt_iff₀ hx0).mpr (by nlinarith [hx])

end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

structure VectorNormers (u : ℕ → Y) where
  D : ℕ → Finset (StrongDual 𝕜 Y)
  unit : ∀ m, ∀ d ∈ D m, ‖d‖ ≤ 1
  norming : ∀ m, ∀ c : ℕ → 𝕜, ∃ d ∈ D m,
    ‖∑ i ∈ Finset.range m, c i • u i‖ ≤ 2 * ‖d (∑ i ∈ Finset.range m, c i • u i)‖
  vanish : ∀ m n, m ≤ n → ∀ d ∈ D m, d (u n) = 0

namespace VectorNormers
variable {u : ℕ → Y} (H : VectorNormers (𝕜 := 𝕜) u)
lemma prefix_eval (c : ℕ → 𝕜) {m N : ℕ} (hm : m ≤ N) {d : StrongDual 𝕜 Y} (hd : d ∈ H.D m) :
    d (∑ i ∈ Finset.range N, c i • u i) = d (∑ i ∈ Finset.range m, c i • u i) := by
  simp only [map_sum,map_smul]
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i _ hi
  rw [H.vanish m i (by simpa using hi) d hd,smul_zero]

include H in
lemma prefix_bound (c : ℕ → 𝕜) {m N : ℕ} (hm : m ≤ N) :
    ‖∑ i ∈ Finset.range m, c i • u i‖ ≤ 2*‖∑ i ∈ Finset.range N, c i • u i‖ := by
  obtain ⟨d,hd,hb⟩ := H.norming m c
  rw [← H.prefix_eval c hm hd] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left ((d.le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (H.unit m d hd) (norm_nonneg _))) (by norm_num))

include H in
lemma coefficient_bound (hu : ∀ n, ‖u n‖ = 1) (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n‖ ≤ 4*‖∑ i ∈ Finset.range N, c i • u i‖ := by
  have hp := H.prefix_bound c (Nat.succ_le_of_lt hn)
  have hq := H.prefix_bound c hn.le
  have he : c n • u n = (∑ i ∈ Finset.range (n+1), c i • u i) - (∑ i ∈ Finset.range n, c i • u i) := by
    rw [Finset.sum_range_succ,add_sub_cancel_left]
  have hh := norm_sub_le (∑ i ∈ Finset.range (n+1), c i • u i) (∑ i ∈ Finset.range n, c i • u i)
  rw [← he,norm_smul,hu,mul_one] at hh
  linarith

lemma linearCombination_eq_range (c : ℕ →₀ 𝕜) {N : ℕ} (hN : c.support ⊆ Finset.range N) :
    Finsupp.linearCombination 𝕜 u c = ∑ i ∈ Finset.range N, c i • u i := by
  change (∑ i ∈ c.support, c i • u i) = _
  apply Finset.sum_subset hN
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi,zero_smul]

include H in
lemma finsupp_bound (hu : ∀ n, ‖u n‖ = 1) (c : ℕ →₀ 𝕜) (n : ℕ) :
    ‖c n‖ ≤ 4*‖Finsupp.linearCombination 𝕜 u c‖ := by
  obtain ⟨N,hN⟩ := (insert n c.support).exists_nat_subset_range
  rw [linearCombination_eq_range c (fun i hi => hN (Finset.mem_insert_of_mem hi))]
  exact H.coefficient_bound hu c (Finset.mem_range.mp (hN (Finset.mem_insert_self _ _)))

include H in
lemma linearIndependent (hu : ∀ n, ‖u n‖ = 1) : LinearIndependent 𝕜 u := by
  rw [linearIndependent_iff]
  intro c hc
  ext n
  have hb := H.finsupp_bound hu c n
  rw [hc,norm_zero,mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
end VectorNormers

namespace SmallRestriction

def listSpan (l : List Y) : Submodule 𝕜 Y := Submodule.span 𝕜 (l.toFinset : Set Y)
instance instFiniteDimensionalSubtypeMemSubmoduleListSpan (l : List Y) : FiniteDimensional 𝕜 (listSpan (𝕜 := 𝕜) l) := FiniteDimensional.span_finset 𝕜 _

def listNormers (l : List Y) : Finset (StrongDual 𝕜 Y) :=
  (exists_finite_vector_normers (listSpan (𝕜 := 𝕜) l)).choose
lemma listNormers_spec (l : List Y) : (∀ d ∈ listNormers (𝕜 := 𝕜) l, ‖d‖ ≤ 1) ∧
    ∀ x ∈ listSpan (𝕜 := 𝕜) l, ∃ d ∈ listNormers (𝕜 := 𝕜) l, ‖x‖ ≤ 2*‖d x‖ := by
  have hh := (exists_finite_vector_normers (listSpan (𝕜 := 𝕜) l)).choose_spec
  exact ⟨hh.1,fun x hx => hh.2 ⟨x,hx⟩⟩

structure State (𝕜 Y : Type*) [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  vectors : List Y
  normers : Finset (StrongDual 𝕜 Y)

variable (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
  (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
  (ε : ℝ) (hε : 0 < ε)

include hT hM hI hε in
lemma exists_next (s : State 𝕜 Y) : ∃ y : Y, y ∈ M ∧ ‖y‖ = 1 ∧
    ‖T y‖ < ε*(1/2 : ℝ)^(s.vectors.length+3) ∧ ∀ d ∈ s.normers, d y = 0 := by
  obtain ⟨N,hNM,hNc,hNi,hNd⟩ := finite_annihilator M hM hI s.normers
  obtain ⟨y,hy,hTy⟩ := StrictlySingular.exists_unit_small T hT N hNc hNi
    (ε*(1/2 : ℝ)^(s.vectors.length+3)) (by positivity)
  exact ⟨y,hNM y.property,hy,hTy,hNd y y.property⟩

def nextVector (s : State 𝕜 Y) : Y := (exists_next T hT M hM hI ε hε s).choose
lemma nextVector_spec (s : State 𝕜 Y) : nextVector T hT M hM hI ε hε s ∈ M ∧
    ‖nextVector T hT M hM hI ε hε s‖ = 1 ∧
    ‖T (nextVector T hT M hM hI ε hε s)‖ < ε*(1/2 : ℝ)^(s.vectors.length+3) ∧
    ∀ d ∈ s.normers, d (nextVector T hT M hM hI ε hε s) = 0 :=
  (exists_next T hT M hM hI ε hε s).choose_spec

def step (s : State 𝕜 Y) : State 𝕜 Y :=
  let l := s.vectors ++ [nextVector T hT M hM hI ε hε s]
  ⟨l,s.normers ∪ listNormers l⟩

def state : ℕ → State 𝕜 Y
  | 0 => ⟨[],listNormers []⟩
  | n+1 => step T hT M hM hI ε hε (state n)

def seq (n : ℕ) : Y := nextVector T hT M hM hI ε hε (state T hT M hM hI ε hε n)

local notation "s" => state T hT M hM hI ε hε
local notation "u" => seq T hT M hM hI ε hε
lemma vectors_state (n : ℕ) : (s n).vectors = List.ofFn (fun i : Fin n => u i) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change (s n).vectors ++ [u n] = _
    rw [ih,List.ofFn_succ_last (f := fun i : Fin (n+1) => u i)]
    rfl

lemma state_length (n : ℕ) : (s n).vectors.length = n := by rw [vectors_state,List.length_ofFn]
lemma seq_spec (n : ℕ) : u n ∈ M ∧ ‖u n‖ = 1 ∧ ‖T (u n)‖ < ε*(1/2 : ℝ)^(n+3) := by
  have hh := nextVector_spec T hT M hM hI ε hε (s n)
  rw [state_length] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

lemma normers_mono : Monotone (fun n => (s n).normers) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

lemma normers_unit (n : ℕ) : ∀ d ∈ (s n).normers, ‖d‖ ≤ 1 := by
  induction n with
  | zero => exact (listNormers_spec []).1
  | succ n ih =>
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact ih d hd
    · exact (listNormers_spec _).1 d hd

lemma listNormers_subset (n : ℕ) : listNormers (s n).vectors ⊆ (s n).normers := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact Finset.subset_union_right

def normers : VectorNormers (𝕜 := 𝕜) u where
  D := fun n => (s n).normers
  unit := normers_unit T hT M hM hI ε hε
  norming := by
    intro m c
    have hx : (∑ i ∈ Finset.range m, c i • u i) ∈ listSpan (𝕜 := 𝕜) (s m).vectors := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      apply Submodule.subset_span
      rw [Finset.mem_coe,List.mem_toFinset,vectors_state]
      exact List.mem_ofFn.mpr ⟨⟨i,Finset.mem_range.mp hi⟩,rfl⟩
    obtain ⟨d,hd,hb⟩ := (listNormers_spec (s m).vectors).2 _ hx
    exact ⟨d,listNormers_subset T hT M hM hI ε hε m hd,hb⟩
  vanish := by
    intro m n hmn d hd
    exact (nextVector_spec T hT M hM hI ε hε (s n)).2.2.2 d
      (normers_mono T hT M hM hI ε hε hmn hd)

end SmallRestriction
end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma VectorNormers.norm_small {u : ℕ → Y} (H : VectorNormers (𝕜 := 𝕜) u)
    (hu : ∀ n, ‖u n‖ = 1) (T : Y →L[𝕜] Z) (ε : ℝ) (hε : 0 ≤ ε)
    (hT : ∀ n, ‖T (u n)‖ ≤ ε*(1/2 : ℝ)^(n+3)) (c : ℕ →₀ 𝕜) :
    ‖T (Finsupp.linearCombination 𝕜 u c)‖ ≤ ε*‖Finsupp.linearCombination 𝕜 u c‖ := by
  let x := Finsupp.linearCombination 𝕜 u c
  have hc (n : ℕ) := H.finsupp_bound hu c n
  have hgeo : (∑ i ∈ c.support, (1/2 : ℝ)^i) ≤ 2 := by
    simpa only [tsum_geometric_two] using summable_geometric_two.sum_le_tsum c.support (fun i _ => by positivity)
  calc
    ‖T x‖ ≤ ∑ i ∈ c.support, ‖c i‖*‖T (u i)‖ := by
      change ‖T (∑ i ∈ c.support, c i • u i)‖ ≤ _
      rw [map_sum]
      simpa only [map_smul,norm_smul] using norm_sum_le c.support (fun i => T (c i • u i))
    _ ≤ ∑ i ∈ c.support, (4*‖x‖)*(ε*(1/2 : ℝ)^(i+3)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (hT i) (norm_nonneg _) (by positivity)
    _ = (4*‖x‖*ε*(1/2 : ℝ)^3)*(∑ i ∈ c.support, (1/2 : ℝ)^i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]; ring
    _ ≤ (4*‖x‖*ε*(1/2 : ℝ)^3)*2 := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = ε*‖x‖ := by ring

/-- A strictly singular operator has arbitrarily small norm on a closed infinite-dimensional subspace. -/
theorem StrictlySingular.exists_small_restriction_oai (T : Y →L[𝕜] Z)
    (hT : ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) → ¬ FiniteDimensional 𝕜 M →
      ∀ c : ℝ, 0 < c → ∃ x : M, ‖T x‖ < c*‖x‖)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ x ∈ N, ‖T x‖ ≤ ε*‖x‖ := by
  change StrictlySingular T at hT
  let u := SmallRestriction.seq T hT M hM hI ε hε
  have hu (n : ℕ) := SmallRestriction.seq_spec T hT M hM hI ε hε n
  let H := SmallRestriction.normers T hT M hM hI ε hε
  let A := Submodule.span 𝕜 (Set.range u)
  let N := A.topologicalClosure
  have hAM : A ≤ M := Submodule.span_le.mpr (by rintro _ ⟨n,rfl⟩; exact (hu n).1)
  refine ⟨N,closure_minimal hAM hM,Submodule.isClosed_topologicalClosure _,?_,?_⟩
  · intro hn
    let : FiniteDimensional 𝕜 N := hn
    let v (n : ℕ) : N := ⟨u n,Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))⟩
    have hv : LinearIndependent 𝕜 v := LinearIndependent.of_comp N.subtype
      (H.linearIndependent (fun n => (hu n).2.1))
    exact Module.Finite.not_linearIndependent_of_infinite v hv
  · have hc : IsClosed {x : Y | ‖T x‖ ≤ ε*‖x‖} :=
      isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
    apply closure_minimal _ hc
    intro x hx
    obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    exact H.norm_small (fun n => (hu n).2.1) T ε hε.le (fun n => (hu n).2.2.le) c

end SeparableQuotient.Singular

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction_oai.{u_1, u_2, u_3} := @OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction_oai.{u_1, u_2, u_3}
