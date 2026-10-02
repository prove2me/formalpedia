-- Prove2me | solution 1 for MooreFoelner.mass_lt_of_marginalizes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T05:28:42.12031+00:00
-- url     : https://prove2.me/submissions/28d4ffb2-93e2-4588-8c1b-10a3ced43595

import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §3 group A: Lemmas 3.4, 3.5, 3.9 and 3.11

Shared tools: `pull act a f` is `s ↦ f (s · a)` (zero where `s · a` is undefined), so that
`valAt act μ s a = pull act a μ s`. The adjoint formula `∑_s g(s) f(s·a) = ∑_x f(x) g(x·a⁻¹)`
(`finsum_mul_pull`) gives `∑_s f(s · a) ≤ ∑_x f(x)` for nonnegative `f`, and the telescoping along a
shortest word (`finsum_abs_pull_sub_le`, `finsum_max_sub_pull_le`) gives Lemmas 3.5 and 3.9.
-/

set_option linter.unusedSectionVars false

namespace MooreFoelner.Dev.Sec3A

open Classical Function MooreFoelner

variable {G S : Type*} [Group G]

/-- `pull act a f s = f (s · a)`, and `0` when `s · a` is undefined. -/
noncomputable def pull (act : S → G → Option S) (a : G) (f : S → ℝ) (s : S) : ℝ :=
  match act s a with
  | some x => f x
  | none => 0

lemma pull_of_some {act : S → G → Option S} {a : G} {f : S → ℝ} {s x : S}
    (h : act s a = some x) : pull act a f s = f x := by
  simp [pull, h]

lemma pull_of_none {act : S → G → Option S} {a : G} {f : S → ℝ} {s : S}
    (h : act s a = none) : pull act a f s = 0 := by
  simp [pull, h]

lemma pull_nonneg {act : S → G → Option S} {a : G} {f : S → ℝ} (hf : ∀ x, 0 ≤ f x) (s : S) :
    0 ≤ pull act a f s := by
  cases h : act s a with
  | none => rw [pull_of_none h]
  | some x => rw [pull_of_some h]; exact hf x

lemma pull_one {act : S → G → Option S} (hact : IsPartialAction act) (f : S → ℝ) (s : S) :
    pull act 1 f s = f s := pull_of_some (hact.one s)

section PartialAction

variable {act : S → G → Option S}

lemma act_inv_of (hact : IsPartialAction act) {a : G} {s x : S} (h : act s a = some x) :
    act x a⁻¹ = some s := (hact.inv a s x).1 h

lemma act_of_inv (hact : IsPartialAction act) {a : G} {s x : S} (h : act x a⁻¹ = some s) :
    act s a = some x := (hact.inv a s x).2 h

lemma act_inj (hact : IsPartialAction act) {a : G} {s s' x : S} (h : act s a = some x)
    (h' : act s' a = some x) : s = s' := by
  have h1 := act_inv_of hact h
  have h2 := act_inv_of hact h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- If `y · a = x`, then `y · (a b)` is defined exactly when `x · b` is, with the same value
(Exel's composition law together with the inverse axiom). -/
lemma act_mul_of_act (hact : IsPartialAction act) {y x : S} {a : G} (h : act y a = some x)
    (b : G) : act y (a * b) = act x b := by
  cases hb : act x b with
  | some z => exact hact.mul a b y x z h hb
  | none =>
    cases hab : act y (a * b) with
    | none => rfl
    | some z =>
      have h1 := act_inv_of hact h
      have := hact.mul a⁻¹ (a * b) x y z h1 hab
      rw [inv_mul_cancel_left] at this
      rw [this] at hb
      cases hb

lemma pull_mul_of_act (hact : IsPartialAction act) (f : S → ℝ) {y x : S} {a : G}
    (h : act y a = some x) (b : G) : pull act (a * b) f y = pull act b f x := by
  simp only [pull, act_mul_of_act hact h b]

/-- The adjoint formula `∑_s g(s) f(s · a) = ∑_x f(x) g(x · a⁻¹)`; no finiteness is needed, as the
supports of the two summands correspond bijectively. -/
lemma finsum_mul_pull (hact : IsPartialAction act) (a : G) (f g : S → ℝ) :
    ∑ᶠ s, g s * pull act a f s = ∑ᶠ x, f x * pull act a⁻¹ g x := by
  rw [← finsum_mem_support, ← finsum_mem_support (fun x => f x * pull act a⁻¹ g x)]
  apply finsum_mem_eq_of_bijOn (fun s => (act s a).getD s)
  · refine ⟨?_, ?_, ?_⟩
    · intro s hs
      simp only [mem_support] at hs ⊢
      cases h : act s a with
      | none => simp [pull_of_none h] at hs
      | some x =>
        rw [pull_of_some h] at hs
        simp only [Option.getD_some]
        rw [pull_of_some (act_inv_of hact h), mul_comm]
        exact hs
    · intro s1 hs1 s2 hs2 heq
      simp only [mem_support] at hs1 hs2
      cases h1 : act s1 a with
      | none => simp [pull_of_none h1] at hs1
      | some x1 =>
        cases h2 : act s2 a with
        | none => simp [pull_of_none h2] at hs2
        | some x2 =>
          simp only [h1, h2, Option.getD_some] at heq
          subst heq
          exact act_inj hact h1 h2
    · intro x hx
      simp only [mem_support] at hx
      cases h : act x a⁻¹ with
      | none => simp [pull_of_none h] at hx
      | some s =>
        have h' := act_of_inv hact h
        refine ⟨s, ?_, ?_⟩
        · simp only [mem_support]
          rw [pull_of_some h']
          rw [pull_of_some h] at hx
          rw [mul_comm]
          exact hx
        · simp [h']
  · intro s hs
    simp only [mem_support] at hs
    cases h : act s a with
    | none => simp [pull_of_none h] at hs
    | some x =>
      simp only [Option.getD_some]
      rw [pull_of_some h, pull_of_some (act_inv_of hact h)]
      ring

lemma hasFiniteSupport_pull (hact : IsPartialAction act) (a : G) {f : S → ℝ}
    (hf : HasFiniteSupport f) : HasFiniteSupport (pull act a f) := by
  refine Set.Finite.subset (Set.Finite.image (fun x => (act x a⁻¹).getD x) hf) ?_
  intro s hs
  simp only [mem_support] at hs
  cases h : act s a with
  | none => simp [pull_of_none h] at hs
  | some x =>
    rw [pull_of_some h] at hs
    exact ⟨x, hs, by simp [act_inv_of hact h]⟩

/-- `∑_s f(s · a) ≤ ∑_x f(x)` for nonnegative finitely supported `f`. -/
lemma finsum_pull_le (hact : IsPartialAction act) (a : G) {f : S → ℝ} (hf : HasFiniteSupport f)
    (hf0 : ∀ x, 0 ≤ f x) : ∑ᶠ s, pull act a f s ≤ ∑ᶠ x, f x := by
  have key := finsum_mul_pull hact a f (fun _ => 1)
  simp only [one_mul] at key
  rw [key]
  have hp : ∀ x, 0 ≤ pull act a⁻¹ (fun _ => (1 : ℝ)) x ∧ pull act a⁻¹ (fun _ => (1 : ℝ)) x ≤ 1 := by
    intro x
    cases h : act x a⁻¹ with
    | none => rw [pull_of_none h]; norm_num
    | some y => rw [pull_of_some h]; norm_num
  apply finsum_le_finsum'
  · refine Set.Finite.subset hf ?_
    intro x hx
    simp only [mem_support] at hx ⊢
    intro h0
    simp [h0] at hx
  · exact hf
  · intro x
    exact mul_le_of_le_one_right (hf0 x) (hp x).2

end PartialAction

section Word

/-- A shortest word: a list in `Γ` of length `wordLength Γ g` with product `g`. -/
lemma exists_word {Γ : Finset G} (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (g : G) :
    ∃ w : List G, w.length = wordLength Γ g ∧ (∀ γ ∈ w, γ ∈ Γ) ∧ w.prod = g := by
  have hne : {n | ∃ w : List G, w.length = n ∧ (∀ γ ∈ w, γ ∈ Γ) ∧ w.prod = g}.Nonempty := by
    have hg : g ∈ (Subgroup.closure (Γ : Set G)).toSubmonoid := by
      rw [hgen]; exact Subgroup.mem_top g
    rw [Subgroup.closure_toSubmonoid] at hg
    obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hg
    refine ⟨l.length, l, rfl, fun γ hγ => ?_, hprod⟩
    rcases hl γ hγ with h | h
    · exact h
    · have := hsymm γ⁻¹ (by simpa using h)
      simpa using this
  exact Nat.sInf_mem hne

lemma wordLength_pos {Γ : Finset G} (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) {g : G} (hg : g ≠ 1) : 0 < wordLength Γ g := by
  obtain ⟨w, hlen, -, hprod⟩ := exists_word hsymm hgen g
  rw [← hlen]
  rcases w with _ | ⟨a, w⟩
  · simp at hprod; exact absurd hprod.symm hg
  · simp

lemma prod_take_succ' (w : List G) (i : ℕ) :
    (w.take (i + 1)).prod = (w.take i).prod * w.getD i 1 := by
  by_cases hi : i < w.length
  · rw [List.prod_take_succ w i hi, List.getD_eq_getElem _ _ hi]
  · push Not at hi
    rw [List.take_of_length_le (by omega), List.take_of_length_le hi,
      List.getD_eq_default _ _ hi, mul_one]

lemma getD_mem {Γ : Finset G} {w : List G} (hw : ∀ γ ∈ w, γ ∈ Γ) {i : ℕ} (hi : i < w.length) :
    w.getD i 1 ∈ Γ := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hw _ (List.getElem_mem hi)

end Word

section Telescope

variable {act : S → G → Option S}

/-- The summand of the Følner sum for one generator: `x ↦ |μ(x · γ) − μ(x)|`. -/
noncomputable def folTerm (act : S → G → Option S) (μ : S →₀ ℝ) (γ : G) (x : S) : ℝ :=
  |pull act γ μ x - μ x|

lemma F_nonneg (act : S → G → Option S) (μ : S →₀ ℝ) (γ : G) (x : S) : 0 ≤ folTerm act μ γ x :=
  abs_nonneg _

lemma hasFiniteSupport_F (hact : IsPartialAction act) (μ : S →₀ ℝ) (γ : G) :
    HasFiniteSupport (folTerm act μ γ) := by
  refine Set.Finite.subset
    (Set.Finite.union (hasFiniteSupport_pull hact γ μ.hasFiniteSupport) μ.hasFiniteSupport) ?_
  intro x hx
  simp only [mem_support, folTerm, ne_eq, abs_eq_zero] at hx
  by_contra hc
  simp only [Set.mem_union, mem_support, ne_eq, not_or, not_not] at hc
  apply hx
  rw [hc.1, hc.2]; ring

/-- One step of the telescoping in Lemma 3.9: only the decrease is counted. -/
lemma step_sub (hact : IsPartialAction act) (μ : S →₀ ℝ) (hμ : ∀ s, 0 ≤ μ s) (a γ : G) (y : S) :
    pull act a μ y - pull act (a * γ) μ y ≤ pull act a (folTerm act μ γ) y := by
  cases h : act y a with
  | some x =>
    rw [pull_mul_of_act hact _ h, pull_of_some h, pull_of_some h]
    simp only [folTerm]
    rw [abs_sub_comm]
    exact le_abs_self _
  | none =>
    rw [pull_of_none h, pull_of_none h, zero_sub, neg_nonpos]
    exact pull_nonneg (fun x => hμ x) y

/-- The total Følner sum `∑_{γ ∈ Γ} ∑_s |μ(s · γ) − μ(s)|`. -/
noncomputable def total (act : S → G → Option S) (Γ : Finset G) (μ : S →₀ ℝ) : ℝ :=
  ∑ γ ∈ Γ, ∑ᶠ s, folTerm act μ γ s

lemma finsum_F_le_total {Γ : Finset G} (μ : S →₀ ℝ) {γ : G} (hγ : γ ∈ Γ) :
    ∑ᶠ s, folTerm act μ γ s ≤ total act Γ μ := by
  unfold total
  exact Finset.single_le_sum (f := fun γ => ∑ᶠ s, folTerm act μ γ s)
    (fun γ _ => finsum_nonneg (fun s => F_nonneg act μ γ s)) hγ

lemma sub_pull_le (hact : IsPartialAction act) (μ : S →₀ ℝ) (hμ : ∀ s, 0 ≤ μ s) (w : List G)
    (y : S) :
    μ y - pull act w.prod μ y ≤ ∑ i ∈ Finset.range w.length,
      pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y := by
  have htel := Finset.sum_range_sub (fun i => pull act (w.take i).prod μ y) w.length
  simp only [List.take_length, List.take_zero, List.prod_nil, pull_one hact] at htel
  have : μ y - pull act w.prod μ y =
      ∑ i ∈ Finset.range w.length,
        (pull act (w.take i).prod μ y - pull act (w.take (i + 1)).prod μ y) := by
    rw [← neg_sub, ← htel, ← Finset.sum_neg_distrib]
    simp
  rw [this]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [prod_take_succ']
  exact step_sub hact μ hμ _ _ y

/-- Lemma 3.9's bound before the Følner hypothesis: `∑_s max(μ(s) − μ(s · g), 0) ≤ d T`. -/
lemma finsum_max_sub_pull_le (hact : IsPartialAction act) {Γ : Finset G} (μ : S →₀ ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (w : List G) (hw : ∀ γ ∈ w, γ ∈ Γ) :
    ∑ᶠ y, max (μ y - pull act w.prod μ y) 0 ≤ w.length * total act Γ μ := by
  have hfin : ∀ i, HasFiniteSupport (fun y =>
      pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y) :=
    fun i => hasFiniteSupport_pull hact _ (hasFiniteSupport_F hact μ _)
  calc ∑ᶠ y, max (μ y - pull act w.prod μ y) 0
      ≤ ∑ᶠ y, ∑ i ∈ Finset.range w.length,
          pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y := by
        apply finsum_le_finsum'
        · refine Set.Finite.subset μ.hasFiniteSupport ?_
          intro y hy
          simp only [mem_support, ne_eq] at hy ⊢
          intro h0
          apply hy
          rw [h0, zero_sub]
          exact max_eq_right (neg_nonpos.2 (pull_nonneg (fun x => hμ x) y))
        · exact Set.Finite.subset (Set.finite_iUnion (fun i : Finset.range w.length => hfin i))
            (by
              intro y hy
              simp only [mem_support] at hy
              obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
              exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hne⟩)
        · intro y
          exact max_le (sub_pull_le hact μ hμ w y)
            (Finset.sum_nonneg fun i _ => pull_nonneg (F_nonneg act μ _) y)
    _ = ∑ i ∈ Finset.range w.length, ∑ᶠ y,
          pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y :=
        finsum_sum_comm _ _ (fun i _ => hfin i)
    _ ≤ ∑ i ∈ Finset.range w.length, total act Γ μ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hγ := getD_mem hw (Finset.mem_range.1 hi)
        exact (finsum_pull_le hact (w.take i).prod (hasFiniteSupport_F hact μ (w.getD i 1))
          (F_nonneg act μ _)).trans (finsum_F_le_total μ hγ)
    _ = w.length * total act Γ μ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Telescope


section MapDomain

variable {T : Type*}

end MapDomain


section Marginal

variable {act : S → G → Option S}

/-- If `x · gⁱ = x' · g^{i'}` with `i < i'` and `x, x' ∈ E`, and `x' · gˡ` is defined and in the
support of `μ` for every `l < i'`, then `g` does not marginalize `E` off the complement of the
support: `x' · g^{i' - i} = x ∈ E`. -/
lemma no_return (hact : IsPartialAction act) {μ : S →₀ ℝ} {g : G} {E : Set S}
    (hE : Marginalizes act g E (↑μ.support)ᶜ) {x x' z : S} (hx : x ∈ E) (hx' : x' ∈ E)
    {i i' : ℕ} (hii : i < i') (h1 : act x (g ^ i) = some z) (h2 : act x' (g ^ i') = some z)
    (hgood : ∀ l < i', ∃ y, act x' (g ^ l) = some y ∧ μ y ≠ 0) : False := by
  have h3 := act_inv_of hact h1
  have h4 := hact.mul _ _ x' z x h2 h3
  rw [← pow_sub g hii.le] at h4
  obtain ⟨l, hl, hbad⟩ := hE x' hx' (i' - i) (by omega) ⟨x, hx, h4⟩
  obtain ⟨y, hy, hμy⟩ := hgood l (by omega)
  rcases hbad with hbad | ⟨y', hy', hbad⟩
  · simp [actPow, hy] at hbad
  · simp only [actPow, hy, Option.some.injEq] at hbad
    subst hbad
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finsupp.mem_support_iff, not_not] at hy'
    exact hμy hy'

/-- Every chain `x, x · g, x · g², …` from a point of `E` eventually leaves the support. -/
lemma exists_exit (hact : IsPartialAction act) {μ : S →₀ ℝ} {g : G} {E : Set S}
    (hE : Marginalizes act g E (↑μ.support)ᶜ) {x : S} (hx : x ∈ E) :
    ∃ n, ¬ ∃ y, act x (g ^ n) = some y ∧ μ y ≠ 0 := by
  by_contra hall
  push Not at hall
  choose f hf using hall
  have hfin : ∀ n, f n ∈ μ.support := fun n => Finsupp.mem_support_iff.2 (hf n).2
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨f n, hfin n⟩ : μ.support))
  simp only [Subtype.mk.injEq] at heq
  rcases lt_or_gt_of_ne hij with h | h
  · exact no_return hact hE hx hx h (hf i).1 (heq ▸ (hf j).1) (fun l _ => ⟨f l, hf l⟩)
  · exact no_return hact hE hx hx h (hf j).1 (heq ▸ (hf i).1) (fun l _ => ⟨f l, hf l⟩)

/-- Exit times: `x · gⁱ` lies in the support for `i < n x`, and `x · g^{n x}` does not. -/
lemma exists_exitTime (hact : IsPartialAction act) {μ : S →₀ ℝ} {g : G} {E : Set S}
    (hE : Marginalizes act g E (↑μ.support)ᶜ) :
    ∃ n : S → ℕ, ∀ x ∈ E, (¬ ∃ y, act x (g ^ n x) = some y ∧ μ y ≠ 0) ∧
      ∀ l < n x, ∃ y, act x (g ^ l) = some y ∧ μ y ≠ 0 := by
  refine ⟨fun x => if hx : x ∈ E then Nat.find (exists_exit hact hE hx) else 0, ?_⟩
  intro x hx
  simp only [dif_pos hx]
  refine ⟨Nat.find_spec (exists_exit hact hE hx), fun l hl => ?_⟩
  have := Nat.find_min (exists_exit hact hE hx) hl
  push Not at this
  exact this

/-- The point `x · gⁱ` (or `x` when undefined). -/
noncomputable def chainPt (act : S → G → Option S) (g : G) (x : S) (i : ℕ) : S :=
  (act x (g ^ i)).getD x

/-- `max(μ(y) − μ(y · g), 0)`. -/
noncomputable def decr (act : S → G → Option S) (μ : S →₀ ℝ) (g : G) (y : S) : ℝ :=
  max (μ y - pull act g μ y) 0

/-- Lemma 3.9's chain estimate: `∑_{x ∈ E} μ(x) ≤ ∑_y max(μ(y) − μ(y · g), 0)`. -/
lemma mass_le_finsum_max (hact : IsPartialAction act) {μ : S →₀ ℝ} (hμ0 : ∀ s, 0 ≤ μ s)
    {g : G} {E : Set S} (hE : Marginalizes act g E (↑μ.support)ᶜ) :
    mass μ E ≤ ∑ᶠ y, decr act μ g y := by
  obtain ⟨n, hn⟩ := exists_exitTime hact hE
  have hφ0 : ∀ y, 0 ≤ decr act μ g y := fun y => le_max_right _ _
  have hgood : ∀ x ∈ E, ∀ i < n x,
      act x (g ^ i) = some (chainPt act g x i) ∧ μ (chainPt act g x i) ≠ 0 := by
    intro x hx i hi
    obtain ⟨y, hy, hμy⟩ := (hn x hx).2 i hi
    have : chainPt act g x i = y := by simp [chainPt, hy]
    rw [this]
    exact ⟨hy, hμy⟩
  -- (i) each point is bounded by the decreases along its chain
  have hchain : ∀ x ∈ E, μ x ≤ ∑ i ∈ Finset.range (n x), decr act μ g (chainPt act g x i) := by
    intro x hx
    have htel := Finset.sum_range_sub (fun i => pull act (g ^ i) μ x) (n x)
    simp only [pow_zero, pull_one hact] at htel
    have hend : pull act (g ^ n x) μ x = 0 := by
      cases h : act x (g ^ n x) with
      | none => exact pull_of_none h
      | some y =>
        rw [pull_of_some h]
        by_contra hy
        exact (hn x hx).1 ⟨y, h, hy⟩
    rw [hend, zero_sub] at htel
    have : μ x = ∑ i ∈ Finset.range (n x),
        (pull act (g ^ i) μ x - pull act (g ^ (i + 1)) μ x) := by
      rw [← neg_neg (μ x), ← htel, ← Finset.sum_neg_distrib]
      simp
    rw [this]
    refine Finset.sum_le_sum fun i hi => ?_
    have hgi := (hgood x hx i (Finset.mem_range.1 hi)).1
    rw [pow_succ, pull_mul_of_act hact _ hgi, pull_of_some hgi]
    exact le_max_left _ _
  -- (ii) the chains are disjoint and do not repeat
  have hinj : Set.InjOn (fun p : (_ : S) × ℕ => chainPt act g p.1 p.2)
      ↑((μ.support.filter (· ∈ E)).sigma fun x => Finset.range (n x)) := by
    rintro ⟨x, i⟩ hp ⟨x', i'⟩ hq heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hp hq
    simp only at heq
    have hx := hp.1.2
    have hx' := hq.1.2
    have h1 := (hgood x hx i hp.2).1
    have h2 := (hgood x' hx' i' hq.2).1
    rw [← heq] at h2
    rcases lt_trichotomy i i' with h | h | h
    · exact (no_return hact hE hx hx' h h1 h2
        (fun l hl => (hn x' hx').2 l (by omega))).elim
    · subst h
      have := act_inj hact h1 h2
      subst this
      rfl
    · exact (no_return hact hE hx' hx h h2 h1
        (fun l hl => (hn x hx).2 l (by omega))).elim
  have hsuppφ : support (decr act μ g) ⊆ ↑μ.support := by
    intro y hy
    simp only [mem_support, ne_eq] at hy
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
    intro h0
    apply hy
    simp only [decr, h0, zero_sub]
    exact max_eq_right (neg_nonpos.2 (pull_nonneg (fun x => hμ0 x) y))
  calc mass μ E = ∑ x ∈ μ.support.filter (· ∈ E), μ x := rfl
    _ ≤ ∑ x ∈ μ.support.filter (· ∈ E), ∑ i ∈ Finset.range (n x),
          decr act μ g (chainPt act g x i) :=
        Finset.sum_le_sum fun x hx => hchain x (Finset.mem_filter.1 hx).2
    _ = ∑ p ∈ (μ.support.filter (· ∈ E)).sigma (fun x => Finset.range (n x)),
          decr act μ g (chainPt act g p.1 p.2) :=
        by rw [Finset.sum_sigma]
    _ = ∑ y ∈ ((μ.support.filter (· ∈ E)).sigma (fun x => Finset.range (n x))).image
          (fun p => chainPt act g p.1 p.2), decr act μ g y :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ μ.support, decr act μ g y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro y hy
          simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_filter,
            Finset.mem_range] at hy
          obtain ⟨⟨x, i⟩, ⟨⟨-, hx⟩, hi⟩, rfl⟩ := hy
          exact Finsupp.mem_support_iff.2 (hgood x hx i hi).2
        · exact fun y _ _ => hφ0 y
    _ = ∑ᶠ y, decr act μ g y := (finsum_eq_sum_of_support_subset _ hsuppφ).symm

end Marginal

end MooreFoelner.Dev.Sec3A

namespace MooreFoelner

open Classical CannonFloydParry Function
open MooreFoelner.Dev.Sec3A

end MooreFoelner

namespace MooreFoelner

open Classical CannonFloydParry Function
open MooreFoelner.Dev.Sec3A

end MooreFoelner

namespace MooreFoelner

open Classical CannonFloydParry Function
open MooreFoelner.Dev.Sec3A

end MooreFoelner

namespace MooreFoelner

open Classical CannonFloydParry Function
open MooreFoelner.Dev.Sec3A

end MooreFoelner
end

open MooreFoelner in
open Classical Function MooreFoelner in
open Classical CannonFloydParry Function in
open MooreFoelner.Dev.Sec3A in
open Classical CannonFloydParry Function in
open MooreFoelner.Dev.Sec3A in
open Classical CannonFloydParry Function in
open MooreFoelner.Dev.Sec3A in
open Classical CannonFloydParry Function in
open MooreFoelner.Dev.Sec3A in
theorem solution {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε) (μ : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (E : Set S) (g : G) (hg : g ≠ 1)
    (hE : Marginalizes act g E (↑μ.support)ᶜ) :
    mass μ E < wordLength Γ g * ε * mass μ Set.univ := by
  obtain ⟨w, hlen, hw, hprod⟩ := exists_word hsymm hgen g
  have hd : (0 : ℝ) < wordLength Γ g := by exact_mod_cast wordLength_pos hsymm hgen hg
  have key := finsum_max_sub_pull_le hact μ hμ.1 w hw
  rw [hprod, hlen] at key
  have hT : total act Γ μ < ε * mass μ Set.univ := hμ.2
  calc mass μ E ≤ ∑ᶠ y, decr act μ g y := mass_le_finsum_max hact hμ.1 hE
    _ ≤ wordLength Γ g * total act Γ μ := key
    _ < wordLength Γ g * (ε * mass μ Set.univ) := mul_lt_mul_of_pos_left hT hd
    _ = wordLength Γ g * ε * mass μ Set.univ := by ring
