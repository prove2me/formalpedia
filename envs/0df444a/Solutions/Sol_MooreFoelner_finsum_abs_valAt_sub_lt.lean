-- Prove2me | solution 1 for MooreFoelner.finsum_abs_valAt_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T04:58:13.192703+00:00
-- url     : https://prove2.me/submissions/a425bc96-2cf7-455c-8f3e-4216a31b1581

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

lemma valAt_eq_pull (act : S → G → Option S) (μ : S →₀ ℝ) (s : S) (g : G) :
    valAt act μ s g = pull act g μ s := rfl

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

/-- If `y · a` is undefined but `y · (a b) = z`, then `z · b⁻¹` is undefined. -/
lemma act_inv_none_of_none (hact : IsPartialAction act) {y z : S} {a b : G}
    (ha : act y a = none) (hab : act y (a * b) = some z) : act z b⁻¹ = none := by
  cases h : act z b⁻¹ with
  | none => rfl
  | some w =>
    have := hact.mul (a * b) b⁻¹ y z w hab h
    rw [mul_inv_cancel_right] at this
    rw [this] at ha
    cases ha

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

/-- One step of the telescoping in Lemma 3.5 (p. 6), including the case where `s · gᵢ₊₁` is
defined but `s · gᵢ` is not. -/
lemma step_abs (hact : IsPartialAction act) (μ : S →₀ ℝ) (a γ : G) (y : S) :
    |pull act (a * γ) μ y - pull act a μ y| ≤
      pull act a (folTerm act μ γ) y + pull act (a * γ) (folTerm act μ γ⁻¹) y := by
  have h0 : 0 ≤ pull act (a * γ) (folTerm act μ γ⁻¹) y := pull_nonneg (F_nonneg act μ γ⁻¹) y
  cases h : act y a with
  | some x =>
    rw [pull_mul_of_act hact _ h, pull_of_some h, pull_of_some h]
    simp only [folTerm]
    linarith
  | none =>
    rw [pull_of_none h, pull_of_none h, zero_add, sub_zero]
    cases h2 : act y (a * γ) with
    | none => rw [pull_of_none h2, pull_of_none h2]; simp
    | some z =>
      rw [pull_of_some h2, pull_of_some h2]
      simp only [folTerm, pull_of_none (act_inv_none_of_none hact h h2), zero_sub, abs_neg]
      exact le_refl _

/-- The total Følner sum `∑_{γ ∈ Γ} ∑_s |μ(s · γ) − μ(s)|`. -/
noncomputable def total (act : S → G → Option S) (Γ : Finset G) (μ : S →₀ ℝ) : ℝ :=
  ∑ γ ∈ Γ, ∑ᶠ s, folTerm act μ γ s

lemma finsum_F_le_total {Γ : Finset G} (μ : S →₀ ℝ) {γ : G} (hγ : γ ∈ Γ) :
    ∑ᶠ s, folTerm act μ γ s ≤ total act Γ μ := by
  unfold total
  exact Finset.single_le_sum (f := fun γ => ∑ᶠ s, folTerm act μ γ s)
    (fun γ _ => finsum_nonneg (fun s => F_nonneg act μ γ s)) hγ

/-- Telescoping along a word, pointwise: `|μ(y · w) − μ(y)| ≤ ∑ᵢ (…)`. -/
lemma abs_pull_sub_le (hact : IsPartialAction act) (μ : S →₀ ℝ) (w : List G) (y : S) :
    |pull act w.prod μ y - μ y| ≤ ∑ i ∈ Finset.range w.length,
      (pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y +
        pull act (w.take (i + 1)).prod (folTerm act μ (w.getD i 1)⁻¹) y) := by
  have htel := Finset.sum_range_sub (fun i => pull act (w.take i).prod μ y) w.length
  simp only [List.take_length, List.take_zero, List.prod_nil, pull_one hact] at htel
  rw [← htel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [prod_take_succ']
  exact step_abs hact μ _ _ y

lemma hasFiniteSupport_abs_pull_sub (hact : IsPartialAction act) (μ : S →₀ ℝ) (a : G) :
    HasFiniteSupport (fun y => |pull act a μ y - μ y|) :=
  hasFiniteSupport_F hact μ a

/-- Lemma 3.5's bound before the Følner hypothesis: `∑_s |μ(s · g) − μ(s)| ≤ 2 d T`. -/
lemma finsum_abs_pull_sub_le (hact : IsPartialAction act) {Γ : Finset G}
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (μ : S →₀ ℝ) (w : List G) (hw : ∀ γ ∈ w, γ ∈ Γ) :
    ∑ᶠ y, |pull act w.prod μ y - μ y| ≤ 2 * w.length * total act Γ μ := by
  have hfin : ∀ i, HasFiniteSupport (fun y =>
      pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y +
        pull act (w.take (i + 1)).prod (folTerm act μ (w.getD i 1)⁻¹) y) := by
    intro i
    exact Set.Finite.subset (Set.Finite.union
      (hasFiniteSupport_pull hact _ (hasFiniteSupport_F hact μ _))
      (hasFiniteSupport_pull hact _ (hasFiniteSupport_F hact μ _))) (support_add _ _)
  calc ∑ᶠ y, |pull act w.prod μ y - μ y|
      ≤ ∑ᶠ y, ∑ i ∈ Finset.range w.length,
          (pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y +
            pull act (w.take (i + 1)).prod (folTerm act μ (w.getD i 1)⁻¹) y) := by
        apply finsum_le_finsum' (hasFiniteSupport_abs_pull_sub hact μ _)
        · exact Set.Finite.subset (Set.finite_iUnion (fun i : Finset.range w.length => hfin i))
            (by
              intro y hy
              simp only [mem_support] at hy
              obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
              exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hne⟩)
        · exact fun y => abs_pull_sub_le hact μ w y
    _ = ∑ i ∈ Finset.range w.length, ∑ᶠ y,
          (pull act (w.take i).prod (folTerm act μ (w.getD i 1)) y +
            pull act (w.take (i + 1)).prod (folTerm act μ (w.getD i 1)⁻¹) y) :=
        finsum_sum_comm _ _ (fun i _ => hfin i)
    _ ≤ ∑ i ∈ Finset.range w.length, (2 * total act Γ μ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < w.length := Finset.mem_range.1 hi
        have hγ := getD_mem hw hi'
        rw [finsum_add_distrib (hasFiniteSupport_pull hact _ (hasFiniteSupport_F hact μ _))
          (hasFiniteSupport_pull hact _ (hasFiniteSupport_F hact μ _))]
        have h1 := (finsum_pull_le hact (w.take i).prod (hasFiniteSupport_F hact μ (w.getD i 1))
          (F_nonneg act μ _)).trans (finsum_F_le_total μ hγ)
        have h2 := (finsum_pull_le hact (w.take (i + 1)).prod
          (hasFiniteSupport_F hact μ (w.getD i 1)⁻¹) (F_nonneg act μ _)).trans
            (finsum_F_le_total μ (hsymm _ hγ))
        linarith
    _ = 2 * w.length * total act Γ μ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Telescope


section MapDomain

variable {T : Type*}

end MapDomain


section Marginal

variable {act : S → G → Option S}

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
theorem solution {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε) (μ : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (g : G) (hg : g ≠ 1) :
    ∑ᶠ s, |valAt act μ s g - μ s| < 2 * ε * wordLength Γ g * mass μ Set.univ := by
  obtain ⟨w, hlen, hw, hprod⟩ := exists_word hsymm hgen g
  have hd : (0 : ℝ) < wordLength Γ g := by exact_mod_cast wordLength_pos hsymm hgen hg
  have key := finsum_abs_pull_sub_le hact hsymm μ w hw
  rw [hprod, hlen] at key
  have hT : total act Γ μ < ε * mass μ Set.univ := hμ.2
  simp only [valAt_eq_pull]
  calc ∑ᶠ s, |pull act g μ s - μ s| ≤ 2 * wordLength Γ g * total act Γ μ := key
    _ < 2 * wordLength Γ g * (ε * mass μ Set.univ) := by
        apply mul_lt_mul_of_pos_left hT; positivity
    _ = 2 * ε * wordLength Γ g * mass μ Set.univ := by ring
