-- Prove2me | solution 1 for MooreFoelner.isWeightedFolner_of_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T06:04:36.856921+00:00
-- url     : https://prove2.me/submissions/15d0261a-08c2-4b13-ac4d-36adf7b94e52

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

lemma pull_le_pull {act : S → G → Option S} {a : G} {f g : S → ℝ} (hfg : ∀ x, f x ≤ g x) (s : S) :
    pull act a f s ≤ pull act a g s := by
  cases h : act s a with
  | none => rw [pull_of_none h, pull_of_none h]
  | some x => rw [pull_of_some h, pull_of_some h]; exact hfg x

lemma pull_sub {act : S → G → Option S} {a : G} (f g : S → ℝ) (s : S) :
    pull act a (fun x => f x - g x) s = pull act a f s - pull act a g s := by
  cases h : act s a with
  | none => rw [pull_of_none h, pull_of_none h, pull_of_none h]; ring
  | some x => rw [pull_of_some h, pull_of_some h, pull_of_some h]

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

/-- The total Følner sum `∑_{γ ∈ Γ} ∑_s |μ(s · γ) − μ(s)|`. -/
noncomputable def total (act : S → G → Option S) (Γ : Finset G) (μ : S →₀ ℝ) : ℝ :=
  ∑ γ ∈ Γ, ∑ᶠ s, folTerm act μ γ s

lemma total_eq (act : S → G → Option S) (Γ : Finset G) (μ : S →₀ ℝ) :
    ∑ γ ∈ Γ, ∑ᶠ s, |valAt act μ s γ - μ s| = total act Γ μ := rfl

lemma total_nonneg (Γ : Finset G) (μ : S →₀ ℝ) : 0 ≤ total act Γ μ :=
  Finset.sum_nonneg fun γ _ => finsum_nonneg (fun s => F_nonneg act μ γ s)

end Telescope


lemma mass_univ_eq (μ : S →₀ ℝ) : mass μ Set.univ = ∑ᶠ s, μ s := by
  unfold mass
  rw [finsum_eq_sum_of_support_subset (μ : S → ℝ) (s := μ.support)
    (by rw [Finsupp.fun_support_eq])]
  simp

/-- The pointwise inequality in the proof of Lemma 3.11. -/
lemma abs_sub_le_of_le {a b A B : ℝ} (haA : a ≤ A) (hbB : b ≤ B) :
    |a - b| ≤ |A - B| + (B - b) + (A - a) := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self (A - B), neg_abs_le (A - B)]


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
open Classical CannonFloydParry Function in
open MooreFoelner.Dev.Sec3A in
theorem solution {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε δ : ℝ) (μ ν : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (hν : ∀ s, 0 ≤ ν s) (hle : ∀ s, ν s ≤ μ s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hmass : mass ν Set.univ ≥ (1 - δ) * mass μ Set.univ) :
    IsWeightedFolner act Γ ν ((ε + 2 * Γ.card * δ) / (1 - δ)) := by
  refine ⟨hν, ?_⟩
  rw [total_eq]
  have hμ0 := hμ.1
  have hTμ : total act Γ μ < ε * mass μ Set.univ := hμ.2
  have hM := mass_univ_eq μ
  have hN := mass_univ_eq ν
  set M := mass μ Set.univ
  set N := mass ν Set.univ
  have hM0 : 0 ≤ M := by rw [hM]; exact finsum_nonneg hμ0
  have hNM : N ≤ M := by
    rw [hM, hN]; exact finsum_le_finsum' ν.hasFiniteSupport μ.hasFiniteSupport hle
  have hεpos : 0 < ε := by
    have h0 := total_nonneg (act := act) Γ μ
    by_contra hc
    push Not at hc
    nlinarith
  have hD : HasFiniteSupport (fun s => μ s - ν s) :=
    Set.Finite.subset (Set.Finite.union μ.hasFiniteSupport ν.hasFiniteSupport) (support_sub _ _)
  have hsumD : ∑ᶠ s, (μ s - ν s) = M - N := by
    rw [finsum_sub_distrib μ.hasFiniteSupport ν.hasFiniteSupport, hM, hN]
  have hstep : ∀ γ ∈ Γ, ∑ᶠ s, folTerm act ν γ s ≤ ∑ᶠ s, folTerm act μ γ s + 2 * (M - N) := by
    intro γ _
    have hpD := finsum_pull_le hact γ hD (fun s => sub_nonneg.2 (hle s))
    have hP : HasFiniteSupport (pull act γ (fun x => μ x - ν x)) := hasFiniteSupport_pull hact γ hD
    have hFμ := hasFiniteSupport_F hact μ γ
    have hsum : HasFiniteSupport (fun s => folTerm act μ γ s + (μ s - ν s)) :=
      Set.Finite.subset (Set.Finite.union hFμ hD) (support_add _ _)
    calc ∑ᶠ s, folTerm act ν γ s
        ≤ ∑ᶠ s, (folTerm act μ γ s + (μ s - ν s) + pull act γ (fun x => μ x - ν x) s) := by
          apply finsum_le_finsum' (hasFiniteSupport_F hact ν γ)
          · exact Set.Finite.subset (Set.Finite.union hsum hP) (support_add _ _)
          · intro s
            simp only [folTerm, pull_sub]
            exact abs_sub_le_of_le (pull_le_pull hle s) (hle s)
      _ = ∑ᶠ s, folTerm act μ γ s + ∑ᶠ s, (μ s - ν s) + ∑ᶠ s, pull act γ (fun x => μ x - ν x) s := by
          rw [finsum_add_distrib hsum hP, finsum_add_distrib hFμ hD]
      _ ≤ ∑ᶠ s, folTerm act μ γ s + 2 * (M - N) := by linarith
  have htot : total act Γ ν ≤ total act Γ μ + Γ.card * (2 * (M - N)) := by
    unfold total
    calc ∑ γ ∈ Γ, ∑ᶠ s, folTerm act ν γ s ≤ ∑ γ ∈ Γ, (∑ᶠ s, folTerm act μ γ s + 2 * (M - N)) :=
          Finset.sum_le_sum hstep
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) ≤ Γ.card := Nat.cast_nonneg _
  have hMN : M - N ≤ δ * M := by linarith
  have h1 : total act Γ ν < (ε + 2 * Γ.card * δ) * M := by nlinarith
  have h2 : (ε + 2 * Γ.card * δ) * M ≤ (ε + 2 * Γ.card * δ) / (1 - δ) * N := by
    have hpos : 0 < 1 - δ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    have : 0 ≤ ε + 2 * Γ.card * δ := by positivity
    nlinarith
  exact lt_of_lt_of_le h1 h2
