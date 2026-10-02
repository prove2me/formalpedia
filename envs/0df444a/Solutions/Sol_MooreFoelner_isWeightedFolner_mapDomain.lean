-- Prove2me | solution 1 for MooreFoelner.isWeightedFolner_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T04:41:04.604152+00:00
-- url     : https://prove2.me/submissions/0cf28750-a4db-484b-8e1b-2f477b28f0c5

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

end PartialAction

section Word

end Word

section Telescope

variable {act : S → G → Option S}

end Telescope


section MapDomain

variable {T : Type*}

lemma mapDomain_apply_eq_finsum (μ : S →₀ ℝ) (h : S → T) (t : T) :
    μ.mapDomain h t = ∑ᶠ s, if h s = t then μ s else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [finsum_eq_sum_of_support_subset _ (s := μ.support)]
  · simp [Finsupp.sum, Finsupp.single_apply]
  · intro s hs
    simp only [mem_support, ne_eq, ite_eq_right_iff, not_forall] at hs
    obtain ⟨-, hs⟩ := hs
    simpa using hs

lemma mass_mapDomain (μ : S →₀ ℝ) (h : S → T) :
    mass (μ.mapDomain h) Set.univ = mass μ Set.univ := by
  have := Finsupp.sum_mapDomain_index (f := h) (s := μ) (h := fun _ v => v)
    (fun _ => rfl) (fun _ _ _ => rfl)
  simpa [mass, Finsupp.sum] using this

/-- The key identity in the proof of Lemma 3.4: `ν(t · γ) = ∑_{h(s) = t} μ(s · γ)`. -/
lemma valAt_mapDomain {actS : S → G → Option S} {actT : T → G → Option T}
    (hS : IsPartialAction actS) (hT : IsPartialAction actT) (μ : S →₀ ℝ) (hμ0 : ∀ s, 0 ≤ μ s)
    (h : S → T) (γ : G)
    (hh : ∀ s, 0 < μ s + valAt actS μ s γ⁻¹ →
      ∃ y, actS s γ⁻¹ = some y ∧ actT (h s) γ⁻¹ = some (h y)) (t : T) :
    valAt actT (μ.mapDomain h) t γ = ∑ᶠ s, if h s = t then valAt actS μ s γ else 0 := by
  have hR : ∑ᶠ s, (if h s = t then valAt actS μ s γ else 0) =
      ∑ᶠ u, μ u * pull actS γ⁻¹ (fun s => if h s = t then 1 else 0) u := by
    rw [← finsum_mul_pull hS γ μ (fun s => if h s = t then 1 else 0)]
    congr 1
    ext s
    split_ifs <;> simp [valAt_eq_pull]
  have hL : valAt actT (μ.mapDomain h) t γ = ∑ᶠ u, if actT t γ = some (h u) then μ u else 0 := by
    cases ht : actT t γ with
    | none => simp [valAt, ht]
    | some t' =>
      simp only [valAt, ht, Option.some.injEq]
      rw [mapDomain_apply_eq_finsum]
      congr 1
      ext u
      simp [eq_comm]
  rw [hL, hR]
  congr 1
  ext u
  by_cases hu : μ u = 0
  · simp [hu]
  · have hpos : 0 < μ u + valAt actS μ u γ⁻¹ := by
      have := pull_nonneg (act := actS) (a := γ⁻¹) hμ0 u
      have := lt_of_le_of_ne (hμ0 u) (Ne.symm hu)
      rw [valAt_eq_pull]
      linarith
    obtain ⟨y, hy1, hy2⟩ := hh u hpos
    rw [pull_of_some hy1]
    have hiff : h y = t ↔ actT t γ = some (h u) := by
      constructor
      · rintro rfl
        exact act_of_inv hT hy2
      · intro h'
        have := act_inv_of hT h'
        rw [hy2] at this
        exact Option.some.inj this
    by_cases hc : h y = t
    · simp [hc, hiff.1 hc]
    · simp [hc, mt hiff.2 hc]

/-- Lemma 3.4 for one generator: pushing forward does not increase the Følner sum. -/
lemma finsum_abs_mapDomain_le {actS : S → G → Option S} {actT : T → G → Option T}
    (hS : IsPartialAction actS) (hT : IsPartialAction actT) (μ : S →₀ ℝ) (hμ0 : ∀ s, 0 ≤ μ s)
    (h : S → T) (γ : G)
    (hh : ∀ s, 0 < μ s + valAt actS μ s γ⁻¹ →
      ∃ y, actS s γ⁻¹ = some y ∧ actT (h s) γ⁻¹ = some (h y)) :
    ∑ᶠ t, |valAt actT (μ.mapDomain h) t γ - μ.mapDomain h t| ≤
      ∑ᶠ s, |valAt actS μ s γ - μ s| := by
  set Fs : S → ℝ := fun s => valAt actS μ s γ - μ s with hFs_def
  have hFs : (support Fs).Finite :=
    Set.Finite.subset (Set.Finite.union (hasFiniteSupport_pull hS γ μ.hasFiniteSupport)
      μ.hasFiniteSupport) (support_sub _ _)
  set P := hFs.toFinset with hP
  have hD : ∀ t, valAt actT (μ.mapDomain h) t γ - μ.mapDomain h t =
      ∑ s ∈ P, if h s = t then Fs s else 0 := by
    intro t
    rw [valAt_mapDomain hS hT μ hμ0 h γ hh t, mapDomain_apply_eq_finsum]
    have h1 : HasFiniteSupport (fun s => if h s = t then valAt actS μ s γ else 0) := by
      refine Set.Finite.subset (hasFiniteSupport_pull hS γ μ.hasFiniteSupport) ?_
      intro s hs
      simp only [mem_support, ne_eq, ite_eq_right_iff, not_forall] at hs
      exact hs.2
    have h2 : HasFiniteSupport (fun s => if h s = t then μ s else 0) := by
      refine Set.Finite.subset μ.hasFiniteSupport ?_
      intro s hs
      simp only [mem_support, ne_eq, ite_eq_right_iff, not_forall] at hs
      exact hs.2
    rw [← finsum_sub_distrib h1 h2]
    rw [finsum_eq_sum_of_support_subset _ (s := P)]
    · refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> simp [Fs]
    · intro s hs
      rw [hP, Set.Finite.coe_toFinset]
      simp only [mem_support, ne_eq] at hs ⊢
      split_ifs at hs <;> simp_all [Fs]
  have hDle : ∀ t, |valAt actT (μ.mapDomain h) t γ - μ.mapDomain h t| ≤
      ∑ s ∈ P, if h s = t then |Fs s| else 0 := by
    intro t
    rw [hD t]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
    split_ifs <;> simp
  have hsupp : support (fun t => |valAt actT (μ.mapDomain h) t γ - μ.mapDomain h t|) ⊆
      ↑(P.image h) := by
    intro t ht
    simp only [mem_support, ne_eq] at ht
    by_contra hc
    apply ht
    rw [hD t, abs_eq_zero]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg]
    rintro rfl
    exact hc (Finset.mem_coe.2 (Finset.mem_image_of_mem h hs))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hsuppS : support (fun s => |valAt actS μ s γ - μ s|) ⊆ ↑P := by
    intro s hs
    rw [hP, Set.Finite.coe_toFinset]
    simpa [Fs] using hs
  rw [finsum_eq_sum_of_support_subset _ hsuppS]
  calc ∑ t ∈ P.image h, |valAt actT (μ.mapDomain h) t γ - μ.mapDomain h t|
      ≤ ∑ t ∈ P.image h, ∑ s ∈ P, if h s = t then |Fs s| else 0 :=
        Finset.sum_le_sum fun t _ => hDle t
    _ = ∑ s ∈ P, ∑ t ∈ P.image h, if h s = t then |Fs s| else 0 := Finset.sum_comm
    _ = ∑ s ∈ P, |Fs s| := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem h hs)]

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
open Classical CannonFloydParry Function in
open MooreFoelner.Dev.Sec3A in
theorem solution {G S T : Type*} [Group G] (actS : S → G → Option S)
    (actT : T → G → Option T) (hS : IsPartialAction actS) (hT : IsPartialAction actT)
    (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤)
    (μ : S →₀ ℝ) (ε : ℝ) (hμ : IsWeightedFolner actS Γ μ ε) (h : S → T)
    (hh : ∀ γ ∈ Γ, ∀ s, 0 < μ s + valAt actS μ s γ →
      ∃ y, actS s γ = some y ∧ actT (h s) γ = some (h y)) :
    IsWeightedFolner actT Γ (μ.mapDomain h) ε := by
  have hμ0 := hμ.1
  refine ⟨fun t => ?_, ?_⟩
  · rw [mapDomain_apply_eq_finsum]
    exact finsum_nonneg fun s => by split_ifs <;> simp [hμ0 s]
  · rw [mass_mapDomain]
    refine lt_of_le_of_lt (Finset.sum_le_sum fun γ hγ => ?_) hμ.2
    exact finsum_abs_mapDomain_le hS hT μ hμ0 h γ (hh γ⁻¹ (hsymm γ hγ))
