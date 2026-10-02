-- Prove2me | solution 1 for MooreFoelner.exists_const_mass_lt_of_isMarginal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T05:45:35.694898+00:00
-- url     : https://prove2.me/submissions/f347fdb0-06f7-4a2b-a645-ae70e5beeab2

import Theorems.Thm_MooreFoelner_isWeightedFolner_of_le
import Theorems.Thm_MooreFoelner_mass_lt_of_marginalizes
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
# Moore 2013, §3 (group Sec3B): Remark 3.8, Lemmas 3.10, 3.12, 3.14, 3.15
-/

namespace MooreFoelner.Dev.Sec3B

open Classical MooreFoelner

set_option linter.unusedSectionVars false

variable {G S : Type*} [Group G]

/-! ## Marginal sets -/

theorem marginalizes_mono {act : S → G → Option S} {g : G} {E E' I I' : Set S}
    (h : Marginalizes act g E I) (hE : E' ⊆ E) (hI : I ⊆ I') : Marginalizes act g E' I' := by
  intro x hx k hk ⟨y, hy, hxy⟩
  obtain ⟨i, hi, h'⟩ := h x (hE hx) k hk ⟨y, hE hy, hxy⟩
  refine ⟨i, hi, ?_⟩
  rcases h' with h' | ⟨z, hz, hxz⟩
  · exact Or.inl h'
  · exact Or.inr ⟨z, hI hz, hxz⟩

theorem marginalizes_one {act : S → G → Option S} (hact : IsPartialAction act) {E I : Set S}
    (h : Marginalizes act 1 E I) : E ⊆ I := by
  intro x hx
  have h1 : actPow act x 1 1 = some x := by simp [actPow, hact.one]
  obtain ⟨i, hi, h'⟩ := h x hx 1 one_pos ⟨x, hx, h1⟩
  have hi0 : i = 0 := by omega
  subst hi0
  have h0 : actPow act x 1 0 = some x := by simp [actPow, hact.one]
  rcases h' with h' | ⟨y, hy, hxy⟩
  · rw [h0] at h'; exact absurd h' (by simp)
  · rw [h0] at hxy; cases hxy; exact hy

/-! ## Mass, restriction and `valAt` -/

theorem mass_eq_sum (μ : S →₀ ℝ) (A : Set S) :
    mass μ A = ∑ s ∈ μ.support, if s ∈ A then μ s else 0 := by
  rw [mass, Finset.sum_filter]

theorem mass_empty (μ : S →₀ ℝ) : mass μ ∅ = 0 := by simp [mass]

theorem mass_nonneg {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A : Set S) : 0 ≤ mass μ A :=
  Finset.sum_nonneg fun s _ => hμ s

theorem mass_mono {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) {A B : Set S} (h : A ⊆ B) :
    mass μ A ≤ mass μ B := by
  rw [mass_eq_sum, mass_eq_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hA : s ∈ A
  · simp [hA, h hA]
  · by_cases hB : s ∈ B <;> simp [hA, hB, hμ s]

theorem mass_iUnion_le {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) {l : ℕ} (F : Fin l → Set S) :
    mass μ (⋃ i, F i) ≤ ∑ i, mass μ (F i) := by
  simp_rw [mass_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ => ?_
  have hnn : ∀ j, 0 ≤ (if s ∈ F j then μ s else 0) := fun j => by
    split_ifs <;> simp [hμ s]
  split_ifs with h
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    calc μ s = if s ∈ F i then μ s else 0 := by rw [if_pos hi]
      _ ≤ ∑ j, if s ∈ F j then μ s else 0 :=
        Finset.single_le_sum (f := fun j => if s ∈ F j then μ s else 0)
          (fun j _ => hnn j) (Finset.mem_univ i)
  · exact Finset.sum_nonneg fun j _ => hnn j

theorem mass_union_le {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A B : Set S) :
    mass μ (A ∪ B) ≤ mass μ A + mass μ B := by
  simp_rw [mass_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hA : s ∈ A <;> by_cases hB : s ∈ B <;> simp [hA, hB, hμ s]

theorem mass_add_compl (μ : S →₀ ℝ) (A : Set S) :
    mass μ A + mass μ Aᶜ = mass μ Set.univ := by
  simp_rw [mass_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hA : s ∈ A <;> simp [hA]

theorem restrict_apply (μ : S →₀ ℝ) (A : Set S) (s : S) :
    restrict μ A s = if s ∈ A then μ s else 0 := by
  simp [restrict, Finsupp.filter_apply]

theorem support_restrict (μ : S →₀ ℝ) (A : Set S) :
    (restrict μ A).support = μ.support.filter (· ∈ A) := by
  simp [restrict, Finsupp.support_filter]

theorem mem_of_mem_support_restrict {μ : S →₀ ℝ} {A : Set S} {s : S}
    (h : s ∈ (restrict μ A).support) : s ∈ A := by
  rw [Finsupp.mem_support_iff, restrict_apply] at h
  by_contra hs
  exact h (if_neg hs)

theorem restrict_nonneg {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A : Set S) (s : S) :
    0 ≤ restrict μ A s := by
  rw [restrict_apply]; split_ifs <;> simp [hμ s]

theorem restrict_le {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A : Set S) (s : S) :
    restrict μ A s ≤ μ s := by
  rw [restrict_apply]; split_ifs <;> simp [hμ s]

theorem mass_restrict (μ : S →₀ ℝ) (A B : Set S) :
    mass (restrict μ A) B = mass μ (B ∩ A) := by
  rw [mass_eq_sum, mass_eq_sum, support_restrict, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [restrict_apply]
  by_cases hA : s ∈ A <;> by_cases hB : s ∈ B <;> simp [hA, hB]

/-! ## Weighted Følner sets -/

theorem wf_pos {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ}
    (h : IsWeightedFolner act Γ μ ε) : 0 < ε * mass μ Set.univ :=
  lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => finsum_nonneg fun _ => abs_nonneg _) h.2

theorem wf_mono {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε ε' : ℝ}
    (h : IsWeightedFolner act Γ μ ε) (hε : ε ≤ ε') : IsWeightedFolner act Γ μ ε' :=
  ⟨h.1, lt_of_lt_of_le h.2 (mul_le_mul_of_nonneg_right hε (mass_nonneg h.1 _))⟩

/-! ## Lemma 3.10 -/

theorem mass_inter_compl_le {act : S → G → Option S} (hact : IsPartialAction act)
    (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤)
    {ε : ℝ} (hε : 0 < ε) {μ : S →₀ ℝ} (hμ : IsWeightedFolner act Γ μ ε) {E I : Set S} {g : G}
    (hg : Marginalizes act g E I) {C : ℝ} (hC1 : 1 ≤ C) (hCε : C * ε ≤ 1 / 2)
    (hI : mass μ I ≤ C * ε * mass μ Set.univ) :
    mass μ (E ∩ Iᶜ) ≤ 2 * wordLength Γ g * (1 + 2 * Γ.card * C) * ε * mass μ Set.univ := by
  have hM := mass_nonneg hμ.1 Set.univ
  have hC0 : 0 ≤ C := by linarith
  have hRHS : 0 ≤ 2 * (wordLength Γ g : ℝ) * (1 + 2 * Γ.card * C) * ε * mass μ Set.univ := by
    positivity
  by_cases hg1 : g = 1
  · subst hg1
    have hEI := marginalizes_one hact hg
    have : E ∩ Iᶜ = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_and, not_not]
      exact fun hx => hEI hx
    rw [this, mass_empty]; exact hRHS
  set ν := restrict μ Iᶜ with hνdef
  set ε' := 2 * (1 + 2 * Γ.card * C) * ε with hε'def
  have hε' : 0 < ε' := by positivity
  have hνM : mass ν Set.univ = mass μ Set.univ - mass μ I := by
    rw [hνdef, mass_restrict, Set.univ_inter, ← mass_add_compl μ I]; ring
  have hν : IsWeightedFolner act Γ ν ε' := by
    -- Lemma 3.11 (#13) with `δ = Cε`
    have hδ : 0 < C * ε := by positivity
    have hmass : mass ν Set.univ ≥ (1 - C * ε) * mass μ Set.univ := by
      rw [hνM]; linarith
    have h13 := isWeightedFolner_of_le act hact Γ hsymm hgen ε (C * ε) μ ν hμ
      (restrict_nonneg hμ.1 _) (restrict_le hμ.1 _) hδ (by linarith) hmass
    refine wf_mono h13 ?_
    rw [div_le_iff₀ (by linarith), hε'def]
    have hcard : (0 : ℝ) ≤ Γ.card := Nat.cast_nonneg _
    have h1 : 0 ≤ (1 + 2 * Γ.card * C) * ε * (1 / 2 - C * ε) := by
      apply mul_nonneg _ (by linarith); positivity
    nlinarith
  have hmarg : Marginalizes act g E (↑ν.support)ᶜ := by
    refine marginalizes_mono hg le_rfl ?_
    intro x hx hxν
    exact mem_of_mem_support_restrict hxν hx
  have key := mass_lt_of_marginalizes act hact Γ hsymm hgen ε' hε' ν hν E g hg1 hmarg
  rw [hνdef, mass_restrict] at key
  have hνle : mass ν Set.univ ≤ mass μ Set.univ := by
    rw [hνM]; linarith [mass_nonneg hμ.1 I]
  calc mass μ (E ∩ Iᶜ) ≤ wordLength Γ g * ε' * mass ν Set.univ := key.le
    _ ≤ wordLength Γ g * ε' * mass μ Set.univ := by
        apply mul_le_mul_of_nonneg_left hνle; positivity
    _ = _ := by rw [hε'def]; ring

theorem kMarginal_mass_le {act : S → G → Option S} (hact : IsPartialAction act)
    (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤)
    {k : ℕ} {E : Set S} (h : IsKMarginal act k E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ μ : S →₀ ℝ, IsWeightedFolner act Γ μ ε →
      mass μ E ≤ C * ε * mass μ Set.univ := by
  induction h with
  | zero =>
    refine ⟨1, le_rfl, fun ε hε μ hμ => ?_⟩
    rw [mass_empty, one_mul]; exact (wf_pos hμ).le
  | succ E I g hI hg ih =>
    rename_i k l
    choose C hC1 hC using ih
    have hC0 : ∀ i, 0 ≤ C i := fun i => by linarith [hC1 i]
    set D : Fin l → ℝ := fun i => 3 * C i + 2 * wordLength Γ (g i) * (1 + 2 * Γ.card * C i)
      with hDdef
    have hD0 : ∀ i, 0 ≤ D i := fun i => by have := hC0 i; positivity
    have hDs : 0 ≤ ∑ i, D i := Finset.sum_nonneg fun i _ => hD0 i
    refine ⟨1 + ∑ i, D i, by linarith, ?_⟩
    intro ε hε μ hμ
    have hM := mass_nonneg hμ.1 Set.univ
    have hεM : 0 ≤ ε * mass μ Set.univ := by positivity
    by_cases hbig : ∃ i, 1 / 2 < C i * ε
    · obtain ⟨i, hi⟩ := hbig
      have h1 : mass μ (⋃ i, E i) ≤ mass μ Set.univ := mass_mono hμ.1 (Set.subset_univ _)
      have h2 : 2 * C i ≤ ∑ j, D j := by
        calc 2 * C i ≤ D i := by
              have := hC0 i
              have : (0 : ℝ) ≤ 2 * wordLength Γ (g i) * (1 + 2 * Γ.card * C i) := by positivity
              simp only [hDdef]; linarith
          _ ≤ _ := Finset.single_le_sum (fun j _ => hD0 j) (Finset.mem_univ i)
      have h3 : mass μ Set.univ ≤ 2 * C i * ε * mass μ Set.univ := by nlinarith
      have h4 := mul_le_mul_of_nonneg_right h2 hεM
      calc mass μ (⋃ i, E i) ≤ mass μ Set.univ := h1
        _ ≤ 2 * C i * ε * mass μ Set.univ := h3
        _ ≤ (1 + ∑ j, D j) * ε * mass μ Set.univ := by linarith
    · push Not at hbig
      calc mass μ (⋃ i, E i) ≤ ∑ i, mass μ (E i) := mass_iUnion_le hμ.1 E
        _ ≤ ∑ i, D i * ε * mass μ Set.univ := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hsplit : E i ⊆ I i ∪ (E i ∩ (I i)ᶜ) := by
              intro x hx
              by_cases h : x ∈ I i
              · exact Or.inl h
              · exact Or.inr ⟨hx, h⟩
            have h1 := mass_mono hμ.1 hsplit
            have h2 := mass_union_le hμ.1 (I i) (E i ∩ (I i)ᶜ)
            have h3 := hC i ε hε μ hμ
            have h4 := mass_inter_compl_le hact Γ hsymm hgen hε hμ (hg i) (hC1 i) (hbig i) h3
            have h5 : 0 ≤ C i * ε * mass μ Set.univ := by have := hC0 i; positivity
            simp only [hDdef]
            linarith
        _ = (∑ i, D i) * ε * mass μ Set.univ := by rw [Finset.sum_mul, Finset.sum_mul]
        _ ≤ (1 + ∑ i, D i) * ε * mass μ Set.univ := by linarith

/-! ## Γ-connected sets and components -/

section comp

variable {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ}

end comp

/-! ## The right action of `G` on itself -/

end MooreFoelner.Dev.Sec3B

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Sec3B in
theorem solution {G S : Type*} [Group G]
    (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (E : Set S) (hE : IsMarginal act E) :
    ∃ C : ℝ, ∀ (ε : ℝ), 0 < ε → ∀ μ : S →₀ ℝ, IsWeightedFolner act Γ μ ε →
      mass μ E < C * ε * mass μ Set.univ := by
  obtain ⟨k, hk⟩ := hE
  obtain ⟨C, _, hC⟩ := kMarginal_mass_le hact Γ hsymm hgen hk
  refine ⟨C + 1, fun ε hε μ hμ => ?_⟩
  have h1 := hC ε hε μ hμ
  have h2 := wf_pos hμ
  linarith
