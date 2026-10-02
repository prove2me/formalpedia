-- Prove2me | solution 1 for MooreFoelner.exists_const_isWeightedFolner_restrict_compl
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T06:15:54.597189+00:00
-- url     : https://prove2.me/submissions/474030a5-8990-4e15-b441-7d4cd8e4f770

import Theorems.Thm_MooreFoelner_isWeightedFolner_of_le
import Theorems.Thm_MooreFoelner_exists_const_mass_lt_of_isMarginal
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

/-! ## Mass, restriction and `valAt` -/

theorem mass_eq_sum (μ : S →₀ ℝ) (A : Set S) :
    mass μ A = ∑ s ∈ μ.support, if s ∈ A then μ s else 0 := by
  rw [mass, Finset.sum_filter]

theorem mass_univ (μ : S →₀ ℝ) : mass μ Set.univ = ∑ s ∈ μ.support, μ s := by
  simp [mass]

theorem mass_nonneg {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A : Set S) : 0 ≤ mass μ A :=
  Finset.sum_nonneg fun s _ => hμ s

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

theorem wf_mass_pos {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ}
    (h : IsWeightedFolner act Γ μ ε) : 0 < mass μ Set.univ := by
  have h1 := wf_pos h
  have h2 := mass_nonneg h.1 Set.univ
  rcases h2.lt_or_eq with h2 | h2
  · exact h2
  · rw [← h2, mul_zero] at h1; exact absurd h1 (lt_irrefl _)

theorem wf_eps_pos {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ}
    (h : IsWeightedFolner act Γ μ ε) : 0 < ε := by
  have h1 := wf_pos h
  have h2 := wf_mass_pos h
  by_contra hε
  push Not at hε
  nlinarith

theorem wf_mono {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε ε' : ℝ}
    (h : IsWeightedFolner act Γ μ ε) (hε : ε ≤ ε') : IsWeightedFolner act Γ μ ε' :=
  ⟨h.1, lt_of_lt_of_le h.2 (mul_le_mul_of_nonneg_right hε (mass_nonneg h.1 _))⟩

/-! ## Lemma 3.10 -/

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
    (act : S → G → Option S) (hact : IsPartialAction act) (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (E : Set S)
    (hE : IsMarginal act E) (hne : (Eᶜ).Nonempty) :
    ∃ C : ℝ, ∀ (ε : ℝ) (μ : S →₀ ℝ), IsWeightedFolner act Γ μ ε → C * ε ≤ 1 →
      IsWeightedFolner act Γ (restrict μ Eᶜ) (C * ε) ∧ (restrict μ Eᶜ).support.Nonempty := by
  obtain ⟨C0, hC0⟩ := exists_const_mass_lt_of_isMarginal act hact Γ hsymm hgen E hE
  set C1 := max C0 1 with hC1def
  have hC1 : 1 ≤ C1 := le_max_right _ _
  have hcard : (0 : ℝ) ≤ Γ.card := Nat.cast_nonneg _
  refine ⟨2 + 4 * Γ.card * C1 + 2 * C1, fun ε μ hμ hCε => ?_⟩
  have hε := wf_eps_pos hμ
  have hM := wf_mass_pos hμ
  set M := mass μ Set.univ with hMdef
  have hEM : mass μ E < C1 * ε * M := by
    have h1 := hC0 ε hε μ hμ
    have h2 : C0 * ε * M ≤ C1 * ε * M := by
      apply mul_le_mul_of_nonneg_right _ hM.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
    linarith
  set δ := C1 * ε with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    have : 0 ≤ 4 * (Γ.card : ℝ) * C1 * ε := by positivity
    nlinarith
  set ν := restrict μ Eᶜ with hνdef
  have hνM : mass ν Set.univ = M - mass μ E := by
    rw [hνdef, mass_restrict, Set.univ_inter, hMdef, ← mass_add_compl μ E]; ring
  have hmass : mass ν Set.univ ≥ (1 - δ) * M := by
    rw [hνM]; nlinarith
  have h13 := isWeightedFolner_of_le act hact Γ hsymm hgen ε δ μ ν hμ (restrict_nonneg hμ.1 _)
    (restrict_le hμ.1 _) hδ0 (by linarith) hmass
  refine ⟨wf_mono h13 ?_, ?_⟩
  · rw [div_le_iff₀ (by linarith)]
    have h1 : 0 ≤ (2 + 4 * (Γ.card : ℝ) * C1 + 2 * C1) * ε := by positivity
    have h2 : 0 ≤ (Γ.card : ℝ) * δ := by positivity
    have h3 : (2 + 4 * (Γ.card : ℝ) * C1 + 2 * C1) * ε * δ ≤
        (2 + 4 * (Γ.card : ℝ) * C1 + 2 * C1) * ε * (1 / 2) :=
      mul_le_mul_of_nonneg_left hδ2 h1
    have h4 : 0 ≤ C1 * ε := by positivity
    rw [hδdef] at h2 h3 ⊢
    nlinarith
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h0 : mass ν Set.univ = 0 := by rw [mass_univ, h, Finset.sum_empty]
    have : 0 < (1 - δ) * M := by
      apply mul_pos _ hM; linarith
    linarith
