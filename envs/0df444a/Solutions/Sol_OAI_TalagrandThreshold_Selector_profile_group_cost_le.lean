-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.profile_group_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:02:36.46263+00:00
-- url     : https://prove2.me/submissions/d563180b-3401-4f93-a11f-35dd18fe63ea

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGroupCost.lean:L26-L91
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.profile_group_cost_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Theorems.Thm_OAI_TalagrandThreshold_Selector_card_le_profile_encoding
import Theorems.Thm_OAI_TalagrandThreshold_colorMass_profile_likelihood
import Theorems.Thm_OAI_TalagrandThreshold_selector_entropy_bound

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityColors ----
namespace OAI

/-!
# The actual independent color law

Colors are indexed from zero; their numerical levels are one larger. The
first `s` colors have masses `256^(i+1) * p`, and the final color carries the
remaining mass. All laws below use these literal weights.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α]

theorem colorMass_pos (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) : 0 < colorMass p s a := by
  exact Finset.prod_pos fun x _ => colorProb_pos p s hp hs (a x)

theorem colorMass_nonneg (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a : Coloring α s) : 0 ≤ colorMass p s a :=
  (colorMass_pos p s hp hs a).le

variable [DecidableEq α]

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorProfile ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Exact counts in a selector profile

The full profile records each strict downward move by its final and original
colors. These counting identities hold even without a global `Earlier`
hypothesis: every point counted by a crossing already moves downward.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- The last color cannot be the final color of a strict downward move. -/
theorem changes_filter_last (a z : Coloring α s) :
    (changes a z).filter (fun x => z x = Fin.last s) = ∅ := by
  ext x
  simp only [Finset.mem_filter, changes, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_and]
  intro hmove hlast
  have hlt : (z x).val < (a x).val := hmove
  have hz : (z x).val = s := congrArg Fin.val hlast
  have ha := (a x).isLt
  omega

omit [DecidableEq α] in
/-- The nonterminal final-color fibers are exactly the moved rows. -/
theorem changes_filter_castSucc (a z : Coloring α s) (i : Fin s) :
    (changes a z).filter (fun x => z x = i.castSucc) = movedRow a z i := by
  ext x
  simp only [Finset.mem_filter, changes, movedRow, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hmove, hz⟩
    exact ⟨congrArg Fin.val hz, hmove⟩
  · rintro ⟨hz, hmove⟩
    exact ⟨hmove, Fin.ext hz⟩

omit [DecidableEq α] in
/-- Every changed point has exactly one nonterminal final color. -/
theorem profileSize_profile (a z : Coloring α s) :
    profileSize (profile a z) = (changes a z).card := by
  have hpartition :
      (∑ h : Color s, ((changes a z).filter fun x => z x = h).card) =
        (changes a z).card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (changes a z) Finset.univ z
  rw [Fin.sum_univ_castSucc, changes_filter_last, Finset.card_empty,
    add_zero] at hpartition
  simp_rw [changes_filter_castSucc] at hpartition
  simpa only [profileSize, rowCount_profile] using hpartition

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ColorArithmetic ----
namespace OAI

/-!
# Exact normalization of the profile coefficient

At level `i+1`, the color probability is `256^(i+1)*p`. Its likelihood
factor cancels the density and turns the counting factor `3*4^(i+1)`
into the geometric coefficient `3/64^(i+1)`.
-/

namespace TalagrandThreshold

theorem profile_coefficient_eq {p : ℝ} (hp : 0 < p) (s : ℕ) (i : Fin s) :
    ((3 : ℝ) * (4 : ℝ) ^ (i.val + 1)) * (p / colorProb p s i.castSucc) =
      3 / (64 : ℝ) ^ (i.val + 1) := by
  rw [colorProb_castSucc]
  have hpne : p ≠ 0 := ne_of_gt hp
  have hpow : (256 : ℝ) ^ (i.val + 1) =
      (4 : ℝ) ^ (i.val + 1) * (64 : ℝ) ^ (i.val + 1) := by
    rw [← mul_pow]
    norm_num
  calc
    _ = 3 * ((4 : ℝ) ^ (i.val + 1) / (256 : ℝ) ^ (i.val + 1)) := by
      field_simp [hpne]
    _ = 3 / (64 : ℝ) ^ (i.val + 1) := by
      rw [hpow]
      field_simp

theorem profile_coefficient_pow_eq {p : ℝ} (hp : 0 < p)
    (s : ℕ) (i : Fin s) (t : ℕ) :
    ((3 : ℝ) * (4 : ℝ) ^ (i.val + 1)) ^ t *
        (p / colorProb p s i.castSucc) ^ t =
      (3 / (64 : ℝ) ^ (i.val + 1)) ^ t := by
  rw [← mul_pow, profile_coefficient_eq hp s i]

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorGroupCost ----
namespace OAI

/-!
# The actual contribution of one full selector profile

The common heavy sets are obtained separately for each occurring profile.
The entropy estimate removes their sizes before profiles are summed, so no
uniform choice of heavy sets across distinct profiles is required.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite group with a fixed final coloring and full profile has the
claimed weighted contribution whenever its rows fit the actual heavy sets. -/
theorem profile_group_cost_le (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2)
    (G : Finset (Coloring α s)) (z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α)
    (hEarlier : ∀ a ∈ G, Earlier a z)
    (hprofile : ∀ a ∈ G, profile a z = n)
    (hrows : ∀ a ∈ G, ∀ i, movedRow a z i ⊆ R i)
    (hR : ∀ i, (R i).card ≤ 2 ^ (i.val + 1) * profileSize n) :
    (∑ a ∈ G, colorMass p s a * p ^ (changes a z).card) ≤
      colorMass p s z *
        (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
        (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
          ∏ h : Color s, colorProb p s h ^ (n i h))) := by
  classical
  let C : ℝ := ∏ i : Fin s, ((R i).card.choose (rowCount n i) : ℝ)
  let W : ℝ := ∏ i : Fin s, (wordCount (rowCount n i) (n i) : ℝ)
  let L : ℝ := ∏ i : Fin s, (p / colorProb p s i.castSucc) ^ (rowCount n i)
  let Q : ℝ := ∏ i : Fin s, ∏ h : Color s, colorProb p s h ^ (n i h)
  let E : ℝ := ∏ i : Fin s, (3 * 4 ^ (i.val + 1) : ℝ) ^ (rowCount n i)
  let K : ℝ := ∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)
  have hW : 0 ≤ W := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  have hL : 0 ≤ L := Finset.prod_nonneg fun i _ =>
    pow_nonneg (div_nonneg hp.le (colorProb_nonneg p s hp hs _)) _
  have hQ : 0 ≤ Q := Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun h _ => pow_nonneg (colorProb_nonneg p s hp hs h) _
  have hP : 0 ≤ colorMass p s z := colorMass_nonneg p s hp hs z
  have hcard : (G.card : ℝ) ≤ C * W := by
    have h := card_le_profile_encoding G z n R hEarlier hprofile hrows
    have hcast : (G.card : ℝ) ≤
        ∏ i : Fin s, ((R i).card.choose (rowCount n i) : ℝ) *
          (wordCount (rowCount n i) (n i) : ℝ) := by
      exact_mod_cast h
    simpa only [Finset.prod_mul_distrib] using hcast
  have hentropy : C ≤ E :=
    selector_entropy_bound s (fun i => (R i).card) (rowCount n) hR
  have hnormalize : E * L = K := by
    dsimp [E, L, K]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact profile_coefficient_pow_eq hp s i (rowCount n i)
  have hterm (a : Coloring α s) (ha : a ∈ G) :
      colorMass p s a * p ^ (changes a z).card = colorMass p s z * L * Q := by
    have h := colorMass_profile_likelihood p s hp hs a z (hEarlier a ha)
    rw [hprofile a ha] at h
    have hsize : (changes a z).card = profileSize n := by
      rw [← profileSize_profile, hprofile a ha]
    rw [hsize, mul_comm]
    simpa only [Finset.prod_mul_distrib, mul_assoc] using h
  calc
    (∑ a ∈ G, colorMass p s a * p ^ (changes a z).card) =
        (G.card : ℝ) * (colorMass p s z * L * Q) := by
      simp only [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * W) * (colorMass p s z * L * Q) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg hP hL) hQ)
    _ = C * (W * (colorMass p s z * L * Q)) := by ring
    _ ≤ E * (W * (colorMass p s z * L * Q)) :=
      mul_le_mul_of_nonneg_right hentropy
        (mul_nonneg hW (mul_nonneg (mul_nonneg hP hL) hQ))
    _ = colorMass p s z * (E * L) * (W * Q) := by ring
    _ = colorMass p s z * K * (W * Q) := by rw [hnormalize]
    _ = _ := by
      dsimp [K, W, Q]
      rw [← Finset.prod_mul_distrib]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.profile_group_cost_le := @_root_.OAI.TalagrandThreshold.Selector.profile_group_cost_le
