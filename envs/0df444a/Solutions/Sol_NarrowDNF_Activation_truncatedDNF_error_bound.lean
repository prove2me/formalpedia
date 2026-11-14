-- Prove2me | solution 1 for NarrowDNF.Activation.truncatedDNF_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:52.171549+00:00
-- url     : https://prove2.me/submissions/8e708fac-02f0-429e-8043-e2288aa8af93

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CertificateBounds
import Definitions.Def_NarrowDNF_Certificates
import Theorems.Thm_NarrowDNF_Activation_positive_certificate
import Theorems.Thm_NarrowDNF_Weighted_integer_markov

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

section


namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









namespace Activation





omit [DecidableEq ι] in
@[simp] private theorem mem_activeFinset (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.activeFinset x ↔ i ∈ J.active x := by
  classical
  simp [activeFinset]

omit [DecidableEq ι] in
@[simp] private theorem mem_certificate (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.certificate x ↔ i ∈ J.active x ∧ x i = true := by
  classical
  simp [certificate]

omit [DecidableEq ι] in
private theorem certificate_card_le (J : Activation ι) (x : Cube ι) :
    (J.certificate x).card ≤ (J.activeFinset x).card := Finset.card_filter_le _ _

omit [DecidableEq ι] in
private theorem certificate_holds (J : Activation ι) (x : Cube ι) :
    TermHolds (J.certificate x) x := by
  intro i hi
  exact ((mem_certificate J x i).mp hi).2

omit [DecidableEq ι] in
private theorem certificate_forces {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    {x : Cube ι} (hx : u x = true) {y : Cube ι}
    (hy : TermHolds (J.certificate x) y) : u y = true := by
  apply positive_certificate hJ hu hm hx
  intro i hi hxi
  exact hy i ((mem_certificate J x i).mpr ⟨hi, hxi⟩)





private theorem truncatedTerms_sound {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    {y : Cube ι} (hy : DNFHolds (J.truncatedTerms u w) y) : u y = true := by
  classical
  obtain ⟨T, hT, hyT⟩ := hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
  exact certificate_forces hJ hu hm (Finset.mem_filter.mp hx).2.1 hyT

private theorem truncatedTerms_complete {J : Activation ι} {u : Cube ι → Bool}
    {w : ℕ} {x : Cube ι} (hx : u x = true)
    (hw : (J.certificate x).card ≤ w) : DNFHolds (J.truncatedTerms u w) x := by
  classical
  refine ⟨J.certificate x, Finset.mem_image.mpr ⟨x, ?_, rfl⟩, certificate_holds J x⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hw⟩

/-- Deterministic part of the truncation estimate: all lost accepted points
have certificate size larger than the cutoff. -/
private theorem truncatedTerms_missed_large {J : Activation ι} {u : Cube ι → Bool}
    {w : ℕ} {x : Cube ι} (hx : u x = true)
    (hmiss : ¬ DNFHolds (J.truncatedTerms u w) x) : w < (J.certificate x).card := by
  exact Nat.lt_of_not_ge fun hw => hmiss (truncatedTerms_complete hx hw)

end Activation
end NarrowDNF


end

section


namespace NarrowDNF
namespace Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem truncatedDNF_eq_true (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) (x : Cube ι) :
    J.truncatedDNF u w x = true ↔ DNFHolds (J.truncatedTerms u w) x := by
  classical simp [truncatedDNF]



private theorem truncatedDNF_le {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ) :
    J.truncatedDNF u w ≤ u := by
  intro x
  cases hx : J.truncatedDNF u w x
  · exact Bool.false_le _
  · rw [truncatedTerms_sound hJ hu hm w ((truncatedDNF_eq_true J u w x).mp hx)]

private theorem truncatedDNF_disagreement_large {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    {x : Cube ι} (hx : u x ≠ J.truncatedDNF u w x) :
    w < (J.certificate x).card := by
  have hle := truncatedDNF_le hJ hu hm w x
  cases hux : u x <;> cases hg : J.truncatedDNF u w x
  · exact False.elim (hx (hux.trans hg.symm))
  · rw [hux, hg] at hle
    exact False.elim ((by decide : ¬(true ≤ false)) hle)
  · apply truncatedTerms_missed_large hux
    intro h
    have := (truncatedDNF_eq_true J u w x).mpr h
    simp [hg] at this
  · exact False.elim (hx (hux.trans hg.symm))



end Activation
end NarrowDNF


end

open NarrowDNF
open NarrowDNF
open NarrowDNF.Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The full two-stage inequality of Lemma 4.1, valid under every nonnegative
finite weighting (and therefore every Bernoulli product probability). -/
theorem solution {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    (weights : Cube ι → ℝ) (hw : ∀ x, 0 ≤ weights x) :
    (∑ x, weights x * (if u x ≠ J.truncatedDNF u w x then 1 else 0)) ≤
      (∑ x, weights x * (if w < (J.certificate x).card then 1 else 0)) ∧
    (∑ x, weights x * (if w < (J.certificate x).card then 1 else 0)) ≤
      (∑ x, weights x * ((J.activeFinset x).card : ℝ)) / (w + 1 : ℝ) := by
  classical
  constructor
  · apply Finset.sum_le_sum
    intro x _
    by_cases h : u x ≠ J.truncatedDNF u w x
    · simp [h, truncatedDNF_disagreement_large hJ hu hm w h]
    · simp only [if_neg h, mul_zero]
      split <;> simp_all
  · apply (Weighted.integer_markov weights hw (fun x => (J.certificate x).card) w).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hw x)
    exact_mod_cast certificate_card_le J x
