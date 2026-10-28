-- Prove2me | solution 1 for OAI.SharpLogRamsey.PreparedRow.geometric_row_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:39:38.837625+00:00
-- url     : https://prove2.me/submissions/8b5b0256-66b2-4013-8f4c-fe8d94067a7a

import Mathlib
import Definitions.Def_OAIQ045S002

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_PoissonLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_positiveEvent (C : Finset ι) : MeasurableSet (positiveEvent C) :=
  MeasurableSet.pi C.finite_toSet.countable (fun _ _ => (measurableSet_singleton 0).compl)
omit [DecidableEq ι] in

lemma integrable_certificateIndicator (rate : ι → ℝ≥0) (C : Finset ι) :
    Integrable (certificateIndicator C) (poissonLaw rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_positiveEvent C)

omit [Fintype ι] [DecidableEq ι] in
lemma indicator_nonneg (C : Finset ι) (ω : ι → ℕ) :
    0 ≤ certificateIndicator C ω := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
omit [DecidableEq ι] in

lemma integral_certificateIndicator (rate : ι → ℝ≥0) (C : Finset ι) :
    (∫ ω, certificateIndicator C ω ∂poissonLaw rate) =
      ∏ i ∈ C, (1 - Real.exp (-(rate i : ℝ))) := by
  unfold certificateIndicator
  rw [integral_indicator_const _ (measurableSet_positiveEvent C)]
  simp only [smul_eq_mul, mul_one]
  rw [Measure.real, poissonLaw, positiveEvent, Measure.pi_pi_finset,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Measure.real, measureReal_compl (measurableSet_singleton 0),
    probReal_univ, Measure.real, poissonMeasure_singleton]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
omit [DecidableEq ι] in

lemma integral_certificateIndicator_le (rate : ι → ℝ≥0) (C : Finset ι) :
    (∫ ω, certificateIndicator C ω ∂poissonLaw rate) ≤ weight rate C := by
  rw [integral_certificateIndicator]
  apply Finset.prod_le_prod
  · intro i _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate i).coe_nonneg)
    linarith
  · intro i _
    have he := Real.add_one_le_exp (-(rate i : ℝ))
    linarith

omit [Fintype ι] [DecidableEq ι] in
lemma weight_nonneg (rate : ι → ℝ≥0) (C : Finset ι) : 0 ≤ weight rate C := by
  exact Finset.prod_nonneg (fun i _ => (rate i).coe_nonneg)

omit [DecidableEq ι] in

theorem static_union_bound {κ : Type*} (D : Finset κ) (requirements : κ → Finset ι)
    (rate : ι → ℝ≥0) (E : Set (ι → ℕ)) (hE : MeasurableSet E)
    (hcover : ∀ ω ∈ E, ∃ c ∈ D, ω ∈ positiveEvent (requirements c)) :
    (poissonLaw rate).real E ≤ ∑ c ∈ D, weight rate (requirements c) := by
  have hp (ω : ι → ℕ) : E.indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ c ∈ D, certificateIndicator (requirements c) ω := by
    by_cases hω : ω ∈ E
    · obtain ⟨c, hc, he⟩ := hcover ω hω
      have := Finset.single_le_sum (f := fun c => certificateIndicator (requirements c) ω)
        (fun c _ => indicator_nonneg _ _) hc
      simpa [certificateIndicator, he, hω] using this
    · simp only [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg (fun c _ => indicator_nonneg _ _)
  calc
    _ = ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂poissonLaw rate := by
      rw [integral_indicator_const _ hE]
      simp
    _ ≤ ∫ ω, ∑ c ∈ D, certificateIndicator (requirements c) ω ∂poissonLaw rate :=
      integral_mono ((integrable_const (1 : ℝ)).indicator hE)
        (integrable_finsetSum _ (fun c _ => integrable_certificateIndicator _ _)) hp
    _ = ∑ c ∈ D, ∫ ω, certificateIndicator (requirements c) ω ∂poissonLaw rate :=
      integral_finsetSum _ (fun c _ => integrable_certificateIndicator _ _)
    _ ≤ _ := Finset.sum_le_sum (fun c _ => integral_certificateIndicator_le _ _)

section PairWitnesses

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
lemma witnessRequirements_card (T : Finset κ) (S : Finset ι) (f : T → S) :
    (witnessRequirements T S f).card = T.card := by
  rw [witnessRequirements, Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro a b h
    exact Subtype.ext (congrArg Prod.fst h)

omit [Fintype ι] [Fintype κ] in
lemma witness_weight (rate : ι → ℝ≥0) (T : Finset κ) (S : Finset ι) (f : T → S) :
    weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f) =
      ∏ r : T, (rate (f r) : ℝ) := by
  unfold weight witnessRequirements
  rw [Finset.prod_image]
  · rw [Finset.univ_eq_attach T]
  · intro a _ b _ h
    exact Subtype.ext (congrArg Prod.fst h)
omit [Fintype ι] [Fintype κ] in

lemma sum_witness_weight (rate : ι → ℝ≥0) (T : Finset κ) (S : Finset ι) :
    (∑ f : T → S, weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f)) =
      (∑ i ∈ S, (rate i : ℝ)) ^ T.card := by
  simp_rw [witness_weight]
  rw [← Fintype.prod_sum (fun (_r : T) (i : S) => (rate i : ℝ))]
  rw [Finset.sum_coe_sort S (fun i => (rate i : ℝ))]
  simp

omit [Fintype ι] in

theorem pair_certificate_weight (rate : ι → ℝ≥0) (S : Finset ι) (K : ℕ) :
    (∑ T ∈ (Finset.univ : Finset κ).powersetCard K,
      ∑ f : T → S, weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f)) =
      (Fintype.card κ).choose K * (∑ i ∈ S, (rate i : ℝ)) ^ K := by
  simp_rw [sum_witness_weight]
  calc
    _ = ∑ _T ∈ (Finset.univ : Finset κ).powersetCard K,
        (∑ i ∈ S, (rate i : ℝ)) ^ K := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [(Finset.mem_powersetCard.mp hT).2]
    _ = _ := by simp

omit [Fintype ι] in

theorem pair_certificate_weight_le (rate : ι → ℝ≥0) (S : Finset ι) (K : ℕ) :
    (∑ T ∈ (Finset.univ : Finset κ).powersetCard K,
      ∑ f : T → S, weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f)) ≤
        ((Fintype.card κ : ℝ) * ∑ i ∈ S, (rate i : ℝ)) ^ K := by
  rw [pair_certificate_weight, mul_pow]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast Nat.choose_le_pow (Fintype.card κ) K
  · positivity

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma direction_mem_dictionary {C : Finset (κ × ι)} {r : κ} {i : ι}
    (h : (r, i) ∈ C) : i ∈ dictionary C := Finset.mem_image_of_mem _ h
omit [Fintype ι] [Fintype κ] in

lemma witnessRequirements_disjoint {C : Finset (κ × ι)} (T : Finset κ) (S : Finset ι)
    (f : T → S) (hnew : Disjoint S (dictionary C)) :
    Disjoint C (witnessRequirements T S f) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hp'
  have he := congrArg Prod.snd hr
  have hf : p.2 ∈ S := he ▸ (f r).property
  exact Finset.disjoint_left.mp hnew hf (direction_mem_dictionary hp)

omit [Fintype ι] [Fintype κ] in
lemma weight_union_fresh (rate : κ × ι → ℝ≥0) (C D : Finset (κ × ι))
    (hfresh : Disjoint C D) : weight rate (C ∪ D) = weight rate C * weight rate D := by
  exact Finset.prod_union hfresh

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma dictionary_card_le (C : Finset (κ × ι)) : (dictionary C).card ≤ C.card :=
  Finset.card_image_le

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma AnchorChoice.cost_nonneg (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} (x : AnchorChoice C S) : 0 ≤ x.cost rate := by
  cases x <;> simp [AnchorChoice.cost]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in

lemma AnchorChoice.fresh {C : Finset (κ × ι)} {S : Finset ι}
    (x : AnchorChoice C S) : Disjoint C x.requirements := by
  cases x with
  | inl d => exact Finset.disjoint_empty_right _
  | inr rd =>
    apply Finset.disjoint_singleton_right.mpr
    intro he
    exact (Finset.mem_sdiff.mp rd.2.property).2 (direction_mem_dictionary he)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma AnchorChoice.weight (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} (x : AnchorChoice C S) :
    weight (fun p : κ × ι => rate p.2) x.requirements = x.cost rate := by
  cases x <;> simp [AnchorChoice.requirements, StaticCertificates.weight, AnchorChoice.cost]

omit [Fintype ι] [DecidableEq κ] in
lemma sum_anchor_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι)) (S : Finset ι) :
    (∑ x : AnchorChoice C S, x.cost rate) =
      (S ∩ dictionary C).card + Fintype.card κ * ∑ i ∈ S \ dictionary C, (rate i : ℝ) := by
  rw [Fintype.sum_sum_type]
  simp only [AnchorChoice.cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one, Fintype.sum_prod_type]
  rw [Finset.sum_coe_sort (S \ dictionary C) (fun i => (rate i : ℝ))]

omit [Fintype ι] [DecidableEq κ] in

theorem sum_anchor_cost_le (rate : ι → ℝ≥0) (C : Finset (κ × ι)) (S : Finset ι) :
    (∑ x : AnchorChoice C S, x.cost rate) ≤
      C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ) := by
  rw [sum_anchor_cost]
  apply add_le_add
  · exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right (s₁ := S))).trans
      (dictionary_card_le C)
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (by intro i _ _; exact (rate i).coe_nonneg)

section AnchorGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
omit [Fintype ι] [DecidableEq κ] in

theorem one_anchor_geometric_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S : Finset ι) (lineSet : H → Finset ι) (N₁ : ℕ)
    (hN : ∀ d, (Finset.univ.filter (fun H => d ∈ lineSet H)).card ≤ N₁) :
    (∑ x : AnchorChoice C S, x.cost rate *
      (Finset.univ.filter (fun H => x.direction ∈ lineSet H)).card) ≤
      (N₁ : ℝ) * (C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ)) := by
  calc
    _ ≤ ∑ x : AnchorChoice C S, x.cost rate * N₁ := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (x.cost_nonneg rate)
      exact_mod_cast hN x.direction
    _ = (N₁ : ℝ) * ∑ x : AnchorChoice C S, x.cost rate := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_anchor_cost_le rate C S) (Nat.cast_nonneg _)

end AnchorGeometry
end PairWitnesses
end SharpRamseyFive.StaticCertificates
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TwoAnchorCrossCost
attribute [-instance] _root_.OAI.SharpRamseyFive.CertificateCover.completePrograms_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section PairWitnesses
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
section AnchorGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]
omit [Fintype ι] [DecidableEq κ] [DecidableEq H] in
theorem two_anchor_cross_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S T : Finset ι) (lineSet : H → Finset ι) (N₂ : ℕ)
    (hN : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun H => d ∈ lineSet H ∧ e ∈ lineSet H)).card ≤ N₂) :
    (∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
      if x.direction ≠ y.direction then x.cost rate * y.cost rate *
        (Finset.univ.filter (fun H => x.direction ∈ lineSet H ∧ y.direction ∈ lineSet H)).card
      else 0) ≤
      (N₂ : ℝ) * (C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ)) *
        (C.card + Fintype.card κ * ∑ i ∈ T, (rate i : ℝ)) := by
  classical
  calc
    _ ≤ ∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
        x.cost rate * y.cost rate * N₂ := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      split_ifs with hxy
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (x.cost_nonneg rate) (y.cost_nonneg rate))
        exact_mod_cast hN x.direction y.direction hxy
      · exact mul_nonneg (mul_nonneg (x.cost_nonneg rate) (y.cost_nonneg rate)) (Nat.cast_nonneg _)
    _ = (N₂ : ℝ) * (∑ x : AnchorChoice C S, x.cost rate) *
        (∑ y : AnchorChoice C T, y.cost rate) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (sum_anchor_cost_le rate C S) (Nat.cast_nonneg _)
      · exact sum_anchor_cost_le rate C T
      · exact Finset.sum_nonneg (fun x _ => x.cost_nonneg rate)
      · positivity

omit [Fintype ι] [DecidableEq κ] [DecidableEq H] in

lemma one_anchor_subtype_sum (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S : Finset ι) (lineSet : H → Finset ι) :
    (∑ x : AnchorChoice C S, ∑ _h : {h : H // x.direction ∈ lineSet h}, x.cost rate) =
      ∑ x : AnchorChoice C S, x.cost rate *
        (Finset.univ.filter (fun h => x.direction ∈ lineSet h)).card := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
    Fintype.card_subtype]

omit [Fintype ι] [DecidableEq κ] [DecidableEq H] in
lemma two_anchor_subtype_sum (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S T : Finset ι) (lineSet : H → Finset ι) :
    (∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
      ∑ _h : {h : H // x.direction ≠ y.direction ∧
        x.direction ∈ lineSet h ∧ y.direction ∈ lineSet h}, x.cost rate * y.cost rate) =
      ∑ x : AnchorChoice C S, ∑ y : AnchorChoice C T,
        if x.direction ≠ y.direction then x.cost rate * y.cost rate *
          (Finset.univ.filter (fun h => x.direction ∈ lineSet h ∧ y.direction ∈ lineSet h)).card
        else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x.direction ≠ y.direction <;>
    simp [hxy, Fintype.card_subtype, mul_comm]

end AnchorGeometry

end PairWitnesses

end SharpRamseyFive.StaticCertificates

open scoped BigOperators
namespace SharpRamseyFive.CertificateEnumeration

universe u v
variable {S : Type u} {A : Type v}

section Dependent
variable (C : S → Type v) (step : (s : S) → C s → S)

lemma dWeight_nonneg (cost : (s : S) → C s → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) {n : ℕ} (s : S) (w : DWord C step n s) :
    0 ≤ dWeight C step cost s w := by
  induction n generalizing s with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hc s w.1) (ih _ w.2)

theorem sum_dWeight_le [∀ s, Fintype (C s)] (cost : (s : S) → C s → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ s, (∑ a, cost s a) ≤ M) (n : ℕ) (s : S) :
    (∑ w : DWord C step n s, dWeight C step cost s w) ≤ M ^ n := by
  induction n generalizing s with
  | zero =>
    let : Unique (DWord C step 0 s) := inferInstanceAs (Unique PUnit)
    simp [dWeight]
  | succ n ih =>
    change (∑ w : (a : C s) × DWord C step n (step s a), cost s w.1 *
      dWeight C step cost (step s w.1) w.2) ≤ M ^ (n + 1)
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ a, cost s a * ∑ w : DWord C step n (step s a),
          dWeight C step cost (step s a) w := by simp only [Finset.mul_sum]
      _ ≤ ∑ a, cost s a * M ^ n := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (ih (step s a)) (hc s a)
      _ = (∑ a, cost s a) * M ^ n := by rw [Finset.sum_mul]
      _ ≤ M * M ^ n := mul_le_mul_of_nonneg_right (hrow s) (pow_nonneg hM n)
      _ = _ := (pow_succ' M n).symm

lemma dReweighted (cost : (s : S) → C s → ℝ)
    (c : (s : S) → C s → ℤ) (b : ℝ) (hb : b ≠ 0)
    {n : ℕ} (s : S) (w : DWord C step n s) :
    dWeight C step (fun s a => cost s a * b ^ c s a) s w =
      dWeight C step cost s w * b ^ dCharge C step c s w := by
  induction n generalizing s with
  | zero => simp [dWeight, dCharge]
  | succ n ih =>
    simp only [dWeight, dCharge, ih, zpow_add₀ hb]
    ring

theorem constrained_dSum_le [∀ s, Fintype (C s)] (cost : (s : S) → C s → ℝ)
    (hc : ∀ s a, 0 ≤ cost s a) (c : (s : S) → C s → ℤ)
    (b M : ℝ) (hb : 1 ≤ b) (hM : 0 ≤ M)
    (hrow : ∀ s, (∑ a, cost s a * b ^ c s a) ≤ M)
    (n : ℕ) (s : S) (valid : DWord C step n s → Prop) [DecidablePred valid]
    (hvalid : ∀ w, valid w → 0 ≤ dCharge C step c s w) :
    (∑ w : DWord C step n s, if valid w then dWeight C step cost s w else 0) ≤ M ^ n := by
  classical
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  calc
    _ ≤ ∑ w : DWord C step n s,
        dWeight C step (fun s a => cost s a * b ^ c s a) s w := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with hv
      · rw [dReweighted C step cost c b hb0.ne']
        apply le_mul_of_one_le_right (dWeight_nonneg C step cost hc s w)
        exact one_le_zpow₀ hb (hvalid w hv)
      · exact dWeight_nonneg C step _
          (fun s a => mul_nonneg (hc s a) (zpow_nonneg hb0.le _)) s w
    _ ≤ _ := sum_dWeight_le C step _
      (fun s a => mul_nonneg (hc s a) (zpow_nonneg hb0.le _)) M hM hrow n s

end Dependent

end SharpRamseyFive.CertificateEnumeration

namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

variable (lines : H → Finset D)

omit [Fintype   V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D] [DecidableEq B] in
lemma anchorBudget_nonneg (rate : D → ℝ≥0) (s : State V H D B)
    (mass : ℝ) (hmass : 0 ≤ mass) : 0 ≤ anchorBudget rate s mass := by
  unfold anchorBudget
  positivity

omit [DecidableEq V] in
omit [DecidableEq H] in
omit [Fintype D] [DecidableEq B] in

theorem sum_oneCost_le (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (s : State V H D B) (mass : ℝ)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (N₁ : ℕ) (hN : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁) :
    (∑ c : OneChoice lines s, oneCost lines rate denom s c) ≤
      Fintype.card V ^ 2 * (N₁ : ℝ) * anchorBudget rate s mass / denom := by
  classical
  simp only [OneChoice, oneCost, Fintype.sum_sigma]
  simp only [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hd
  calc
    _ ≤ ∑ _v : V, ∑ _u : V, (N₁ : ℝ) * anchorBudget rate s mass := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      rw [one_anchor_subtype_sum]
      apply (one_anchor_geometric_cost rate s.2 (lines (s.1 u)) lines N₁ hN).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmass (s.1 u)) (Nat.cast_nonneg _))
    _ = _ := by simp [pow_two, anchorBudget]; ring

omit [DecidableEq V] [DecidableEq H] in
omit [Fintype D] [DecidableEq B] in

theorem sum_twoCost_le (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (s : State V H D B) (mass : ℝ) (hm0 : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (N₂ : ℕ) (hN : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂) :
    (∑ c : TwoChoice lines s, twoCost lines rate denom s c) ≤
      Fintype.card V ^ 3 * (N₂ : ℝ) * anchorBudget rate s mass ^ 2 / denom := by
  classical
  simp only [TwoChoice, twoCost, Fintype.sum_sigma]
  simp only [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hd
  calc
    _ ≤ ∑ _v : V, ∑ _u : V, ∑ _w : V,
        (N₂ : ℝ) * anchorBudget rate s mass ^ 2 := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro w _
      rw [two_anchor_subtype_sum]
      apply (two_anchor_cross_cost rate s.2 (lines (s.1 u)) (lines (s.1 w)) lines N₂ hN).trans
      have ha (j : V) : (s.2.card : ℝ) + Fintype.card B *
          ∑ d ∈ lines (s.1 j), (rate d : ℝ) ≤ anchorBudget rate s mass :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmass (s.1 j)) (Nat.cast_nonneg _))
      rw [pow_two, ← mul_assoc]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (ha u) (Nat.cast_nonneg _)
      · exact ha w
      · positivity
      · exact mul_nonneg (Nat.cast_nonneg _) (anchorBudget_nonneg rate s mass hm0)
    _ = _ := by simp; ring

omit [Fintype D] [DecidableEq B] in
lemma pairMoment_nonneg (rate : D → ℝ≥0) (K : ℕ) :
    0 ≤ pairMoment (B := B) lines rate K := by
  unfold pairMoment
  positivity

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma sum_pair_choices_le (rate : D → ℝ≥0) (K : ℕ) (s : State V H D B) (h h' : H) :
    (∑ T : {T : Finset B // T ∈ (Finset.univ : Finset B).powersetCard K},
      ∑ f : T.val → PairDirections lines s h h',
        weight (fun p : B × D => rate p.2)
          (witnessRequirements T.val (PairDirections lines s h h') f)) ≤
      ((Fintype.card B : ℝ) * ∑ d ∈ lines h ∩ lines h', (rate d : ℝ)) ^ K := by
  classical
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard K)
    (fun T : Finset B => ∑ f : T → PairDirections lines s h h',
      weight (fun p : B × D => rate p.2)
        (witnessRequirements T (PairDirections lines s h h') f))]
  apply (pair_certificate_weight_le rate (PairDirections lines s h h') K).trans
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (by intro d _ _; exact (rate d).coe_nonneg)

omit [DecidableEq V] in
omit [Fintype D] in

theorem sum_pairCost_le (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ)
    (s : State V H D B) :
    (∑ c : PairChoice lines K s, pairCost lines rate denom K s c) ≤
      Fintype.card V ^ 2 * pairMoment (B := B) lines rate K / denom ^ 2 := by
  classical
  simp only [PairChoice, pairCost, Fintype.sum_sigma]
  simp only [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ∑ _v : V, ∑ _u : V, pairMoment (B := B) lines rate K := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      unfold pairMoment
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro h' _
      exact sum_pair_choices_le lines rate K s h h'.val
    _ = _ := by simp [pow_two]; ring

end SharpRamseyFive.WeightedPrograms
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_NewEvents
attribute [-instance] _root_.OAI.SharpRamseyFive.CertificateCover.completePrograms_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma newEvents_fresh (K : ℕ) (s : State V H D B) (a : Action lines K s) :
    Disjoint s.2 (newEvents lines K s a) := by
  rcases a with a | a
  · exact Finset.disjoint_empty_right _
  rcases a with a | a
  · exact a.2.2.1.fresh
  rcases a with a | a
  · exact Finset.disjoint_union_right.mpr ⟨a.2.2.2.1.fresh, a.2.2.2.2.1.fresh⟩
  · apply witnessRequirements_disjoint
    apply Finset.disjoint_left.mpr
    intro d hd hdC
    exact (Finset.mem_sdiff.mp hd).2 hdC

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma rawCost_nonneg (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) :
    0 ≤ rawCost lines rate denom K low s a := by
  rcases a with a | a
  · exact div_nonneg zero_le_one hd
  rcases a with a | a
  · change 0 ≤ if low then _ else 0
    split_ifs
    · exact div_nonneg (a.2.2.1.cost_nonneg rate) hd
    · exact le_rfl
  rcases a with a | a
  · exact div_nonneg (mul_nonneg (a.2.2.2.1.cost_nonneg rate)
      (a.2.2.2.2.1.cost_nonneg rate)) hd
  · exact div_nonneg (weight_nonneg _ _) (sq_nonneg _)
omit [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma programCost_nonneg (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) :
    0 ≤ programCost lines rate denom K low s a := by
  unfold programCost
  split_ifs
  · exact rawCost_nonneg lines rate denom hd K low s a
  · exact le_rfl

omit [DecidableEq V] in
omit [Fintype D] [DecidableEq B] in
lemma branchingBound_nonneg (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 ≤ denom) (hb : 0 ≤ b) (hm : 0 ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool) :
    0 ≤ branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low := by
  unfold branchingBound uniformAnchorBudget
  have hp := pairMoment_nonneg (B := B) lines rate K
  split_ifs <;> positivity

omit [DecidableEq V] [Fintype D] in
lemma discounted_raw_sum (rate : D → ℝ≥0) (denom b : ℝ)
    (K : ℕ) (low : Bool) (s : State V H D B) :
    (∑ a : Action lines K s, rawCost lines rate denom K low s a * b ^ actionCharge lines K s a) =
      ((Fintype.card V : ℝ) * Fintype.card H / denom) / b ^ 8 +
      (if low then ∑ c : OneChoice lines s, oneCost lines rate denom s c else 0) +
      (∑ c : TwoChoice lines s, twoCost lines rate denom s c) * b +
      ∑ c : PairChoice lines K s, pairCost lines rate denom K s c := by
  classical
  change (∑ a : RootChoice (V := V) (H := H) ⊕
      OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s, _) = _
  simp only [Fintype.sum_sum_type, rawCost, actionCharge]
  cases low <;>
    simp only [Bool.false_eq_true, ↓reduceIte,
      zpow_neg, zpow_ofNat, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, RootChoice, Nat.cast_mul] <;> ring

omit [DecidableEq V] in
omit [Fintype D] in

theorem discounted_row_bound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 ≤ denom) (hb : 0 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (s : State V H D B) :
    (∑ a : Action lines K s,
      programCost lines rate denom K low s a * b ^ actionCharge lines K s a) ≤
      branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low := by
  classical
  by_cases hs : s.2.card ≤ K * Fintype.card V
  · simp only [programCost, ite_eq_left hs]
    rw [discounted_raw_sum]
    have hA : anchorBudget rate s mass ≤ uniformAnchorBudget (V := V) (B := B) K mass := by
      unfold anchorBudget uniformAnchorBudget
      apply add_le_add _ le_rfl
      exact_mod_cast hs
    have h1 := sum_oneCost_le lines rate denom hd s mass hmass N₁ hN₁
    have h2 := sum_twoCost_le lines rate denom hd s mass hm hmass N₂ hN₂
    have h3 := sum_pairCost_le lines rate denom K s
    unfold branchingBound
    apply add_le_add
    · apply add_le_add
      · apply add_le_add le_rfl
        split_ifs with hl
        · apply h1.trans
          apply div_le_div_of_nonneg_right _ hd
          exact mul_le_mul_of_nonneg_left hA (by positivity)
        · exact le_rfl
      · apply mul_le_mul_of_nonneg_right _ hb
        apply h2.trans
        apply div_le_div_of_nonneg_right _ hd
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (anchorBudget_nonneg rate s mass hm) hA 2
    · exact h3
  · simp only [programCost, ite_eq_right hs, zero_mul, Finset.sum_const_zero]
    exact branchingBound_nonneg (V := V) lines rate denom b mass hd hb hm K N₁ N₂ low

omit [Fintype D] in

theorem program_enumeration (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 ≤ denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (n : ℕ) (s : State V H D B) :
    (∑ w : DWord (Action lines K) (advance lines K) n s,
      if 0 ≤ dCharge (Action lines K) (advance lines K) (actionCharge lines K) s w
      then dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s w
      else 0) ≤
      branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n := by
  classical
  exact constrained_dSum_le (Action lines K) (advance lines K)
    (programCost lines rate denom K low) (programCost_nonneg lines rate denom hd K low)
    (actionCharge lines K) b _ hb
    (branchingBound_nonneg (V := V) lines rate denom b mass hd (by linarith) hm K N₁ N₂ low)
    (discounted_row_bound lines rate denom b mass hd (by linarith) hm hmass K N₁ N₂ low hN₁ hN₂)
    n s _ (fun _ h => h)

end SharpRamseyFive.WeightedPrograms

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma integrable_bounded (f : (V → Bool) → ℝ) (C : ℝ) (hf : ∀ ω, |f ω| ≤ C) :
    Integrable f rootMeasure := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (by intro ω; simpa only [Real.norm_eq_abs] using hf ω)
omit [DecidableEq V] in

lemma integrable_voidIndicator (W : Finset V) : Integrable (voidIndicator W) rootMeasure := by
  apply integrable_bounded _ 1
  intro ω
  by_cases h : ω ∈ voidEvent W <;> simp [voidIndicator, h]

lemma integrable_badIndicator (W : Finset V) : Integrable (badIndicator W) rootMeasure := by
  apply integrable_bounded _ 1
  intro ω
  simp only [badIndicator]
  split_ifs <;> norm_num

omit [Fintype V] [DecidableEq V] in
lemma voidIndicator_nonneg (W : Finset V) (ω : V → Bool) : 0 ≤ voidIndicator W ω := by
  by_cases h : ω ∈ voidEvent W <;> simp [voidIndicator, h]

lemma badIndicator_nonneg (W : Finset V) (ω : V → Bool) : 0 ≤ badIndicator W ω := by
  simp only [badIndicator]
  split_ifs <;> norm_num

omit [DecidableEq V] in
lemma integral_voidIndicator (W : Finset V) :
    ∫ ω, voidIndicator W ω ∂rootMeasure = (19 / 20 : ℝ) ^ W.card := by
  have hm : MeasurableSet (voidEvent W) := MeasurableSet.pi W.finite_toSet.countable
    (fun _ _ => measurableSet_singleton false)
  have hprob : rootMeasure (voidEvent W) = ENNReal.ofReal ((19 / 20 : ℝ) ^ W.card) := by
    rw [rootMeasure, voidEvent, Measure.pi_pi_finset]
    simp only [bernoulliMeasure_apply rootProbability (measurableSet_singleton false)]
    norm_num [rootProbability, unitInterval.toNNReal, unitInterval.symm]
    congr 1
    exact ENNReal.ofReal_coe_nnreal.symm
  simp only [voidIndicator]
  rw [ integral_indicator_const _ hm, Measure.real, hprob,
    ENNReal.toReal_ofReal (by positivity)]
  simp

lemma erase_void_witness (W : Finset V) (hW : W.Nonempty) (ω : V → Bool)
    (hbad : (W ∩ selected ω).card < 2) :
    ∃ j ∈ W, ω ∈ voidEvent (W.erase j) := by
  have hsmall : (W ∩ selected ω).card ≤ 1 := by omega
  have hc := Finset.card_le_one.mp hsmall
  by_cases he : (W ∩ selected ω).Nonempty
  · obtain ⟨j, hj⟩ := he
    refine ⟨j, (Finset.mem_inter.mp hj).1, ?_⟩
    intro k hk
    apply Set.mem_singleton_iff.mpr
    apply Bool.eq_false_of_not_eq_true
    intro hkt
    have hkm : k ∈ W ∩ selected ω := by
      simp only [Finset.mem_inter, selected, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(Finset.mem_erase.mp hk).2, hkt⟩
    exact (Finset.mem_erase.mp hk).1 (hc k hkm j hj)
  · obtain ⟨j, hj⟩ := hW
    refine ⟨j, hj, ?_⟩
    intro k hk
    apply Set.mem_singleton_iff.mpr
    apply Bool.eq_false_of_not_eq_true
    intro hkt
    apply he
    refine ⟨k, ?_⟩
    simp only [Finset.mem_inter, selected, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(Finset.mem_erase.mp hk).2, hkt⟩

lemma badIndicator_le_erase_void (W : Finset V) (hW : W.Nonempty) (ω : V → Bool) :
    badIndicator W ω ≤ ∑ j ∈ W, voidIndicator (W.erase j) ω := by
  unfold badIndicator
  split_ifs with hb
  · obtain ⟨j, hj, hv⟩ := erase_void_witness W hW ω hb
    have hle := Finset.single_le_sum (f := fun j => voidIndicator (W.erase j) ω)
      (fun j _ => voidIndicator_nonneg _ _) hj
    simpa only [voidIndicator, Set.indicator_of_mem hv] using hle
  · exact Finset.sum_nonneg (fun j _ => voidIndicator_nonneg _ _)

lemma integral_badIndicator_le (W : Finset V) (hW : W.Nonempty) :
    ∫ ω, badIndicator W ω ∂rootMeasure ≤
      W.card * (19 / 20 : ℝ) ^ (W.card - 1) := by
  calc
    _ ≤ ∫ ω, ∑ j ∈ W, voidIndicator (W.erase j) ω ∂rootMeasure :=
      integral_mono (integrable_badIndicator W)
        (integrable_finsetSum _ (fun j _ => integrable_voidIndicator _))
        (badIndicator_le_erase_void W hW)
    _ = ∑ j ∈ W, (19 / 20 : ℝ) ^ (W.card - 1) := by
      rw [integral_finsetSum _ (fun j _ => integrable_voidIndicator _)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_voidIndicator, Finset.card_erase_of_mem hj]
    _ = _ := by simp

omit [DecidableEq V] in
lemma indicator_selected (ω : V → Bool) :
    ((selected ω).card : ℝ) = ∑ v : V, if ω v = true then (1 : ℝ) else 0 := by
  symm
  exact Finset.sum_boole _ _
omit [DecidableEq V] in

lemma integrable_selected_card :
    Integrable (fun ω : V → Bool => ((selected ω).card : ℝ)) rootMeasure := by
  simp_rw [indicator_selected]
  apply integrable_finsetSum
  intro v hv
  apply integrable_bounded _ 1
  intro ω
  split_ifs <;> norm_num
omit [DecidableEq V] in

lemma integral_selected_card :
    ∫ ω : V → Bool, ((selected ω).card : ℝ) ∂rootMeasure = (Fintype.card V : ℝ) / 20 := by
  simp_rw [indicator_selected]
  rw [integral_finsetSum]
  · have hv (v : V) :
        (∫ ω : V → Bool, if ω v = true then (1 : ℝ) else 0 ∂rootMeasure) = 1 / 20 := by
      rw [rootMeasure, integral_comp_eval (μ := fun _ : V => bernoulliMeasure true false rootProbability) (i := v) (f := fun a : Bool => if a = true then (1 : ℝ) else 0)
        (measurable_of_countable _).aestronglyMeasurable,
        integral_bernoulliMeasure]
      norm_num [rootProbability]
    simp_rw [hv]
    simp [div_eq_mul_inv]
  · intro v hv
    apply integrable_bounded _ 1
    intro ω
    split_ifs <;> norm_num

theorem exists_small_root_set (W : V → Finset V) {k : ℕ} (hk : 0 < k)
    (hW : ∀ v, (W v).card = k)
    (herr : (Fintype.card V : ℝ) * k * (19 / 20 : ℝ) ^ (k - 1) < 1 / 2) :
    ∃ roots : Finset V, 10 * roots.card ≤ Fintype.card V ∧
      ∀ v, 2 ≤ (W v ∩ roots).card := by
  classical
  by_cases hn : Fintype.card V = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    exact ⟨∅, by simp [], fun v => isEmptyElim v⟩
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let F : (V → Bool) → ℝ := fun ω =>
    (10 / Fintype.card V : ℝ) * (selected ω).card + ∑ v, badIndicator (W v) ω
  have hFi : Integrable F rootMeasure :=
    (integrable_selected_card.const_mul _).add
      (integrable_finsetSum _ (fun v _ => integrable_badIndicator (W v)))
  have hFint : ∫ ω, F ω ∂rootMeasure < 1 := by
    have he (v : V) : ∫ ω, badIndicator (W v) ω ∂rootMeasure ≤
        k * (19 / 20 : ℝ) ^ (k - 1) := by
      simpa only [hW] using integral_badIndicator_le (W v) (Finset.card_pos.mp (by rw [hW v]; exact hk))
    have sumle : ∑ v : V, (∫ ω, badIndicator (W v) ω ∂rootMeasure) ≤
        (Fintype.card V : ℝ) * k * (19 / 20 : ℝ) ^ (k - 1) := by
      calc
        _ ≤ ∑ _v : V, (k : ℝ) * (19 / 20 : ℝ) ^ (k - 1) := Finset.sum_le_sum (fun v _ => he v)
        _ = _ := by simp; ring
    have hc : (10 / Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / 20) = 1 / 2 := by
      field_simp
      ; ring
    dsimp [F]
    rw [integral_add (integrable_selected_card.const_mul _)
      (integrable_finsetSum _ (fun v _ => integrable_badIndicator (W v))),
      integral_const_mul, integral_selected_card, integral_finsetSum _
        (fun v _ => integrable_badIndicator (W v)), hc]
    linarith
  have hex : ∃ ω, F ω < 1 := by
    by_contra h
    push Not at h
    have hle := integral_mono (integrable_const (1 : ℝ)) hFi h
    simp only [integral_const] at hle
    simp at hle
    linarith
  obtain ⟨ω, hω⟩ := hex
  have hsum : 0 ≤ ∑ v : V, badIndicator (W v) ω :=
    Finset.sum_nonneg (fun v _ => badIndicator_nonneg _ _)
  have hcost : 0 ≤ (10 / Fintype.card V : ℝ) * (selected ω).card := by positivity
  refine ⟨selected ω, ?_, ?_⟩
  · have ht : (10 / Fintype.card V : ℝ) * (selected ω).card < 1 := by dsimp [F] at hω; linarith
    have hcard : (10 : ℝ) * (selected ω).card ≤ Fintype.card V := by
      have := (mul_lt_mul_iff_right₀ hnpos).mpr ht
      field_simp at this
      nlinarith
    exact_mod_cast hcard
  · intro v
    by_contra hv
    have hbad : badIndicator (W v) ω = 1 := by simp [badIndicator, show (W v ∩ selected ω).card < 2 by omega]
    have hle := Finset.single_le_sum (f := fun v => badIndicator (W v) ω)
      (fun v _ => badIndicator_nonneg _ _) (Finset.mem_univ v)
    rw [hbad] at hle
    dsimp [F] at hω
    linarith

section WitnessMatching

variable {E N D : Type*} [DecidableEq E] [DecidableEq N] [DecidableEq D]

theorem exists_distinct_witnesses (s : Finset E) (neighbor : E → N) (direction : E → D)
    (K : ℕ) (hn : ∀ n, (s.filter (fun e => neighbor e = n)).card ≤ K)
    (hd : ∀ d, (s.filter (fun e => direction e = d)).card ≤ K) :
    ∃ t ⊆ s, Set.InjOn neighbor (t : Set E) ∧ Set.InjOn direction (t : Set E) ∧
      s.card ≤ 2 * K * t.card := by
  classical
  let family : Finset (Finset E) := s.powerset.filter (fun t =>
    Set.InjOn neighbor (t : Set E) ∧ Set.InjOn direction (t : Set E))
  have hempty : ∅ ∈ family := by simp [family, Set.injOn_empty]
  obtain ⟨t, htf, hmax⟩ := Finset.exists_max_image family Finset.card ⟨∅, hempty⟩
  have ht : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp htf).1
  have hinj := (Finset.mem_filter.mp htf).2
  have hcover (e : E) (he : e ∈ s) :
      ∃ a ∈ t, neighbor e = neighbor a ∨ direction e = direction a := by
    by_contra h
    push Not at h
    have hen : e ∉ t := by
      intro het
      exact (h e het).1 rfl
    have hnnew : Set.InjOn neighbor (↑(insert e t) : Set E) := by
      rw [Finset.coe_insert, Set.injOn_insert hen]
      refine ⟨hinj.1, ?_⟩
      rintro ⟨a, ha, hea⟩
      exact (h a ha).1 hea.symm
    have hdnew : Set.InjOn direction (↑(insert e t) : Set E) := by
      rw [Finset.coe_insert, Set.injOn_insert hen]
      refine ⟨hinj.2, ?_⟩
      rintro ⟨a, ha, hea⟩
      exact (h a ha).2 hea.symm
    have hnew : insert e t ∈ family := by
      simp only [family, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset he ht, hnnew, hdnew⟩
    have := hmax _ hnew
    rw [Finset.card_insert_of_notMem hen] at this
    omega
  refine ⟨t, ht, hinj.1, hinj.2, ?_⟩
  have hsub : s ⊆ t.biUnion (fun a =>
      (s.filter (fun e => neighbor e = neighbor a)) ∪
      (s.filter (fun e => direction e = direction a))) := by
    intro e he
    obtain ⟨a, ha, hor⟩ := hcover e he
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    simpa only [Finset.mem_union, Finset.mem_filter, and_or_left] using
      And.intro he hor
  calc
    s.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ t, ((s.filter (fun e => neighbor e = neighbor a)) ∪
        (s.filter (fun e => direction e = direction a))).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ t, 2 * K := by
      apply Finset.sum_le_sum
      intro a ha
      exact (Finset.card_union_le _ _).trans (by have := hn (neighbor a); have := hd (direction a); omega)
    _ = 2 * K * t.card := by simp [Nat.mul_comm]

end WitnessMatching
end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_WitnessList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
section WitnessMatching
variable {E N D : Type*} [DecidableEq E] [DecidableEq N] [DecidableEq D]
theorem exists_witness_list (s : Finset E) (neighbor : E → N) (direction : E → D)
    (K h : ℕ) (hn : ∀ n, (s.filter (fun e => neighbor e = n)).card ≤ K)
    (hd : ∀ d, (s.filter (fun e => direction e = d)).card ≤ K)
    (hh : h ≤ s.card / (2 * K)) :
    ∃ t ⊆ s, t.card = h ∧ Set.InjOn neighbor (t : Set E) ∧ Set.InjOn direction (t : Set E) := by
  obtain ⟨u, hu, hun, hud, hcard⟩ := exists_distinct_witnesses s neighbor direction K hn hd
  have hle : h ≤ u.card := hh.trans (Nat.div_le_of_le_mul hcard)
  obtain ⟨t, htu, htc⟩ := Finset.exists_subset_card_eq hle
  exact ⟨t, htu.trans hu, htc, hun.mono htu, hud.mono htu⟩

theorem exists_residual_roots [Fintype N] (batchSet : N → Finset E)
    (neighbor : N → E → N) (direction : N → E → D) (K h : ℕ)
    (hh : 0 < h)
    (hsize : ∀ v, h ≤ (batchSet v).card / (2 * K))
    (hn : ∀ v n, ((batchSet v).filter (fun e => neighbor v e = n)).card ≤ K)
    (hd : ∀ v d, ((batchSet v).filter (fun e => direction v e = d)).card ≤ K)
    (herr : (Fintype.card N : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ roots : Finset N, 10 * roots.card ≤ Fintype.card N ∧
      ∀ v, ∃ b₁ ∈ batchSet v, ∃ b₂ ∈ batchSet v,
        neighbor v b₁ ∈ roots ∧ neighbor v b₂ ∈ roots ∧
        neighbor v b₁ ≠ neighbor v b₂ ∧ direction v b₁ ≠ direction v b₂ := by
  classical
  have hex (v : N) := exists_witness_list (batchSet v) (neighbor v) (direction v)
    K h (hn v) (hd v) (hsize v)
  choose lists hsub hcard hin hn_dir using hex
  let W : N → Finset N := fun v => (lists v).image (neighbor v)
  have hW (v : N) : (W v).card = h := by
    change ((lists v).image (neighbor v)).card = h
    rw [Finset.card_image_of_injOn (hin v), hcard v]
  obtain ⟨roots, hr, hall⟩ := exists_small_root_set W hh hW herr
  refine ⟨roots, hr, ?_⟩
  intro v
  have htwo : 1 < (W v ∩ roots).card := by have := hall v; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
  obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
  refine ⟨b₁, hsub v hb₁, b₂, hsub v hb₂, (Finset.mem_inter.mp ha).2,
    (Finset.mem_inter.mp hb).2, hab, ?_⟩
  intro heq
  have := hn_dir v hb₁ hb₂ heq
  exact hab (congrArg (neighbor v) this)

end WitnessMatching

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

omit [Fintype D] in

theorem roots_from_shared_hits (s : V → Finset D) (hit : B → D → Prop)
    (K h : ℕ) (hh : 0 < h)
    (hsize : ∀ v, h ≤ (touchedBatches s hit v).card / (2 * K))
    (hpair : ∀ v u, v ≠ u → (sharedBatches s hit v u).card ≤ K)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ roots : Finset V, 10 * roots.card ≤ Fintype.card V ∧
      ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
        ∃ d₁ ∈ s v ∩ s u, ∃ d₂ ∈ s v ∩ s w,
          d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  have hwit (v : V) (r : touchedBatches s hit v) :
      ∃ z : V × D, z.1 ≠ v ∧ z.2 ∈ s v ∩ s z.1 ∧ hit r.val z.2 := by
    obtain ⟨u, hu, hs⟩ := (Finset.mem_filter.mp r.property).2
    obtain ⟨d, hd, hr⟩ := (Finset.mem_filter.mp hs).2
    exact ⟨(u, d), hu, hd, hr⟩
  choose wit hwit using hwit
  let neighbor (v : V) (r : B) : V :=
    if hr : r ∈ touchedBatches s hit v then (wit v ⟨r, hr⟩).1 else v
  let direction (v : V) (r : B) : Option D :=
    if hr : r ∈ touchedBatches s hit v then some (wit v ⟨r, hr⟩).2 else none
  have hvalid (v : V) (r : B) (hr : r ∈ touchedBatches s hit v) :
      ∃ d, direction v r = some d ∧ neighbor v r ≠ v ∧
        d ∈ s v ∩ s (neighbor v r) ∧ hit r d := by
    refine ⟨(wit v ⟨r, hr⟩).2, ?_⟩
    simp only [neighbor, direction, dite_eq_left hr]
    exact ⟨trivial, hwit v ⟨r, hr⟩⟩
  have hn (v u : V) :
      ((touchedBatches s hit v).filter (fun r => neighbor v r = u)).card ≤ K := by
    by_cases hu : v = u
    · have he : (touchedBatches s hit v).filter (fun r => neighbor v r = u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hr, he⟩ := Finset.mem_filter.mp hr
        obtain ⟨d, _, hd, _⟩ := hvalid v r hr
        exact hd (he.trans hu.symm)
      simp [he]
    · apply (Finset.card_le_card (show
          (touchedBatches s hit v).filter (fun r => neighbor v r = u) ⊆
            sharedBatches s hit v u from ?_)).trans (hpair v u hu)
      intro r hr
      obtain ⟨hr, he⟩ := Finset.mem_filter.mp hr
      obtain ⟨d, _, _, hd, hp⟩ := hvalid v r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, he ▸ hd, hp⟩
  have hd (v : V) (d : Option D) :
      ((touchedBatches s hit v).filter (fun r => direction v r = d)).card ≤ K := by
    let T := (touchedBatches s hit v).filter (fun r => direction v r = d)
    by_cases he : T.Nonempty
    · obtain ⟨r₀, hr₀⟩ := he
      obtain ⟨hm₀, hd₀⟩ := Finset.mem_filter.mp hr₀
      obtain ⟨a, ha, hu, has, hp⟩ := hvalid v r₀ hm₀
      apply (Finset.card_le_card (show T ⊆ sharedBatches s hit v (neighbor v r₀) from ?_)).trans
        (hpair v (neighbor v r₀) hu.symm)
      intro r hr
      obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hr
      obtain ⟨b, hb, _, hbs, hhit⟩ := hvalid v r hm
      have heq : b = a := Option.some.inj (hb.symm.trans (hd.trans (hd₀.symm.trans ha)))
      subst b
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbs).1, (Finset.mem_inter.mp has).2⟩, hhit⟩
    · have hem : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      change T.card ≤ K
      simp [hem]
  obtain ⟨roots, hr, hroots⟩ := exists_residual_roots (touchedBatches s hit)
    neighbor direction K h hh hsize hn hd herr
  refine ⟨roots, hr, ?_⟩
  intro v
  obtain ⟨r₁, hr₁, r₂, hr₂, hu, hw, huv, hdir⟩ := hroots v
  obtain ⟨a, ha, hne₁, hmem₁, hhit₁⟩ := hvalid v r₁ hr₁
  obtain ⟨b, hb, hne₂, hmem₂, hhit₂⟩ := hvalid v r₂ hr₂
  refine ⟨neighbor v r₁, hu, neighbor v r₂, hw, huv, hne₁, hne₂,
    a, hmem₁, b, hmem₂, ?_, ⟨r₁, hhit₁⟩, ⟨r₂, hhit₂⟩⟩
  intro heq
  exact hdir (ha.trans (congrArg some heq) |>.trans hb.symm)

omit [Fintype D] [DecidableEq D] in
lemma mem_batchesOn (hit : B → D → Prop) (T : Finset D) (r : B) :
    r ∈ batchesOn hit T ↔ ∃ d ∈ T, hit r d := by
  simp [batchesOn]

omit [Fintype D] in

lemma surviving_touches (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : {v // v ∉ E}) :
    touchedBatches s hit v.val \ batchesOn hit (touchedToEncoded s hit E v.val) ⊆
      touchedBatches (survivingDirections s E) hit v := by
  classical
  intro r hr
  obtain ⟨hr, hnot⟩ := Finset.mem_sdiff.mp hr
  obtain ⟨u, huv, hu⟩ := (Finset.mem_filter.mp hr).2
  obtain ⟨d, hd, hh⟩ := (Finset.mem_filter.mp hu).2
  have hde : d ∉ encodedDirections s E := by
    intro he
    apply hnot
    rw [mem_batchesOn]
    exact ⟨d, Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hd).1, he⟩, ⟨r, hh⟩⟩, hh⟩
  have hue : u ∉ E := by
    intro hu
    exact hde (Finset.mem_biUnion.mpr ⟨u, hu, (Finset.mem_inter.mp hd).2⟩)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, hue⟩, ?_, ?_⟩
  · intro he
    exact huv (congrArg Subtype.val he)
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, ?_, hh⟩
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hd).1, hde⟩,
      Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hd).2, hde⟩⟩

omit [Fintype D] [DecidableEq D] in
lemma batchesOn_card_le (hit : B → D → Prop) (T : Finset D) (J : ℕ)
    (hJ : ∀ d ∈ T, (Finset.univ.filter (fun r => hit r d)).card ≤ J) :
    (batchesOn hit T).card ≤ T.card * J := by
  classical
  apply (Finset.card_biUnion_le).trans
  calc
    ∑ d ∈ T, (Finset.univ.filter (fun r => hit r d)).card ≤ ∑ _d ∈ T, J :=
      Finset.sum_le_sum hJ
    _ = _ := by simp
omit [Fintype D] in

lemma surviving_touches_card (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : {v // v ∉ E}) (J N : ℕ)
    (hbad : N ≤ (touchedBatches s hit v.val).card)
    (hloss : (batchesOn hit (touchedToEncoded s hit E v.val)).card ≤ J) :
    N - J ≤ (touchedBatches (survivingDirections s E) hit v).card := by
  have hs := Finset.card_le_card (surviving_touches s hit E v)
  have hd := Finset.card_sdiff_add_card_inter
    (touchedBatches s hit v.val) (batchesOn hit (touchedToEncoded s hit E v.val))
  have hi := Finset.card_le_card (Finset.inter_subset_right
    (s₁ := touchedBatches s hit v.val)
    (s₂ := batchesOn hit (touchedToEncoded s hit E v.val)))
  omega

omit [Fintype V] [DecidableEq V] in
omit [Fintype D] in

lemma terminal_high_loss (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) (J : ℕ)
    (hanchor : (touchedToEncoded s hit E v).card ≤ 1)
    (htrunc : ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J) :
    (batchesOn hit (touchedToEncoded s hit E v)).card ≤ J := by
  exact (batchesOn_card_le hit _ J (fun d _ => htrunc d)).trans
    (by simpa using Nat.mul_le_mul_right J hanchor)

omit [Fintype V] [DecidableEq V] [Fintype D] in
lemma terminal_low_loss (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) (hanchor : touchedToEncoded s hit E v = ∅) :
    (batchesOn hit (touchedToEncoded s hit E v)).card = 0 := by
  simp [hanchor, batchesOn]

omit [Fintype D] in

theorem terminal_state_roots (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (K J h : ℕ) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2 - J) / (2 * K))
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches s hit v).card)
    (hloss : ∀ v ∉ E, (batchesOn hit (touchedToEncoded s hit E v)).card ≤ J)
    (hpair : ∀ (v u : {v // v ∉ E}), v ≠ u →
      (sharedBatches (survivingDirections s E) hit v u).card < K)
    (herr : (Fintype.card {v // v ∉ E} : ℝ) * h *
      (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ roots : Finset {v // v ∉ E}, 10 * roots.card ≤ Fintype.card {v // v ∉ E} ∧
      ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
        ∃ d₁ ∈ survivingDirections s E v ∩ survivingDirections s E u,
        ∃ d₂ ∈ survivingDirections s E v ∩ survivingDirections s E w,
          d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  apply roots_from_shared_hits (survivingDirections s E) hit K h hh
  · intro v
    apply hsize.trans
    apply Nat.div_le_div_right
    exact surviving_touches_card s hit E v J _ (hbad v.val v.property)
      (hloss v.val v.property)
  · intro v u hvu
    exact (hpair v u hvu).le
  · exact herr

omit [Fintype V] [Fintype D] [DecidableEq B] in
lemma encodingStep_strict (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) {E F : Finset V} (h : EncodingStep s hit a K E F) : E ⊂ F := by
  cases h with
  | anchor v hv ha => exact Finset.ssubset_insert hv
  | pair v u hv hu hne hp =>
    exact (Finset.ssubset_insert hu).trans_subset (Finset.subset_insert _ _)
omit [Fintype V] [Fintype D] [DecidableEq B] in

lemma encoding_reachable_subset (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) {E F : Finset V} (h : Relation.ReflTransGen (EncodingStep s hit a K) E F) :
    E ⊆ F := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @tail F G h hFG ih => exact ih.trans (encodingStep_strict s hit a K hFG).subset

omit [Fintype D] [DecidableEq B] in

theorem exists_terminal_encoding (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) (E : Finset V) :
    ∃ F, Relation.ReflTransGen (EncodingStep s hit a K) E F ∧
      (∀ v ∉ F, (touchedToEncoded s hit F v).card < a) ∧
      ∀ v ∉ F, ∀ u ∉ F, v ≠ u →
        (sharedBatches (outsideDirections s F) hit v u).card < K := by
  classical
  let reachable : Finset (Finset V) := Finset.univ.filter
    (fun F => Relation.ReflTransGen (EncodingStep s hit a K) E F)
  have hE : E ∈ reachable := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  obtain ⟨F, hF, hmax⟩ := reachable.exists_max_image Finset.card ⟨E, hE⟩
  have hreach := (Finset.mem_filter.mp hF).2
  have hterminal (G : Finset V) : ¬EncodingStep s hit a K F G := by
    intro hs
    have hG : G ∈ reachable := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach.tail hs⟩
    exact (Nat.not_lt_of_ge (hmax G hG)) (Finset.card_lt_card (encodingStep_strict s hit a K hs))
  refine ⟨F, hreach, ?_, ?_⟩
  · intro v hv
    by_contra ha
    exact hterminal _ (.anchor F v hv (Nat.not_lt.mp ha))
  · intro v hv u hu hne
    by_contra hp
    exact hterminal _ (.pair F v u hv hu hne (Nat.not_lt.mp hp))

omit [Fintype D] in

theorem high_case_certificate_geometry (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (K J h : ℕ) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2 - J) / (2 * K))
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches s hit v).card)
    (htrunc : ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ F, Relation.ReflTransGen (EncodingStep s hit 2 K) E F ∧
      ∃ roots : Finset {v // v ∉ F}, 10 * roots.card ≤ Fintype.card {v // v ∉ F} ∧
        ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
          ∃ d₁ ∈ survivingDirections s F v ∩ survivingDirections s F u,
          ∃ d₂ ∈ survivingDirections s F v ∩ survivingDirections s F w,
            d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  obtain ⟨F, hF, ha, hp⟩ := exists_terminal_encoding s hit 2 K E
  refine ⟨F, hF, ?_⟩
  apply terminal_state_roots s hit F K J h hh hsize
  · intro v hv
    exact hbad v (fun he => hv (encoding_reachable_subset s hit 2 K hF he))
  · intro v hv
    exact terminal_high_loss s hit F v J (by have := ha v hv; omega) htrunc
  · intro v u hvu
    have hne : v.val ≠ u.val := fun he => hvu (Subtype.ext he)
    exact hp v.val v.property u.val u.property hne
  · apply lt_of_le_of_lt _ herr
    have hc : (Fintype.card {v // v ∉ F} : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Fintype.card_subtype_le (fun v => v ∉ F)
    gcongr

omit [Fintype D] in

theorem low_case_certificate_geometry (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (K h : ℕ) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2) / (2 * K))
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches s hit v).card)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ F, Relation.ReflTransGen (EncodingStep s hit 1 K) E F ∧
      ∃ roots : Finset {v // v ∉ F}, 10 * roots.card ≤ Fintype.card {v // v ∉ F} ∧
        ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
          ∃ d₁ ∈ survivingDirections s F v ∩ survivingDirections s F u,
          ∃ d₂ ∈ survivingDirections s F v ∩ survivingDirections s F w,
            d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  obtain ⟨F, hF, ha, hp⟩ := exists_terminal_encoding s hit 1 K E
  refine ⟨F, hF, ?_⟩
  apply terminal_state_roots s hit F K 0 h hh (by simpa using hsize)
  · intro v hv
    exact hbad v (fun he => hv (encoding_reachable_subset s hit 1 K hF he))
  · intro v hv
    have hem : touchedToEncoded s hit F v = ∅ := Finset.card_eq_zero.mp (by
      have := ha v hv
      omega)
    exact (terminal_low_loss s hit F v hem).le
  · intro v u hvu
    have hne : v.val ≠ u.val := fun he => hvu (Subtype.ext he)
    exact hp v.val v.property u.val u.property hne
  · apply lt_of_le_of_lt _ herr
    have hc : (Fintype.card {v // v ∉ F} : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Fintype.card_subtype_le (fun v => v ∉ F)
    gcongr

omit [Fintype V] [DecidableEq V] [Fintype D] in
lemma encodedDirections_mono (s : V → Finset D) {E F : Finset V} (h : E ⊆ F) :
    encodedDirections s E ⊆ encodedDirections s F := by
  intro d hd
  obtain ⟨v, hv, hdv⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨v, h hv, hdv⟩

omit [Fintype D] [Fintype B] in
lemma paidDirections_union (C C' : Finset (B × D)) :
    paidDirections (C ∪ C') = paidDirections C ∪ paidDirections C' := by
  simp only [paidDirections, Finset.image_union]

omit [Fintype D] [Fintype B] in
lemma realized_union (hit : B → D → Prop) {C C' : Finset (B × D)}
    (h : Realized hit C) (h' : Realized hit C') : Realized hit (C ∪ C') := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_AnchorEventsRealized
attribute [-instance] _root_.OAI.SharpRamseyFive.CertificateCover.completePrograms_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
section SharedHitGeometry
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

omit [Fintype D] [Fintype B] in
lemma pairEvents_card (T : Finset B) (d : T → D) :
    (pairEvents T d).card = T.card := by
  rw [pairEvents, Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro r r' he
    exact Subtype.ext (congrArg Prod.fst he)

omit [Fintype D] [Fintype B] in
lemma pairEvents_realized (hit : B → D → Prop) (T : Finset B) (d : T → D)
    (h : ∀ r : T, hit r.val (d r)) : Realized hit (pairEvents T d) := by
  intro p hp
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
  exact h r

omit [Fintype V] [Fintype D] in

theorem pair_step_witnesses (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (C : Finset (B × D)) (v u : V) (K : ℕ)
    (hC : DictionaryInvariant s E C) (hreal : Realized hit C)
    (hp : K ≤ (sharedBatches (outsideDirections s E) hit v u).card) :
    ∃ (T : Finset B) (d : T → D), T.card = K ∧
      (∀ r : T, d r ∈ s v ∩ s u ∧ d r ∉ encodedDirections s E ∧ hit r.val (d r)) ∧
      Disjoint C (pairEvents T d) ∧ Realized hit (C ∪ pairEvents T d) ∧
      DictionaryInvariant s (insert v (insert u E)) (C ∪ pairEvents T d) ∧
      (C ∪ pairEvents T d).card = C.card + K := by
  classical
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hp
  have hh (r : T) : ∃ d, d ∈ s v ∩ s u ∧ d ∉ encodedDirections s E ∧ hit r.val d := by
    obtain ⟨d, hd, hr⟩ := (Finset.mem_filter.mp (hT r.property)).2
    obtain ⟨hdv, hdu⟩ := Finset.mem_inter.mp hd
    exact ⟨d, Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hdv).1,
      (Finset.mem_sdiff.mp hdu).1⟩, (Finset.mem_sdiff.mp hdv).2, hr⟩
  choose d hd using hh
  have hfresh : Disjoint C (pairEvents T d) := by
    apply Finset.disjoint_left.mpr
    intro p hp he
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
    exact (hd r).2.1 (hC (Finset.mem_image_of_mem Prod.snd hp))
  refine ⟨T, d, hTc, hd, hfresh,
    realized_union hit hreal (pairEvents_realized hit T d (fun r => (hd r).2.2)), ?_, ?_⟩
  · unfold DictionaryInvariant
    rw [paidDirections_union]
    apply Finset.union_subset
    · exact hC.trans (encodedDirections_mono s ((Finset.subset_insert _ _).trans
        (Finset.subset_insert _ _)))
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _,
        (Finset.mem_inter.mp (hd r).1).1⟩
  · rw [Finset.card_union_of_disjoint hfresh, pairEvents_card, hTc]

end SharedHitGeometry

end SharpRamseyFive.ResidualCertificate

namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B] in
lemma agrees_update (f : V → H) (E : Finset V) (s : State V H D B)
    (hs : Agrees f E s) (v : V) (C : Finset (B × D)) :
    Agrees f (insert v E) (Function.update s.1 v (f v), C) := by
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · simp
  · by_cases he : u = v
    · subst u; simp
    · simpa [Function.update_of_ne he] using hs u hu

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchorName_direction (C : Finset (B × D)) (S : Finset D)
    (d : D) (hd : d ∈ S) (r : B) : (anchorName C S d hd r).direction = d := by
  unfold anchorName
  split_ifs <;> rfl

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchorName_realized (hit : B → D → Prop) (C : Finset (B × D))
    (S : Finset D) (d : D) (hd : d ∈ S) (r : B) (hr : hit r d) :
    Realized hit (anchorName C S d hd r).requirements := by
  unfold anchorName
  split_ifs <;> simp_all [AnchorChoice.requirements, Realized]

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchor_req_card {C : Finset (B × D)} {S : Finset D} (a : AnchorChoice C S) :
    a.requirements.card ≤ 1 := by
  cases a <;> simp [AnchorChoice.requirements]

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchor_req_directions {C : Finset (B × D)} {S : Finset D}
    (a : AnchorChoice C S) : paidDirections a.requirements ⊆ {a.direction} := by
  cases a <;> simp [AnchorChoice.requirements, AnchorChoice.direction, paidDirections]
omit [Fintype D] [Fintype B] [DecidableEq B] in

lemma anchor_req_disjoint {C : Finset (B × D)} {S T : Finset D}
    (a : AnchorChoice C S) (b : AnchorChoice C T) (hne : a.direction ≠ b.direction) :
    Disjoint a.requirements b.requirements := by
  apply Finset.disjoint_left.mpr
  intro p ha hb
  have ha' := anchor_req_directions a (Finset.mem_image_of_mem Prod.snd ha)
  have hb' := anchor_req_directions b (Finset.mem_image_of_mem Prod.snd hb)
  exact hne ((Finset.mem_singleton.mp ha').symm.trans (Finset.mem_singleton.mp hb'))

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma rawCost_eq_weight (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) (a : Action lines K s)
    (henabled : ∀ c : OneChoice lines s, a = .inr (.inl c) → low = true) :
    rawCost lines rate denom K low s a =
      weight (fun p : B × D => rate p.2) (newEvents lines K s a) /
        denom ^ degree lines K s a := by
  rcases a with a | a
  · simp [rawCost, newEvents, degree, weight]
  rcases a with a | a
  · rw [henabled a rfl]
    simp [rawCost, newEvents, degree, oneCost, AnchorChoice.weight]
  rcases a with a | a
  · simp only [rawCost, newEvents, degree, twoCost, pow_one]
    rw [weight_union_fresh _ _ _ (anchor_req_disjoint _ _ a.2.2.2.2.2.property.1),
      AnchorChoice.weight, AnchorChoice.weight]
  · rfl

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma newEvents_card (K : ℕ) (hK : 2 ≤ K) (s : State V H D B) (a : Action lines K s) :
    (newEvents lines K s a).card ≤ K * degree lines K s a := by
  rcases a with a | a
  · simp [newEvents, degree]
  rcases a with a | a
  · simpa [newEvents, degree] using (anchor_req_card a.2.2.1).trans (by omega : 1 ≤ K)
  rcases a with a | a
  · change (a.2.2.2.1.requirements ∪ a.2.2.2.2.1.requirements).card ≤ K * 1
    have hc := Finset.card_union_le a.2.2.2.1.requirements a.2.2.2.2.1.requirements
    have h1 := anchor_req_card a.2.2.2.1
    have h2 := anchor_req_card a.2.2.2.2.1
    omega
  · simp only [newEvents, degree, witnessRequirements_card]
    have ht := (Finset.mem_powersetCard.mp a.2.2.2.2.1.property).2
    omega

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma step_weight (rate : D → ℝ≥0) (denom : ℝ) (hdenom : denom ≠ 0)
    (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s)
    (he : Enabled lines K low s a) (hs : s.2.card ≤ K * Fintype.card V) :
    weight (fun p : B × D => rate p.2) (advance lines K s a).2 =
      weight (fun p : B × D => rate p.2) s.2 *
        programCost lines rate denom K low s a * denom ^ degree lines K s a := by
  rw [programCost, ite_eq_left hs, rawCost_eq_weight lines rate denom K low s a he]
  rw [advance, weight_union_fresh _ _ _ (newEvents_fresh lines K s a)]
  field_simp

omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma coherent_step (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (E F : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (a : Action lines K s) (hEF : E ⊆ F)
    (hag : Agrees f F (advance lines K s a))
    (hdict : paidDirections (newEvents lines K s a) ⊆ encodedDirections (fun v => lines (f v)) F)
    (hreal : Realized hit (newEvents lines K s a))
    (hcard : F.card = E.card + degree lines K s a) :
    Coherent lines f hit K F (advance lines K s a) := by
  refine ⟨hag, ?_, realized_union hit hs.2.2.1 hreal, ?_⟩
  · change paidDirections (s.2 ∪ newEvents lines K s a) ⊆ _
    rw [paidDirections_union]
    exact Finset.union_subset
      (hs.2.1.trans (encodedDirections_mono _ hEF)) hdict
  · change (s.2 ∪ newEvents lines K s a).card ≤ _
    apply (Finset.card_union_le _ _).trans
    calc
      _ ≤ K * E.card + K * degree lines K s a :=
        Nat.add_le_add hs.2.2.2 (newEvents_card lines K hK s a)
      _ = _ := by rw [hcard, Nat.mul_add]

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] [DecidableEq B] in
lemma touched_anchor (f : V → H) (hit : B → D → Prop)
    (E : Finset V) (s : State V H D B) (hs : Agrees f E s) (v : V) (d : D)
    (hd : d ∈ touchedToEncoded (fun v => lines (f v)) hit E v) :
    ∃ u ∈ E, ∃ x : AnchorChoice s.2 (lines (s.1 u)),
      x.direction = d ∧ d ∈ lines (f v) ∧ Realized hit x.requirements := by
  classical
  obtain ⟨hgeom, r, hr⟩ := Finset.mem_filter.mp hd
  obtain ⟨hv, henc⟩ := Finset.mem_inter.mp hgeom
  obtain ⟨u, hu, hdu⟩ := Finset.mem_biUnion.mp henc
  have hdu' : d ∈ lines (s.1 u) := by rw [hs u hu]; exact hdu
  exact ⟨u, hu, anchorName s.2 _ d hdu' r,
    anchorName_direction _ _ _ _ _, hv, anchorName_realized hit _ _ _ _ _ hr⟩

omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_one (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (v : V) (hv : v ∉ E)
    (ha : 1 ≤ (touchedToEncoded (fun v => lines (f v)) hit E v).card) :
    ∃ a : Action lines K s, Coherent lines f hit K (insert v E) (advance lines K s a) ∧
      (insert v E).card = E.card + degree lines K s a ∧
      Enabled lines K true s a ∧ actionCharge lines K s a = 0 := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (touchedToEncoded (fun v => lines (f v)) hit E v).card)
  obtain ⟨u, hu, x, hxd, hdv, hxreal⟩ := touched_anchor lines f hit E s hs.1 v d hd
  let c : OneChoice lines s := ⟨v, u, x, f v, hxd ▸ hdv⟩
  let a : Action lines K s := .inr (.inl c)
  have hc : (insert v E).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv]
  refine ⟨a, ?_, hc, fun _ _ => rfl, rfl⟩
  apply coherent_step lines f hit K hK E (insert v E) s hs a (Finset.subset_insert _ _) _ _ hxreal hc
  · exact agrees_update f E s hs.1 v _
  · apply (anchor_req_directions x).trans
    intro z hz
    have hz' : z = x.direction := Finset.mem_singleton.mp hz
    apply Finset.mem_biUnion.mpr
    exact ⟨v, Finset.mem_insert_self _ _, hz' ▸ (hxd ▸ hdv)⟩
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_two (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (low : Bool) (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (v : V) (hv : v ∉ E)
    (ha : 2 ≤ (touchedToEncoded (fun v => lines (f v)) hit E v).card) :
    ∃ a : Action lines K s, Coherent lines f hit K (insert v E) (advance lines K s a) ∧
      (insert v E).card = E.card + degree lines K s a ∧
      Enabled lines K low s a ∧ actionCharge lines K s a = 1 := by
  classical
  obtain ⟨d, hd, e, he, hde⟩ := Finset.one_lt_card.mp (by omega :
    1 < (touchedToEncoded (fun v => lines (f v)) hit E v).card)
  obtain ⟨u, hu, x, hxd, hdv, hxreal⟩ := touched_anchor lines f hit E s hs.1 v d hd
  obtain ⟨w, hw, y, hye, hev, hyreal⟩ := touched_anchor lines f hit E s hs.1 v e he
  let c : TwoChoice lines s := ⟨v, u, w, x, y, f v,
    by simpa only [hxd, hye] using And.intro hde (And.intro hdv hev)⟩
  let a : Action lines K s := .inr (.inr (.inl c))
  have hc : (insert v E).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv]
  refine ⟨a, ?_, hc, ?_, rfl⟩
  · apply coherent_step lines f hit K hK E (insert v E) s hs a (Finset.subset_insert _ _) _ _
      (realized_union hit hxreal hyreal) hc
    · exact agrees_update f E s hs.1 v _
    · change paidDirections (x.requirements ∪ y.requirements) ⊆ _
      rw [paidDirections_union]
      apply Finset.union_subset
      · apply (anchor_req_directions x).trans
        intro z hz
        have hz' := Finset.mem_singleton.mp hz
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, hz' ▸ (hxd ▸ hdv)⟩
      · apply (anchor_req_directions y).trans
        intro z hz
        have hz' := Finset.mem_singleton.mp hz
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, hz' ▸ (hye ▸ hev)⟩
  · intro c' he
    simp [a] at he
end SharpRamseyFive.CertificateCover
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_MakePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)
omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma make_pair (f : V → H) (hf : Function.Injective f) (hit : B → D → Prop)
    (K : ℕ) (hK : 2 ≤ K) (low : Bool) (E : Finset V) (s : State V H D B)
    (hs : Coherent lines f hit K E s) (v u : V) (hv : v ∉ E) (hu : u ∉ E) (hne : v ≠ u)
    (hp : K ≤ (sharedBatches (outsideDirections (fun v => lines (f v)) E) hit v u).card) :
    ∃ a : Action lines K s,
      Coherent lines f hit K (insert v (insert u E)) (advance lines K s a) ∧
      (insert v (insert u E)).card = E.card + degree lines K s a ∧
      Enabled lines K low s a ∧ actionCharge lines K s a = 0 := by
  classical
  obtain ⟨T, d, hT, hd, _, _, _, _⟩ :=
    pair_step_witnesses (fun v => lines (f v)) hit E s.2 v u K hs.2.1 hs.2.2.1 hp
  have hmem (r : T) : d r ∈ PairDirections lines s (f v) (f u) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(hd r).1, ?_⟩
    intro hc
    exact (hd r).2.1 (hs.2.1 hc)
  let c : PairChoice lines K s := ⟨v, u, f v, ⟨f u, fun he => hne (hf he.symm)⟩,
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩, fun r => ⟨d r, hmem r⟩⟩
  let a : Action lines K s := .inr (.inr (.inr c))
  have hv' : v ∉ insert u E := by simp [hne, hv]
  have hc : (insert v (insert u E)).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv', Finset.card_insert_of_notMem hu,
      Nat.add_assoc]
  refine ⟨a, ?_, hc, ?_, rfl⟩
  · apply coherent_step lines f hit K hK E (insert v (insert u E)) s hs a
      ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)) _ _ _ hc
    · have hu' := agrees_update f (insert v E)
        (Function.update s.1 v (f v), s.2) (agrees_update f E s hs.1 v s.2) u
        (advance lines K s a).2
      simpa only [a, c, advance, newValues, Finset.insert_comm] using hu'
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, (Finset.mem_inter.mp (hd r).1).1⟩
    · intro p hp
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact (hd r).2.2
  · intro c' he
    simp [a] at he
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_root (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (low : Bool) (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (v : V) (hv : v ∉ E) :
    ∃ a : Action lines K s, Coherent lines f hit K (insert v E) (advance lines K s a) ∧
      (insert v E).card = E.card + degree lines K s a ∧
      Enabled lines K low s a ∧ actionCharge lines K s a = -8 := by
  let a : Action lines K s := .inl (v, f v)
  have hc : (insert v E).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv]
  refine ⟨a, ?_, hc, ?_, rfl⟩
  · apply coherent_step lines f hit K hK E (insert v E) s hs a
      (Finset.subset_insert _ _) (agrees_update f E s hs.1 v _) _ _ hc
    · simp [a, newEvents, paidDirections]
    · simp [a, newEvents, Realized]
  · intro c' he
    simp [a] at he

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma finish_append (K : ℕ) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w)) :
    finish lines K s (append lines K s w w') = finish lines K (finish lines K s w) w' := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _ w.2 w'

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma degreeSum_append (K : ℕ) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w)) :
    degreeSum lines K s (append lines K s w w') =
      degreeSum lines K s w + degreeSum lines K (finish lines K s w) w' := by
  induction n generalizing s with
  | zero => simp only [append, degreeSum, finish, dFinish, Nat.zero_add]
  | succ n ih =>
    simpa only [append, degreeSum, finish, dFinish, Nat.add_assoc] using
      congrArg (fun t => degree lines K s w.1 + t) (ih (advance lines K s w.1) w.2 w')

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma charge_append (K : ℕ) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w)) :
    charge lines K s (append lines K s w w') =
      charge lines K s w + charge lines K (finish lines K s w) w' := by
  induction n generalizing s with
  | zero => simp only [append, charge, dCharge, finish, dFinish, zero_add]
  | succ n ih =>
    simpa only [append, charge, dCharge, finish, dFinish, add_assoc] using
      congrArg (fun t => actionCharge lines K s w.1 + t) (ih (advance lines K s w.1) w.2 w')

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma traceOK_append (K : ℕ) (low : Bool) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w))
    (h : TraceOK lines K low s w) (h' : TraceOK lines K low (finish lines K s w) w') :
    TraceOK lines K low s (append lines K s w w') := by
  induction n generalizing s with
  | zero => exact h'
  | succ n ih => exact ⟨h.1, h.2.1, ih _ w.2 w' h.2.2 h'⟩

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq B] in
lemma one_le_degree (K : ℕ) (s : State V H D B) (a : Action lines K s) :
    1 ≤ degree lines K s a := by
  rcases a with a | a
  · exact le_rfl
  rcases a with a | a
  · exact le_rfl
  rcases a with a | a
  · exact le_rfl
  · norm_num [degree]
omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in

lemma length_le_degreeSum (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :
    n ≤ degreeSum lines K s w := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    have h1 := one_le_degree lines K s w.1
    have h2 := ih _ w.2
    change n + 1 ≤ _ + _
    omega
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma trace_weight (rate : D → ℝ≥0) (denom : ℝ) (hd : denom ≠ 0)
    (K : ℕ) (low : Bool) {n : ℕ} (s : State V H D B) (w : Word lines K n s)
    (hw : TraceOK lines K low s w) :
    weight (fun p : B × D => rate p.2) (finish lines K s w).2 =
      weight (fun p : B × D => rate p.2) s.2 *
        dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s w *
          denom ^ degreeSum lines K s w := by
  induction n generalizing s with
  | zero => simp [finish, dFinish, dWeight, degreeSum]
  | succ n ih =>
    change weight _ (finish lines K (advance lines K s w.1) w.2).2 = _
    rw [ih _ w.2 hw.2.2, step_weight lines rate denom hd K low s w.1 hw.2.1 hw.1]
    simp only [dWeight, degreeSum, pow_add]
    ring

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma segment_empty (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s) :
    Segment lines f hit K low E E s (n := 0) (PUnit.unit : Word lines K 0 s) := by
  exact ⟨hs, by simp [degreeSum], trivial⟩

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma segment_single (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (a : Action lines K s) (hf : Coherent lines f hit K F (advance lines K s a))
    (hc : F.card = E.card + degree lines K s a) (he : Enabled lines K low s a) :
    Segment lines f hit K low E F s (n := 1) (⟨a, PUnit.unit⟩ : Word lines K 1 s) := by
  refine ⟨hf, ?_, ?_⟩
  · simpa [degreeSum] using hc
  · exact ⟨hs.2.2.2.trans (Nat.mul_le_mul_left K (Finset.card_le_univ E)), he, trivial⟩
omit [Fintype H] [DecidableEq H] [Fintype D] in

lemma segment_append (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F G : Finset V) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w))
    (h : Segment lines f hit K low E F s w)
    (h' : Segment lines f hit K low F G (finish lines K s w) w') :
    Segment lines f hit K low E G s (append lines K s w w') := by
  refine ⟨?_, ?_, traceOK_append lines K low s w w' h.2.2 h'.2.2⟩
  · rw [finish_append]; exact h'.1
  · rw [degreeSum_append, ← Nat.add_assoc, ← h.2.1]
    exact h'.2.1
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_encoding (f : V → H) (hf : Function.Injective f) (hit : B → D → Prop)
    (K : ℕ) (hK : 2 ≤ K) (low : Bool) {E F : Finset V}
    (h : EncodingStep (fun v => lines (f v)) hit (if low then 1 else 2) K E F)
    (s : State V H D B) (hs : Coherent lines f hit K E s) :
    ∃ a : Action lines K s, Coherent lines f hit K F (advance lines K s a) ∧
      F.card = E.card + degree lines K s a ∧ Enabled lines K low s a ∧
        0 ≤ actionCharge lines K s a := by
  cases h with
  | anchor v hv ha =>
    cases low with
    | false =>
      obtain ⟨a, hh, hc, he, hq⟩ := make_two lines f hit K hK false E s hs v hv ha
      exact ⟨a, hh, hc, he, by omega⟩
    | true =>
      obtain ⟨a, hh, hc, he, hq⟩ := make_one lines f hit K hK E s hs v hv ha
      exact ⟨a, hh, hc, he, by omega⟩
  | pair v u hv hu hne hp =>
    obtain ⟨a, hh, hc, he, hq⟩ := make_pair lines f hf hit K hK low E s hs v u hv hu hne hp
    exact ⟨a, hh, hc, he, by omega⟩

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

theorem encoding_path_program (f : V → H) (hf : Function.Injective f)
    (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K) (low : Bool) {E F : Finset V}
    (h : Relation.ReflTransGen (EncodingStep (fun v => lines (f v)) hit
      (if low then 1 else 2) K) E F)
    (s : State V H D B) (hs : Coherent lines f hit K E s) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K low E F s w ∧
      0 ≤ charge lines K s w := by
  induction h with
  | refl => exact ⟨0, PUnit.unit, segment_empty lines f hit K low E s hs, le_rfl⟩
  | @tail F G h hFG ih =>
    obtain ⟨n, w, hw, hq⟩ := ih
    obtain ⟨a, ha, hc, he, hqa⟩ := make_encoding lines f hf hit K hK low hFG
      (finish lines K s w) hw.1
    let w' : Word lines K 1 (finish lines K s w) := ⟨a, PUnit.unit⟩
    refine ⟨1 + n, append lines K s w w', ?_, ?_⟩
    · exact segment_append lines f hit K low E F G s w w' hw
        (segment_single lines f hit K low F G _ hw.1 a ha hc he)
    · rw [charge_append]
      exact add_nonneg hq (by simpa [w', charge, dCharge] using hqa)

omit [Fintype H] [DecidableEq H] [Fintype D] in

lemma encode_set (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E R : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s) (c : ℤ)
    (hdis : Disjoint E R)
    (hmake : ∀ F : Finset V, E ⊆ F → ∀ s' : State V H D B,
      Coherent lines f hit K F s' → ∀ v ∈ R, v ∉ F →
      ∃ a : Action lines K s', Coherent lines f hit K (insert v F) (advance lines K s' a) ∧
        (insert v F).card = F.card + degree lines K s' a ∧
        Enabled lines K low s' a ∧ actionCharge lines K s' a = c) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K low E (E ∪ R) s w ∧
      charge lines K s w = c * R.card := by
  classical
  induction R using Finset.induction with
  | empty =>
    refine ⟨0, PUnit.unit, ?_, ?_⟩
    · simpa using segment_empty lines f hit K low E s hs
    · simp [charge, dCharge]
  | @insert v R hvR ih =>
    have hdis' : Disjoint E R := hdis.mono_right (Finset.subset_insert _ _)
    obtain ⟨n, w, hw, hq⟩ := ih hdis' (by
      intro F hEF s' hs' u hu hfu
      exact hmake F hEF s' hs' u (Finset.mem_insert_of_mem hu) hfu)
    have hvE : v ∉ E := fun hvE => Finset.disjoint_left.mp hdis hvE (Finset.mem_insert_self _ _)
    have hvF : v ∉ E ∪ R := by simp [hvE, hvR]
    obtain ⟨a, ha, hc, he, hqa⟩ := hmake (E ∪ R) Finset.subset_union_left
      (finish lines K s w) hw.1 v (Finset.mem_insert_self _ _) hvF
    let w' : Word lines K 1 (finish lines K s w) := ⟨a, PUnit.unit⟩
    refine ⟨1 + n, append lines K s w w', ?_, ?_⟩
    · have hh := segment_append lines f hit K low E (E ∪ R) (insert v (E ∪ R)) s w w' hw
        (segment_single lines f hit K low (E ∪ R) _ _ hw.1 a ha hc he)
      simpa only [Finset.union_insert] using hh
    · rw [charge_append, hq]
      change c * (R.card : ℤ) + (actionCharge lines K _ a + 0) = _
      rw [hqa, Finset.card_insert_of_notMem hvR, Nat.cast_add, Nat.cast_one]
      ring
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma residual_program (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (low : Bool) (F : Finset V) (s : State V H D B) (hs : Coherent lines f hit K F s)
    (roots : Finset {v // v ∉ F})
    (hsize : 10 * roots.card ≤ Fintype.card {v // v ∉ F})
    (hroot : ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
      ∃ d ∈ survivingDirections (fun v => lines (f v)) F v ∩
          survivingDirections (fun v => lines (f v)) F u,
      ∃ e ∈ survivingDirections (fun v => lines (f v)) F v ∩
          survivingDirections (fun v => lines (f v)) F w,
        d ≠ e ∧ (∃ r, hit r d) ∧ (∃ r, hit r e)) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K low F Finset.univ s w ∧
      0 ≤ charge lines K s w := by
  classical
  let R : Finset V := roots.image Subtype.val
  have hRc : R.card = roots.card := by
    dsimp [R]
    apply Finset.card_image_of_injective
    exact Subtype.val_injective
  have hdis : Disjoint F R := by
    apply Finset.disjoint_left.mpr
    intro v hv hR
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hR
    exact u.property hv
  obtain ⟨n, w, hw, hq⟩ := encode_set lines f hit K low F R s hs (-8) hdis (by
    intro G hFG s' hs' v hv hvg
    exact make_root lines f hit K hK low G s' hs' v hvg)
  let NR : Finset V := Finset.univ \ (F ∪ R)
  have hdisNR : Disjoint (F ∪ R) NR := Finset.disjoint_sdiff
  have hmake : ∀ G : Finset V, F ∪ R ⊆ G → ∀ s' : State V H D B,
      Coherent lines f hit K G s' → ∀ v ∈ NR, v ∉ G →
      ∃ a : Action lines K s', Coherent lines f hit K (insert v G) (advance lines K s' a) ∧
        (insert v G).card = G.card + degree lines K s' a ∧
        Enabled lines K low s' a ∧ actionCharge lines K s' a = 1 := by
    intro G hFG s' hs' v hv hvg
    have hvF : v ∉ F := fun hvF => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left R hvF)
    obtain ⟨u, hu, u', hu', _, _, _, d, hd, e, he, hde, hdp, hep⟩ := hroot ⟨v, hvF⟩
    have hdv : d ∈ lines (f v) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hd).1).1
    have hdu : d ∈ lines (f u.val) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hd).2).1
    have hev : e ∈ lines (f v) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).1).1
    have heu : e ∈ lines (f u'.val) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1
    have hdE : d ∈ encodedDirections (fun v => lines (f v)) G :=
      Finset.mem_biUnion.mpr ⟨u.val, hFG (Finset.mem_union_right F
        (Finset.mem_image_of_mem Subtype.val hu)), hdu⟩
    have heE : e ∈ encodedDirections (fun v => lines (f v)) G :=
      Finset.mem_biUnion.mpr ⟨u'.val, hFG (Finset.mem_union_right F
        (Finset.mem_image_of_mem Subtype.val hu')), heu⟩
    apply make_two lines f hit K hK low G s' hs' v hvg
    apply Finset.one_lt_card.mpr
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hdv, hdE⟩, hdp⟩,
      e, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hev, heE⟩, hep⟩, hde⟩
  obtain ⟨m, w', hw', hq'⟩ := encode_set lines f hit K low (F ∪ R) NR
    (finish lines K s w) hw.1 1 hdisNR hmake
  have hfull : (F ∪ R) ∪ NR = Finset.univ := by
    ext v
    simp only [NR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  refine ⟨m + n, append lines K s w w', ?_, ?_⟩
  · simpa only [hfull] using segment_append lines f hit K low F (F ∪ R) _ s w w' hw hw'
  · rw [charge_append, hq, hq', one_mul]
    have hr : Fintype.card {v // v ∉ F} = Fintype.card V - F.card := by
      rw [Fintype.card_subtype_compl]
      simp
    have hc : NR.card + (F.card + R.card) = Fintype.card V := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F ∪ R))
      simpa only [NR, Finset.card_univ, Finset.card_union_of_disjoint hdis] using hh
    rw [← hRc, hr] at hsize
    omega

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

theorem bad_program_high (f : V → H) (hf : Function.Injective f)
    (hit : B → D → Prop) [∀ r d, Decidable (hit r d)] (K J h : ℕ) (hK : 2 ≤ K) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2 - J) / (2 * K))
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤
      (touchedBatches (fun v => lines (f v)) hit v).card)
    (htrunc : ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K false E Finset.univ s w ∧
      0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
  classical
  obtain ⟨F, hpath, roots, hr, hroot⟩ := high_case_certificate_geometry
    (fun v => lines (f v)) hit E K J h hh hsize hbad
      (by
        intro d
        apply le_trans _ (htrunc d)
        apply Finset.card_le_card
        intro r hr
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hr) herr
  obtain ⟨n, w, hw, hq⟩ := encoding_path_program lines f hf hit K hK false hpath s hs
  obtain ⟨m, w', hw', hq'⟩ := residual_program lines f hit K hK false F
    (finish lines K s w) hw.1 roots hr hroot
  refine ⟨m + n, append lines K s w w', segment_append lines f hit K false E F _ s w w' hw hw', ?_, ?_⟩
  · rw [charge_append]; exact add_nonneg hq hq'
  · have hl := length_le_degreeSum lines K s (append lines K s w w')
    have hc := (segment_append lines f hit K false E F _ s w w' hw hw').2.1
    simp only [Finset.card_univ] at hc
    omega
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

 theorem bad_program_low (f : V → H) (hf : Function.Injective f)
    (hit : B → D → Prop) (K h : ℕ) (hK : 2 ≤ K) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2) / (2 * K))
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤
      (touchedBatches (fun v => lines (f v)) hit v).card)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K true E Finset.univ s w ∧
      0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
  obtain ⟨F, hpath, roots, hr, hroot⟩ := low_case_certificate_geometry
    (fun v => lines (f v)) hit E K h hh hsize hbad herr
  obtain ⟨n, w, hw, hq⟩ := encoding_path_program lines f hf hit K hK true hpath s hs
  obtain ⟨m, w', hw', hq'⟩ := residual_program lines f hit K hK true F
    (finish lines K s w) hw.1 roots hr hroot
  refine ⟨m + n, append lines K s w w', segment_append lines f hit K true E F _ s w w' hw hw', ?_, ?_⟩
  · rw [charge_append]; exact add_nonneg hq hq'
  · have hl := length_le_degreeSum lines K s (append lines K s w w')
    have hc := (segment_append lines f hit K true E F _ s w w' hw hw').2.1
    simp only [Finset.card_univ] at hc
    omega

omit [DecidableEq D] [DecidableEq B] in
lemma decoded_static_union_bound {F C : Type*} [Fintype F] [DecidableEq F]
    [Fintype C] [DecidableEq C]
    (rate : D → ℝ≥0) (requirements : C → Finset (B × D)) (decode : C → F)
    (events : F → Set ((B × D) → ℕ))
    (hm : ∀ f, MeasurableSet (events f))
    (hc : ∀ f ω, ω ∈ events f → ∃ c, decode c = f ∧ ω ∈ positiveEvent (requirements c)) :
    (∑ f, (poissonLaw (fun p : B × D => rate p.2)).real (events f)) ≤
      ∑ c, weight (fun p : B × D => rate p.2) (requirements c) := by
  classical
  calc
    _ ≤ ∑ f, ∑ c ∈ Finset.univ.filter (fun c => decode c = f),
        weight (fun p : B × D => rate p.2) (requirements c) := by
      apply Finset.sum_le_sum
      intro f _
      apply static_union_bound _ requirements _ (events f) (hm f)
      intro ω hω
      obtain ⟨c, hd, he⟩ := hc f ω hω
      exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, he⟩
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simp

end SharpRamseyFive.CertificateCover
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_emptyEvent (s : Finset ι) : MeasurableSet (emptyEvent s) := by
  exact MeasurableSet.pi (s.finite_toSet.countable) (fun _ _ => measurableSet_singleton 0)

omit [DecidableEq ι] in
lemma measure_emptyEvent (rate : ι → ℝ≥0) (s : Finset ι) :
    batchMeasure rate (emptyEvent s) = ENNReal.ofReal (Real.exp (-mass rate s)) := by
  rw [batchMeasure, emptyEvent, Measure.pi_pi_finset]
  simp_rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl
omit [DecidableEq ι] in

lemma integral_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    ∫ ω, emptyIndicator s ω ∂batchMeasure rate = Real.exp (-mass rate s) := by
  simp only [emptyIndicator]
  rw [integral_indicator_const _ (measurableSet_emptyEvent s),
    Measure.real, measure_emptyEvent, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp
omit [DecidableEq ι] in

lemma integrable_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    Integrable (emptyIndicator s) (batchMeasure rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_emptyEvent s)

omit [Fintype ι] in
lemma emptyIndicator_mul (s t : Finset ι) (ω : ι → ℕ) :
    emptyIndicator s ω * emptyIndicator t ω = emptyIndicator (s ∪ t) ω := by
  have hu : emptyEvent (s ∪ t) = emptyEvent s ∩ emptyEvent t := by
    ext x
    simp [emptyEvent, Set.mem_pi, or_imp, forall_and]
  rw [emptyIndicator, emptyIndicator, emptyIndicator, hu]
  by_cases hs : ω ∈ emptyEvent s <;> by_cases ht : ω ∈ emptyEvent t <;>
    simp [hs, ht]

omit [Fintype ι] in
lemma mass_union_inter (rate : ι → ℝ≥0) (s t : Finset ι) :
    mass rate (s ∪ t) + mass rate (s ∩ t) = mass rate s + mass rate t := by
  exact Finset.sum_union_inter

omit [DecidableEq ι] in

lemma integrable_centeredFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    Integrable (centeredFactor s b) (batchMeasure rate) :=
  (integrable_emptyIndicator rate s).sub (integrable_const b)
omit [DecidableEq ι] in

lemma integral_centeredFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    ∫ ω, centeredFactor s b ω ∂batchMeasure rate = Real.exp (-mass rate s) - b := by
  simp only [centeredFactor]
  rw [integral_sub (integrable_emptyIndicator rate s)
    (integrable_const b), integral_emptyIndicator]
  simp

lemma integral_centeredFactor_mul (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) :
    (∫ ω, centeredFactor s b ω * centeredFactor t b ω ∂batchMeasure rate) =
      (Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b) +
      Real.exp (-(mass rate s + mass rate t)) *
        (Real.exp (mass rate (s ∩ t)) - 1) := by
  have he : (fun ω => centeredFactor s b ω * centeredFactor t b ω) =
      fun ω => emptyIndicator (s ∪ t) ω - b * emptyIndicator s ω -
        b * emptyIndicator t ω + b ^ 2 := by
    funext ω
    rw [centeredFactor, centeredFactor]
    have := emptyIndicator_mul s t ω
    nlinarith [this]
  rw [he]
  have hs := integrable_emptyIndicator rate s
  have ht := integrable_emptyIndicator rate t
  have hu := integrable_emptyIndicator rate (s ∪ t)
  have h1 := integral_sub hu (hs.const_mul b)
  have h2 := integral_sub (hu.sub (hs.const_mul b)) (ht.const_mul b)
  have h3 := integral_add ((hu.sub (hs.const_mul b)).sub (ht.const_mul b))
    (integrable_const (b ^ 2))
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h3, h2, h1]
  simp only [integral_const_mul, integral_emptyIndicator, integral_const,
    probReal_univ, one_smul]
  have hmass := mass_union_inter rate s t
  have hu : Real.exp (-mass rate (s ∪ t)) =
      Real.exp (-(mass rate s + mass rate t)) * Real.exp (mass rate (s ∩ t)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hp : Real.exp (-mass rate s) * Real.exp (-mass rate t) =
      Real.exp (-(mass rate s + mass rate t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hu]
  nlinarith [hp]

omit [Fintype ι] [DecidableEq ι] in
lemma emptyIndicator_nonneg (s : Finset ι) (ω : ι → ℕ) : 0 ≤ emptyIndicator s ω := by
  unfold emptyIndicator
  apply Set.indicator_nonneg
  intro _ _
  norm_num

omit [Fintype ι] [DecidableEq ι] in
lemma abs_centeredFactor_le_one (s : Finset ι) (b : ℝ) (hb : b ∈ Set.Icc 0 1)
    (ω : ι → ℕ) : |centeredFactor s b ω| ≤ 1 := by
  unfold centeredFactor emptyIndicator
  by_cases h : ω ∈ emptyEvent s <;> simp [h, abs_le] <;> constructor <;> linarith [hb.1, hb.2]

omit [Fintype ι] [DecidableEq ι] in
lemma centeredFactor_of_hit (s : Finset ι) (b : ℝ) (ω : ι → ℕ)
    {i : ι} (hi : i ∈ s) (hhit : ω i ≠ 0) : centeredFactor s b ω = -b := by
  have h : ω ∉ emptyEvent s := by
    intro he
    exact hhit (he i hi)
  simp [centeredFactor, emptyIndicator, h]
omit [DecidableEq ι] in

lemma integral_abs_centeredFactor_le (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    (∫ ω, |centeredFactor s b ω| ∂batchMeasure rate) ≤ Real.exp (-mass rate s) + |b| := by
  calc
    _ ≤ ∫ ω, emptyIndicator s ω + |b| ∂batchMeasure rate := by
      apply integral_mono (integrable_centeredFactor rate s b).abs
        ((integrable_emptyIndicator rate s).add (integrable_const |b|))
      intro ω
      dsimp [centeredFactor]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (emptyIndicator_nonneg s ω)])
    _ = _ := by
      rw [integral_add (integrable_emptyIndicator rate s) (integrable_const |b|),
        integral_emptyIndicator]
      simp

lemma abs_exp_neg_sub_exp_neg_le {a b c : ℝ} (ha : c ≤ a) (hb : c ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-c) * |a - b| := by
  have ordered : ∀ {a b : ℝ}, c ≤ a → a ≤ b →
      Real.exp (-a) - Real.exp (-b) ≤ Real.exp (-c) * (b - a) := by
    intro a b hca hab
    have he := Real.add_one_le_exp (a - b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have hprod : Real.exp (-a) * Real.exp (a - b) = Real.exp (-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hprod] at hm
    have hec : Real.exp (-a) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (neg_le_neg hca)
    have hd := mul_le_mul_of_nonneg_right hec (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using ordered ha hab
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg hba))),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    simpa only [neg_sub] using ordered hb hba

omit [DecidableEq ι] in

lemma abs_integral_centeredFactor_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hmass : mass rate s = L * lam)
    (hlam : c ≤ lam) (hbase : c ≤ base) :
    |∫ ω, centeredFactor s (Real.exp (-L * base)) ω ∂batchMeasure rate| ≤
      L * Real.exp (-L * c) * |lam - base| := by
  rw [integral_centeredFactor, hmass]
  have he := abs_exp_neg_sub_exp_neg_le
    (mul_le_mul_of_nonneg_left hlam hL) (mul_le_mul_of_nonneg_left hbase hL)
  simpa only [neg_mul, mul_neg, ← mul_sub, abs_mul, abs_of_nonneg hL, mul_comm,
    mul_left_comm, mul_assoc] using he

omit [DecidableEq ι] in

lemma integral_abs_centeredFactor_exp_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hmass : mass rate s = L * lam)
    (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |centeredFactor s (Real.exp (-L * base)) ω| ∂batchMeasure rate) ≤
      2 * Real.exp (-L * c) := by
  have h1 := integral_abs_centeredFactor_le rate s (Real.exp (-L * base))
  rw [hmass, abs_of_pos (Real.exp_pos _)] at h1
  have h2 : Real.exp (-(L * lam)) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

lemma integrable_centeredFactor_mul (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) :
    Integrable (fun ω => centeredFactor s b ω * centeredFactor t b ω) (batchMeasure rate) := by
  have he : (fun ω => centeredFactor s b ω * centeredFactor t b ω) =
      fun ω => emptyIndicator (s ∪ t) ω - b * emptyIndicator s ω -
        b * emptyIndicator t ω + b ^ 2 := by
    funext ω
    rw [centeredFactor, centeredFactor]
    nlinarith [emptyIndicator_mul s t ω]
  rw [he]
  exact (((integrable_emptyIndicator rate (s ∪ t)).sub
    ((integrable_emptyIndicator rate s).const_mul b)).sub
    ((integrable_emptyIndicator rate t).const_mul b)).add (integrable_const (b^2))

omit [Fintype ι] [DecidableEq ι] in
lemma mass_nonneg (rate : ι → ℝ≥0) (s : Finset ι) : 0 ≤ mass rate s := by
  exact Finset.sum_nonneg (fun i _ => (rate i).coe_nonneg)

omit [Fintype ι] [DecidableEq ι] in
lemma mass_mono (rate : ι → ℝ≥0) {s t : Finset ι} (hst : s ⊆ t) :
    mass rate s ≤ mass rate t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (rate i).coe_nonneg)

lemma one_sub_exp_neg_le (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

omit [Fintype ι] in

lemma covariance_le (rate : ι → ℝ≥0) (s t : Finset ι) :
    Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1) ≤
    mass rate (s ∩ t) * Real.exp (-mass rate (s ∪ t)) := by
  have hu := mass_union_inter rate s t
  have he : Real.exp (-(mass rate s + mass rate t)) =
      Real.exp (-mass rate (s ∪ t)) * Real.exp (-mass rate (s ∩ t)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  rw [he]
  have hh : Real.exp (-mass rate (s ∩ t)) * Real.exp (mass rate (s ∩ t)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hb := mul_le_mul_of_nonneg_left (one_sub_exp_neg_le (mass rate (s ∩ t)))
    (Real.exp_pos (-mass rate (s ∪ t))).le
  calc
    _ = Real.exp (-mass rate (s ∪ t)) * (1 - Real.exp (-mass rate (s ∩ t))) := by
      rw [mul_assoc, mul_sub, hh, mul_one]
    _ ≤ _ := by simpa only [mul_comm] using hb
omit [Fintype ι] in

lemma covariance_nonneg (rate : ι → ℝ≥0) (s t : Finset ι) :
    0 ≤ Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1) := by
  apply mul_nonneg (Real.exp_pos _).le
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mass_nonneg rate _))

lemma abs_integral_centeredFactor_mul_le_mass (rate : ι → ℝ≥0)
    (s t : Finset ι) (b : ℝ) :
    |∫ ω, centeredFactor s b ω * centeredFactor t b ω ∂batchMeasure rate| ≤
      |Real.exp (-mass rate s) - b| * |Real.exp (-mass rate t) - b| +
      mass rate (s ∩ t) * Real.exp (-mass rate (s ∪ t)) := by
  rw [integral_centeredFactor_mul]
  calc
    _ ≤ |(Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b)| +
        |Real.exp (-(mass rate s + mass rate t)) *
          (Real.exp (mass rate (s ∩ t)) - 1)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (covariance_nonneg rate s t)]
      exact add_le_add le_rfl (covariance_le rate s t)

lemma abs_integral_centeredFactor_mul_exp_le (rate : ι → ℝ≥0)
    (s t : Finset ι) {L lam₁ lam₂ base c θ : ℝ}
    (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hs : mass rate s = L * lam₁) (ht : mass rate t = L * lam₂)
    (hi : mass rate (s ∩ t) = L * θ)
    (h₁ : c ≤ lam₁) (h₂ : c ≤ lam₂) (hbase : c ≤ base) :
    |∫ ω, centeredFactor s (Real.exp (-L * base)) ω *
      centeredFactor t (Real.exp (-L * base)) ω ∂batchMeasure rate| ≤
        L ^ 2 * Real.exp (-L * c) * (|lam₁ - base| * |lam₂ - base| + θ) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hi0 := mass_nonneg rate (s ∩ t)
  have hθ : 0 ≤ θ := by rw [hi] at hi0; nlinarith
  have hu : L * c ≤ mass rate (s ∪ t) := by
    calc
      _ ≤ L * lam₁ := mul_le_mul_of_nonneg_left h₁ hL0
      _ = mass rate s := hs.symm
      _ ≤ mass rate (s ∪ t) := mass_mono rate Finset.subset_union_left
  have huse : Real.exp (-mass rate (s ∪ t)) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by linarith)
  have hepos := Real.exp_pos (-L * c)
  have hele : Real.exp (-L * c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e₁ := abs_integral_centeredFactor_le rate s hL0 hs h₁ hbase
  have e₂ := abs_integral_centeredFactor_le rate t hL0 ht h₂ hbase
  rw [integral_centeredFactor] at e₁ e₂
  have hmul := mul_le_mul e₁ e₂ (abs_nonneg _)
    (mul_nonneg (mul_nonneg hL0 hepos.le) (abs_nonneg _))
  have hab := mul_nonneg (abs_nonneg (lam₁ - base)) (abs_nonneg (lam₂ - base))
  have hpow : Real.exp (-L * c) ^ 2 ≤ Real.exp (-L * c) := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (sq_nonneg L) hab)
  have hcov := mul_le_mul_of_nonneg_left huse hi0
  rw [hi] at hcov
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hcov' := mul_le_mul_of_nonneg_right hLsq (mul_nonneg hθ hepos.le)
  have hfinal := abs_integral_centeredFactor_mul_le_mass rate s t (Real.exp (-L * base))
  nlinarith

lemma integrable_scoreTerm_mul (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    Integrable (fun ω => scoreTerm s b ownS ω * scoreTerm t b ownT ω)
      (scheduleMeasure rate R) := by
  simp only [scoreTerm, ← Finset.prod_mul_distrib]
  apply Integrable.fintype_prod (f := fun r ω => (if ownS r then centeredFactor s b ω else 0) * (if ownT r then centeredFactor t b ω else 0))
  intro r
  cases hs : ownS r <;> cases ht : ownT r <;>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero]
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_centeredFactor_mul rate s t b

lemma integral_scoreTerm_mul (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    (∫ ω, scoreTerm s b ownS ω * scoreTerm t b ownT ω ∂scheduleMeasure rate R) =
      ∏ r, if ownS r && ownT r then pairMean rate s t b else 0 := by
  simp only [scoreTerm, ← Finset.prod_mul_distrib, scheduleMeasure]
  rw [integral_fintype_prod_eq_prod (f := fun r ω => (if ownS r then centeredFactor s b ω else 0) * (if ownT r then centeredFactor t b ω else 0))]
  congr 1
  funext r
  cases hs : ownS r <;> cases ht : ownT r <;>
    simp [integral_centeredFactor_mul, pairMean]

lemma abs_integral_scoreTerm_mul_le (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    |∫ ω, scoreTerm s b ownS ω * scoreTerm t b ownT ω ∂scheduleMeasure rate R| ≤
      |pairMean rate s t b| ^ R := by
  rw [integral_scoreTerm_mul, Finset.abs_prod]
  calc
    _ ≤ ∏ _ : Fin R, |pairMean rate s t b| := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro r _
      split_ifs <;> simp
    _ = _ := by simp

variable {κ : Type*}

lemma integral_typicalScore_sq (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) :
    (∫ ω, (typicalScore H directions b own ω)^2 ∂scheduleMeasure rate R) =
      ∑ h ∈ H, ∑ k ∈ H,
        ∏ r, if own h r && own k r then pairMean rate (directions h) (directions k) b else 0 := by
  simp only [typicalScore, pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum H (fun h _ =>
    integrable_finsetSum H (fun k _ =>
      integrable_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k)))]
  apply Finset.sum_congr rfl
  intro h _
  rw [integral_finsetSum H (fun k _ =>
      integrable_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k))]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_IntegralTypicalScoreSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
lemma integral_typicalScore_sq_le (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) :
    (∫ ω, (typicalScore H directions b own ω)^2 ∂scheduleMeasure rate R) ≤
      ∑ h ∈ H, ∑ k ∈ H, |pairMean rate (directions h) (directions k) b|^R := by
  rw [integral_typicalScore_sq]
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro k _
  rw [← integral_scoreTerm_mul]
  exact (le_abs_self _).trans
    (abs_integral_scoreTerm_mul_le rate (directions h) (directions k) b (own h) (own k))

omit [Fintype ι] [DecidableEq ι] in

lemma abs_maskedFactor_le_one (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    (own touched : Bool) (ω : ι → ℕ) : |maskedFactor s b own touched ω| ≤ 1 := by
  cases own <;> cases touched <;> simp [maskedFactor, abs_centeredFactor_le_one s b hb ω,
    abs_of_nonneg hb.1, hb.2]
omit [Fintype ι] [DecidableEq ι] in

lemma abs_maskedTerm_le_one {R : ℕ} (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) :
    |maskedTerm s b own touched ω| ≤ 1 := by
  rw [maskedTerm, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => abs_maskedFactor_le_one s hb _ _ _)

omit [DecidableEq ι] in
lemma integrable_schedule_of_abs_le (rate : ι → ℝ≥0) {R : ℕ}
    (f : (Fin R → ι → ℕ) → ℝ) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f (scheduleMeasure rate R) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using h ω)
omit [DecidableEq ι] in

lemma integral_maskedFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ)
    (own touched : Bool) :
    (∫ ω, maskedFactor s b own touched ω ∂batchMeasure rate) =
      if own then (if touched then -b else Real.exp (-mass rate s) - b) else 0 := by
  cases own <;> cases touched <;> simp [maskedFactor, integral_centeredFactor]
omit [DecidableEq ι] in

lemma integral_maskedTerm (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (b : ℝ)
    (own touched : Fin R → Bool) :
    (∫ ω, maskedTerm s b own touched ω ∂scheduleMeasure rate R) =
      ∏ r, if own r then (if touched r then -b else Real.exp (-mass rate s) - b) else 0 := by
  unfold maskedTerm scheduleMeasure
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_maskedFactor]
omit [DecidableEq ι] in

lemma integral_abs_maskedFactor_exp_le (rate : ι → ℝ≥0) (s : Finset ι)
    (own touched : Bool) {L lam base c : ℝ} (hL : 0 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |maskedFactor s (Real.exp (-L * base)) own touched ω| ∂batchMeasure rate) ≤
      2 * Real.exp (-L * c) := by
  have he := Real.exp_pos (-L * c)
  have hb : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  cases own <;> cases touched <;> simp only [maskedFactor, Bool.false_eq_true, ↓reduceIte]
  · simp only [abs_zero, integral_zero]; positivity
  · simp only [abs_zero, integral_zero]; positivity
  · exact integral_abs_centeredFactor_exp_le rate s hL hmass hlam hbase
  · simp only [abs_neg, abs_of_pos (Real.exp_pos _), integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    linarith
omit [DecidableEq ι] in

lemma integral_abs_maskedTerm_exp_le (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι)
    (own touched : Fin R → Bool) {L lam base c : ℝ} (hL : 0 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |maskedTerm s (Real.exp (-L * base)) own touched ω| ∂scheduleMeasure rate R) ≤
      (2 * Real.exp (-L * c)) ^ R := by
  simp only [maskedTerm, Finset.abs_prod, scheduleMeasure]
  rw [integral_fintype_prod_eq_prod (f := fun r ω =>
    |maskedFactor s (Real.exp (-L * base)) (own r) (touched r) ω|)]
  calc
    _ ≤ ∏ _ : Fin R, 2 * Real.exp (-L * c) := by
      apply Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
      intro r _
      exact integral_abs_maskedFactor_exp_le rate s (own r) (touched r) hL hmass hlam hbase
    _ = _ := by simp

omit [DecidableEq ι] in

lemma abs_integral_maskedTerm_le_untouched (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (own touched : Fin R → Bool) {L base c delta alpha : ℝ}
    (hL : 1 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : c ≤ base + delta - alpha) (hbase : c ≤ base) (ha : 0 ≤ alpha) :
    |∫ ω, maskedTerm s (Real.exp (-L * base)) own touched ω ∂scheduleMeasure rate R| ≤
      (L * Real.exp (-L * c)) ^ R * (|delta| + alpha) ^ (untouchedBatches touched).card := by
  have hL0 : 0 ≤ L := by linarith
  have he := (Real.exp_pos (-L * c)).le
  have hd : 0 ≤ |delta| + alpha := add_nonneg (abs_nonneg _) ha
  have hu := abs_integral_centeredFactor_le rate s hL0 hmass hinternal hbase
  rw [integral_centeredFactor] at hu
  have hdif : |base + delta - alpha - base| ≤ |delta| + alpha := by
    calc
      |base + delta - alpha - base| = |delta - alpha| := by congr 1; ring
      _ ≤ |delta| + |alpha| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg ha]
  have hu' := hu.trans (mul_le_mul_of_nonneg_left hdif (mul_nonneg hL0 he))
  have hb : Real.exp (-L * base) ≤ L * Real.exp (-L * c) := by
    have h₁ : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h₂ := mul_le_mul_of_nonneg_right hL he
    nlinarith
  rw [integral_maskedTerm, Finset.abs_prod]
  calc
    _ ≤ ∏ r, (L * Real.exp (-L * c)) * (if touched r then 1 else |delta| + alpha) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro r _
      cases ho : own r <;> cases ht : touched r <;>
        simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_zero, mul_one]
      · exact mul_nonneg (mul_nonneg hL0 he) hd
      · exact mul_nonneg hL0 he
      · exact hu'
      · simpa only [abs_of_pos (Real.exp_pos _)] using hb
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_ite, untouchedBatches]
omit [DecidableEq ι] in

lemma abs_integral_maskedTerm_le_designations (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (own touched : Fin R → Bool) {L base c delta alpha : ℝ}
    (hL : 1 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : c ≤ base + delta - alpha) (hbase : c ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches touched).card) (hK : K ≤ N) :
    |∫ ω, maskedTerm s (Real.exp (-L * base)) own touched ω ∂scheduleMeasure rate R| ≤
      (2 * L * Real.exp (-L * c)) ^ R * (|delta| ^ N + alpha ^ K) := by
  have hNR : N ≤ R := hN.trans (by simpa using Finset.card_le_univ (untouchedBatches touched))
  have hKpow : alpha ^ N ≤ alpha ^ K :=
    pow_le_pow_of_le_one ha (by linarith [abs_nonneg delta]) hK
  have h2pow : (2 : ℝ) ^ (N - 1) ≤ 2 ^ R :=
    pow_le_pow_right₀ (by norm_num) ((Nat.sub_le N 1).trans hNR)
  have hsplit : (|delta| + alpha) ^ (untouchedBatches touched).card ≤
      2 ^ R * (|delta| ^ N + alpha ^ K) := calc
    _ ≤ (|delta| + alpha) ^ N := pow_le_pow_of_le_one (by positivity) hd hN
    _ ≤ 2 ^ (N - 1) * (|delta| ^ N + alpha ^ N) := add_pow_le (abs_nonneg _) ha N
    _ ≤ _ := mul_le_mul h2pow (add_le_add le_rfl hKpow) (by positivity) (by positivity)
  calc
    _ ≤ (L * Real.exp (-L * c)) ^ R * (|delta| + alpha) ^ (untouchedBatches touched).card :=
      abs_integral_maskedTerm_le_untouched rate s own touched hL hmass hinternal hbase ha
    _ ≤ (L * Real.exp (-L * c)) ^ R * (2 ^ R * (|delta| ^ N + alpha ^ K)) :=
      mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; congr 2; ring

lemma two_mul_le_exp_small {L : ℝ} (hL : 10000 ≤ L) :
    2 * L ≤ Real.exp ((3 / 50 : ℝ) * L) := by
  have hL0 : 0 ≤ L := by linarith
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (3 / 50 : ℝ) * L by positivity)
  have hs : 10000 * L ≤ L ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hL0]
  nlinarith

lemma two_mul_score_attenuation {L : ℝ} (hL : 10000 ≤ L) (R : ℕ) :
    (2 * L * Real.exp (-(37 / 50 : ℝ) * L)) ^ R ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) := by
  have h := mul_le_mul_of_nonneg_right (two_mul_le_exp_small hL)
    (Real.exp_pos (-(37 / 50 : ℝ) * L)).le
  rw [← Real.exp_add] at h
  have heq : (3 / 50 : ℝ) * L + -(37 / 50 : ℝ) * L = -(17 / 25 : ℝ) * L := by ring
  rw [heq] at h
  have hp := pow_le_pow_left₀ (show 0 ≤ 2 * L * Real.exp (-(37 / 50 : ℝ) * L) by
    have : 0 ≤ L := by linarith
    positivity) h R
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

omit [DecidableEq ι] in

lemma simple_singleton_attenuation (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (own touched : Fin R → Bool) {L base delta alpha : ℝ}
    (hL : 10000 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches touched).card) (hK : K ≤ N) :
    |∫ ω, maskedTerm s (Real.exp (-L * base)) own touched ω ∂scheduleMeasure rate R| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) * (|delta| ^ N + alpha ^ K) := by
  have h := abs_integral_maskedTerm_le_designations rate s own touched
    (show 1 ≤ L by linarith) hmass hinternal hbase ha hd hN hK
  apply h.trans
  simpa only [neg_mul, mul_comm L (37 / 50 : ℝ)] using
    mul_le_mul_of_nonneg_right (two_mul_score_attenuation hL R)
    (show 0 ≤ |delta| ^ N + alpha ^ K by positivity)

omit [Fintype ι] [DecidableEq ι] in
lemma hitIndicator_eq (i : ι) (ω : ι → ℕ) :
    hitIndicator i ω = if ω i = 0 then 0 else 1 := by
  simp only [hitIndicator, emptyIndicator, emptyEvent
    ]
  by_cases h : ω i = 0 <;> simp [h]
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_nonneg (i : ι) (ω : ι → ℕ) : 0 ≤ hitIndicator i ω := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_le_one (i : ι) (ω : ι → ℕ) : hitIndicator i ω ≤ 1 := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [DecidableEq ι] in

lemma integral_hitIndicator (rate : ι → ℝ≥0) (i : ι) :
    (∫ ω, hitIndicator i ω ∂batchMeasure rate) = 1 - Real.exp (-(rate i : ℝ)) := by
  unfold hitIndicator
  rw [integral_sub (integrable_const 1) (integrable_emptyIndicator rate {i}),
    integral_emptyIndicator]
  simp [mass]
omit [Fintype ι] [DecidableEq ι] in

lemma maskedFactor_mul_hit (s : Finset ι) (i : ι) (hi : i ∈ s) (b : ℝ)
    (own touched : Bool) (ω : ι → ℕ) :
    maskedFactor s b own touched ω * hitIndicator i ω =
      (if own then -b else 0) * hitIndicator i ω := by
  rw [hitIndicator_eq]
  by_cases hz : ω i = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, mul_one]
    have hh : ω ∉ emptyEvent s := by
      intro h
      exact hz (h i hi)
    cases own <;> cases touched <;> simp [maskedFactor, centeredFactor_of_hit s b ω hi hz]
omit [DecidableEq ι] in

lemma integral_abs_maskedFactor_hit_le (rate : ι → ℝ≥0)
    (s : Finset ι) (i : ι) (hi : i ∈ s) (own touched : Bool)
    {L base c : ℝ} (hL : 0 ≤ L) (hbase : c ≤ base) :
    (∫ ω, |maskedFactor s (Real.exp (-L * base)) own touched ω| * hitIndicator i ω
      ∂batchMeasure rate) ≤ Real.exp (-L * c) * (rate i : ℝ) := by
  have heq : (fun ω => |maskedFactor s (Real.exp (-L * base)) own touched ω| * hitIndicator i ω) =
      fun ω => (if own then Real.exp (-L * base) else 0) * hitIndicator i ω := by
    funext ω
    rw [← abs_of_nonneg (hitIndicator_nonneg i ω), ← abs_mul, maskedFactor_mul_hit s i hi]
    cases own <;>
      simp [abs_mul, abs_of_nonneg (hitIndicator_nonneg i ω), abs_of_pos (Real.exp_pos _)]
  rw [heq, integral_const_mul, integral_hitIndicator]
  have hnonneg : 0 ≤ 1 - Real.exp (-(rate i : ℝ)) := by
    have : Real.exp (-(rate i : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate i).coe_nonneg)
    linarith
  have hb : Real.exp (-L * base) ≤ Real.exp (-L * c) := Real.exp_le_exp.mpr (by nlinarith)
  cases own
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul]; positivity
  · simp only [↓reduceIte]
    exact mul_le_mul hb (one_sub_exp_neg_le (rate i : ℝ)) hnonneg (Real.exp_pos _).le

omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_nonneg {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    0 ≤ forcedHits i T ω := Finset.prod_nonneg (fun _ _ => hitIndicator_nonneg _ _)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
omit [Fintype ι] [DecidableEq ι] in
lemma forcedHits_le_one {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    forcedHits i T ω ≤ 1 := Finset.prod_le_one (fun _ _ => hitIndicator_nonneg _ _)
      (fun _ _ => hitIndicator_le_one _ _)

omit [Fintype ι] [DecidableEq ι] in
lemma abs_maskedTerm_mul_forcedHits {R : ℕ} (s : Finset ι) (i : ι)
    (T : Finset (Fin R)) (b : ℝ) (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) :
    |maskedTerm s b own touched ω| * forcedHits i T ω =
      ∏ r, (|maskedFactor s b (own r) (touched r) (ω r)| *
        if r ∈ T then hitIndicator i (ω r) else 1) := by
  simp only [maskedTerm, Finset.abs_prod, Finset.prod_mul_distrib,
    Finset.prod_ite_mem, Finset.univ_inter, forcedHits]
omit [DecidableEq ι] in

lemma integral_abs_maskedTerm_forcedHits_le (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (i : ι) (hi : i ∈ s) (T : Finset (Fin R))
    (own touched : Fin R → Bool) {L lam base c : ℝ} (hL : 0 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |maskedTerm s (Real.exp (-L * base)) own touched ω| * forcedHits i T ω
      ∂scheduleMeasure rate R) ≤
      (2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ T.card := by
  simp_rw [abs_maskedTerm_mul_forcedHits]
  unfold scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω =>
    |maskedFactor s (Real.exp (-L * base)) (own r) (touched r) ω| *
        if r ∈ T then hitIndicator i ω else 1)]
  calc
    _ ≤ ∏ r, (2 * Real.exp (-L * c)) * (if r ∈ T then (rate i : ℝ) else 1) := by
      apply Finset.prod_le_prod
      · intro r _
        apply integral_nonneg
        intro ω
        apply mul_nonneg (abs_nonneg _)
        split
        · exact hitIndicator_nonneg _ _
        · norm_num
      · intro r _
        by_cases hr : r ∈ T
        · simp only [hr, ↓reduceIte]
          have h := integral_abs_maskedFactor_hit_le rate s i hi (own r) (touched r) hL hbase
          have he := Real.exp_pos (-L * c)
          have hi0 : 0 ≤ (rate i : ℝ) := (rate i).coe_nonneg
          nlinarith
        · simp only [hr, ↓reduceIte, mul_one]
          exact integral_abs_maskedFactor_exp_le rate s _ _ hL hmass hlam hbase
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [Finset.prod_ite_mem]

omit [Fintype ι] [DecidableEq ι] in

lemma overloaded_eq_empty {R J : ℕ} (s : Finset ι) (h : R < J) :
    (overloaded s J : Set (Fin R → ι → ℕ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω he
  obtain ⟨i, hi, hJ⟩ := he
  have hc : (hitBatches i ω).card ≤ R := by
    simpa only [hitBatches, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun r : Fin R => ω r i ≠ 0) Finset.univ)
  omega
omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_eq_one_of_subset {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) (h : T ⊆ hitBatches i ω) : forcedHits i T ω = 1 := by
  apply Finset.prod_eq_one
  intro r hr
  rw [hitIndicator_eq]
  have hz : ω r i ≠ 0 := (Finset.mem_filter.mp (h hr)).2
  simp [hz]
omit [Fintype ι] [DecidableEq ι] in

lemma overload_indicator_le_certificates {R : ℕ} (s : Finset ι) (J : ℕ)
    (ω : Fin R → ι → ℕ) :
    (overloaded s J).indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
  have hnonneg : ∀ i, 0 ≤ ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
    intro i
    exact Finset.sum_nonneg (fun T _ => forcedHits_nonneg i T ω)
  by_cases h : ω ∈ overloaded s J
  · rw [Set.indicator_of_mem h]
    obtain ⟨i, hi, hcard⟩ := h
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
    have hTm : T ∈ (Finset.univ : Finset (Fin R)).powersetCard J := by
      simp only [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hTc⟩
    calc
      1 = forcedHits i T ω := (forcedHits_eq_one_of_subset i T ω hT).symm
      _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i U ω :=
        Finset.single_le_sum (fun U _ => forcedHits_nonneg i U ω) hTm
      _ ≤ _ := Finset.single_le_sum (fun i _ => hnonneg i) hi
  · rw [Set.indicator_of_notMem h]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
omit [DecidableEq ι] in

lemma integrable_abs_maskedTerm_forcedHits (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1) (own touched : Fin R → Bool)
    (i : ι) (T : Finset (Fin R)) :
    Integrable (fun ω => |maskedTerm s b own touched ω| * forcedHits i T ω)
      (scheduleMeasure rate R) := by
  apply integrable_schedule_of_abs_le rate _ 1
  intro ω
  rw [abs_mul, abs_abs, abs_of_nonneg (forcedHits_nonneg i T ω)]
  exact (mul_le_of_le_one_left (forcedHits_nonneg i T ω)
    (abs_maskedTerm_le_one s hb own touched ω)).trans (forcedHits_le_one i T ω)

omit [DecidableEq ι] in

lemma truncation_error_raw (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (J : ℕ)
    (own touched : Fin R → Bool) {L lam base c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, (overloaded s J).indicator (fun ω =>
        |maskedTerm s (Real.exp (-L * base)) own touched ω|) ω ∂scheduleMeasure rate R) ≤
      (2 * Real.exp (-L * c)) ^ R * ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J := by
  have hb : Real.exp (-L * base) ∈ Set.Icc 0 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  let f := fun ω => |maskedTerm s (Real.exp (-L * base)) own touched ω|
  have hf (i : ι) (T : Finset (Fin R)) := integrable_abs_maskedTerm_forcedHits rate s hb own touched i T
  have hpoint (ω) : (overloaded s J).indicator f ω ≤
      ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, f ω * forcedHits i T ω := by
    have hh := mul_le_mul_of_nonneg_left (overload_indicator_le_certificates s J ω) (abs_nonneg
      (maskedTerm s (Real.exp (-L * base)) own touched ω))
    by_cases he : ω ∈ overloaded s J
    · simpa [he, f, Finset.mul_sum] using hh
    · simpa [he, f, Finset.mul_sum] using hh
  calc
    _ ≤ ∫ ω, ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J,
        f ω * forcedHits i T ω ∂scheduleMeasure rate R := by
      apply integral_mono
      · apply integrable_schedule_of_abs_le rate _ 1
        intro ω
        by_cases h : ω ∈ overloaded s J
        · simpa [h] using abs_maskedTerm_le_one s hb own touched ω
        · simp [h]
      · exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun T _ => hf i T))
      · exact hpoint
    _ = ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J,
        ∫ ω, f ω * forcedHits i T ω ∂scheduleMeasure rate R := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun T _ => hf i T))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun T _ => hf i T)]
    _ ≤ ∑ i ∈ s, (2 * Real.exp (-L * c)) ^ R * ((R : ℝ) * (rate i : ℝ)) ^ J := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J,
            (2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ J := by
          apply Finset.sum_le_sum
          intro T hT
          have hTJ := (Finset.mem_powersetCard.mp hT).2
          simpa only [hTJ] using integral_abs_maskedTerm_forcedHits_le rate s i hi T
            own touched hL hmass hlam hbase
        _ = (R.choose J : ℝ) * ((2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ J) := by simp
        _ ≤ _ := by
          have hchoose : (R.choose J : ℝ) ≤ (R : ℝ) ^ J := by exact_mod_cast Nat.choose_le_pow R J
          calc
            _ ≤ (R : ℝ) ^ J * ((2 * Real.exp (-L * c)) ^ R * (rate i : ℝ) ^ J) :=
              mul_le_mul_of_nonneg_right hchoose (by positivity)
            _ = _ := by rw [mul_pow]; ring
    _ = _ := (Finset.mul_sum _ _ _).symm
omit [DecidableEq ι] in

lemma truncation_error (rate : ι → ℝ≥0) {R : ℕ} (s : Finset ι) (J : ℕ)
    (own touched : Fin R → Bool) {L lam base : ℝ} (hL : 10000 ≤ L)
    (hmass : mass rate s = L * lam) (hlam : (37 / 50 : ℝ) ≤ lam)
    (hbase : (37 / 50 : ℝ) ≤ base) :
    (∫ ω, (overloaded s J).indicator (fun ω =>
        |maskedTerm s (Real.exp (-L * base)) own touched ω|) ω ∂scheduleMeasure rate R) ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J := by
  have hraw := truncation_error_raw rate s J own touched (show 0 ≤ L by linarith)
    (show (0 : ℝ) ≤ 37 / 50 by norm_num) hmass hlam hbase
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => by positivity))
  calc
    (2 * Real.exp (-L * (37 / 50 : ℝ))) ^ R ≤
        (2 * L * Real.exp (-L * (37 / 50 : ℝ))) ^ R := by
      apply pow_le_pow_left₀ (by positivity)
      have := Real.exp_pos (-L * (37 / 50 : ℝ))
      nlinarith
    _ ≤ _ := by simpa only [neg_mul, mul_comm L (37 / 50 : ℝ)] using two_mul_score_attenuation hL R
omit [DecidableEq ι] in

lemma abs_integral_compl_indicator_le (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1) (own touched : Fin R → Bool)
    (E : Set (Fin R → ι → ℕ)) :
    |∫ ω, Eᶜ.indicator (maskedTerm s b own touched) ω ∂scheduleMeasure rate R| ≤
      |∫ ω, maskedTerm s b own touched ω ∂scheduleMeasure rate R| +
        ∫ ω, E.indicator (fun ω => |maskedTerm s b own touched ω|) ω ∂scheduleMeasure rate R := by
  have hf := integrable_schedule_of_abs_le rate _ 1 (abs_maskedTerm_le_one s hb own touched)
  have hEf : Integrable (E.indicator (maskedTerm s b own touched)) (scheduleMeasure rate R) := by
    apply integrable_schedule_of_abs_le rate _ 1
    intro ω
    by_cases h : ω ∈ E
    · simpa [h] using abs_maskedTerm_le_one s hb own touched ω
    · simp [h]
  have heq : Eᶜ.indicator (maskedTerm s b own touched) =
      fun ω => maskedTerm s b own touched ω - E.indicator (maskedTerm s b own touched) ω := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [heq, integral_sub hf hEf]
  apply (abs_sub _ _).trans
  apply add_le_add le_rfl
  have habs : (fun ω => |E.indicator (maskedTerm s b own touched) ω|) =
      (E.indicator (fun ω => |maskedTerm s b own touched ω|)) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [← habs]
  exact abs_integral_le_integral_abs

omit [DecidableEq ι] in

lemma simple_singleton_truncated (rate : ι → ℝ≥0) {R : ℕ}
    (s : Finset ι) (J : ℕ) (own touched : Fin R → Bool) {L base delta alpha : ℝ}
    (hL : 10000 ≤ L) (hmass : mass rate s = L * (base + delta - alpha))
    (hinternal : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches touched).card) (hK : K ≤ N) :
    |∫ ω, (overloaded s J)ᶜ.indicator
        (maskedTerm s (Real.exp (-L * base)) own touched) ω ∂scheduleMeasure rate R| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ N + alpha ^ K + ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J) := by
  have hb : Real.exp (-L * base) ∈ Set.Icc 0 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  calc
    _ ≤ _ := abs_integral_compl_indicator_le rate s hb own touched (overloaded s J)
    _ ≤ Real.exp (-(17 / 25 : ℝ) * (L * R)) * (|delta| ^ N + alpha ^ K) +
        Real.exp (-(17 / 25 : ℝ) * (L * R)) * ∑ i ∈ s, ((R : ℝ) * (rate i : ℝ)) ^ J :=
      add_le_add (simple_singleton_attenuation rate s own touched hL hmass hinternal hbase ha hd hN hK)
        (truncation_error rate s J own touched hL hmass hinternal hbase)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
lemma measurePreserving_partition (rate : ι → ℝ≥0) (label : ι → κ) :
    MeasurePreserving (partitionEquiv label) (batchMeasure rate)
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
  have hc : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))
      (Measure.pi (fun p : (c : κ) × {i : ι // label i = c} => poissonMeasure (rate p.2)))
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
    refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, batchMeasure] using
      Measure.infinitePi_map_piCurry (fun (c : κ) (i : {i : ι // label i = c}) =>
        poissonMeasure (rate i))
  exact hc.comp ((measurePreserving_piCongrLeft (fun i => poissonMeasure (rate i))
    (Equiv.sigmaFiberEquiv label)).symm)

omit [DecidableEq ι] in

lemma measurePreserving_external (rate : ι → ℝ≥0) (label : ι → Option κ) :
    MeasurePreserving (externalEquiv label) (batchMeasure rate)
      ((Measure.pi (fun c : κ => batchMeasure
          (fun i : {i : ι // label i = some c} => rate i))).prod
        (batchMeasure (fun i : {i : ι // label i = none} => rate i))) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd
        (fun c : Option κ => {i : ι // label i = c} → ℕ)).symm
      ((Measure.pi (fun c : κ => batchMeasure
          (fun i : {i : ι // label i = some c} => rate i))).prod
        (batchMeasure (fun i : {i : ι // label i = none} => rate i)))
      (Measure.pi (fun c : Option κ => batchMeasure
          (fun i : {i : ι // label i = c} => rate i))) :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun c : Option κ =>
        batchMeasure (fun i : {i : ι // label i = c} => rate i))⟩
  exact h.symm.comp (measurePreserving_partition rate label)

omit [DecidableEq ι] in

lemma integral_external_components (rate : ι → ℝ≥0) (label : ι → Option κ)
    (weight : ({i : ι // label i = none} → ℕ) → ℝ)
    (f : ∀ c : κ, ({i : ι // label i = none} → ℕ) →
      ({i : ι // label i = some c} → ℕ) → ℝ)
    (hw : ∀ z, |weight z| ≤ 1) (hf : ∀ c z x, |f c z x| ≤ 1) :
    (∫ ω, weight (fun i => ω i) * ∏ c, f c (fun i => ω i) (fun i => ω i)
      ∂batchMeasure rate) =
      ∫ z, weight z * ∏ c, ∫ x, f c z x
        ∂batchMeasure (fun i : {i : ι // label i = some c} => rate i)
      ∂batchMeasure (fun i : {i : ι // label i = none} => rate i) := by
  let μ := Measure.pi (fun c : κ => batchMeasure
    (fun i : {i : ι // label i = some c} => rate i))
  let ν := batchMeasure (fun i : {i : ι // label i = none} => rate i)
  let F : (∀ c : κ, {i : ι // label i = some c} → ℕ) ×
      ({i : ι // label i = none} → ℕ) → ℝ :=
    fun p => weight p.2 * ∏ c, f c p.2 (p.1 c)
  have hF : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro p
    simp only [F, Real.norm_eq_abs, abs_mul, Finset.abs_prod]
    exact (mul_le_of_le_one_left (by positivity) (hw _)).trans
      (Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _ _ _))
  calc
    _ = ∫ p, F p ∂μ.prod ν := (measurePreserving_external rate label).integral_comp
      (externalEquiv label).measurableEmbedding F
    _ = ∫ z, ∫ x, weight z * ∏ c, f c z (x c) ∂μ ∂ν :=
      integral_prod_symm F hF
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [integral_const_mul]
      congr 1
      exact integral_fintype_prod_eq_prod _

section ComponentGeometry

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma cross_component_overlap (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ)
    {h k : H} (hd : (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k) :
    mass rate (s h ∩ s k) ≤ t := by
  by_contra hn
  have hk : h ≠ k := by intro e; exact hd (congrArg _ e)
  exact hd (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (G := strongGraph rate s t) ⟨hk, lt_of_not_ge hn⟩)

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma external_iff_other (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ)
    {h : H} {i : ι} (hi : i ∈ s h) :
    External rate s t i ↔ ∃ k : H, i ∈ s k ∧
      (strongGraph rate s t).connectedComponentMk h ≠
        (strongGraph rate s t).connectedComponentMk k := by
  classical
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    by_cases e : (strongGraph rate s t).connectedComponentMk h =
        (strongGraph rate s t).connectedComponentMk u
    · exact ⟨v, hv, by simpa only [e] using huv⟩
    · exact ⟨u, hu, e⟩
  · rintro ⟨k, hk, hd⟩
    exact ⟨h, k, hi, hk, hd⟩

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma internal_external_mass (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) :
    mass rate (externalPart rate s t h) + mass rate (internalPart rate s t h) =
      mass rate (s h) := by
  classical
  exact Finset.sum_filter_add_sum_filter_not _ _ _

omit [Fintype ι] [DecidableEq H] in

lemma external_mass_le_sum (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) :
    mass rate (externalPart rate s t h) ≤
      ∑ k ∈ otherComponents rate s t h, mass rate (s h ∩ s k) := by
  classical
  let K := otherComponents rate s t h
  have hp (i : ι) (hi : i ∈ s h) :
      (if External rate s t i then (rate i : ℝ) else 0) ≤
        ∑ k ∈ K, if i ∈ s k then (rate i : ℝ) else 0 := by
    split_ifs with he
    · obtain ⟨k, hk, hd⟩ := (external_iff_other rate s t hi).mp he
      have hkK : k ∈ K := by
        simpa only [K, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] using hd
      simpa only [ite_eq_left hk] using
        (Finset.single_le_sum (f := fun j : H => if i ∈ s j then (rate i : ℝ) else 0)
          (fun j (_ : j ∈ K) => by split_ifs <;> positivity) hkK :
          (if i ∈ s k then (rate i : ℝ) else 0) ≤
            ∑ j ∈ K, if i ∈ s j then (rate i : ℝ) else 0)
    · exact Finset.sum_nonneg (by intro k hk; split_ifs <;> positivity)
  calc
    _ = ∑ i ∈ s h, if External rate s t i then (rate i : ℝ) else 0 := by
      simp only [externalPart, mass, Finset.sum_filter]
    _ ≤ ∑ i ∈ s h, ∑ k ∈ K, if i ∈ s k then (rate i : ℝ) else 0 :=
      Finset.sum_le_sum hp
    _ = ∑ k ∈ K, mass rate (s h ∩ s k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mass, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    _ = _ := rfl

end ComponentGeometry
end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
section ComponentGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]
omit [Fintype ι] in
lemma external_mass_le (rate : ι → ℝ≥0) (s : H → Finset ι)
    {t : ℝ} (ht : 0 ≤ t) (h : H) :
    mass rate (externalPart rate s t h) ≤ (Fintype.card H - 1 : ℕ) * t := by
  classical
  let K := otherComponents rate s t h
  have hK : K ⊆ Finset.univ.erase h := by
    intro k hk
    simp only [K, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst k
    exact hk rfl
  have hc : K.card ≤ Fintype.card H - 1 := by
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ] using
      Finset.card_le_card hK
  calc
    _ ≤ ∑ k ∈ K, mass rate (s h ∩ s k) := external_mass_le_sum rate s t h
    _ ≤ K.card * t := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul K
        (fun k => mass rate (s h ∩ s k)) t (by
          intro k hk
          apply cross_component_overlap rate s t
          simpa only [K, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] using hk)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ht

omit [Fintype ι] in

lemma internal_mass_lower (rate : ι → ℝ≥0) (s : H → Finset ι)
    {t c : ℝ} (ht : 0 ≤ t) (hs : ∀ h, c ≤ mass rate (s h)) (h : H) :
    c - (Fintype.card H - 1 : ℕ) * t ≤ mass rate (internalPart rate s t h) := by
  have := external_mass_le rate s ht h
  have := internal_external_mass rate s t h
  have := hs h
  linarith

omit [Fintype ι] [DecidableEq H] in
lemma componentLabel_external (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {i : ι} (hi : External rate s t i) :
    componentLabel rate s t i = none := by
  classical
  simp only [componentLabel, hi, ↓reduceIte]
  split_ifs <;> rfl

omit [Fintype ι] [DecidableEq H] in
lemma componentLabel_internal (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {h : H} {i : ι} (hi : i ∈ internalPart rate s t h) :
    componentLabel rate s t i = some ((strongGraph rate s t).connectedComponentMk h) := by
  classical
  simp only [internalPart, Finset.mem_filter] at hi
  have hex : ∃ k, i ∈ s k := ⟨h, hi.1⟩
  have he := hex.choose_spec
  have hc : (strongGraph rate s t).connectedComponentMk hex.choose =
      (strongGraph rate s t).connectedComponentMk h := by
    by_contra hn
    exact hi.2 ⟨hex.choose, h, he, hi.1, hn⟩
  simp only [componentLabel, dite_eq_left hex, ite_eq_right hi.2, hc]
omit [Fintype ι] [DecidableEq H] in

lemma internalPart_iff_label (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) (i : ι) :
    i ∈ internalPart rate s t h ↔ i ∈ s h ∧
      componentLabel rate s t i = some ((strongGraph rate s t).connectedComponentMk h) := by
  classical
  constructor
  · intro hi
    exact ⟨(Finset.mem_filter.mp hi).1, componentLabel_internal rate s t hi⟩
  · rintro ⟨hi, he⟩
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro hn
    rw [componentLabel_external rate s t hn] at he
    cases he

omit [Fintype ι] [DecidableEq H] in

lemma direction_internal_or_external (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {h : H} {i : ι} (hi : i ∈ s h) :
    componentLabel rate s t i = none ∨
      componentLabel rate s t i = some ((strongGraph rate s t).connectedComponentMk h) := by
  classical
  by_cases he : External rate s t i
  · exact Or.inl (componentLabel_external rate s t he)
  · exact Or.inr (componentLabel_internal rate s t (Finset.mem_filter.mpr ⟨hi, he⟩))
omit [Fintype ι] in

lemma source_internal_mass_lower (rate : ι → ℝ≥0) (s : H → Finset ι)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card H ≤ p)
    (hs : ∀ h, (3 / 4 : ℝ) ≤ mass rate (s h)) (h : H) :
    (37 / 50 : ℝ) ≤ mass rate (internalPart rate s (1 / (100 * p)) h) := by
  have ht : (0 : ℝ) ≤ 1 / (100 * p : ℝ) := by positivity
  have hl := internal_mass_lower rate s ht hs h
  have hh : (0 : ℝ) < p := by exact_mod_cast hp
  have hcard : ((Fintype.card H - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast ((Nat.sub_le (Fintype.card H) 1).trans hc)
  have hm : ((Fintype.card H - 1 : ℕ) : ℝ) * (1 / (100 * p)) ≤ (1 / 100 : ℝ) := by
    calc
      _ ≤ (p : ℝ) * (1 / (100 * p)) := mul_le_mul_of_nonneg_right hcard ht
      _ = _ := by field_simp
  linarith

end ComponentGeometry

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

omit [Fintype D] [DecidableEq D] [Fintype C] in
lemma fill_restrict (c : C) (ω : Fin R × D → ℕ) {d : D}
    (hd : label d = none ∨ label d = some c) (r : Fin R) :
    fill label R c (fun i => ω i) (fun i => ω i) r d = ω (r,d) := by
  rcases hd with hd | hd <;> simp [fill, hd]

lemma lineTrunc_range (J : ℕ) (ω : Fin R → ℕ) :
    lineTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by unfold lineTrunc; split_ifs <;> norm_num

omit [DecidableEq D] [Fintype C] in
lemma blockTrunc_range (J : ℕ) (c : Option C) (ω : Block label R c → ℕ) :
    blockTrunc label R J c ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => (lineTrunc_range R J _).1)
  · exact Finset.prod_le_one (fun _ _ => (lineTrunc_range R J _).1)
      (fun _ _ => (lineTrunc_range R J _).2)

lemma prod_fibers {A K : Type} [Fintype A] [Fintype K] [DecidableEq K]
    (col : A → K) (f : A → ℝ) :
    (∏ c : K, ∏ a : {a : A // col a = c}, f a) = ∏ a, f a := by
  classical
  calc
    _ = ∏ c : K, ∏ a ∈ Finset.univ.filter (fun a => col a = c), f a := by
      apply Finset.prod_congr rfl
      intro c _
      symm
      exact Finset.prod_subtype _ (by simp) f
    _ = _ := by
      simpa using Finset.prod_fiberwise Finset.univ col f

omit [DecidableEq D] in
lemma trunc_split (J : ℕ) (ω : Fin R × D → ℕ) :
    (∏ d : D, lineTrunc R J (fun r => ω (r,d))) =
      blockTrunc label R J none (fun i => ω i) *
        ∏ c : C, blockTrunc label R J (some c) (fun i => ω i) := by
  rw [← Fintype.prod_option (fun c => blockTrunc label R J c (fun i => ω i))]
  exact (prod_fibers label (fun d => lineTrunc R J (fun r => ω (r,d)))).symm

omit [Fintype D] [DecidableEq D] in
lemma emptyIndicator_congr (s : Finset D) (ω ν : D → ℕ)
    (he : ∀ d ∈ s, ω d = ν d) : emptyIndicator s ω = emptyIndicator s ν := by
  have h : ω ∈ emptyEvent s ↔ ν ∈ emptyEvent s := by
    simp only [emptyEvent, Set.mem_pi, Set.mem_singleton_iff, Finset.mem_coe]
    exact forall₂_congr (fun d hd => by rw [he d hd])
  by_cases hω : ω ∈ emptyEvent s
  · simp [emptyIndicator, hω, h.mp hω]
  · simp [emptyIndicator, hω, (not_congr h).mp hω]
omit [Fintype D] [DecidableEq D] in

lemma scoreTerm_congr (s : Finset D) (b : ℝ) (own : Fin R → Bool)
    (ω ν : Fin R → D → ℕ) (he : ∀ r d, d ∈ s → ω r d = ν r d) :
    scoreTerm s b own ω = scoreTerm s b own ν := by
  unfold scoreTerm
  apply Finset.prod_congr rfl
  intro r _
  simp only [centeredFactor, emptyIndicator_congr s (ω r) (ν r) (he r)]

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

omit [DecidableEq V] in
omit [Fintype C] in
omit [DecidableEq D] in
lemma componentFactor_bound (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1) (c : C)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) :
    |componentFactor label R color s b own J c z x| ≤ 1 := by
  rw [componentFactor, abs_mul, Finset.abs_prod]
  have htrunc : |blockTrunc label R J (some c) x| ≤ 1 := by
    rw [abs_of_nonneg (blockTrunc_range label R J (some c) x).1]
    exact (blockTrunc_range label R J (some c) x).2
  refine (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    htrunc).trans ?_
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro vertex _
  simpa only [maskedTerm, maskedFactor, Bool.false_eq_true, ↓reduceIte, scoreTerm]
    using abs_maskedTerm_le_one (s vertex) hb (own vertex) (fun _ => false)
      (fill label R c z x)

omit [DecidableEq V] in
omit [DecidableEq D] in
lemma tuple_pointwise_split (J : ℕ)
    (hcompat : ∀ v d, d ∈ s v → label d = none ∨ label d = some (color v))
    (ω : Fin R × D → ℕ) :
    (∏ d : D, lineTrunc R J (fun r => ω (r,d))) *
        (∏ v : V, scoreTerm (s v) b (own v) (fun r d => ω (r,d))) =
      blockTrunc label R J none (fun i => ω i) *
        ∏ c : C, componentFactor label R color s b own J c
          (fun i => ω i) (fun i => ω i) := by
  have he (c : C) (v : {v : V // color v = c}) :
      scoreTerm (s v) b (own v)
        (fill label R c (fun i => ω i) (fun i => ω i)) =
      scoreTerm (s v) b (own v) (fun r d => ω (r,d)) := by
    apply scoreTerm_congr R
    intro r d hd
    apply fill_restrict label R c ω _ r
    simpa only [v.property] using hcompat v d hd
  simp_rw [componentFactor, he]
  rw [Finset.prod_mul_distrib, prod_fibers color (fun v => scoreTerm (s v) b (own v) (fun r d => ω (r,d)))]
  rw [trunc_split label R J ω]
  ring

omit [DecidableEq V] in
omit [DecidableEq D] in

theorem tuple_integral_split (rate : D → ℝ≥0) (J : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ v d, d ∈ s v → label d = none ∨ label d = some (color v)) :
    (∫ ω, (∏ d : D, lineTrunc R J (fun r => ω (r,d))) *
        (∏ v : V, scoreTerm (s v) b (own v) (fun r d => ω (r,d)))
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) =
      ∫ z, blockTrunc label R J none z * ∏ c : C,
        ∫ x, componentFactor label R color s b own J c z x
          ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)
        ∂batchMeasure (fun i : Block label R none => rate i.1.2) := by
  have he := integral_external_components (fun i : Fin R × D => rate i.2)
    (fun i => label i.2) (blockTrunc label R J none)
    (componentFactor label R color s b own J)
    (fun z => by rw [abs_of_nonneg (blockTrunc_range label R J none z).1];
                 exact (blockTrunc_range label R J none z).2)
    (componentFactor_bound label R color s b own J hb)
  rw [← he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (tuple_pointwise_split label R color s b own J hcompat)

lemma strong_tuple_integral_split (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, (∏ d : D, lineTrunc R J (fun r => ω (r,d))) *
        (∏ v : V, scoreTerm (s v) b (own v) (fun r d => ω (r,d)))
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) =
      strongSplit R s b own weight rate t J := by
  classical
  unfold strongSplit
  apply tuple_integral_split _ R _ s b own rate J hb
  intro v d hd
  exact direction_internal_or_external weight s t hd

omit [Fintype C] in
lemma fill_empty_iff (c : C) (S : Finset D)
    (hc : ∀ d ∈ S, label d = none ∨ label d = some c)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) (r : Fin R) :
    fill label R c z x r ∈ emptyEvent S ↔
      touched label R c S z r = false ∧
        unblock label R c x r ∈ emptyEvent (inside label c S) := by
  simp only [emptyEvent, Set.mem_pi, Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · intro h
    constructor
    · simp only [touched, decide_eq_false_iff_not, not_exists, not_and]
      intro d hd
      have := h d hd
      simpa [fill, d.property] using this
    · intro d hd
      have := h d (Finset.mem_filter.mp hd).2
      simpa [fill, d.property, unblock] using this
  · rintro ⟨he, hi⟩ d hd
    rcases hc d hd with hd0 | hdc
    · have hz : z ⟨(r,d), hd0⟩ = 0 := by
        have he' : ¬ ∃ d : {d : D // label d = none},
            d.val ∈ S ∧ z ⟨(r,d), d.property⟩ ≠ 0 := by
          simpa only [touched, decide_eq_false_iff_not] using he
        by_contra hn
        exact he' ⟨⟨d,hd0⟩, hd, hn⟩
      simpa [fill, hd0] using hz
    · have hz := hi ⟨d,hdc⟩ (by simp [inside, hd])
      simpa [fill, hdc, unblock] using hz
omit [Fintype C] in

lemma scoreTerm_eq_masked (c : C) (S : Finset D) (B : ℝ) (o : Fin R → Bool)
    (hc : ∀ d ∈ S, label d = none ∨ label d = some c)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) :
    scoreTerm S B o (fill label R c z x) =
      maskedTerm (inside label c S) B o (touched label R c S z) (unblock label R c x) := by
  apply Finset.prod_congr rfl
  intro r _
  have hh := fill_empty_iff label R c S hc z x r
  cases ho : o r <;> simp only [maskedFactor, Bool.false_eq_true, ↓reduceIte]
  by_cases he : touched label R c S z r = true
  · have hn : fill label R c z x r ∉ emptyEvent S := by simpa [he] using hh
    simp [he, centeredFactor, emptyIndicator, hn]
  · have ht : touched label R c S z r = false := Bool.eq_false_of_not_eq_true he
    simp only [ht, true_and] at hh
    by_cases hi : unblock label R c x r ∈ emptyEvent (inside label c S)
    · simp [ht, centeredFactor, emptyIndicator, hi, hh.mpr hi]
    · simp [ht, centeredFactor, emptyIndicator, hi, (not_congr hh).mpr hi]

omit [Fintype C] in
omit [DecidableEq D] in
lemma measurePreserving_unblock (rate : D → ℝ≥0) (c : C) :
    MeasurePreserving (unblockEquiv label R c)
      (batchMeasure (fun i : Block label R (some c) => rate i.1.2))
      (scheduleMeasure (fun d : IntDir label c => rate d) R) := by
  exact (measurePreserving_uncurry_schedule (fun d : IntDir label c => rate d) R).symm.comp
    (measurePreserving_piCongrLeft
      (fun i : Block label R (some c) => poissonMeasure (rate i.1.2))
      (blockCoords label R c)).symm

omit [DecidableEq D] [Fintype C] in
lemma integrable_block_bounded (rate : D → ℝ≥0) (c : Option C)
    (f : (Block label R c → ℕ) → ℝ) (h : ∀ x, |f x| ≤ 1) :
    Integrable f (batchMeasure (fun i : Block label R c => rate i.1.2)) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using h x)
omit [Fintype C] in
omit [DecidableEq D] in

lemma componentFactor_abs_le_term (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (c : C) (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ)
    (v : {v : V // color v = c}) :
    |componentFactor label R color s b own J c z x| ≤
      |scoreTerm (s v) b (own v) (fill label R c z x)| := by
  have hterm (u : V) : |scoreTerm (s u) b (own u) (fill label R c z x)| ≤ 1 := by
    simpa only [maskedTerm, maskedFactor, Bool.false_eq_true, ↓reduceIte, scoreTerm]
      using abs_maskedTerm_le_one (s u) hb (own u) (fun _ => false) (fill label R c z x)
  rw [componentFactor, abs_mul, Finset.abs_prod]
  have hp : (∏ u : {v : V // color v = c},
      |scoreTerm (s u) b (own u) (fill label R c z x)|) ≤
      |scoreTerm (s v) b (own v) (fill label R c z x)| := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
    have he : (∏ u ∈ Finset.univ.erase v,
        |scoreTerm (s u) b (own u) (fill label R c z x)|) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun u _ => hterm u)
    simpa using mul_le_mul_of_nonneg_right he (abs_nonneg
      (scoreTerm (s v) b (own v) (fill label R c z x)))
  calc
    _ ≤ ∏ u : {v : V // color v = c},
        |scoreTerm (s u) b (own u) (fill label R c z x)| := by
      apply mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      rw [abs_of_nonneg (blockTrunc_range label R J (some c) x).1]
      exact (blockTrunc_range label R J (some c) x).2
    _ ≤ _ := hp

omit [Fintype C] in

lemma component_integral_abs_le (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c}) (z : Block label R none → ℕ)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    {L lam base a : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) = L * lam)
    (hlam : a ≤ lam) (hbase : a ≤ base) :
    (∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)) ≤
        (2 * Real.exp (-L * a)) ^ R := by
  have hb : Real.exp (-L * base) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  let f := fun w => |maskedTerm (inside label c (s v)) (Real.exp (-L * base))
    (own v) (touched label R c (s v) z) w|
  have he (x : Block label R (some c) → ℕ) :
      |scoreTerm (s v) (Real.exp (-L * base)) (own v) (fill label R c z x)| =
      f (unblockEquiv label R c x) := by
    rw [scoreTerm_eq_masked label R c (s v) _ _ hcompat]
    rfl
  calc
    _ ≤ ∫ x, f (unblockEquiv label R c x)
        ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := by
      apply integral_mono
      · apply integrable_block_bounded label R rate (some c)
        intro x
        rw [abs_abs]
        exact componentFactor_bound label R color s _ own J hb c z x
      · apply integrable_block_bounded label R rate (some c)
        intro x
        dsimp only [f]
        rw [abs_abs]
        exact abs_maskedTerm_le_one _ hb _ _ _
      · intro x
        dsimp only
        rw [← he x]
        exact componentFactor_abs_le_term label R color s _ own J hb c z x v
    _ = ∫ w, f w ∂scheduleMeasure (fun d : IntDir label c => rate d) R :=
      (measurePreserving_unblock label R rate c).integral_comp
        (unblockEquiv label R c).measurableEmbedding f
    _ ≤ _ := integral_abs_maskedTerm_exp_le _ _ _ _ hL hmass hlam hbase

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ComponentLabelWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)
variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)
omit [Fintype D] [DecidableEq V] in
lemma componentLabel_witness (weight : D → ℝ≥0) (t : ℝ) (d : D)
    (c : (strongGraph weight s t).ConnectedComponent)
    (hc : componentLabel weight s t d = some c) :
    ∃ v, d ∈ s v ∧ (strongGraph weight s t).connectedComponentMk v = c := by
  unfold componentLabel at hc
  split_ifs at hc with h h'
  exact ⟨h.choose, h.choose_spec, Option.some.inj hc⟩
omit [DecidableEq V] in

lemma simple_inside_univ (weight : D → ℝ≥0) (t : ℝ) (v : V)
    (hsingle : ∀ u, (strongGraph weight s t).connectedComponentMk u =
      (strongGraph weight s t).connectedComponentMk v → u = v) :
    inside (componentLabel weight s t) ((strongGraph weight s t).connectedComponentMk v)
      (s v) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro d
  obtain ⟨u, hu, hc⟩ := componentLabel_witness s weight t d.val _ d.property
  have he := hsingle u hc
  simpa [inside, he] using hu

omit [DecidableEq D] [Fintype C] in
lemma blockTrunc_eq_indicator (J : ℕ) (c : C) (x : Block label R (some c) → ℕ) :
    blockTrunc label R J (some c) x =
      (overloaded Finset.univ J)ᶜ.indicator (fun _ => (1 : ℝ)) (unblock label R c x) := by
  by_cases he : unblock label R c x ∈ overloaded Finset.univ J
  · simp only [Set.indicator_of_notMem (show unblock label R c x ∉
      (overloaded Finset.univ J)ᶜ by simpa using he)]
    obtain ⟨d, _, hd⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ d)
    change lineTrunc R J (fun r => x ⟨(r,d), d.property⟩) = 0
    have hn : ¬ (Finset.univ.filter (fun r => x ⟨(r,d), d.property⟩ ≠ 0)).card < J := by
      exact not_lt.mpr hd
    simp only [lineTrunc, ite_eq_right hn]
  · rw [Set.indicator_of_mem (show unblock label R c x ∈
      (overloaded Finset.univ J)ᶜ by simpa using he)]
    apply Finset.prod_eq_one
    intro d _
    change lineTrunc R J (fun r => x ⟨(r,d), d.property⟩) = 1
    have hd : (Finset.univ.filter (fun r => x ⟨(r,d), d.property⟩ ≠ 0)).card < J := by
      by_contra hn
      exact he ⟨d, Finset.mem_univ _, not_lt.mp hn⟩
    simp only [lineTrunc, ite_eq_left hd]

omit [DecidableEq V] in
omit [Fintype C] in
lemma componentFactor_eq_single (J : ℕ) (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) :
    componentFactor label R color s b own J c z x =
      (overloaded (inside label c (s v)) J)ᶜ.indicator
        (maskedTerm (inside label c (s v)) b (own v) (touched label R c (s v) z))
        (unblock label R c x) := by
  have hp : (∏ u : {v : V // color v = c}, scoreTerm (s u) b (own u) (fill label R c z x)) =
      scoreTerm (s v) b (own v) (fill label R c z x) := by
    apply Finset.prod_eq_single v
    · intro u _ huv
      exfalso
      exact huv (Subtype.ext (hsingle u u.property))
    · simp
  rw [componentFactor, hp, scoreTerm_eq_masked label R c (s v) b (own v) hcompat,
    blockTrunc_eq_indicator label R J c, hin]
  by_cases he : unblock label R c x ∈ (overloaded Finset.univ J)ᶜ <;> simp [he]
omit [DecidableEq V] in
omit [Fintype C] in

lemma simple_component_integral (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ) :
    (∫ x, componentFactor label R color s b own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)) =
      ∫ w, (overloaded (inside label c (s v)) J)ᶜ.indicator
        (maskedTerm (inside label c (s v)) b (own v) (touched label R c (s v) z)) w
        ∂scheduleMeasure (fun d : IntDir label c => rate d) R := by
  simp_rw [componentFactor_eq_single label R color s b own J c v hsingle hcompat hin]
  exact (measurePreserving_unblock label R rate c).integral_comp
    (unblockEquiv label R c).measurableEmbedding _
omit [DecidableEq V] in
omit [Fintype C] in

lemma simple_component_attenuation (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ)
    {L base delta alpha : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) =
      L * (base + delta - alpha))
    (hint : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches (touched label R c (s v) z)).card) (hK : K ≤ N) :
    |∫ x, componentFactor label R color s (Real.exp (-L * base)) own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ N + alpha ^ K +
          ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J) := by
  rw [simple_component_integral label R color s _ own rate J c v hsingle hcompat hin z]
  exact simple_singleton_truncated _ _ J (own v) (touched label R c (s v) z)
    hL hmass hint hbase ha hd hN hK
omit [Fintype C] in

lemma nonsimple_component_attenuation (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c}) (z : Block label R none → ℕ)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    {L lam base : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) = L * lam)
    (hlam : (37 / 50 : ℝ) ≤ lam) (hbase : (37 / 50 : ℝ) ≤ base) :
    (∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)) ≤
        Real.exp (-(7 / 10 : ℝ) * (L * R)) := by
  apply (component_integral_abs_le label R color s own rate J c v z hcompat
    (show 0 ≤ L by linarith) (by norm_num : (0 : ℝ) ≤ 37 / 50) hmass hlam hbase).trans
  have he : (2 : ℝ) ≤ Real.exp ((1 / 25 : ℝ) * L) := by
    have := Real.add_one_le_exp ((1 / 25 : ℝ) * L)
    linarith
  have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (-L * (37 / 50 : ℝ))).le
  rw [← Real.exp_add] at hmul
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-L * (37 / 50 : ℝ))) hmul R
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1 ; congr 1 ; ring

end SharpRamseyFive.TupleComponents

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
omit [DecidableEq V] in

lemma mass_inside_eq (weight rate : D → ℝ≥0) (s : V → Finset D) (t : ℝ) (v : V) :
    mass (fun d : IntDir (componentLabel weight s t)
      ((strongGraph weight s t).connectedComponentMk v) => rate d)
      (inside (componentLabel weight s t) _ (s v)) =
      mass rate (internalPart weight s t v) := by
  unfold mass
  apply Finset.sum_bij (fun d _ => d.val)
  · intro d hd
    exact (internalPart_iff_label weight s t v d.val).mpr
      ⟨(Finset.mem_filter.mp hd).2, d.property⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro d hd
    obtain ⟨hm, hl⟩ := (internalPart_iff_label weight s t v d).mp hd
    exact ⟨⟨d,hl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩,rfl⟩
  · intro d _
    rfl

omit [Fintype D] [DecidableEq D] in
lemma mass_scaled (L : ℝ≥0) (weight : D → ℝ≥0) (S : Finset D) :
    mass (fun d => L * weight d) S = (L : ℝ) * mass weight S := by
  simp only [mass, NNReal.coe_mul, Finset.mul_sum]

variable (label : D → Option C) (R : ℕ) (color : V → C)
  (s : V → Finset D) (own : V → Fin R → Bool)

lemma batches_partition {R : ℕ} (mask : Fin R → Bool) :
    (hitBatches mask).card + (untouchedBatches mask).card = R := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun r : Fin R => mask r = true)
  simpa only [hitBatches, untouchedBatches, Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] using h

lemma untouched_of_not_bad {R : ℕ} (mask : Fin R → Bool) (h : ¬ BAD mask) :
    R / 2 ≤ (untouchedBatches mask).card := by
  have hp := batches_partition mask
  simp only [BAD, not_le] at h
  omega

omit [Fintype C] in

theorem simple_component_designations_raw (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ)
    {L base delta alpha : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) =
      L * (base + delta - alpha))
    (hint : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {K : ℕ} (hK : K ≤ R / 2) :
    |∫ x, componentFactor label R color s (Real.exp (-L * base)) own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ (R / 2) + alpha ^ K +
          ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J +
            if BAD (touched label R c (s v) z) then 1 else 0) := by
  by_cases hg : ¬ BAD (touched label R c (s v) z)
  · simp only [ite_eq_right hg, add_zero]
    exact simple_component_attenuation label R color s own rate J c v hsingle hcompat hin z
      hL hmass hint hbase ha hd (untouched_of_not_bad _ hg) hK
  · simp only [not_not] at hg
    simp only [ite_eq_left hg]
    have hn := nonsimple_component_attenuation label R color s own rate J c v z
      hcompat hL hmass hint hbase
    have hat : Real.exp (-(7 / 10 : ℝ) * (L * R)) ≤
        Real.exp (-(17 / 25 : ℝ) * (L * R)) := by
      apply Real.exp_le_exp.mpr
      have hLR : 0 ≤ L * (R : ℝ) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    calc
      _ ≤ ∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
          ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := abs_integral_le_integral_abs
      _ ≤ _ := hn
      _ ≤ Real.exp (-(17 / 25 : ℝ) * (L * R)) := hat
      _ ≤ _ := by
        apply le_mul_of_one_le_right (Real.exp_pos _).le
        have he : 0 ≤ ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J := by positivity
        have haK : 0 ≤ alpha ^ K := pow_nonneg ha K
        have hdN : 0 ≤ |delta| ^ (R / 2) := by positivity
        linarith
omit [Fintype C] in

theorem simple_component_designations (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ)
    {L base delta alpha : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) =
      L * (base + delta - alpha))
    (hint : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {K : ℕ} (hK : K ≤ R / 2) :
    |∫ x, componentFactor label R color s (Real.exp (-L * base)) own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ (R / 2) + alpha ^ K +
          (if R < J then 0 else
            ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J) +
            if BAD (touched label R c (s v) z) then 1 else 0) := by
  by_cases hRJ : R < J
  · simp only [ite_eq_left hRJ, add_zero]
    by_cases hg : ¬ BAD (touched label R c (s v) z)
    · simp only [ite_eq_right hg, add_zero]
      rw [simple_component_integral label R color s _ own rate J c v hsingle hcompat hin z]
      simp_rw [overloaded_eq_empty _ hRJ, Set.compl_empty, Set.indicator_univ]
      exact simple_singleton_attenuation _ _ (own v) (touched label R c (s v) z)
        hL hmass hint hbase ha hd (untouched_of_not_bad _ hg) hK
    · simp only [not_not] at hg
      simp only [ite_eq_left hg]
      have hn := nonsimple_component_attenuation label R color s own rate J c v z
        hcompat hL hmass hint hbase
      have hat : Real.exp (-(7 / 10 : ℝ) * (L * R)) ≤
          Real.exp (-(17 / 25 : ℝ) * (L * R)) := by
        apply Real.exp_le_exp.mpr
        have hLR : 0 ≤ L * (R : ℝ) := mul_nonneg (by linarith) (by positivity)
        nlinarith
      calc
        _ ≤ ∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
            ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := abs_integral_le_integral_abs
        _ ≤ _ := hn
        _ ≤ Real.exp (-(17 / 25 : ℝ) * (L * R)) := hat
        _ ≤ _ := by
          apply le_mul_of_one_le_right (Real.exp_pos _).le
          have haK : 0 ≤ alpha ^ K := pow_nonneg ha K
          have hdN : 0 ≤ |delta| ^ (R / 2) := by positivity
          linarith
  · simpa only [ite_eq_right hRJ] using
      simple_component_designations_raw label R color s own rate J c v hsingle
        hcompat hin z hL hmass hint hbase ha hd hK

end SharpRamseyFive.TupleComponents

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)

omit [DecidableEq D] in
lemma allTrunc_range (J : ℕ) (ω : Fin R × D → ℕ) :
    allTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => (lineTrunc_range R J _).1)
  · exact Finset.prod_le_one (fun _ _ => (lineTrunc_range R J _).1)
      (fun _ _ => (lineTrunc_range R J _).2)

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] [DecidableEq D] in
lemma scoreTerm_abs_le (hb : b ∈ Set.Icc (0 : ℝ) 1) (h : H) (ω : Fin R × D → ℕ) :
    |scoreTerm (s h) b (own h) (fun r d => ω (r,d))| ≤ 1 := by
  simpa only [maskedTerm, maskedFactor, Bool.false_eq_true, ↓reduceIte, scoreTerm]
    using abs_maskedTerm_le_one (s h) hb (own h) (fun _ => false) (fun r d => ω (r,d))
omit [Fintype H] [DecidableEq H] in
omit [DecidableEq D] in

lemma truncated_tuple_abs_le (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [Fintype V] (f : V → H) (ω : Fin R × D → ℕ) :
    |allTrunc R J ω * ∏ v, scoreTerm (s (f v)) b (own (f v)) (fun r d => ω (r,d))| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (allTrunc_range R J ω).1, Finset.abs_prod]
  exact (mul_le_of_le_one_left (by positivity) (allTrunc_range R J ω).2).trans
    (Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun _ _ => scoreTerm_abs_le R s b own hb _ ω))

end SharpRamseyFive.HighMoment
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TruncatedTupleIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)
omit [Fintype H] [DecidableEq H] [DecidableEq D] in
lemma truncated_tuple_integrable (rate : D → ℝ≥0) (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [Fintype V] (f : V → H) :
    Integrable (fun ω => allTrunc R J ω *
      ∏ v, scoreTerm (s (f v)) b (own (f v)) (fun r d => ω (r,d)))
      (batchMeasure (fun i : Fin R × D => rate i.2)) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using truncated_tuple_abs_le R s b own J hb f ω)

omit [DecidableEq H] in

theorem integral_truncated_score_pow (weight rate : D → ℝ≥0) (t : ℝ) (J p : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, allTrunc R J ω *
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) =
        ∑ f : Fin p → H, strongSplit R (s ∘ f) b (own ∘ f) weight rate t J := by
  have hp (ω : Fin R × D → ℕ) :
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p =
        ∑ f : Fin p → H, ∏ v, scoreTerm (s (f v)) b (own (f v)) (fun r d => ω (r,d)) := by
    simpa using Finset.sum_pow' Finset.univ
      (fun h : H => scoreTerm (s h) b (own h) (fun r d => ω (r,d))) p
  simp_rw [hp, Finset.mul_sum]
  rw [integral_finsetSum _ (fun f _ => truncated_tuple_integrable R s b own rate J hb f)]
  apply Finset.sum_congr rfl
  intro f _
  exact strong_tuple_integral_split R (s ∘ f) b (own ∘ f) weight rate t J hb

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
omit [DecidableEq D] in

lemma integral_abs_component_le_one {C : Type} [Fintype C] [DecidableEq C]
    (label : D → Option C) (col : V → C) (sf : V → Finset D)
    (of : V → Fin R → Bool) (rate : D → ℝ≥0) (J : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (c : C) (z : Block label R none → ℕ) :
    |∫ x, componentFactor label R col sf b of J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤ 1 := by
  have hi : Integrable (fun x => |componentFactor label R col sf b of J c z x|)
      (batchMeasure (fun i : Block label R (some c) => rate i.1.2)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        componentFactor_bound label R col sf b of J hb c z x)
  calc
    _ ≤ ∫ x, |componentFactor label R col sf b of J c z x|
        ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := abs_integral_le_integral_abs
    _ ≤ ∫ _, (1 : ℝ) ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) :=
      integral_mono hi (integrable_const _) (componentFactor_bound label R col sf b of J hb c z)
    _ = 1 := by simp

omit [Fintype H] [DecidableEq H] in
lemma strongSplit_abs_le (f : V → H) (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ)
    (_hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |strongSplit R (s ∘ f) b (own ∘ f) weight rate t J| ≤
      absSplit R s b own f weight rate t J := by
  unfold strongSplit absSplit
  apply (abs_integral_le_integral_abs).trans_eq
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [abs_mul, abs_of_nonneg (blockTrunc_range _ R J none z).1, Finset.abs_prod]

omit [DecidableEq H] in

theorem truncated_moment_le_tuple_sum (weight rate : D → ℝ≥0) (t : ℝ) (J p : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, allTrunc R J ω *
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) ≤
        ∑ f : Fin p → H, absSplit R s b own f weight rate t J := by
  rw [integral_truncated_score_pow R s b own weight rate t J p hb]
  apply Finset.sum_le_sum
  intro f _
  exact (le_abs_self _).trans (strongSplit_abs_le R s b own f weight rate t J hb)

end SharpRamseyFive.HighMoment

namespace SharpRamseyFive.Designations
open MeasureTheory
open scoped BigOperators
open Classical
variable {C Ω : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
lemma badIndicator_range (bad : C → Ω → Prop) (c : C) (z : Ω) :
    badIndicator bad c z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold badIndicator
  split_ifs <;> constructor <;> norm_num

lemma product_expansion (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (z : Ω) :
    T z * ∏ c : C, (if c ∈ S then A * (w c + badIndicator bad c z) else N) =
      (A ^ S.card * N ^ (Fintype.card C - S.card)) *
        ∑ U ∈ S.powerset, (∏ c ∈ S \ U, w c) * (T z * ∏ c ∈ U, badIndicator bad c z) := by
  have hf : Finset.univ.filter (fun c : C => c ∈ S) = S := by ext; simp
  have hg : Finset.univ.filter (fun c : C => c ∉ S) = Finset.univ \ S := by ext; simp
  rw [Finset.prod_ite, hf, hg, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have ha : (∏ c ∈ S, (w c + badIndicator bad c z)) =
      ∑ U ∈ S.powerset, (∏ c ∈ U, badIndicator bad c z) * ∏ c ∈ S \ U, w c := by
    rw [← Finset.prod_add]
    apply Finset.prod_congr rfl
    intro c _
    exact add_comm _ _
  rw [ha, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

variable [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
omit [Fintype C] [DecidableEq C] in
lemma badTerm_range (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (bad : C → Ω → Prop) (U : Finset C) (z : Ω) :
    T z * ∏ c ∈ U, badIndicator bad c z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (hT z).1 (Finset.prod_nonneg (fun c _ => (badIndicator_range bad c z).1))
  · exact (mul_le_of_le_one_left
      (Finset.prod_nonneg (fun component _ => (badIndicator_range bad component z).1))
      (hT z).2).trans
      (Finset.prod_le_one (fun component _ => (badIndicator_range bad component z).1)
        (fun component _ => (badIndicator_range bad component z).2))
omit [Fintype C] [DecidableEq C] in

lemma badTerm_integrable (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (bad : C → Ω → Prop) (U : Finset C) :
    Integrable (fun z => T z * ∏ c ∈ U, badIndicator bad c z) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (badTerm_range T hT bad U z).1]
    exact (badTerm_range T hT bad U z).2)

omit [IsProbabilityMeasure μ] in
omit [Countable Ω] [MeasurableSingletonClass Ω] in
omit [Fintype C] [DecidableEq C] in
lemma badMass_nonneg (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (bad : C → Ω → Prop) (U : Finset C) : 0 ≤ badMass μ T bad U :=
  integral_nonneg (fun z => (badTerm_range T hT bad U z).1)

lemma majorant_integrable (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun z => T z * ∏ c : C,
      if c ∈ S then A * (w c + badIndicator bad c z) else N) μ := by
  simp_rw [product_expansion]
  exact (integrable_finsetSum _ (fun U _ =>
    (badTerm_integrable μ T hT bad U).const_mul (∏ c ∈ S \ U, w c))).const_mul _

lemma integral_expansion (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, T z * ∏ c : C,
      if c ∈ S then A * (w c + badIndicator bad c z) else N ∂μ) =
      (A ^ S.card * N ^ (Fintype.card C - S.card)) *
        ∑ U ∈ S.powerset, (∏ c ∈ S \ U, w c) * badMass μ T bad U := by
  simp_rw [product_expansion]
  rw [integral_const_mul, integral_finsetSum _ (fun U _ =>
    (badTerm_integrable μ T hT bad U).const_mul (∏ c ∈ S \ U, w c))]
  simp_rw [integral_const_mul]
  rfl

theorem integral_product_le (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (F : C → Ω → ℝ) (hF : ∀ c z, F c z ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ c ∈ S, ∀ z, F c z ≤ A * (w c + badIndicator bad c z))
    (hn : ∀ c ∉ S, ∀ z, F c z ≤ N) :
    (∫ z, T z * ∏ c, F c z ∂μ) ≤
      (A ^ S.card * N ^ (Fintype.card C - S.card)) *
        ∑ U ∈ S.powerset, (∏ c ∈ S \ U, w c) * badMass μ T bad U := by
  rw [← integral_expansion μ S A N w bad T hT]
  have hi : Integrable (fun z => T z * ∏ c, F c z) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT z).1
      (Finset.prod_nonneg (fun c _ => (hF c z).1)))]
    exact (mul_le_of_le_one_left
      (Finset.prod_nonneg (fun component _ => (hF component z).1)) (hT z).2).trans
      (Finset.prod_le_one (fun component _ => (hF component z).1)
        (fun component _ => (hF component z).2))
  apply integral_mono hi (majorant_integrable μ S A N w bad T hT)
  intro z
  apply mul_le_mul_of_nonneg_left _ (hT z).1
  apply Finset.prod_le_prod (fun component _ => (hF component z).1)
  intro c _
  split_ifs with hc
  · exact hs c hc z
  · exact hn c hc z

end SharpRamseyFive.Designations

namespace SharpRamseyFive.AmbientDesignations
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations
open Classical
variable {D V : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)

omit [Fintype D] [Fintype V] [DecidableEq V] in
lemma vertex_color (c : Components weight s t) :
    (strongGraph weight s t).connectedComponentMk (vertex weight s t c) = c :=
  c.out_eq

omit [Fintype V] [DecidableEq V] in
omit [Fintype D] in
lemma alpha_nonneg (v : V) : 0 ≤ alpha weight s t v := mass_nonneg weight _
omit [Fintype D] in

lemma source_alpha_le {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p) (v : V) :
    alpha weight s (1 / (100 * p)) v ≤ (1 / 100 : ℝ) := by
  have hl := external_mass_le weight s (show (0 : ℝ) ≤ 1 / (100 * p : ℝ) by positivity) v
  have hcr : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ p := by
    exact_mod_cast (Nat.sub_le (Fintype.card V) 1).trans hc
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have he : (p : ℝ) * (1 / (100 * p : ℝ)) = 1 / 100 := by field_simp
  exact hl.trans ((mul_le_mul_of_nonneg_right hcr (by positivity)).trans_eq he)
omit [Fintype D] [Fintype V] [DecidableEq V] in

lemma internal_mass_eq (base : ℝ) (v : V) :
    mass weight (internalPart weight s t v) =
      base + delta weight s base v - alpha weight s t v := by
  have he := internal_external_mass weight s t v
  dsimp [delta, alpha]
  linarith
omit [Fintype D] in

lemma source_local_data {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (base : ℝ) (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (hdelta : ∀ v, |delta weight s base v| ≤ (17 / 100 : ℝ)) (v : V) :
    (37 / 50 : ℝ) ≤ base + delta weight s base v - alpha weight s (1 / (100 * p)) v ∧
      |delta weight s base v| + alpha weight s (1 / (100 * p)) v ≤ 1 := by
  constructor
  · rw [← internal_mass_eq]
    exact source_internal_mass_lower weight s hp hc hlower v
  · have ha := source_alpha_le weight s hp hc v
    have hd := hdelta v
    linarith

variable (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (own : V → Fin R → Bool)

omit [DecidableEq V] in

lemma scaled_internal (c : Components weight s t) :
    mass (fun d : IntDir (componentLabel weight s t) c => L * weight d)
      (inside (componentLabel weight s t) c (s (vertex weight s t c))) =
    (L : ℝ) * (base + delta weight s base (vertex weight s t c) -
      alpha weight s t (vertex weight s t c)) := by
  have he := mass_inside_eq weight (fun d => L * weight d) s t (vertex weight s t c)
  rw [vertex_color] at he
  rw [he, mass_scaled, internal_mass_eq weight s t base]

lemma componentAbs_range (hbase : (23 / 25 : ℝ) ≤ base)
    (c : Components weight s t) (z : Block (componentLabel weight s t) R none → ℕ) :
    componentAbs weight s t R J L base own c z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact abs_nonneg _
  · change |∫ x, componentFactor (componentLabel weight s t) R
      (strongGraph weight s t).connectedComponentMk s (Real.exp (-(L : ℝ) * base)) own J c z x
      ∂batchMeasure (fun i : Block (componentLabel weight s t) R (some c) => L * weight i.1.2)| ≤ 1
    apply SharpRamseyFive.HighMoment.integral_abs_component_le_one R
      (Real.exp (-(L : ℝ) * base)) (componentLabel weight s t)
      (strongGraph weight s t).connectedComponentMk s own (fun d => L * weight d) J
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have hb : 0 ≤ base := by linarith
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg L.coe_nonneg hb)

lemma simple_bound {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (hdelta : ∀ v, |delta weight s base v| ≤ (17 / 100 : ℝ)) (hK : K ≤ R / 2)
    (c : Components weight s (1 / (100 * p)))
    (hs : c ∈ simpleSet weight s (1 / (100 * p)))
    (z : Block (componentLabel weight s (1 / (100 * p))) R none → ℕ) :
    componentAbs weight s (1 / (100 * p)) R J L base own c z ≤
      Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) *
        (extraWeight weight s (1 / (100 * p)) R J K L base c +
          badIndicator (isBad weight s (1 / (100 * p)) R) c z) := by
  let v := vertex weight s (1 / (100 * p)) c
  have hv : (strongGraph weight s (1 / (100 * p))).connectedComponentMk v = c :=
    vertex_color weight s (1 / (100 * p)) c
  have hs' : ∀ u, (strongGraph weight s (1 / (100 * p))).connectedComponentMk u = c → u = v :=
    (Finset.mem_filter.mp hs).2
  have hi := simple_inside_univ s weight (1 / (100 * p)) v (by
    intro u hu
    exact hs' u (hu.trans hv))
  rw [hv] at hi
  have hm := source_local_data weight s hp hc base hlower hdelta v
  exact simple_component_designations (componentLabel weight s (1 / (100 * p))) R
    (strongGraph weight s (1 / (100 * p))).connectedComponentMk s own (fun d => L * weight d)
    J c ⟨v,hv⟩ hs' (fun d hd => by
      simpa only [hv] using direction_internal_or_external weight s (1 / (100 * p)) hd)
    hi z hL (scaled_internal weight s (1 / (100 * p)) L base c)
    hm.1 (by linarith) (alpha_nonneg weight s _ v) hm.2 hK

lemma nonsimple_bound {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (c : Components weight s (1 / (100 * p)))
    (z : Block (componentLabel weight s (1 / (100 * p))) R none → ℕ) :
    componentAbs weight s (1 / (100 * p)) R J L base own c z ≤
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) := by
  let v := vertex weight s (1 / (100 * p)) c
  have hv : (strongGraph weight s (1 / (100 * p))).connectedComponentMk v = c :=
    vertex_color weight s (1 / (100 * p)) c
  change |∫ x, componentFactor (componentLabel weight s (1 / (100 * p))) R
    (strongGraph weight s (1 / (100 * p))).connectedComponentMk s
    (Real.exp (-(L : ℝ) * base)) own J c z x
    ∂batchMeasure (fun i : Block (componentLabel weight s (1 / (100 * p))) R (some c) =>
      L * weight i.1.2)| ≤ _
  apply abs_integral_le_integral_abs.trans
  apply nonsimple_component_attenuation (componentLabel weight s (1 / (100 * p))) R
    (strongGraph weight s (1 / (100 * p))).connectedComponentMk s own (fun d => L * weight d)
    J c ⟨v,hv⟩ z (fun d hd => by
      simpa only [hv] using direction_internal_or_external weight s (1 / (100 * p)) hd)
    hL (scaled_internal weight s (1 / (100 * p)) L base c) _ (by linarith)
  rw [← internal_mass_eq]
  exact source_internal_mass_lower weight s hp hc hlower v

omit [DecidableEq V] in

lemma extraWeight_nonneg (c : Components weight s t) :
    0 ≤ extraWeight weight s t R J K L base c := by
  unfold extraWeight
  apply add_nonneg (add_nonneg (by positivity) (pow_nonneg (alpha_nonneg weight s t _) _))
  split_ifs <;> positivity

theorem component_product_designated {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (hdelta : ∀ v, |delta weight s base v| ≤ (17 / 100 : ℝ)) (hK : K ≤ R / 2) :
    (∫ z, blockTrunc (componentLabel weight s (1 / (100 * p))) R J none z *
      ∏ c, componentAbs weight s (1 / (100 * p)) R J L base own c z
      ∂batchMeasure (fun i : Block (componentLabel weight s (1 / (100 * p))) R none =>
        L * weight i.1.2)) ≤
      designatedBound weight s (1 / (100 * p)) R J K L base := by
  exact integral_product_le _ (simpleSet weight s (1 / (100 * p))) _ _ _ _ _
    (blockTrunc_range _ R J none) _
    (componentAbs_range weight s (1 / (100 * p)) R J L base own hbase)
    (simple_bound weight s R J K L base own hp hc hL hbase hlower hdelta hK)
    (fun c _ z => nonsimple_bound weight s R J L base own hp hc hL hbase hlower c z)

variable {H : Type} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in

theorem truncated_power_designated (sf : H → Finset D) (of : H → Fin R → Bool)
    {p : ℕ} (hp : 0 < p) (hL : 10000 ≤ (L : ℝ))
    (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ h, (3 / 4 : ℝ) ≤ mass weight (sf h))
    (hdelta : ∀ h, |mass weight (sf h) - base| ≤ (17 / 100 : ℝ)) (hK : K ≤ R / 2) :
    (∫ ω, HighMoment.allTrunc R J ω *
      (∑ h : H, scoreTerm (sf h) (Real.exp (-(L : ℝ) * base)) (of h)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        ∑ f : Fin p → H, designatedBound weight (sf ∘ f) (1 / (100 * p)) R J K L base := by
  have hb : Real.exp (-(L : ℝ) * base) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have hbas : 0 ≤ base := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) hbas
  apply (HighMoment.truncated_moment_le_tuple_sum R sf _ of weight
    (fun d => L * weight d) (1 / (100 * p)) J p hb).trans
  apply Finset.sum_le_sum
  intro f _
  exact component_product_designated weight (sf ∘ f) R J K L base (of ∘ f) hp
    (by simp) hL hbase (fun v => hlower (f v)) (fun v => hdelta (f v)) hK

end SharpRamseyFive.AmbientDesignations

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_CompleteProgramWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)
omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma complete_program_weight (rate : D → ℝ≥0) (denom : ℝ) (hd : denom ≠ 0)
    (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (c : completePrograms lines K low E s) :
    weight (fun p : B × D => rate p.2) (finish lines K s c.val.2).2 =
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s c.val.2 := by
  rw [trace_weight lines rate denom hd K low s c.val.2 c.property.1,
    c.property.2.2]
  ring
omit [Fintype D] in

lemma complete_program_sum (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (E : Finset V) (s : State V H D B) :
    (∑ c : completePrograms lines K low E s,
      weight (fun p : B × D => rate p.2) (finish lines K s c.val.2).2) ≤
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        ∑ n : Fin (Fintype.card V - E.card + 1),
          branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  classical
  simp_rw [complete_program_weight lines rate denom hd.ne' K low E s]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (weight_nonneg _ _) (pow_nonneg hd.le _))
  change (∑ c : {c : AllPrograms lines K E s // CompleteProgram lines K low E s c},
    dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s c.val.2) ≤ _
  have hsub := Finset.sum_subtype (p := CompleteProgram lines K low E s)
    (F := completePrograms_fintype lines K low E s)
    (Finset.univ.filter (CompleteProgram lines K low E s)) (fun _ => by simp)
    (fun c : AllPrograms lines K E s => dWeight (Action lines K) (advance lines K)
      (programCost lines rate denom K low) s c.2)
  rw [← hsub, Finset.sum_filter]
  change (∑ c : AllPrograms lines K E s,
    if CompleteProgram lines K low E s c then
      dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s c.2
    else 0) ≤ _
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro n _
  apply le_trans _ (program_enumeration lines rate denom b mass hd.le hb hm hmass
    K N₁ N₂ low hN₁ hN₂ n.val s)
  apply Finset.sum_le_sum
  intro w _
  by_cases hc : CompleteProgram lines K low E s ⟨n, w⟩
  · simp only [ite_eq_left hc, ite_eq_left hc.2.1]
    exact le_rfl
  · simp only [ite_eq_right hc]
    split_ifs
    · exact dWeight_nonneg (Action lines K) (advance lines K) _
        (programCost_nonneg lines rate denom hd.le K low) s w
    · exact le_rfl

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma selected_bad_event_cover (K J h : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (Fintype.card B / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (E : Finset V) (s : State V H D B) (f : V → H) (ω : (B × D) → ℕ)
    (hω : ω ∈ selectedBadEvent lines K J low E s f) :
    ∃ c : completePrograms lines K low E s,
      (finish lines K s c.val.2).1 = f ∧ ω ∈ positiveEvent (finish lines K s c.val.2).2 := by
  classical
  obtain ⟨hfi, hit, hpos, hco, hbad, htr⟩ := hω
  have hex : ∃ n, ∃ w : Word lines K n s,
      Segment lines f hit K low E Finset.univ s w ∧
        0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
    cases low with
    | false =>
      exact bad_program_high lines f hfi hit K J h hK hh
        hsize E s hco hbad (htr rfl) herr
    | true =>
      apply bad_program_low lines f hfi hit K h hK hh _ E s hco hbad herr
      simpa using hsize
  obtain ⟨n, w, hw, hq, hn⟩ := hex
  have hc : CompleteProgram lines K low E s ⟨⟨n, by omega⟩, w⟩ := by
    refine ⟨hw.2.2, hq, ?_⟩
    change degreeSum lines K s w = Fintype.card V - E.card
    have he := hw.2.1
    simp only [Finset.card_univ] at he
    omega
  refine ⟨⟨⟨⟨n, by omega⟩, w⟩, hc⟩, ?_, ?_⟩
  · funext v
    exact hw.1.1 v (Finset.mem_univ _)
  · intro p hp
    exact hpos p.1 p.2 (hw.1.2.2.1 p hp)

theorem selected_bad_completion_bound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (Fintype.card B / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (E : Finset V) (s : State V H D B) :
    (∑ f : V → H, (poissonLaw (fun p : B × D => rate p.2)).real
      (selectedBadEvent lines K J low E s f)) ≤
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        ∑ n : Fin (Fintype.card V - E.card + 1),
          branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  classical
  apply le_trans _ (complete_program_sum lines rate denom b mass hd hb hm hmass
    K N₁ N₂ low hN₁ hN₂ E s)
  apply decoded_static_union_bound rate
    (fun c : completePrograms lines K low E s => (finish lines K s c.val.2).2)
    (fun c => (finish lines K s c.val.2).1) (selectedBadEvent lines K J low E s)
  · intro f
    exact (Set.to_countable _).measurableSet
  · intro f ω hω
    exact selected_bad_event_cover lines K J h hK hh low hsize herr E s f ω hω

end SharpRamseyFive.CertificateCover

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H C : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]
omit [DecidableEq D] in

lemma restriction_preserving (rate : D → ℝ≥0) (lab : D → Option C) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R × D → ℕ => fun i : Block lab R none => ω i)
      (batchMeasure (fun i : Fin R × D => rate i.2))
      (batchMeasure (fun i : Block lab R none => rate i.1.2)) := by
  exact (measurePreserving_eval (fun c : Option C => batchMeasure
    (fun i : Block lab R c => rate i.1.2)) none).comp
      (measurePreserving_partition (fun i : Fin R × D => rate i.2) (fun i => lab i.2))
omit [DecidableEq D] in

lemma integral_restriction (rate : D → ℝ≥0) (lab : D → Option C) (R : ℕ)
    (F : (Block lab R none → ℕ) → ℝ) :
    (∫ z, F z ∂batchMeasure (fun i : Block lab R none => rate i.1.2)) =
      ∫ ω, F (fun i => ω i) ∂batchMeasure (fun i : Fin R × D => rate i.2) := by
  have h := restriction_preserving rate lab R
  rw [← h.map_eq]
  exact integral_map h.measurable.aemeasurable (measurable_of_countable F).aestronglyMeasurable
omit [Fintype D] [DecidableEq V] in

lemma label_none_external (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    {v : V} {d : D} (hd : d ∈ s v) (he : componentLabel weight s t d = none) :
    External weight s t d := by
  by_contra hn
  have hi := componentLabel_internal weight s t (Finset.mem_filter.mpr ⟨hd,hn⟩)
  rw [he] at hi
  cases hi

lemma touched_equals_shared (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R : ℕ) (ω : Fin R × D → ℕ) (v : V) :
    TupleComponents.hitBatches (touched (componentLabel weight s t) R
      ((strongGraph weight s t).connectedComponentMk v) (s v) (fun i => ω i)) =
      ResidualCertificate.touchedBatches s (selectedHit weight s t ω) v := by
  ext r
  simp only [TupleComponents.hitBatches, touched, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, ResidualCertificate.touchedBatches,
    ResidualCertificate.sharedBatches, Finset.mem_inter]
  constructor
  · rintro ⟨d,hd,hpos⟩
    obtain ⟨u,hu,hdiff⟩ := (external_iff_other weight s t hd).mp
      (label_none_external weight s t hd d.property)
    refine ⟨u, ?_, d, ⟨hd,hu⟩, d.property,hpos⟩
    intro he
    subst u
    exact hdiff rfl
  · rintro ⟨u,_,d,⟨hd,_⟩,he,hpos⟩
    exact ⟨⟨d,he⟩,hd,hpos⟩

omit [DecidableEq V] in
lemma selected_trunc (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R J : ℕ) (ω : Fin R × D → ℕ)
    (htr : blockTrunc (componentLabel weight s t) R J none (fun i => ω i) ≠ 0) :
    ∀ d, (Finset.univ.filter (fun r => selectedHit weight s t ω r d)).card ≤ J := by
  intro d
  by_cases hd : componentLabel weight s t d = none
  · have hp : lineTrunc R J (fun r => ω (r,d)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp htr ⟨d,hd⟩ (Finset.mem_univ _)
    have hh : (Finset.univ.filter (fun r => ω (r,d) ≠ 0)).card < J := by
      by_contra hn
      exact hp (ite_eq_right hn)
    simpa only [selectedHit, hd, true_and] using hh.le
  · simp only [selectedHit, hd, false_and, Finset.filter_false, Finset.card_empty]
    exact Nat.zero_le _

omit [Fintype D] [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma empty_coherent (lines : H → Finset D) (f g : V → H) (R K : ℕ)
    (E : Finset V) (hit : Fin R → D → Prop) (he : ∀ v ∈ E, g v = f v) :
    Coherent lines f hit K E (g,∅) := by
  refine ⟨he, ?_, ?_, ?_⟩
  · simp [ResidualCertificate.DictionaryInvariant, ResidualCertificate.paidDirections]
  · intro p hp
    exact False.elim (Finset.notMem_empty p hp)
  · simp
omit [Fintype H] [DecidableEq H] in

lemma bad_mass_le_selected_event (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (f g : V → H) (hf : Function.Injective f) (R J K : ℕ) (t : ℝ) (low : Bool)
    (A : Finset V) (he : ∀ v ∈ Finset.univ \ A, g v = f v) :
    vertexBadMass weight rate (lines ∘ f) t R J A ≤
      (StaticCertificates.poissonLaw (fun i : Fin R × D => rate i.2)).real
        (selectedBadEvent lines K J low (Finset.univ \ A) (g,∅) f) := by
  let lab := componentLabel weight (lines ∘ f) t
  let bad := fun v z => BAD (touched lab R
    ((strongGraph weight (lines ∘ f) t).connectedComponentMk v) (lines (f v)) z)
  let T := blockTrunc lab R J none
  let E : Set ((Fin R × D) → ℕ) := selectedBadEvent lines K J low (Finset.univ \ A) (g,∅) f
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  change (∫ z, T z * ∏ v ∈ A, badIndicator bad v z
    ∂batchMeasure (fun i : Block lab R none => rate i.1.2)) ≤ _
  rw [integral_restriction rate lab R]
  have hi : Integrable (fun ω : Fin R × D → ℕ =>
      T (fun i => ω i) * ∏ v ∈ A, badIndicator bad v (fun i => ω i))
      (batchMeasure (fun i : Fin R × D => rate i.2)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (badTerm_range T (blockTrunc_range lab R J none)
      bad A (fun i => ω i)).1]
    exact (badTerm_range T (blockTrunc_range lab R J none) bad A (fun i => ω i)).2
  change _ ≤ (batchMeasure (fun i : Fin R × D => rate i.2)).real E
  rw [← integral_indicator_one hE]
  apply integral_mono hi ((integrable_const (1 : ℝ)).indicator hE)
  intro ω
  dsimp only
  by_cases hz : T (fun i => ω i) * ∏ v ∈ A, badIndicator bad v (fun i => ω i) = 0
  · rw [hz]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  · have ht : T (fun i => ω i) ≠ 0 := (mul_ne_zero_iff.mp hz).1
    have hb : ∀ v ∈ A, bad v (fun i => ω i) := by
      intro v hv
      have hn := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).2 v hv
      by_contra hn'
      exact hn (ite_eq_right hn')
    have hmem : ω ∈ E := by
      refine ⟨hf, selectedHit weight (lines ∘ f) t ω, ?_, ?_, ?_, ?_⟩
      · intro r d hd
        exact hd.2
      · exact empty_coherent lines f g R K (Finset.univ \ A) _ he
      · intro v hv
        have hvA : v ∈ A := by simpa using hv
        have hvb := hb v hvA
        change R / 2 ≤ (TupleComponents.hitBatches (touched lab R
          ((strongGraph weight (lines ∘ f) t).connectedComponentMk v) (lines (f v))
          (fun i => ω i))).card at hvb
        change R / 2 ≤ (TupleComponents.hitBatches (touched
          (componentLabel weight (lines ∘ f) t) R
          ((strongGraph weight (lines ∘ f) t).connectedComponentMk v)
          ((lines ∘ f) v) (fun i => ω i))).card at hvb
        rw [touched_equals_shared weight (lines ∘ f) t R ω v] at hvb
        simpa only [Fintype.card_fin, Function.comp_def] using hvb
      · intro _
        exact selected_trunc weight (lines ∘ f) t R J ω ht
    rw [Set.indicator_of_mem hmem]
    exact (badTerm_range T (blockTrunc_range lab R J none) bad A (fun i => ω i)).2
omit [Fintype D] [Fintype V] [DecidableEq V] in

lemma vertex_injective (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) : Function.Injective (vertex weight s t) := by
  intro c d he
  have h := congrArg (strongGraph weight s t).connectedComponentMk he
  simpa only [vertex_color] using h

lemma component_bad_mass_eq_vertex (weight rate : D → ℝ≥0) (s : V → Finset D)
    (t : ℝ) (R J : ℕ) (U : Finset (Components weight s t)) :
    badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => rate i.1.2))
      (blockTrunc (componentLabel weight s t) R J none)
      (isBad weight s t R) U =
      vertexBadMass weight rate s t R J (U.image (vertex weight s t)) := by
  unfold badMass vertexBadMass
  congr 1
  funext z
  congr 1
  rw [Finset.prod_image (fun _ _ _ _ he => vertex_injective weight s t he)]
  apply Finset.prod_congr rfl
  intro c hc
  simp only [badIndicator, isBad, vertex_color]
  split_ifs with h <;> simp only [h, ite_true, ite_false]

theorem bad_residual_sum_le (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R : ℕ) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (A : Finset V) (g : V → H) :
    (∑ f : V → H, if Function.Injective f ∧ (∀ v ∉ A, g v = f v) then
      vertexBadMass weight rate (lines ∘ f) t R J A else 0) ≤
      denom ^ A.card * ∑ n : Fin (A.card + 1),
        branchingBound (V := V) (B := Fin R) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  have hbnd := selected_bad_completion_bound (V := V) (B := Fin R)
    lines rate denom b mass hd hb hm hmass K J h N₁ N₂ hK hh low
    (by simpa only [Fintype.card_fin] using hsize) herr hN₁ hN₂
    (Finset.univ \ A) (g,∅)
  have heq : Fintype.card V - (Finset.univ \ A).card = A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp only [Finset.card_univ]
    have := Finset.card_le_card (Finset.subset_univ A)
    simp only [Finset.card_univ] at this
    omega
  rw [Fin.sum_univ_eq_sum_range] at hbnd ⊢
  simp only [heq, StaticCertificates.weight, Finset.prod_empty, one_mul] at hbnd
  apply le_trans _ hbnd
  apply Finset.sum_le_sum
  intro f hf
  split_ifs with hfi
  · apply bad_mass_le_selected_event weight rate lines f g hfi.1 R J K t low A
    intro v hv
    exact hfi.2 v (Finset.mem_sdiff.mp hv).2
  · exact ENNReal.toReal_nonneg

end SharpRamseyFive.SelectionBridge

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma labelled_injective (f : V → H) : Function.Injective (labelled f) := by
  intro u v h
  exact congrArg Prod.snd h

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma labelled_map_injective : Function.Injective (labelled : (V → H) → (V → H × V)) := by
  intro f g h
  funext v
  exact congrArg Prod.fst (congrFun h v)

end SharpRamseyFive.SelectionBridge
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LabelledFilterCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [DecidableEq V] [DecidableEq H] in
lemma labelled_filter_card (P : H → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : H × V => P x.1)).card =
      (Finset.univ.filter P).card * Fintype.card V := by
  have he : Finset.univ.filter (fun x : H × V => P x.1) =
      (Finset.univ.filter P) ×ˢ (Finset.univ : Finset V) := by
    ext z
    simp
  rw [he, Finset.card_product, Finset.card_univ]
omit [DecidableEq V] in

lemma vertexBadMass_nonneg (weight rate : D → ℝ≥0) (s : V → Finset D)
    (t : ℝ) (R J : ℕ) (A : Finset V) : 0 ≤ vertexBadMass weight rate s t R J A := by
  unfold vertexBadMass
  exact badMass_nonneg _ _ (blockTrunc_range _ R J none) _ A

theorem all_bad_residual_sum_le (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R : ℕ) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (A : Finset V) (g : V → H) :
    (∑ f : V → H, if (∀ v ∉ A, g v = f v) then
      vertexBadMass weight rate (lines ∘ f) t R J A else 0) ≤
      denom ^ A.card * ∑ n : Fin (A.card + 1),
        branchingBound (V := V) (B := Fin R) (fun z : H × V => lines z.1)
          rate denom b mass K (N₁ * Fintype.card V) (N₂ * Fintype.card V) low ^ n.val := by
  let F : (V → H × V) → ℝ := fun f =>
    if Function.Injective f ∧ (∀ v ∉ A, labelled g v = f v) then
      vertexBadMass weight rate ((fun z : H × V => lines z.1) ∘ f) t R J A else 0
  have hF (f : V → H × V) : 0 ≤ F f := by
    dsimp [F]
    split_ifs
    · exact vertexBadMass_nonneg weight rate _ t R J A
    · exact le_rfl
  have he (f : V → H) : F (labelled f) =
      if (∀ v ∉ A, g v = f v) then vertexBadMass weight rate (lines ∘ f) t R J A else 0 := by
    have ha : (∀ v ∉ A, labelled g v = labelled f v) ↔ (∀ v ∉ A, g v = f v) := by
      simp only [labelled, Prod.mk.injEq, and_true]
    simp only [F, labelled_injective, true_and, ha]
    rfl
  calc
    _ = ∑ f : V → H, F (labelled f) := by simp only [he]
    _ = ∑ f ∈ Finset.univ.image (labelled : (V → H) → (V → H × V)), F f := by
      rw [Finset.sum_image (fun _ _ _ _ h => labelled_map_injective h)]
    _ ≤ ∑ f : V → H × V, F f :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun f _ _ => hF f)
    _ ≤ _ := by
      apply bad_residual_sum_le weight rate (fun z : H × V => lines z.1) t R
        denom b mass hd hb hm (fun u => hmass u.1) K J h
        (N₁ * Fintype.card V) (N₂ * Fintype.card V) hK hh low hsize herr
      · intro d
        exact (labelled_filter_card (V := V) (H := H) (fun u => d ∈ lines u)).le.trans
          (Nat.mul_le_mul_right _ (hN₁ d))
      · intro d e hde
        exact (labelled_filter_card (V := V) (H := H) (fun u => d ∈ lines u ∧ e ∈ lines u)).le.trans
          (Nat.mul_le_mul_right _ (hN₂ d e hde))

end SharpRamseyFive.SelectionBridge

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma completionSum_mono (E : Finset V) (g : V → H) (F G : (V → H) → ℝ)
    (h : ∀ f, Agrees E g f → F f ≤ G f) :
    completionSum E g F ≤ completionSum E g G := by
  apply Finset.sum_le_sum
  intro f _
  split_ifs with hf
  · exact h f hf
  · exact le_rfl
omit [DecidableEq H] in

lemma completionSum_congr (E : Finset V) (g : V → H) (F G : (V → H) → ℝ)
    (h : ∀ f, Agrees E g f → F f = G f) :
    completionSum E g F = completionSum E g G := by
  apply le_antisymm <;> apply completionSum_mono
  · exact fun f hf => le_of_eq (h f hf)
  · exact fun f hf => le_of_eq (h f hf).symm

omit [DecidableEq H] in
lemma completionSum_mul (E : Finset V) (g : V → H) (c : ℝ) (F : (V → H) → ℝ) :
    completionSum E g (fun f => c * F f) = c * completionSum E g F := by
  simp only [completionSum, Finset.mul_sum, mul_ite, mul_zero]

omit [DecidableEq H] in
lemma completionSum_sum {ι : Type} (T : Finset ι) (E : Finset V) (g : V → H)
    (F : ι → (V → H) → ℝ) :
    completionSum E g (fun f => ∑ i ∈ T, F i f) =
      ∑ i ∈ T, completionSum E g (F i) := by
  unfold completionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : Agrees E g f <;> simp [h]

omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma agrees_erase_iff (E : Finset V) (g f : V → H) {u : V} (hu : u ∈ E) (x : H) :
    Agrees (E.erase u) (Function.update g u x) f ↔ Agrees E g f ∧ f u = x := by
  constructor
  · intro h
    constructor
    · intro v hv
      have hvu : v ≠ u := by intro he; exact hv (he ▸ hu)
      simpa only [Function.update_of_ne hvu] using h v (by simp [hv])
    · simpa using h u (Finset.notMem_erase u E)
  · rintro ⟨h, hx⟩ v hv
    by_cases hvu : v = u
    · subst v; simpa using hx
    · rw [Function.update_of_ne hvu]
      exact h v (by simpa [hvu] using hv)

lemma completionSum_expose (E : Finset V) (g : V → H) {u : V} (hu : u ∈ E)
    (F : (V → H) → ℝ) :
    completionSum E g F = ∑ x : H, completionSum (E.erase u) (Function.update g u x) F := by
  unfold completionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [agrees_erase_iff E g f hu]
  by_cases h : Agrees E g f
  · simp [h, eq_comm]
  · simp [h]

omit [Fintype V] in
lemma prod_erase_le (a : V → ℝ) (ha : ∀ u, a u ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset V) (v : V) : (∏ u ∈ S, a u) ≤ ∏ u ∈ S.erase v, a u := by
  by_cases hv : v ∈ S
  · rw [← Finset.mul_prod_erase S a hv]
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun u _ => (ha u).1)) (ha v).2
  · rw [Finset.erase_eq_of_notMem hv]

omit [Fintype V] in
lemma double_erase_sdiff (E S : Finset V) (u v : V) (hu : u ∈ S) :
    (E.erase u).erase v \ (S.erase u).erase v = (E \ S).erase v := by
  ext w
  by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp [hwu, hwv, hu]

omit [Fintype H] [DecidableEq H] in
lemma term_shift_step (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (W : H → H → ℝ) (ha : ∀ u f, a u f ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ x y, 0 ≤ W x y) (hB : ∀ A f, 0 ≤ B A f)
    (hmono : ∀ A A', A' ⊆ A → ∀ f, B A f ≤ B A' f)
    (hshift : ∀ u f, a u f ≤ ∑ v ∈ Finset.univ.erase u, W (f u) (f v))
    (E S : Finset V) {u : V} (hu : u ∈ S) (f : V → H) :
    term a B E S f ≤ ∑ v ∈ Finset.univ.erase u,
      W (f u) (f v) * term a B ((E.erase u).erase v) ((S.erase u).erase v) f := by
  have hp : 0 ≤ (∏ w ∈ S.erase u, a w f) * B (E \ S) f :=
    mul_nonneg (Finset.prod_nonneg (fun w _ => (ha w f).1)) (hB _ f)
  calc
    term a B E S f = a u f * ((∏ w ∈ S.erase u, a w f) * B (E \ S) f) := by
      rw [term, ← Finset.mul_prod_erase S (fun w => a w f) hu, mul_assoc]
    _ ≤ (∑ v ∈ Finset.univ.erase u, W (f u) (f v)) *
        ((∏ w ∈ S.erase u, a w f) * B (E \ S) f) :=
      mul_le_mul_of_nonneg_right (hshift u f) hp
    _ = ∑ v ∈ Finset.univ.erase u, W (f u) (f v) *
        ((∏ w ∈ S.erase u, a w f) * B (E \ S) f) := by rw [Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_left _ (hW _ _)
      unfold term
      rw [double_erase_sdiff E S u v hu]
      apply mul_le_mul (prod_erase_le (fun w => a w f) (fun w => ha w f) _ v)
        (hmono _ _ (Finset.erase_subset v _) f) (hB _ f)
      exact Finset.prod_nonneg (fun w _ => (ha w f).1)

lemma sum_known_partner (E : Finset V) (g : V → H) {u v : V} (hu : u ∈ E) (hv : v ∉ E)
    (W : H → H → ℝ) (F : (V → H) → ℝ) (X C : ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hX : 0 ≤ X)
    (hrow : ∑ x : H, W x (g v) ≤ C)
    (hF : ∀ x : H, completionSum (E.erase u) (Function.update g u x) F ≤ X) :
    completionSum E g (fun f => W (f u) (f v) * F f) ≤ C * X := by
  rw [completionSum_expose E g hu]
  calc
    _ ≤ ∑ x : H, W x (g v) * X := by
      apply Finset.sum_le_sum
      intro x _
      have he : completionSum (E.erase u) (Function.update g u x)
          (fun f => W (f u) (f v) * F f) = W x (g v) *
            completionSum (E.erase u) (Function.update g u x) F := by
        rw [← completionSum_mul]
        apply completionSum_congr
        intro f hf
        have hfu : f u = x := by simpa using hf u (Finset.notMem_erase u E)
        have hvu : v ≠ u := by intro he; exact hv (he ▸ hu)
        have hfv : f v = g v := by
          simpa only [Function.update_of_ne hvu] using hf v (by simp [hv])
        rw [hfu, hfv]
      rw [he]
      exact mul_le_mul_of_nonneg_left (hF x) (hW _ _)
    _ = (∑ x : H, W x (g v)) * X := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hX

lemma sum_new_partner (E : Finset V) (g : V → H) {u v : V}
    (hu : u ∈ E) (hv : v ∈ E) (hne : v ≠ u)
    (W : H → H → ℝ) (F : (V → H) → ℝ) (X C : ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hX : 0 ≤ X)
    (hpair : (∑ x : H, ∑ y : H, W x y) ≤ C)
    (hF : ∀ x y : H, completionSum ((E.erase u).erase v)
      (Function.update (Function.update g u x) v y) F ≤ X) :
    completionSum E g (fun f => W (f u) (f v) * F f) ≤ C * X := by
  rw [completionSum_expose E g hu]
  have hv' : v ∈ E.erase u := Finset.mem_erase.mpr ⟨hne,hv⟩
  calc
    _ ≤ ∑ x : H, ∑ y : H, W x y * X := by
      apply Finset.sum_le_sum
      intro x _
      rw [completionSum_expose _ _ hv']
      apply Finset.sum_le_sum
      intro y _
      have he : completionSum ((E.erase u).erase v)
          (Function.update (Function.update g u x) v y)
          (fun f => W (f u) (f v) * F f) = W x y *
            completionSum ((E.erase u).erase v)
              (Function.update (Function.update g u x) v y) F := by
        rw [← completionSum_mul]
        apply completionSum_congr
        intro f hf
        have hfu : f u = x := by
          simpa only [Function.update_of_ne hne.symm, Function.update_self] using
            hf u (by simp)
        have hfv : f v = y := by simpa using hf v (by simp)
        rw [hfu, hfv]
      rw [he]
      exact mul_le_mul_of_nonneg_left (hF x y) (hW _ _)
    _ = (∑ x : H, ∑ y : H, W x y) * X := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpair hX

theorem shift_bad_enumeration (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (W : H → H → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ u f, a u f ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ x y, 0 ≤ W x y) (hB : ∀ A f, 0 ≤ B A f)
    (hmono : ∀ A A', A' ⊆ A → ∀ f, B A f ≤ B A' f)
    (hshift : ∀ u f, a u f ≤ ∑ v ∈ Finset.univ.erase u, W (f u) (f v))
    (hrow : ∀ y, (∑ x : H, W x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, W x y) ≤ C ^ 2)
    (hbad : ∀ A g, completionSum A g (B A) ≤ C ^ A.card)
    (E S : Finset V) (hS : S ⊆ E) (g : V → H) :
    completionSum E g (term a B E S) ≤ ((Fintype.card V + 1 : ℝ) * C) ^ E.card := by
  let M : ℝ := (Fintype.card V + 1) * C
  have hCM : C ≤ M := by dsimp [M]; nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
  have hM : 0 ≤ M := hC.trans hCM
  suffices hall : ∀ E : Finset V, ∀ S, S ⊆ E → ∀ g : V → H,
      completionSum E g (term a B E S) ≤ M ^ E.card from hall E S hS g
  intro E
  refine Finset.strongInductionOn E ?_
  intro E ih S hS g
  by_cases hs : S = ∅
  · subst S
    have he : term a B E ∅ = B E := by
      funext f
      simp [term]
    rw [he]
    exact (hbad E g).trans (pow_le_pow_left₀ hC hCM _)
  obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  have huE := hS hu
  have hsub := Finset.erase_ssubset huE
  have hS' : S.erase u ⊆ E.erase u := Finset.erase_subset_erase u hS
  have hcard : E.card = (E.erase u).card + 1 := (Finset.card_erase_add_one huE).symm
  calc
    _ ≤ completionSum E g (fun f => ∑ v ∈ Finset.univ.erase u,
        W (f u) (f v) * term a B ((E.erase u).erase v) ((S.erase u).erase v) f) := by
      apply completionSum_mono
      intro f _
      exact term_shift_step a B W ha hW hB hmono hshift E S hu f
    _ = ∑ v ∈ Finset.univ.erase u, completionSum E g
        (fun f => W (f u) (f v) * term a B ((E.erase u).erase v) ((S.erase u).erase v) f) :=
      completionSum_sum _ E g _
    _ ≤ ∑ _v ∈ Finset.univ.erase u, C * M ^ (E.erase u).card := by
      apply Finset.sum_le_sum
      intro v hv
      have hne : v ≠ u := (Finset.mem_erase.mp hv).1
      by_cases hvE : v ∈ E
      · have hv' : v ∈ E.erase u := Finset.mem_erase.mpr ⟨hne,hvE⟩
        have hsmall : (E.erase u).erase v ⊂ E :=
          Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) hsub
        have hSt : (S.erase u).erase v ⊆ (E.erase u).erase v :=
          Finset.erase_subset_erase v hS'
        have hbnd := sum_new_partner E g huE hvE hne W
          (term a B ((E.erase u).erase v) ((S.erase u).erase v))
          (M ^ ((E.erase u).erase v).card) (C ^ 2) hW (pow_nonneg hM _) hpair
          (fun x y => ih _ hsmall _ hSt _)
        apply hbnd.trans
        rw [show (E.erase u).card = ((E.erase u).erase v).card + 1 from
          (Finset.card_erase_add_one hv').symm, pow_succ M]
        calc
          _ = (C * C) * M ^ ((E.erase u).erase v).card := by ring
          _ ≤ (C * M) * M ^ ((E.erase u).erase v).card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCM hC) (pow_nonneg hM _)
          _ = _ := by ring
      · have hvS : v ∉ S := fun h => hvE (hS h)
        rw [Finset.erase_eq_of_notMem (fun h => hvE (Finset.erase_subset u E h)),
          Finset.erase_eq_of_notMem (fun h => hvS (Finset.erase_subset u S h))]
        exact sum_known_partner E g huE hvE W (term a B (E.erase u) (S.erase u))
          (M ^ (E.erase u).card) C hW (pow_nonneg hM _) (hrow (g v))
          (fun x => ih _ hsub _ hS' _)
    _ ≤ M * M ^ (E.erase u).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
      change ((Finset.univ.erase u).card : ℝ) * C ≤ M
      have hc : ((Finset.univ.erase u).card : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset u (Finset.univ : Finset V))
      dsimp [M]
      nlinarith
    _ = _ := by rw [hcard, pow_succ]; ring

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [DecidableEq V] in

lemma vertexBadMass_antitone (weight rate : D → ℝ≥0) (s : V → Finset D)
    (t : ℝ) (R J : ℕ) {A A' : Finset V} (hA : A' ⊆ A) :
    vertexBadMass weight rate s t R J A ≤ vertexBadMass weight rate s t R J A' := by
  unfold vertexBadMass badMass
  apply integral_mono
    (badTerm_integrable _ _ (blockTrunc_range _ R J none) _ A)
    (badTerm_integrable _ _ (blockTrunc_range _ R J none) _ A')
  intro z
  apply mul_le_mul_of_nonneg_left _ (blockTrunc_range _ R J none z).1
  exact Finset.prod_le_prod_of_subset_of_le_one hA
    (fun v _ => (badIndicator_range _ v z).1)
    (fun v _ _ => (badIndicator_range _ v z).2)

lemma sum_powers_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), x ^ i) ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (1 + x) ^ n + x ^ (n + 1) := add_le_add ih le_rfl
      _ ≤ (1 + x) ^ n + x * (1 + x) ^ n := by
        rw [pow_succ']
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hx (by linarith : x ≤ 1 + x) n) hx)
      _ = _ := by rw [pow_succ]; ring

lemma actual_bad_completion (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R : ℕ) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (A : Finset V) (g : V → H) :
    completionSum A g (fun f => vertexBadMass weight rate (lines ∘ f) t R J A) ≤
      (denom * (1 + branchingBound (V := V) (B := Fin R)
        (fun z : H × V => lines z.1) rate denom b mass K
        (N₁ * Fintype.card V) (N₂ * Fintype.card V) low)) ^ A.card := by
  have he : completionSum A g (fun f => vertexBadMass weight rate (lines ∘ f) t R J A) =
      ∑ f : V → H, if (∀ v ∉ A, g v = f v) then
        vertexBadMass weight rate (lines ∘ f) t R J A else 0 := by
    unfold completionSum
    apply Finset.sum_congr rfl
    intro f _
    have : Agrees A g f ↔ (∀ v ∉ A, g v = f v) := by
      simp only [Agrees, eq_comm]
    simp only [this]
  rw [he]
  apply (all_bad_residual_sum_le weight rate lines t R denom b mass hd hb hm hmass
    K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ A g).trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hd.le _)
  rw [Fin.sum_univ_eq_sum_range]
  apply sum_powers_le
  exact branchingBound_nonneg _ _ _ _ _ hd.le (by linarith) hm _ _ _ _

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma shiftKernel_range (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : shiftKernel weight lines p K x y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold shiftKernel
  exact ⟨le_min zero_le_one (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (mass_nonneg _ _)) _),
    min_le_left _ _⟩

end SharpRamseyFive.SingletonEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma shift_le_kernel_sum (weight : D → ℝ≥0) (lines : H → Finset D)
    {p K : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p) (hK : K ≠ 0)
    (u : V) (f : V → H) :
    alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K ≤
      ∑ v ∈ Finset.univ.erase u, shiftKernel weight lines p K (f u) (f v) := by
  let s := lines ∘ f
  let T := otherComponents weight s (1 / (100 * p)) u
  have hsub : T ⊆ Finset.univ.erase u := by
    intro v hv
    simp only [T, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact Finset.mem_erase.mpr ⟨by intro he; subst v; exact hv rfl, Finset.mem_univ _⟩
  have hmass := external_mass_le_sum weight s (1 / (100 * p)) u
  have hα := source_alpha_le weight s hp hc u
  have hα0 := alpha_nonneg weight s (1 / (100 * p)) u
  have hone : alpha weight s (1 / (100 * p)) u ^ K ≤ 1 :=
    pow_le_one₀ hα0 (by linarith)
  by_cases hT : T.Nonempty
  · obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image T
      (fun v => mass weight (s u ∩ s v)) hT
    have hcard : (T.card : ℝ) ≤ p := by
      exact_mod_cast (Finset.card_le_card (Finset.subset_univ T)).trans
        (by simpa only [Finset.card_univ] using hc)
    have hle : alpha weight s (1 / (100 * p)) u ≤ p * mass weight (s u ∩ s v) := calc
      _ ≤ ∑ w ∈ T, mass weight (s u ∩ s w) := hmass
      _ ≤ T.card * mass weight (s u ∩ s v) := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul T
          (fun w => mass weight (s u ∩ s w)) (mass weight (s u ∩ s v)) hmax
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (mass_nonneg _ _)
    apply (le_min hone (pow_le_pow_left₀ hα0 hle K)).trans
    exact Finset.single_le_sum
      (fun w _ => (shiftKernel_range weight lines p K (f u) (f w)).1) (hsub hv)
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hzero : alpha weight s (1 / (100 * p)) u = 0 := by
      apply le_antisymm _ hα0
      change mass weight (externalPart weight s (1 / (100 * p)) u) ≤ 0
      simpa only [show otherComponents weight s (1 / (100 * p)) u = ∅ from he,
        Finset.sum_empty] using hmass
    change alpha weight s (1 / (100 * p)) u ^ K ≤ _
    rw [hzero, zero_pow hK]
    exact Finset.sum_nonneg (fun w _ => (shiftKernel_range weight lines p K (f u) (f w)).1)

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

section Finite
variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in

theorem moment_le_of_cover (x : α → ℝ) (a : β → ℝ) (T : Finset β)
    (K : ℕ) (hK : K ≠ 0) (C : ℝ) (_hC : 0 ≤ C)
    (hx : ∀ v, 0 ≤ x v) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ v, 0 < x v → ∃ i ∈ T, a i ≤ x v ∧ x v ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun v => a i ≤ x v)).card : ℝ) * a i ^ K ≤ C) :
    (∑ v, x v ^ K) ≤ (T.card : ℝ) * (2 : ℝ) ^ K * C := by
  classical
  have hp (v : α) : x v ^ K ≤
      ∑ i ∈ T, if a i ≤ x v then (2 * a i) ^ K else 0 := by
    by_cases hv : 0 < x v
    · obtain ⟨i, hi, hain, hle⟩ := hcover v hv
      apply (pow_le_pow_left₀ (hx v) hle K).trans
      have hs := Finset.single_le_sum (f := fun j =>
        if a j ≤ x v then (2 * a j) ^ K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa [hain] using hs
    · have hz : x v = 0 := le_antisymm (le_of_not_gt hv) (hx v)
      simp only [hz, zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  calc
    (∑ v, x v ^ K) ≤ ∑ v, ∑ i ∈ T, if a i ≤ x v then (2 * a i) ^ K else 0 :=
      Finset.sum_le_sum (fun v _ => hp v)
    _ = ∑ i ∈ T, (2 : ℝ) ^ K *
        (((Finset.univ.filter (fun v => a i ≤ x v)).card : ℝ) * a i ^ K) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_pow]
      ring
    _ ≤ ∑ _i ∈ T, (2 : ℝ) ^ K * C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcount i hi) (by positivity)
    _ = _ := by simp; ring

omit [DecidableEq α] [DecidableEq β] in

theorem higher_moment_le_of_cover (x : α → ℝ) (a : β → ℝ) (T : Finset β)
    (K J : ℕ) (hK : K ≠ 0) (hKJ : K ≤ J) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hx : ∀ v, 0 ≤ x v)
    (hmax : ∀ v, x v ≤ M) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ v, 0 < x v → ∃ i ∈ T, a i ≤ x v ∧ x v ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun v => a i ≤ x v)).card : ℝ) * a i ^ K ≤ C) :
    (∑ v, x v ^ J) ≤ (T.card : ℝ) * (2 : ℝ) ^ K * C * M ^ (J - K) := by
  have hp (v : α) : x v ^ J ≤ x v ^ K * M ^ (J - K) := by
    calc
      x v ^ J = x v ^ K * x v ^ (J - K) := by
        rw [← pow_add, Nat.add_sub_of_le hKJ]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hx v) (hmax v) _) (by positivity [hx v])
  calc
    _ ≤ ∑ v, x v ^ K * M ^ (J - K) := Finset.sum_le_sum (fun v _ => hp v)
    _ = (∑ v, x v ^ K) * M ^ (J - K) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (moment_le_of_cover x a T K hK C hC hx ha hcover hcount) (by positivity)

end Finite
end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators
open SharpRamseyFive.DyadicMoments

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma strength_nonneg (a : D → ℝ≥0) (p : DistinctPairs H) :
    0 ≤ strength lines a p := by unfold strength; positivity

omit [DecidableEq B] in
omit [Fintype D] [DecidableEq I] in

theorem pairMoment_dyadic (a : D → ℝ≥0) (L : ℝ≥0) (K : ℕ) (hK : K ≠ 0)
    (T : Finset I) (threshold : I → ℝ) (ht : ∀ i ∈ T, 0 ≤ threshold i)
    (hcover : ∀ p, 0 < strength lines a p →
      ∃ i ∈ T, threshold i ≤ strength lines a p ∧ strength lines a p ≤ 2 * threshold i)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun p : DistinctPairs H => threshold i ≤ strength lines a p)).card : ℝ) *
        threshold i ^ K ≤ C) :
    pairMoment (B := B) lines (fun d => L * a d) K ≤
      (T.card : ℝ) * C * (2 * Fintype.card B * (L : ℝ)) ^ K := by
  classical
  have h := moment_le_of_cover (strength lines a) threshold T K hK C hC
    (strength_nonneg lines a) ht hcover hcount
  have he : pairMoment (B := B) lines (fun d => L * a d) K =
      ((Fintype.card B : ℝ) * (L : ℝ)) ^ K *
        ∑ p : DistinctPairs H, strength lines a p ^ K := by
    unfold pairMoment
    change _ = _ * ∑ p : (Σ h : H, {h' : H // h' ≠ h}), _
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h' _
    simp only [NNReal.coe_mul, ← Finset.mul_sum, strength]
    rw [← mul_assoc, mul_pow]
  rw [he]
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  rw [mul_pow, mul_pow]
  ring

end SharpRamseyFive.WeightedPrograms

namespace SharpRamseyFive.SingletonEnumeration
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.DyadicMoments
open SharpRamseyFive.WeightedPrograms
open Classical
variable {D H V I B : Type} [Fintype D] [DecidableEq D]
  [Fintype H] [DecidableEq H] [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq I]

lemma sum_split_diagonal (F : H → ℝ) (y : H) :
    (∑ x : H, F x) = F y + ∑ x : {x : H // x ≠ y}, F x := by
  rw [← Finset.sum_erase_add _ F (Finset.mem_univ y), add_comm]
  congr 1
  exact Finset.sum_subtype _ (by intro x; simp) F

lemma sum_pairs_split_diagonal (F : H → H → ℝ) :
    (∑ x : H, ∑ y : H, F x y) =
      (∑ x : H, F x x) + ∑ z : DistinctPairs H, F z.1 z.2 := by
  change _ = _ + ∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2
  rw [Fintype.sum_sigma, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => sum_split_diagonal (F x) x)

omit [DecidableEq I] in
omit [Fintype D] in

theorem shift_row_dyadic (weight : D → ℝ≥0) (lines : H → Finset D)
    (p K : ℕ) (hK : K ≠ 0) (y : H)
    (T : Finset I) (a : I → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ x : {x : H // x ≠ y}, 0 < mass weight (lines x ∩ lines y) →
      ∃ i ∈ T, a i ≤ mass weight (lines x ∩ lines y) ∧
        mass weight (lines x ∩ lines y) ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        a i ≤ mass weight (lines x ∩ lines y))).card : ℝ) * a i ^ K ≤ C) :
    (∑ x : H, shiftKernel weight lines p K x y) ≤
      1 + (T.card : ℝ) * C * (2 * p) ^ K := by
  rw [sum_split_diagonal _ y]
  apply add_le_add (shiftKernel_range weight lines p K y y).2
  calc
    (∑ x : {x : H // x ≠ y}, shiftKernel weight lines p K x y) ≤
        ∑ x : {x : H // x ≠ y}, ((p : ℝ) * mass weight (lines x ∩ lines y)) ^ K := by
      exact Finset.sum_le_sum (fun x _ => min_le_right _ _)
    _ = (p : ℝ) ^ K * ∑ x : {x : H // x ≠ y}, mass weight (lines x ∩ lines y) ^ K := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ (p : ℝ) ^ K * ((T.card : ℝ) * 2 ^ K * C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact moment_le_of_cover _ a T K hK C hC
        (fun x => mass_nonneg _ _) ha hcover hcount
    _ = _ := by rw [mul_pow]; ring

omit [DecidableEq I] in
omit [Fintype D] in

theorem shift_pairs_dyadic (weight : D → ℝ≥0) (lines : H → Finset D)
    (p K : ℕ) (hK : K ≠ 0) (T : Finset I) (a : I → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)
        * a i ^ K ≤ C) :
    (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤
      Fintype.card H + (T.card : ℝ) * C * (2 * p) ^ K := by
  rw [sum_pairs_split_diagonal]
  apply add_le_add
  · exact (Finset.sum_le_sum (fun x _ => (shiftKernel_range weight lines p K x x).2)).trans_eq
      (by simp)
  · calc
      (∑ z : DistinctPairs H, shiftKernel weight lines p K z.1 z.2) ≤
          ∑ z : DistinctPairs H, ((p : ℝ) * strength lines weight z) ^ K :=
        Finset.sum_le_sum (fun z _ => min_le_right _ _)
      _ = (p : ℝ) ^ K * ∑ z : DistinctPairs H, strength lines weight z ^ K := by
        simp only [mul_pow, Finset.mul_sum]
      _ ≤ (p : ℝ) ^ K * ((T.card : ℝ) * 2 ^ K * C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact moment_le_of_cover _ a T K hK C hC
          (strength_nonneg lines weight) ha hcover hcount
      _ = _ := by rw [mul_pow]; ring

omit [Fintype D] [DecidableEq B] in

theorem pairMoment_labelled_le (lines : H → Finset D) (rate : D → ℝ≥0)
    (K : ℕ) (mass : ℝ) (_hm : 0 ≤ mass)
    (hmass : ∀ x, ∑ d ∈ lines x, (rate d : ℝ) ≤ mass) :
    pairMoment (B := B) (fun x : H × V => lines x.1) rate K ≤
      (Fintype.card V : ℝ) ^ 2 *
        (pairMoment (B := B) lines rate K +
          Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K) := by
  let F : H → H → ℝ := fun x y =>
    ((Fintype.card B : ℝ) * ∑ d ∈ lines x ∩ lines y, (rate d : ℝ)) ^ K
  have hF : ∀ x y, 0 ≤ F x y := by intro x y; dsimp [F]; positivity
  have he : pairMoment (B := B) lines rate K = ∑ x : H, ∑ y : {y : H // y ≠ x}, F x y := rfl
  have hdiag : (∑ x : H, F x x) ≤
      Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    apply (Finset.sum_le_sum (fun x _ => show F x x ≤
      ((Fintype.card B : ℝ) * mass) ^ K from ?_)).trans_eq (by simp)
    dsimp [F]
    simp only [Finset.inter_self]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (hmass x) (Nat.cast_nonneg _)) K
  have hfull : (∑ x : H, ∑ y : H, F x y) ≤
      pairMoment (B := B) lines rate K + Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    rw [sum_pairs_split_diagonal, add_comm]
    change (∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2) + _ ≤ _
    rw [Fintype.sum_sigma, ← he]
    exact add_le_add le_rfl hdiag
  calc
    _ ≤ ∑ x : H × V, ∑ y : H × V, F x.1 y.1 := by
      unfold pairMoment
      apply Finset.sum_le_sum
      intro x _
      rw [sum_split_diagonal _ x]
      apply le_add_of_nonneg_left (hF _ _)
    _ = (Fintype.card V : ℝ) ^ 2 * (∑ x : H, ∑ y : H, F x y) := by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfull (by positivity)

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma patch_mem (g : V → H) (T : Finset V) (x : T → H) (u : T) :
    patch g T x u = x u := by simp [patch]

end SharpRamseyFive.ResidualElimination
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_PatchNotMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma patch_notMem (g : V → H) (T : Finset V) (x : T → H) (u : V) (hu : u ∉ T) :
    patch g T x u = g u := by simp [patch, hu]
omit [Fintype V] [Fintype H] [DecidableEq H] in

lemma agrees_sdiff_patch (E T : Finset V) (hT : T ⊆ E) (g f : V → H) (x : T → H) :
    Agrees (E \ T) (patch g T x) f ↔ Agrees E g f ∧ x = fun u : T => f u := by
  constructor
  · intro h
    constructor
    · intro u hu
      have hnu : u ∉ T := fun hh => hu (hT hh)
      simpa only [patch_notMem g T x u hnu] using h u (by simp [hu])
    · funext u
      have hu := h u (by simp)
      simpa only [patch_mem] using hu.symm
  · rintro ⟨h,rfl⟩ u hu
    by_cases hnu : u ∈ T
    · simp [patch, hnu]
    · rw [patch_notMem g T _ u hnu]
      exact h u (by simpa [hnu] using hu)

lemma completionSum_split (E T : Finset V) (hT : T ⊆ E) (g : V → H)
    (F : (V → H) → ℝ) :
    completionSum E g F = ∑ x : T → H, completionSum (E \ T) (patch g T x) F := by
  unfold completionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [agrees_sdiff_patch E T hT]
  by_cases hf : Agrees E g f <;> simp [hf]

theorem weighted_block_exposure (E T : Finset V) (hT : T ⊆ E) (g : V → H)
    (w : (T → H) → ℝ) (hw : ∀ x, 0 ≤ w x) (F : (V → H) → ℝ)
    (C : ℝ) (hF : ∀ g, completionSum (E \ T) g F ≤ C) :
    completionSum E g (fun f => w (fun u : T => f u) * F f) ≤
      (∑ x : T → H, w x) * C := by
  rw [completionSum_split E T hT, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  calc
    _ = completionSum (E \ T) (patch g T x) (fun f => w x * F f) := by
      apply completionSum_congr
      intro f hf
      have hx := (agrees_sdiff_patch E T hT g f x).mp hf
      rw [← hx.2]
    _ = w x * completionSum (E \ T) (patch g T x) F := completionSum_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (hF _) (hw x)

theorem independent_positions_exposure (E T : Finset V) (hT : T ⊆ E) (g : V → H)
    (w : V → H → ℝ) (hw : ∀ u h, 0 ≤ w u h) (F : (V → H) → ℝ)
    (C : ℝ) (hF : ∀ g, completionSum (E \ T) g F ≤ C) :
    completionSum E g (fun f => (∏ u ∈ T, w u (f u)) * F f) ≤
      (∏ u ∈ T, ∑ h : H, w u h) * C := by
  let W : (T → H) → ℝ := fun x => ∏ u : T, w u (x u)
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    exact Finset.prod_nonneg (fun u _ => hw _ _)
  have he (f : V → H) : (∏ u ∈ T, w u (f u)) = W (fun u : T => f u) := by
    exact (Finset.prod_coe_sort T (fun u => w u (f u))).symm
  simp_rw [he]
  apply (weighted_block_exposure E T hT g W hW F C hF).trans_eq
  have hs : (∑ x : T → H, W x) = ∏ u ∈ T, ∑ h : H, w u h := by
    rw [show (∑ x : T → H, W x) = ∏ u : T, ∑ h : H, w u h from
      (Fintype.prod_sum (fun u : T => w u)).symm]
    exact Finset.prod_coe_sort T (fun u => ∑ h : H, w u h)
  rw [hs]

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

omit [Fintype V] in
lemma powerset_sdiff (E U : Finset V) :
    (E \ U).powerset = E.powerset.filter (fun S => Disjoint S U) := by
  ext S
  simp only [Finset.mem_powerset, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨h.trans Finset.sdiff_subset, Finset.disjoint_left.mpr ?_⟩
    intro u hu hU
    exact (Finset.mem_sdiff.mp (h hu)).2 hU
  · rintro ⟨h,hD⟩ u hu
    exact Finset.mem_sdiff.mpr ⟨h hu, fun hU => Finset.disjoint_left.mp hD hu hU⟩
omit [Fintype V] in

lemma sum_disjoint_swap (E : Finset V) (F : Finset V → Finset V → ℝ) :
    (∑ U ∈ E.powerset, ∑ S ∈ (E \ U).powerset, F U S) =
      ∑ S ∈ E.powerset, ∑ U ∈ (E \ S).powerset, F U S := by
  simp_rw [powerset_sdiff, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro U hU
  simp only [disjoint_comm]

omit [Fintype H] [DecidableEq H] in
omit [Fintype V] in
lemma badExpansion_add (a d : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (f : V → H) :
    badExpansion (fun u f => d u f + a u f) B E f =
      ∑ S ∈ E.powerset, (∏ u ∈ S, d u f) * badExpansion a B (E \ S) f := by
  unfold badExpansion
  simp_rw [Finset.prod_add, Finset.sum_mul]
  rw [sum_disjoint_swap]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have he : (E \ U) \ S = (E \ S) \ U := sdiff_sdiff_comm
  rw [he, mul_assoc]
omit [DecidableEq H] in

lemma badExpansion_sum_le (a : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (g : V → H)
    (M : ℝ) (_hM : 0 ≤ M)
    (hterm : ∀ S, S ⊆ E → completionSum E g (term a B E S) ≤ M ^ E.card) :
    completionSum E g (badExpansion a B E) ≤ (2 * M) ^ E.card := by
  rw [show badExpansion a B E = (fun f => ∑ U ∈ E.powerset,
      (∏ u ∈ E \ U, a u f) * B U f) from rfl, completionSum_sum]
  calc
    _ ≤ ∑ _U ∈ E.powerset, M ^ E.card := by
      apply Finset.sum_le_sum
      intro U hU
      have hU : U ⊆ E := Finset.mem_powerset.mp hU
      have he : E \ (E \ U) = U := Finset.sdiff_sdiff_eq_self hU
      have ht := hterm (E \ U) Finset.sdiff_subset
      change completionSum E g (fun f => (∏ u ∈ E \ U, a u f) *
        B (E \ (E \ U)) f) ≤ M ^ E.card at ht
      simpa only [he] using ht
    _ = _ := by simp [mul_pow]

theorem all_singleton_enumeration
    (a : V → (V → H) → ℝ) (d : V → H → ℝ) (B : Finset V → (V → H) → ℝ)
    (W : H → H → ℝ) (C D : ℝ) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (ha : ∀ u f, a u f ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ u x, 0 ≤ d u x) (hsum : ∀ u, (∑ x : H, d u x) ≤ D)
    (hW : ∀ x y, 0 ≤ W x y) (hB : ∀ A f, 0 ≤ B A f)
    (hmono : ∀ A A', A' ⊆ A → ∀ f, B A f ≤ B A' f)
    (hshift : ∀ u f, a u f ≤ ∑ v ∈ Finset.univ.erase u, W (f u) (f v))
    (hrow : ∀ y, (∑ x : H, W x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, W x y) ≤ C ^ 2)
    (hbad : ∀ A g, completionSum A g (B A) ≤ C ^ A.card)
    (E : Finset V) (g : V → H) :
    completionSum E g (badExpansion (fun u f => d u (f u) + a u f) B E) ≤
      (D + 2 * ((Fintype.card V + 1 : ℝ) * C)) ^ E.card := by
  let M : ℝ := (Fintype.card V + 1) * C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbnd (A : Finset V) (g : V → H) :
      completionSum A g (badExpansion a B A) ≤ (2 * M) ^ A.card := by
    apply badExpansion_sum_le a B A g M hM
    intro S hS
    exact shift_bad_enumeration a B W C hC ha hW hB hmono hshift hrow hpair hbad A S hS g
  have he : badExpansion (fun u f => d u (f u) + a u f) B E =
      fun f => ∑ S ∈ E.powerset, (∏ u ∈ S, d u (f u)) * badExpansion a B (E \ S) f := by
    funext f
    exact badExpansion_add a (fun u f => d u (f u)) B E f
  rw [he, completionSum_sum]
  calc
    _ ≤ ∑ S ∈ E.powerset, D ^ S.card * (2 * M) ^ (E \ S).card := by
      apply Finset.sum_le_sum
      intro S hS
      apply (independent_positions_exposure E S (Finset.mem_powerset.mp hS) g d hd
        (badExpansion a B (E \ S)) ((2 * M) ^ (E \ S).card) (hbnd (E \ S))).trans
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
      calc
        (∏ u ∈ S, ∑ x : H, d u x) ≤ ∏ _u ∈ S, D :=
          Finset.prod_le_prod (fun u _ => Finset.sum_nonneg (fun x _ => hd u x))
            (fun u _ => hsum u)
        _ = _ := Finset.prod_const _
    _ = (D + 2 * M) ^ E.card := by
      have := Finset.prod_add (fun _ : V => D) (fun _ => 2 * M) E
      simpa only [Finset.prod_const] using this.symm

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

omit [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H] in
lemma independentWeight_nonneg (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (R J : ℕ) (base : ℝ) (h : H) : 0 ≤ independentWeight weight rate lines R J base h := by
  unfold independentWeight
  split_ifs <;> positivity

theorem actual_all_singleton_enumeration (weight rate : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (R : ℕ) (denom b mass C D₀ base : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass) (hC : 0 ≤ C) (hD : 0 ≤ D₀)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) rate denom b mass K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight rate lines R J base x) ≤ D₀)
    (E : Finset V) (g : V → H) :
    completionSum E g (badExpansion
      (fun u f => independentWeight weight rate lines R J base (f u) +
        alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K)
      (fun A f => vertexBadMass weight rate (lines ∘ f) (1 / (100 * p)) R J A) E) ≤
      (D₀ + 2 * ((Fintype.card V + 1 : ℝ) * C)) ^ E.card := by
  apply all_singleton_enumeration
    (fun u f => alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K)
    (fun _ x => independentWeight weight rate lines R J base x)
    (fun A f => vertexBadMass weight rate (lines ∘ f) (1 / (100 * p)) R J A)
    (shiftKernel weight lines p K) C D₀ hC hD
  · intro u f
    exact ⟨pow_nonneg (alpha_nonneg _ _ _ _) _,
      pow_le_one₀ (alpha_nonneg _ _ _ _) (by
        have := source_alpha_le weight (lines ∘ f) hp hc u
        linarith)⟩
  · exact fun _ x => independentWeight_nonneg weight rate lines R J base x
  · exact fun _ => hDsum
  · exact fun x y => (shiftKernel_range weight lines p K x y).1
  · exact fun A f => vertexBadMass_nonneg _ _ _ _ _ _ _
  · exact fun A A' hh f => vertexBadMass_antitone _ _ _ _ _ _ hh
  · exact fun u f => shift_le_kernel_sum weight lines hp hc (by omega) u f
  · exact hrow
  · exact hpair
  · intro A g
    apply (actual_bad_completion weight rate lines (1 / (100 * p)) R denom b mass
      hd hb hm hmass K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ A g).trans
    apply pow_le_pow_left₀ _ hBC
    apply mul_nonneg hd.le
    have hn := branchingBound_nonneg (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) rate denom b mass hd.le (by linarith) hm K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low
    linarith

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

lemma inside_sum_le {C : Type} [Fintype C] [DecidableEq C]
    (label : D → Option C) (c : C) (S : Finset D) (F : D → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ inside label c S, F d) ≤ ∑ d ∈ S, F d := by
  have hi : Function.Injective (Subtype.val : IntDir label c → D) := Subtype.val_injective
  rw [← Finset.sum_image (hi.injOn)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rcases Finset.mem_image.mp hd with ⟨e,he,rfl⟩
    exact (Finset.mem_filter.mp he).2
  · exact fun d _ _ => hF d

omit [Fintype H] [DecidableEq H] in
lemma extraWeight_le_independent (weight : D → ℝ≥0) (lines : H → Finset D)
    (f : V → H) (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ)
    (c : Components weight (lines ∘ f) t) :
    extraWeight weight (lines ∘ f) t R J K L base c ≤
      independentWeight weight (fun d => L * weight d) lines R J base
        (f (vertex weight (lines ∘ f) t c)) +
      alpha weight (lines ∘ f) t (vertex weight (lines ∘ f) t c) ^ K := by
  unfold extraWeight independentWeight delta
  have h := inside_sum_le (componentLabel weight (lines ∘ f) t) c
    ((lines ∘ f) (vertex weight (lines ∘ f) t c))
    (fun d => ((R : ℝ) * ((L * weight d : ℝ≥0) : ℝ)) ^ J) (fun _ => by positivity)
  dsimp only [Function.comp_def] at *
  split_ifs <;> linarith

omit [Fintype H] [DecidableEq H] in

theorem designation_sum_le_vertex (weight : D → ℝ≥0) (lines : H → Finset D)
    (f : V → H) (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) :
    let s := lines ∘ f
    let S := simpleSet weight s t
    let E := S.image (vertex weight s t)
    (∑ U ∈ S.powerset, (∏ c ∈ S \ U, extraWeight weight s t R J K L base c) *
      badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => L * weight i.1.2))
        (blockTrunc (componentLabel weight s t) R J none) (isBad weight s t R) U) ≤
      badExpansion
        (fun u f => independentWeight weight (fun d => L * weight d) lines R J base (f u) +
          alpha weight (lines ∘ f) t u ^ K)
        (fun A f => vertexBadMass weight (fun d => L * weight d) (lines ∘ f) t R J A) E f := by
  dsimp only
  unfold badExpansion
  rw [Finset.powerset_image, Finset.sum_image
    (Finset.image_injective (vertex_injective weight (lines ∘ f) t)).injOn]
  apply Finset.sum_le_sum
  intro U hU
  rw [← Finset.image_sdiff _ _ (vertex_injective weight (lines ∘ f) t),
    Finset.prod_image (vertex_injective weight (lines ∘ f) t).injOn,
    component_bad_mass_eq_vertex weight (fun d => L * weight d) (lines ∘ f) t R J U]
  apply mul_le_mul_of_nonneg_right _ (vertexBadMass_nonneg _ _ _ _ _ _ _)
  apply Finset.prod_le_prod
  · exact fun c _ => extraWeight_nonneg _ _ _ _ _ _ _ _ c
  · exact fun c _ => extraWeight_le_independent weight lines f t R J K L base c

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [DecidableEq C]

theorem disjoint_blocks_exposure (E : Finset V) (I : Finset C) (T : C → Finset V)
    (Win : (c : C) → (T c → H) → ℝ) (M : C → ℝ)
    (hw : ∀ c x, 0 ≤ Win c x) (hM : ∀ c, 0 ≤ M c)
    (hwithin : ∀ c ∈ I, T c ⊆ E)
    (hdisj : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → Disjoint (T c) (T d))
    (hsum : ∀ c ∈ I, (∑ x : T c → H, Win c x) ≤ M c)
    (F : (V → H) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hres : ∀ g, completionSum (E \ I.biUnion T) g F ≤ K) (g : V → H) :
    completionSum E g (fun f => (∏ c ∈ I, Win c (fun v => f v)) * F f) ≤
      (∏ c ∈ I, M c) * K := by
  induction I using Finset.induction generalizing E g with
  | empty => simpa using hres g
  | @insert c I hc ih =>
    have hwi : T c ⊆ E := hwithin c (Finset.mem_insert_self c I)
    have hrwithin : ∀ d ∈ I, T d ⊆ E \ T c := by
      intro d hd v hv
      refine Finset.mem_sdiff.mpr ⟨hwithin d (Finset.mem_insert_of_mem hd) hv, ?_⟩
      intro hvc
      exact Finset.disjoint_left.mp
        (hdisj d (Finset.mem_insert_of_mem hd) c (Finset.mem_insert_self _ _)
          (by intro he; subst d; exact hc hd)) hv hvc
    have he : (E \ T c) \ I.biUnion T = E \ (insert c I).biUnion T := by
      ext v
      simp only [Finset.mem_sdiff, Finset.biUnion_insert, Finset.mem_union]
      tauto
    have hr (g : V → H) :
        completionSum (E \ T c) g
          (fun f => (∏ d ∈ I, Win d (fun v => f v)) * F f) ≤ (∏ d ∈ I, M d) * K := by
      apply ih (E \ T c) hrwithin
        (fun d hd e he hne => hdisj d (Finset.mem_insert_of_mem hd)
          e (Finset.mem_insert_of_mem he) hne)
        (fun d hd => hsum d (Finset.mem_insert_of_mem hd))
      intro g
      rw [he]
      exact hres g
    simp_rw [Finset.prod_insert hc, mul_assoc]
    apply (weighted_block_exposure E (T c) hwi g (Win c) (hw c)
      (fun f => (∏ d ∈ I, Win d (fun v => f v)) * F f)
      ((∏ d ∈ I, M d) * K) hr).trans
    exact mul_le_mul_of_nonneg_right (hsum c (Finset.mem_insert_self _ _))
      (mul_nonneg (Finset.prod_nonneg (fun d _ => hM d)) hK)

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

omit [DecidableEq V] [Fintype C] in

lemma self_mem_fiber (r : V → C) (v : V) : v ∈ fiber r (r v) := by simp
omit [DecidableEq V] [Fintype C] in
lemma fiber_card_pos (r : V → C) (v : V) : 0 < (fiber r (r v)).card :=
  Finset.card_pos.mpr ⟨v,self_mem_fiber r v⟩
omit [DecidableEq V] [Fintype C] in

lemma fiber_disjoint (r : V → C) {c d : C} (hne : c ≠ d) :
    Disjoint (fiber r c) (fiber r d) := by
  apply Finset.disjoint_left.mpr
  intro v hc hd
  exact hne ((mem_fiber r c v).mp hc |>.symm.trans ((mem_fiber r d v).mp hd))

lemma large_union (r : V → C) : (largeLabels r).biUnion (fiber r) = Finset.univ \ singles r := by
  ext v
  simp only [Finset.mem_biUnion, mem_largeLabels, mem_fiber, Finset.mem_sdiff,
    Finset.mem_univ, true_and, mem_singles]
  constructor
  · rintro ⟨c,hc,he⟩
    rw [he]
    omega
  · intro hv
    exact ⟨r v,by have := fiber_card_pos r v; omega,rfl⟩
end SharpRamseyFive.ComponentPartition
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_SinglesUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
omit [DecidableEq V] [Fintype C] in
lemma singles_iff_unique (r : V → C) (v : V) :
    v ∈ singles r ↔ ∀ w, r w = r v → w = v := by
  rw [mem_singles]
  constructor
  · intro hc
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hc
    have hvw : v = w := by simpa only [hw, Finset.mem_singleton] using self_mem_fiber r v
    intro u hu
    have huw : u = w := by simpa only [hw, Finset.mem_singleton] using (mem_fiber r (r v) u).mpr hu
    exact huw.trans hvw.symm
  · intro hu
    have he : fiber r (r v) = {v} := by
      ext w
      simp only [mem_fiber, Finset.mem_singleton]
      exact ⟨hu w, fun h => h ▸ rfl⟩
    rw [he,Finset.card_singleton]

lemma large_card_sum (r : V → C) :
    ∑ c ∈ largeLabels r, (fiber r c).card = Fintype.card V - (singles r).card := by
  rw [← Finset.card_biUnion (fun c _ d _ hne => fiber_disjoint r hne), large_union,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

variable (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
lemma componentMap_eq_iff (v w : V) : componentMap G v = componentMap G w ↔
    G.connectedComponentMk v = G.connectedComponentMk w := by
  constructor
  · intro h
    have hh := congrArg G.connectedComponentMk h
    have he (c : G.ConnectedComponent) : G.connectedComponentMk c.out = c := c.out_eq
    simpa only [componentMap, he] using hh
  · intro h
    exact congrArg (fun c : G.ConnectedComponent => c.out) h

end SharpRamseyFive.ComponentPartition
namespace SharpRamseyFive.ComponentEnumeration
open Classical
open scoped BigOperators
open CertificateEnumeration
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H]

omit [Fintype V] in
lemma boundary_of_walk (G : SimpleGraph V) (E : Finset V) {u v : V}
    (p : G.Walk u v) (hu : u ∈ E) (hv : v ∉ E) :
    ∃ a ∈ E, ∃ b ∉ E, G.Adj a b := by
  induction p with
  | nil => exact False.elim (hv hu)
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ E
    · exact ih hb hv
    · exact ⟨a, hu, b, hb, hab⟩

lemma connected_boundary (G : SimpleGraph V) (hG : G.Connected)
    (E : Finset V) (hE : E.Nonempty) (hne : E ≠ Finset.univ) :
    ∃ a ∈ E, ∃ b ∉ E, G.Adj a b := by
  classical
  obtain ⟨u, hu⟩ := hE
  have : ∃ v, v ∉ E := by
    by_contra h
    apply hne
    ext v
    simp only [Finset.mem_univ, iff_true]
    exact Classical.not_not.mp (fun hv => h ⟨v, hv⟩)
  obtain ⟨v, hv⟩ := this
  obtain ⟨p⟩ := hG u v
  exact boundary_of_walk G E p hu hv

variable (R : H → H → Prop)

omit [DecidableEq V] in
lemma extension_card (Δ : ℕ)
    (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ) (s : V → H) :
    Fintype.card (Extension R s) ≤ Fintype.card V ^ 2 * Δ := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod]
  calc
    _ ≤ ∑ u : V, Fintype.card V * Δ := by
      apply Finset.sum_le_sum
      intro u _
      exact Nat.mul_le_mul_left _ (hΔ (s u))
    _ = _ := by simp; ring

lemma dword_card_le {S : Type} (C : S → Type) (step : (s : S) → C s → S)
    [∀ s, Fintype (C s)] (M : ℕ) (hM : ∀ s, Fintype.card (C s) ≤ M)
    (n : ℕ) (s : S) : Fintype.card (DWord C step n s) ≤ M ^ n := by
  induction n generalizing s with
  | zero =>
    change Fintype.card PUnit ≤ 1
    exact le_of_eq Fintype.card_unique
  | succ n ih =>
    change Fintype.card ((a : C s) × DWord C step n (step s a)) ≤ M ^ (n + 1)
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ a : C s, M ^ n := Finset.sum_le_sum (fun a _ => ih (step s a))
      _ = Fintype.card (C s) * M ^ n := by simp
      _ ≤ M * M ^ n := Nat.mul_le_mul_right _ (hM s)
      _ = _ := (pow_succ' M n).symm

omit [Fintype H] in

theorem connected_extension_cover (hsym : Std.Symm R) (f s : V → H)
    (hf : (relationGraph R hsym f).Connected) (E : Finset V) (hE : E.Nonempty)
    (hcoh : ∀ u ∈ E, s u = f u) :
    ∃ w : DWord (Extension R) (extend R) (Fintype.card V - E.card) s,
      dFinish (Extension R) (extend R) s w = f := by
  classical
  generalize hm : Fintype.card V - E.card = m
  induction m generalizing s E with
  | zero =>
    have hEu : E = Finset.univ := by
      apply Finset.eq_univ_of_card
      have := Finset.card_le_univ E
      omega
    have hsf : s = f := by
      funext u
      exact hcoh u (by simp [hEu])
    subst s
    exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    have hne : E ≠ Finset.univ := by
      intro h
      simp [h] at hm
    obtain ⟨u, hu, v, hv, huv⟩ := connected_boundary _ hf E hE hne
    let a : Extension R s := ⟨u, v, f v, by
      rw [hcoh u hu]
      exact huv.2⟩
    have hcoh' : ∀ z ∈ insert v E, extend R s a z = f z := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp [extend, a]
      · have hzv : z ≠ v := by intro h; subst z; exact hv hz
        simpa [extend, a, hzv] using hcoh z hz
    have hn : Fintype.card V - (insert v E).card = n := by
      rw [Finset.card_insert_of_notMem hv]
      omega
    obtain ⟨w, hw⟩ := ih (extend R s a) (insert v E) (by simp) hcoh' hn
    exact ⟨⟨a, w⟩, hw⟩

theorem connected_tuple_count (hsym : Std.Symm R) (hV : 2 ≤ Fintype.card V)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ) :
    Fintype.card {f : V → H // (relationGraph R hsym f).Connected} ≤
      Fintype.card V ^ 2 * Fintype.card (RelatedPair R) *
      (Fintype.card V ^ 2 * Δ) ^ (Fintype.card V - 2) := by
  classical
  let Code := (z : Seed (V := V) R) ×
    DWord (Extension R) (extend R) (Fintype.card V - 2) (seedStart R z)
  let decode : Code → V → H := fun c =>
    dFinish (Extension R) (extend R) (seedStart R c.1) c.2
  have hcover (f : {f : V → H // (relationGraph R hsym f).Connected}) :
      ∃ c : Code, decode c = f.1 := by
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let u : V := Classical.choice inferInstance
    have hne : ({u} : Finset V) ≠ Finset.univ := by
      intro h
      have hh := congrArg Finset.card h
      simp at hh
      omega
    obtain ⟨a, ha, v, hv, huv⟩ := connected_boundary _ f.2 {u} (by simp) hne
    have hau : a = u := by simpa using ha
    subst a
    have hvu : v ≠ u := by simpa using hv
    let z : Seed (V := V) R := ⟨u, v, f.1 u, f.1 v, huv.2⟩
    have hcoh : ∀ x ∈ ({u, v} : Finset V), seedStart R z x = f.1 x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [seedStart, z, hvu.symm]
      · simp [seedStart, z]
    have hcov := connected_extension_cover R hsym f.1 (seedStart R z)
      f.2 {u,v} (by simp) hcoh
    have hcard : ({u,v} : Finset V).card = 2 := by simp [hvu.symm]
    rw [hcard] at hcov
    obtain ⟨w, hw⟩ := hcov
    exact ⟨⟨z, w⟩, hw⟩
  let enc : {f : V → H // (relationGraph R hsym f).Connected} → Code :=
    fun f => Classical.choose (hcover f)
  have henc : Function.Injective enc := by
    intro f g hfg
    apply Subtype.ext
    calc
      f.1 = decode (enc f) := (Classical.choose_spec (hcover f)).symm
      _ = decode (enc g) := congrArg decode hfg
      _ = g.1 := Classical.choose_spec (hcover g)
  calc
    _ ≤ Fintype.card Code := Fintype.card_le_of_injective enc henc
    _ = ∑ z : Seed (V := V) R, Fintype.card
        (DWord (Extension R) (extend R) (Fintype.card V - 2) (seedStart R z)) :=
      Fintype.card_sigma
    _ ≤ ∑ _z : Seed (V := V) R,
        (Fintype.card V ^ 2 * Δ) ^ (Fintype.card V - 2) := by
      apply Finset.sum_le_sum
      intro z _
      exact dword_card_le (Extension R) (extend R) _ (extension_card R Δ hΔ) _ _
    _ = _ := by simp [Seed, Fintype.card_prod, pow_two, mul_assoc]

end SharpRamseyFive.ComponentEnumeration

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype C] [DecidableEq C]

omit [Fintype H] [DecidableEq H] in
lemma connected_fiber (R : H → H → Prop) (hsym : Std.Symm R) (f : V → H)
    (c : V) (hc : (fiber (componentMap (relationGraph R hsym f)) c).Nonempty) :
    (relationGraph R hsym (fun v : fiber (componentMap (relationGraph R hsym f)) c => f v)).Connected := by
  let G := relationGraph R hsym f
  let r := componentMap G
  obtain ⟨w,hw⟩ := hc
  have hw : r w = c := (mem_fiber _ _ _).mp hw
  let S := G.connectedComponentMk w
  let e : fiber r c ≃ S :=
    { toFun := fun v => ⟨v, (S.mem_supp_iff v).mpr
        ((componentMap_eq_iff G v w).mp ((mem_fiber r c v).mp v.property |>.trans hw.symm))⟩
      invFun := fun v => ⟨v, (mem_fiber r c v).mpr
        (((componentMap_eq_iff G v w).mpr ((S.mem_supp_iff v).mp v.property)).trans hw)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let φ : relationGraph R hsym (fun v : fiber r c => f v) ≃g S.toSimpleGraph :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        change (x.val ≠ y.val ∧ R (f x) (f y)) ↔ (x ≠ y ∧ R (f x) (f y))
        simp only [ne_eq, Subtype.val_inj] }
  exact φ.connected_iff.mpr S.connected_toSimpleGraph

omit [Fintype H] [DecidableEq H] [Fintype C] in
lemma connectedWeight_nonneg (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (x : fiber r c → H) : 0 ≤ connectedWeight R hsym r c x := by
  unfold connectedWeight
  split_ifs <;> norm_num

omit [DecidableEq H] in
lemma connectedWeight_sum_le (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (hc : c ∈ largeLabels r)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ) :
    (∑ x : fiber r c → H, connectedWeight R hsym r c x) ≤
      ((fiber r c).card : ℝ) ^ 2 * Fintype.card (RelatedPair R) *
        (((fiber r c).card : ℝ) ^ 2 * Δ) ^ ((fiber r c).card - 2) := by
  have hc : 2 ≤ Fintype.card (fiber r c) := by simpa only [Fintype.card_coe] using (mem_largeLabels r c).mp hc
  have h := connected_tuple_count (V := fiber r c) R hsym hc Δ hΔ
  have he : (∑ x : fiber r c → H, connectedWeight R hsym r c x) =
      (Fintype.card {x : fiber r c → H // (relationGraph R hsym x).Connected} : ℝ) := by
    simp only [connectedWeight, Fintype.card_subtype, Finset.sum_boole]
  rw [he]
  simpa only [Fintype.card_coe, Nat.cast_mul, Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr h

end SharpRamseyFive.ComponentPartition

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype C] [DecidableEq C]

lemma univ_sub_large (r : V → C) :
    Finset.univ \ (largeLabels r).biUnion (fiber r) = singles r := by
  rw [large_union]
  simp

lemma partition_block_bound (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (b A : ℝ) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ)
    (hnum : ∀ c ∈ largeLabels r,
      b * (((fiber r c).card : ℝ) ^ 2 * Fintype.card (RelatedPair R) *
        (((fiber r c).card : ℝ) ^ 2 * Δ) ^ ((fiber r c).card - 2))
          ≤ A ^ (fiber r c).card)
    (F : (V → H) → ℝ)
    (hres : ∀ g, completionSum (singles r) g F ≤ A ^ (singles r).card)
    (g : V → H) :
    completionSum Finset.univ g
      (fun f => (∏ c ∈ largeLabels r,
        b * connectedWeight R hsym r c (fun v => f v)) * F f) ≤ A ^ Fintype.card V := by
  have ht := disjoint_blocks_exposure Finset.univ (largeLabels r) (fiber r)
    (fun c x => b * connectedWeight R hsym r c x) (fun c => A ^ (fiber r c).card)
    (fun c x => mul_nonneg hb (connectedWeight_nonneg R hsym r c x))
    (fun c => pow_nonneg hA _) (fun _ _ => Finset.subset_univ _)
    (fun _ _ _ _ hne => fiber_disjoint r hne)
    (fun c hc => by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (connectedWeight_sum_le R hsym r c hc Δ hΔ) hb).trans (hnum c hc))
    F (A ^ (singles r).card) (pow_nonneg hA _)
    (fun g => by simpa only [univ_sub_large] using hres g) g
  apply ht.trans_eq
  rw [Finset.prod_pow_eq_pow_sum, large_card_sum, ← pow_add]
  rw [Nat.sub_add_cancel (Finset.card_le_univ _)]

theorem graph_partition_sum (R : H → H → Prop) (hsym : Std.Symm R)
    (b A : ℝ) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ)
    (hnum : ∀ m : ℕ, 2 ≤ m → m ≤ Fintype.card V →
      b * ((m : ℝ) ^ 2 * Fintype.card (RelatedPair R) * ((m : ℝ) ^ 2 * Δ) ^ (m - 2)) ≤ A ^ m)
    (F : Finset V → (V → H) → ℝ) (hF : ∀ E f, 0 ≤ F E f)
    (hres : ∀ (r : V → V) g,
      completionSum (singles r) g (F (singles r)) ≤ A ^ (singles r).card) :
    (∑ f : V → H, b ^ (largeLabels (componentMap (relationGraph R hsym f))).card *
      F (singles (componentMap (relationGraph R hsym f))) f) ≤
      (Fintype.card V : ℝ) ^ Fintype.card V * A ^ Fintype.card V := by
  let W (r : V → V) (f : V → H) : ℝ :=
    (∏ c ∈ largeLabels r, b * connectedWeight R hsym r c (fun v => f v)) * F (singles r) f
  have hW (r : V → V) (f : V → H) : 0 ≤ W r f :=
    mul_nonneg (Finset.prod_nonneg (fun c _ => mul_nonneg hb (connectedWeight_nonneg R hsym r c _))) (hF _ f)
  have hw (f : V → H) : W (componentMap (relationGraph R hsym f)) f =
      b ^ (largeLabels (componentMap (relationGraph R hsym f))).card *
        F (singles (componentMap (relationGraph R hsym f))) f := by
    dsimp only [W]
    congr 1
    calc
      _ = ∏ _c ∈ largeLabels (componentMap (relationGraph R hsym f)), b := by
        apply Finset.prod_congr rfl
        intro c hc
        have hfc : (fiber (componentMap (relationGraph R hsym f)) c).Nonempty :=
          Finset.card_pos.mp (by have := (mem_largeLabels _ c).mp hc; omega)
        simp only [connectedWeight, ite_eq_left (connected_fiber R hsym f c hfc), mul_one]
      _ = _ := Finset.prod_const _
  calc
    _ = ∑ f : V → H, W (componentMap (relationGraph R hsym f)) f := by simp only [hw]
    _ ≤ ∑ f : V → H, ∑ r : V → V, W r f := by
      apply Finset.sum_le_sum
      intro f _
      exact Finset.single_le_sum (fun r _ => hW r f) (Finset.mem_univ _)
    _ = ∑ r : V → V, ∑ f : V → H, W r f := Finset.sum_comm
    _ ≤ ∑ _r : V → V, A ^ Fintype.card V := by
      apply Finset.sum_le_sum
      intro r _
      classical
      by_cases hn : Nonempty (V → H)
      · let g : V → H := hn.some
        have hh := partition_block_bound R hsym r b A hb hA Δ hΔ
          (fun c hc => hnum _ ((mem_largeLabels _ _).mp hc) (Finset.card_le_univ _))
          (F (singles r)) (hres r) g
        simpa [completionSum, Agrees, W] using hh
      · have : IsEmpty (V → H) := not_nonempty_iff.mp hn
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
        exact pow_nonneg hA _
    _ = _ := by simp [Nat.cast_pow]

end SharpRamseyFive.ComponentPartition

namespace SharpRamseyFive.AmbientEnumeration
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

omit [Fintype V] [DecidableEq V] in
omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma relation_graph_eq (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ) (f : V → H) :
    relationGraph (overlapRelation weight lines t) (overlapRelation_symm weight lines t) f =
      strongGraph weight (lines ∘ f) t := by
  rfl
omit [Fintype D] in

lemma simple_image (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    (simpleSet weight s t).image (vertex weight s t) = singles (componentMap (strongGraph weight s t)) := by
  ext v
  rw [singles_iff_unique]
  simp only [Finset.mem_image, simpleSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c,hc,rfl⟩ w hw
    exact hc w (((componentMap_eq_iff _ _ _).mp hw).trans (vertex_color weight s t c))
  · intro hv
    let c := (strongGraph weight s t).connectedComponentMk v
    have he : vertex weight s t c = v := hv _ ((componentMap_eq_iff _ _ _).mpr (vertex_color weight s t c))
    exact ⟨c, fun w hw => (hv w ((componentMap_eq_iff _ _ _).mpr hw)).trans he.symm, he⟩
omit [Fintype D] in

lemma simple_card (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    (simpleSet weight s t).card = (singles (componentMap (strongGraph weight s t))).card := by
  rw [← simple_image, Finset.card_image_of_injective _ (vertex_injective weight s t)]
omit [Fintype D] in

lemma large_image (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    (Finset.univ \ simpleSet weight s t).image (vertex weight s t) =
      largeLabels (componentMap (strongGraph weight s t)) := by
  let G := strongGraph weight s t
  let r := componentMap G
  ext v
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_largeLabels]
  constructor
  · rintro ⟨c,hc,rfl⟩
    have hpos : 0 < (fiber r (vertex weight s t c)).card := by
      apply Finset.card_pos.mpr
      refine ⟨vertex weight s t c, ?_⟩
      rw [mem_fiber]
      exact congrArg (vertex weight s t) (vertex_color weight s t c)
    have hne : (fiber r (vertex weight s t c)).card ≠ 1 := by
      intro he
      apply hc
      simp only [simpleSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro w hw
      have hr : r (vertex weight s t c) = vertex weight s t c := by
        exact congrArg (vertex weight s t) (vertex_color weight s t c)
      have hs : vertex weight s t c ∈ singles r := by
        rw [mem_singles, hr]; exact he
      exact (singles_iff_unique r (vertex weight s t c)).mp hs w
        ((componentMap_eq_iff G _ _).mpr (hw.trans (vertex_color weight s t c).symm))
    change 2 ≤ (fiber r (vertex weight s t c)).card
    omega
  · intro hv
    change 2 ≤ (fiber r v).card at hv
    have hpos : 0 < (fiber r v).card := by omega
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hpos
    let c := G.connectedComponentMk w
    have he : vertex weight s t c = v := (mem_fiber r v w).mp hw
    refine ⟨c, ?_, he⟩
    intro hc
    have hs : vertex weight s t c ∈ singles r := by
      rw [← simple_image]
      exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
    have hcard := (mem_singles r (vertex weight s t c)).mp hs
    have hr : r (vertex weight s t c) = vertex weight s t c := by
      exact congrArg (vertex weight s t) (vertex_color weight s t c)
    rw [hr,he] at hcard
    omega

end SharpRamseyFive.AmbientEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AmbientEnumeration
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [Fintype D] in
lemma large_card (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    Fintype.card (Components weight s t) - (simpleSet weight s t).card =
      (largeLabels (componentMap (strongGraph weight s t))).card := by
  rw [← large_image, Finset.card_image_of_injective _ (vertex_injective weight s t),
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

end SharpRamseyFive.AmbientEnumeration

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in

lemma vertexExpansion_nonneg (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (E : Finset V) (f : V → H) :
    0 ≤ vertexExpansion weight lines t R J K L base E f := by
  apply Finset.sum_nonneg
  intro U _
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro u _
    exact add_nonneg (independentWeight_nonneg _ _ _ _ _ _ _) (pow_nonneg (alpha_nonneg _ _ _ _) _)
  · exact vertexBadMass_nonneg _ _ _ _ _ _ _
omit [Fintype H] [DecidableEq H] in

lemma designated_le_partition (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (f : V → H) :
    designatedBound weight (lines ∘ f) t R J K L base ≤
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
        (largeLabels (componentMap (strongGraph weight (lines ∘ f) t))).card *
      (Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^
        (singles (componentMap (strongGraph weight (lines ∘ f) t))).card *
        vertexExpansion weight lines t R J K L base
          (singles (componentMap (strongGraph weight (lines ∘ f) t))) f) := by
  have ht := mul_le_mul_of_nonneg_left
    (designation_sum_le_vertex weight lines f t R J K L base)
    (show 0 ≤ Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^ (simpleSet weight (lines ∘ f) t).card *
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
        (Fintype.card (Components weight (lines ∘ f) t) - (simpleSet weight (lines ∘ f) t).card) by positivity)
  change designatedBound weight (lines ∘ f) t R J K L base ≤ _ at ht
  rw [large_card, simple_card, simple_image] at ht
  exact ht.trans_eq (by unfold vertexExpansion; ring)

theorem designation_sum_enumerated (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (R : ℕ) (L : ℝ≥0) (denom rootB mass C D₀ base A : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hA : 0 ≤ A)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight (fun d => L * weight d) lines R J base x) ≤ D₀)
    (hsingle : Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) *
      (D₀ + 2 * ((Fintype.card V + 1 : ℝ) * C)) ≤ A)
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hnum : ∀ m : ℕ, 2 ≤ m → m ≤ Fintype.card V →
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) *
        ((m : ℝ) ^ 2 * Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) *
          ((m : ℝ) ^ 2 * Δ) ^ (m - 2)) ≤ A ^ m) :
    (∑ f : V → H, designatedBound weight (lines ∘ f) (1 / (100 * p)) R J K L base) ≤
      (Fintype.card V : ℝ) ^ Fintype.card V * A ^ Fintype.card V := by
  let t : ℝ := 1 / (100 * p)
  let a := Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R))
  let b := Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R))
  let F (E : Finset V) (f : V → H) := a ^ E.card * vertexExpansion weight lines t R J K L base E f
  have hres (r : V → V) (g : V → H) :
      completionSum (singles r) g (F (singles r)) ≤ A ^ (singles r).card := by
    change completionSum (singles r) g (fun f => a ^ (singles r).card *
      vertexExpansion weight lines t R J K L base (singles r) f) ≤ _
    rw [completionSum_mul]
    apply (mul_le_mul_of_nonneg_left (actual_all_singleton_enumeration weight
      (fun d => L * weight d) lines hp hc R denom rootB mass C D₀ base hd hb hm hC hD
      hmass K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ hBC hrow hpair hDsum (singles r) g)
        (show 0 ≤ a ^ (singles r).card by dsimp [a]; positivity)).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsingle _
  apply (Finset.sum_le_sum (fun f _ => designated_le_partition weight lines t R J K L base f)).trans
  have ht := graph_partition_sum (V := V) (overlapRelation weight lines t)
    (overlapRelation_symm weight lines t) b A (Real.exp_pos _).le hA Δ hΔ hnum F
    (fun E f => mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (vertexExpansion_nonneg _ _ _ _ _ _ _ _ _ _)) hres
  simpa only [relation_graph_eq] using ht

end SharpRamseyFive.AmbientEnumeration

namespace SharpRamseyFive.MomentBudgets
open scoped BigOperators

lemma block_cost (P B E Δ : ℝ) (p m : ℕ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hE : 0 ≤ E) (hΔ : 0 ≤ Δ) (hm : 2 ≤ m) (hmp : m ≤ p)
    (hp : (p : ℝ) ^ 2 ≤ Real.exp (P / 10))
    (hpair : E ≤ B ^ 2 * Real.exp (P / 10))
    (hdeg : Δ ≤ B * Real.exp (-P)) :
    Real.exp (-(7 / 10 : ℝ) * P) *
      ((m : ℝ) ^ 2 * E * ((m : ℝ) ^ 2 * Δ) ^ (m - 2)) ≤
      (B * Real.exp (-(1 / 5 : ℝ) * P)) ^ m := by
  let A := B * Real.exp (-(1 / 5 : ℝ) * P)
  have hA : 0 ≤ A := mul_nonneg hB (Real.exp_pos _).le
  have hm2 : (m : ℝ) ^ 2 ≤ Real.exp (P / 10) := by
    apply (pow_le_pow_left₀ (by positivity) (show (m : ℝ) ≤ p by exact_mod_cast hmp) 2).trans hp
  have hfirst : Real.exp (-(7 / 10 : ℝ) * P) * ((m : ℝ) ^ 2 * E) ≤ A ^ 2 := by
    calc
      _ ≤ Real.exp (-(7 / 10 : ℝ) * P) * (Real.exp (P / 10) * (B ^ 2 * Real.exp (P / 10))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hm2 hpair hE (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = B ^ 2 * Real.exp (-(1 / 2 : ℝ) * P) := by
        rw [show Real.exp (-(7 / 10 : ℝ) * P) * (Real.exp (P / 10) * (B ^ 2 * Real.exp (P / 10))) =
          B ^ 2 * (Real.exp (-(7 / 10 : ℝ) * P) * Real.exp (P / 10) * Real.exp (P / 10)) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ B ^ 2 * Real.exp (-(2 / 5 : ℝ) * P) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg B)
      _ = A ^ 2 := by
        dsimp [A]
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hstep : (m : ℝ) ^ 2 * Δ ≤ A := by
    calc
      _ ≤ Real.exp (P / 10) * (B * Real.exp (-P)) :=
        mul_le_mul hm2 hdeg hΔ (Real.exp_pos _).le
      _ = B * Real.exp (-(9 / 10 : ℝ) * P) := by
        rw [show Real.exp (P / 10) * (B * Real.exp (-P)) = B * (Real.exp (P / 10) * Real.exp (-P)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ A := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hB
  calc
    _ = (Real.exp (-(7 / 10 : ℝ) * P) * ((m : ℝ) ^ 2 * E)) *
      ((m : ℝ) ^ 2 * Δ) ^ (m - 2) := by ring
    _ ≤ A ^ 2 * A ^ (m - 2) := mul_le_mul hfirst
      (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hΔ) hstep _) (by positivity) (pow_nonneg hA _)
    _ = A ^ m := by rw [← pow_add, Nat.add_sub_of_le hm]

lemma singleton_cost (P B M : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hM : M ≤ B * Real.exp (P / 5)) :
    Real.exp (-(17 / 25 : ℝ) * P) * M ≤ B * Real.exp (-(1 / 5 : ℝ) * P) := by
  calc
    _ ≤ Real.exp (-(17 / 25 : ℝ) * P) * (B * Real.exp (P / 5)) :=
      mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = B * Real.exp (-(12 / 25 : ℝ) * P) := by
      rw [show Real.exp (-(17 / 25 : ℝ) * P) * (B * Real.exp (P / 5)) =
        B * (Real.exp (-(17 / 25 : ℝ) * P) * Real.exp (P / 5)) by ring, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hB

lemma partition_cost (P B : ℝ) (p : ℕ) (hB : 0 ≤ B)
    (hp : (p : ℝ) ≤ Real.exp (P / 10)) :
    (p : ℝ) ^ p * (B * Real.exp (-(1 / 5 : ℝ) * P)) ^ p ≤
      B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * P)) := by
  calc
    _ ≤ Real.exp (P / 10) ^ p * (B * Real.exp (-(1 / 5 : ℝ) * P)) ^ p :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) (by positivity)
    _ = _ := by
      rw [← mul_pow, show Real.exp (P / 10) * (B * Real.exp (-(1 / 5 : ℝ) * P)) =
        B * (Real.exp (P / 10) * Real.exp (-(1 / 5 : ℝ) * P)) by ring, ← Real.exp_add,
        mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

end SharpRamseyFive.MomentBudgets

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

theorem ambient_refined_truncated_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
    (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hB : 0 ≤ B)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * p) (N₂ * p) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight (fun d => L * weight d) lines R J base x) ≤ D₀)
    (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
    (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
    (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
      B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
    (∫ ω, HighMoment.allTrunc R J ω *
      (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R))) := by
  have hP : 0 ≤ (L : ℝ) * R := by positivity
  apply (truncated_power_designated weight R J K L base lines own hp hL hbase hlower hdelta hKR).trans
  have hs := designation_sum_enumerated (V := Fin p) weight lines hp (by simp)
    R L denom rootB mass C D₀ base (B * Real.exp (-(1 / 5 : ℝ) * ((L : ℝ) * R))) hd hb hm hC hD
    (by positivity) hmass K J h N₁ N₂ hK hh low hsize
    (by simpa only [Fintype.card_fin] using herr) hN₁ hN₂
    (by simpa only [Fintype.card_fin] using hBC) hrow hpair hDsum
    (by simpa only [Fintype.card_fin] using MomentBudgets.singleton_cost _ B _ hP hB hcost)
    Δ hΔ (fun m hm hmp => MomentBudgets.block_cost _ B _ _ p m hP hB
      (by positivity) (by positivity) hm (by simpa only [Fintype.card_fin] using hmp) hp2 hRelPairs hdeg)
  apply hs.trans
  simp only [Fintype.card_fin]
  apply MomentBudgets.partition_cost _ B p hB
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact (show (p : ℝ) ≤ (p : ℝ) ^ 2 by nlinarith).trans hp2

omit [DecidableEq D] in

lemma allTrunc_eq_one {R J : ℕ} (h : R < J) (ω : Fin R × D → ℕ) :
    HighMoment.allTrunc R J ω = 1 := by
  apply Finset.prod_eq_one
  intro d _
  unfold lineTrunc
  apply ite_eq_left
  exact (show (Finset.univ.filter (fun r => ω (r,d) ≠ 0)).card ≤ R by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun r : Fin R => ω (r,d) ≠ 0) Finset.univ)).trans_lt h

theorem ambient_untruncated_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
    (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hB : 0 ≤ B)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h)
    (hsize : h ≤ (R / 2) / (2 * K))
    (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * p) (N₂ * p) true) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, |PoissonScore.mass weight (lines x) - base| ^ (R / 2)) ≤ D₀)
    (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
    (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
    (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
      B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
    (∫ ω, (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R))) := by
  have hs := ambient_refined_truncated_moment weight lines hp R own L denom rootB mass C D₀ base B
    hL hbase hlower hdelta hd hb hm hC hD hB hmass K (R+1) h N₁ N₂ hK hKR hh true
    (by simpa using hsize) herr hN₁ hN₂ hBC hrow hpair
    (by simpa only [independentWeight, Nat.lt_succ_self, ite_true, add_zero] using hDsum)
    hcost hp2 Δ hΔ hdeg hRelPairs
  simpa only [allTrunc_eq_one (Nat.lt_succ_self R), one_mul] using hs

end SharpRamseyFive.AmbientEnumeration

namespace SharpLogRamsey.MomentBudgetBridge

lemma anchorBudget_nonneg (p : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anchorBudget p P := by
  unfold anchorBudget
  positivity

theorem labelled_branching_bound (p D : ℕ) (P B H N M : ℝ)
    (hP : 0 ≤ P) (hB : 1 ≤ B) (hH : H ≤ 4*B^2) (hN : N ≤ 4*B)
    (hM : M ≤ (p : ℝ)^2 * (B^2 * Real.exp (P/50) * ((D : ℝ)+4) * (2*P)^200)) :
    1 + (((p : ℝ)*(H*p)/B)/B^8 +
      (p : ℝ)^2*(N*p)*anchorBudget p P/B +
      ((p : ℝ)^3*p*(anchorBudget p P)^2/B)*B +
      (p : ℝ)^2*M/B^2) ≤ Real.exp (P/50)*certificateOverhead p D P := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hA := anchorBudget_nonneg p hP
  have he : 1 ≤ Real.exp (P/50) := Real.one_le_exp_iff.mpr (by positivity)
  have hroot : ((p : ℝ)*(H*p)/B)/B^8 ≤ 4*(p : ℝ)^2 := by
    apply (div_le_iff₀ (pow_pos hB0 8)).mpr
    apply (div_le_iff₀ hB0).mpr
    have hpow : B^2 ≤ B^9 := pow_le_pow_right₀ hB (by decide)
    calc
      (p : ℝ)*(H*p) ≤ (p : ℝ)*(4*B^2*p) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH hp) hp
      _ = 4*(p : ℝ)^2*B^2 := by ring
      _ ≤ 4*(p : ℝ)^2*B^9 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 4*(p : ℝ)^2*B^8*B := by ring
  have hanchor : (p : ℝ)^2*(N*p)*anchorBudget p P/B ≤
      4*(p : ℝ)^3*anchorBudget p P := by
    apply (div_le_iff₀ hB0).mpr
    calc
      _ ≤ (p : ℝ)^2*(4*B*p)*anchorBudget p P := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hp) (by positivity)) hA
      _ = _ := by ring
  have htwo : ((p : ℝ)^3*p*(anchorBudget p P)^2/B)*B =
      (p : ℝ)^4*(anchorBudget p P)^2 := by
    rw [div_mul_cancel₀ _ hB0.ne']
    ring
  have hpair : (p : ℝ)^2*M/B^2 ≤
      Real.exp (P/50)*((p : ℝ)^4*((D : ℝ)+4)*(2*P)^200) := by
    apply (div_le_iff₀ (pow_pos hB0 2)).mpr
    calc
      _ ≤ (p : ℝ)^2*((p : ℝ)^2*(B^2*Real.exp (P/50)*((D : ℝ)+4)*(2*P)^200)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  have hplain : 1 + 4*(p : ℝ)^2 + 4*(p : ℝ)^3*anchorBudget p P +
      (p : ℝ)^4*(anchorBudget p P)^2 ≤
      Real.exp (P/50)*(1 + 4*(p : ℝ)^2 + 4*(p : ℝ)^3*anchorBudget p P +
      (p : ℝ)^4*(anchorBudget p P)^2) := by
    exact le_mul_of_one_le_left (by positivity) he
  unfold certificateOverhead
  rw [htwo]
  nlinarith only [hroot, hanchor, hpair, hplain]

theorem absorb_certificate (p D : ℕ) (P : ℝ)
    (h : certificateOverhead p D P ≤ Real.exp (2*P/25)) :
    Real.exp (P/50)*certificateOverhead p D P ≤ Real.exp (P/10) := by
  calc
    _ ≤ Real.exp (P/50)*Real.exp (2*P/25) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem singleton_budget (p : ℕ) (B P : ℝ) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hp : 2*(p : ℝ)+3 ≤ Real.exp (P/10)) :
    B*Real.exp (P/100) + 2*((p+1 : ℝ)*(B*Real.exp (P/10))) ≤
      B*Real.exp (P/5) := by
  have he : Real.exp (P/100) ≤ Real.exp (P/10) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ B*Real.exp (P/10)+2*((p+1 : ℝ)*(B*Real.exp (P/10))) := by
      linarith only [mul_le_mul_of_nonneg_left he hB]
    _ = (B*Real.exp (P/10))*(2*(p : ℝ)+3) := by ring
    _ ≤ (B*Real.exp (P/10))*Real.exp (P/10) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hB (Real.exp_pos _).le)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma shifted_dyadic_budget (p D : ℕ) (P C : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hpoly : shiftOverhead p D ≤ Real.exp (2*P/25)) :
    4*C+(D : ℝ)*C*Real.exp (P/50)*(2*(p : ℝ))^200 ≤ C*Real.exp (P/10) := by
  have he : 1 ≤ Real.exp (P/50) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : (2*(p : ℝ))^200 ≤ (200*(p : ℝ))^200 :=
    pow_le_pow_left₀ (by positivity) (by have := (Nat.cast_nonneg p : (0 : ℝ) ≤ p); linarith) _
  have heC : 4*C ≤ 4*C*Real.exp (P/50) := le_mul_of_one_le_right (by positivity) he
  have hpow := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (D : ℝ)*C*Real.exp (P/50) by positivity)
  calc
    _ ≤ C*Real.exp (P/50)*shiftOverhead p D := by
      unfold shiftOverhead
      nlinarith only [heC, hpow]
    _ ≤ C*Real.exp (P/50)*Real.exp (2*P/25) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma strong_dyadic_budget (p D : ℕ) (P C : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hpoly : shiftOverhead p D ≤ Real.exp (2*P/25)) :
    4*C+(D : ℝ)*C*Real.exp (P/50)*(200*(p : ℝ))^200 ≤ C*Real.exp (P/10) := by
  have he : 1 ≤ Real.exp (P/50) := Real.one_le_exp_iff.mpr (by positivity)
  have heC : 4*C ≤ 4*C*Real.exp (P/50) := le_mul_of_one_le_right (by positivity) he
  calc
    _ ≤ C*Real.exp (P/50)*shiftOverhead p D := by
      unfold shiftOverhead
      nlinarith only [heC]
    _ ≤ C*Real.exp (P/50)*Real.exp (2*P/25) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end SharpLogRamsey.MomentBudgetBridge
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_StrongDegreeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpLogRamsey.MomentBudgetBridge
lemma strong_degree_budget (B P : ℝ) (hP : 1 ≤ P) (hB : Real.exp (3*P) ≤ B) :
    1+B*Real.exp (-3*P) ≤ B*Real.exp (-P) := by
  have he := mul_le_mul_of_nonneg_right hB (Real.exp_pos (-3*P)).le
  have h1 : 1 ≤ B*Real.exp (-3*P) := by
    simpa only [← Real.exp_add, show 3*P + -3*P = 0 by ring, Real.exp_zero] using he
  have hexp : 2*Real.exp (-3*P) ≤ Real.exp (-P) := by
    have h2 : 2 ≤ Real.exp (2*P) := by
      have ht := Real.add_one_le_exp (2*P)
      linarith
    have hm := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-3*P)).le
    calc
      _ ≤ Real.exp (2*P)*Real.exp (-3*P) := hm
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hm := mul_le_mul_of_nonneg_left hexp (le_trans (Real.exp_pos _).le hB)
  nlinarith only [h1, hm]

end SharpLogRamsey.MomentBudgetBridge

namespace SharpLogRamsey.HighMoment
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive WeightedPrograms SingletonEnumeration
open PoissonScore AmbientEnumeration ComponentEnumeration
open SharpLogRamsey.MomentBudgetBridge

variable {D H I : Type} [Fintype D] [DecidableEq D]
  [Fintype H] [DecidableEq H] [DecidableEq I]

omit [Fintype D] [DecidableEq I] in

theorem labelled_pair_bound (weight : D → ℝ≥0) (lines : H → Finset D)
    (p R : ℕ) (L : ℝ≥0) (B : ℝ)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (hmass : ∀ x, mass weight (lines x) ≤ 2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ) *
        a i ^ 200 ≤ B^2*Real.exp (((L : ℝ)*R)/50)) :
    pairMoment (B := Fin R) (fun z : H × Fin p => lines z.1) (fun d => L*weight d) 200 ≤
      (p : ℝ)^2 * (B^2*Real.exp (((L : ℝ)*R)/50)*((T.card : ℝ)+4)*(2*((L : ℝ)*R))^200) := by
  have he : 1 ≤ Real.exp (((L : ℝ)*R)/50) := Real.one_le_exp_iff.mpr (by positivity)
  have hmass' x : ∑ d ∈ lines x, ((L*weight d : ℝ≥0) : ℝ) ≤ 2*(L : ℝ) := by
    simp only [NNReal.coe_mul, ← Finset.mul_sum]
    have ht := mul_le_mul_of_nonneg_left (hmass x) L.coe_nonneg
    simpa only [mass, mul_comm] using ht
  have hlabel := pairMoment_labelled_le (V := Fin p) (B := Fin R) lines
    (fun d => L*weight d) 200 (2*(L : ℝ)) (by positivity) hmass'
  have hpair := pairMoment_dyadic (B := Fin R) lines weight L 200 (by decide) T a ha hcover
    (B^2*Real.exp (((L : ℝ)*R)/50)) (by positivity) hcount
  have hH' : (Fintype.card H : ℝ) ≤ 4*B^2*Real.exp (((L : ℝ)*R)/50) :=
    hH.trans (le_mul_of_one_le_right (by positivity) he)
  simp only [Fintype.card_fin] at hlabel hpair
  apply hlabel.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hdiag := mul_le_mul_of_nonneg_right hH' (pow_nonneg (show 0 ≤ (R : ℝ)*(2*(L : ℝ)) by positivity) 200)
  calc
    _ ≤ (T.card : ℝ)*(B^2*Real.exp (((L : ℝ)*R)/50))*(2*R*(L : ℝ))^200 +
        4*B^2*Real.exp (((L : ℝ)*R)/50)*((R : ℝ)*(2*(L : ℝ)))^200 := add_le_add hpair hdiag
    _ = _ := by ring

omit [Fintype D] [DecidableEq I] in

theorem full_branching_bound (weight : D → ℝ≥0) (lines : H → Finset D)
    (p R N : ℕ) (L : ℝ≥0) (B : ℝ) (hB : 1 ≤ B)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2) (hN : (N : ℝ) ≤ 4*B)
    (hmass : ∀ x, mass weight (lines x) ≤ 2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ) *
        a i ^ 200 ≤ B^2*Real.exp (((L : ℝ)*R)/50))
    (hpoly : certificateOverhead p T.card ((L : ℝ)*R) ≤ Real.exp (2*((L : ℝ)*R)/25)) :
    B*(1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L*weight d) B B (2*(L : ℝ)) 200
      (N*p) (1*p) true) ≤ B*Real.exp (((L : ℝ)*R)/10) := by
  have hM := labelled_pair_bound weight lines p R L B hH hmass T a ha hcover hcount
  have hn := labelled_branching_bound p T.card ((L : ℝ)*R) B (Fintype.card H) N
    (pairMoment (B := Fin R) (fun z : H × Fin p => lines z.1) (fun d => L*weight d) 200)
    (by positivity) hB hH hN hM
  have hid : uniformAnchorBudget (V := Fin p) (B := Fin R) 200 (2*(L : ℝ)) =
      anchorBudget p ((L : ℝ)*R) := by
    simp only [uniformAnchorBudget, MomentBudgetBridge.anchorBudget, Fintype.card_fin, Nat.cast_ofNat]
    ring
  have hnorm : 1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L*weight d) B B (2*(L : ℝ)) 200
      (N*p) (1*p) true ≤ Real.exp (((L : ℝ)*R)/10) := by
    unfold branchingBound
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ite_true, one_mul, hid]
    exact hn.trans (absorb_certificate p T.card ((L : ℝ)*R) hpoly)
  exact mul_le_mul_of_nonneg_left hnorm (by linarith)

lemma relation_row_card (rel : H → H → Prop) (y : H) :
    (Fintype.card {x : H // rel y x} : ℝ) ≤
      1+((Finset.univ.filter (fun x : {x : H // x ≠ y} => rel y x)).card : ℝ) := by
  classical
  have he : (Fintype.card {x : H // rel y x} : ℝ) =
      ∑ x : H, if rel y x then (1 : ℝ) else 0 := by
    simp only [Fintype.card_subtype, Finset.sum_boole]
  rw [he, sum_split_diagonal _ y]
  simp only [Finset.sum_boole]
  split_ifs <;> linarith

lemma relation_pairs_card (rel : H → H → Prop) :
    (Fintype.card (RelatedPair rel) : ℝ) ≤ Fintype.card H+
      ((Finset.univ.filter (fun z : DistinctPairs H => rel z.1 z.2)).card : ℝ) := by
  classical
  have he : (Fintype.card (RelatedPair rel) : ℝ) =
      ∑ x : H, ∑ y : H, if rel x y then (1 : ℝ) else 0 := by
    simp only [RelatedPair, Fintype.card_sigma, Nat.cast_sum, Fintype.card_subtype,
      Finset.sum_boole]
  rw [he, sum_pairs_split_diagonal]
  simp only [Finset.sum_boole]
  gcongr
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

lemma strong_pairs_markov (θ : DistinctPairs H → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (t : ℝ) (ht : 0 ≤ t) (K : ℕ) :
    ((Finset.univ.filter (fun z => t < θ z)).card : ℝ)*t^K ≤ ∑ z, θ z ^ K := by
  classical
  have he : ((Finset.univ.filter (fun z => t < θ z)).card : ℝ) =
      ∑ z, if t < θ z then (1 : ℝ) else 0 := by simp only [Finset.sum_boole]
  rw [he, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases htz : t < θ z
  · simpa only [ite_eq_left htz, one_mul] using pow_le_pow_left₀ ht htz.le K
  · simp only [ite_eq_right htz, zero_mul]
    exact pow_nonneg (hθ z) K

omit [Fintype D] [DecidableEq D] [DecidableEq H] in

lemma deviation_sum (weight : D → ℝ≥0) (lines : H → Finset D)
    (base : ℝ) (R : ℕ) (hR : 4 ≤ R)
    (hdelta : ∀ x, |mass weight (lines x)-base| ≤ (17/100 : ℝ))
    (C : ℝ) (hsq : (∑ x, (mass weight (lines x)-base)^2) ≤ C) :
    (∑ x, |mass weight (lines x)-base|^(R/2)) ≤ C := by
  apply le_trans _ hsq
  apply Finset.sum_le_sum
  intro x _
  calc
    _ ≤ |mass weight (lines x)-base|^2 :=
      pow_le_pow_of_le_one (abs_nonneg _) ((hdelta x).trans (by norm_num)) (by omega)
    _ = _ := sq_abs _

omit [DecidableEq I] in
omit [Fintype D] in

theorem dyadic_shift_bounds (weight : D → ℝ≥0) (lines : H → Finset D)
    (p : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)*
        a i^200 ≤ B^2*Real.exp (P/50))
    (hrow : ∀ y i, i ∈ T →
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        a i ≤ mass weight (lines x ∩ lines y))).card : ℝ)*a i^200 ≤ B*Real.exp (P/50))
    (hpoly : shiftOverhead p T.card ≤ Real.exp (2*P/25)) :
    (∀ y, (∑ x : H, shiftKernel weight lines p 200 x y) ≤ B*Real.exp (P/10)) ∧
    (∑ x : H, ∑ y : H, shiftKernel weight lines p 200 x y) ≤ (B*Real.exp (P/10))^2 := by
  have hB0 : 0 ≤ B := by linarith
  constructor
  · intro y
    have hcover' (x : {x : H // x ≠ y}) (hx : 0 < mass weight (lines x ∩ lines y)) :
        ∃ i ∈ T, a i ≤ mass weight (lines x ∩ lines y) ∧
          mass weight (lines x ∩ lines y) ≤ 2*a i := by
      have hh := hcover ⟨y, x⟩
      simpa only [strength, mass, Finset.inter_comm] using hh (by
        simpa only [strength, mass, Finset.inter_comm] using hx)
    have hs := shift_row_dyadic weight lines p 200 (by decide) y T a
      (B*Real.exp (P/50)) (by positivity) ha hcover' (hrow y)
    apply hs.trans
    calc
      _ ≤ 4*B+(T.card : ℝ)*B*Real.exp (P/50)*(2*(p : ℝ))^200 := by
        nlinarith only [hB]
      _ ≤ _ := shifted_dyadic_budget p T.card P B hP hB0 hpoly
  · have hs := shift_pairs_dyadic weight lines p 200 (by decide) T a
      (B^2*Real.exp (P/50)) (by positivity) ha hcover hcount
    apply hs.trans
    calc
      _ ≤ 4*B^2+(T.card : ℝ)*B^2*Real.exp (P/50)*(2*(p : ℝ))^200 := by
        nlinarith only [hH]
      _ ≤ B^2*Real.exp (P/10) := shifted_dyadic_budget p T.card P (B^2) hP (sq_nonneg _) hpoly
      _ ≤ (B*Real.exp (P/10))^2 := by
        have he : 1 ≤ Real.exp (P/10) := Real.one_le_exp_iff.mpr (by positivity)
        have hsq : Real.exp (P/10) ≤ Real.exp (P/10)^2 := le_self_pow₀ he (by decide : 2 ≠ 0)
        simpa only [mul_pow] using mul_le_mul_of_nonneg_left hsq (sq_nonneg B)

omit [Fintype D] [DecidableEq I] in

theorem strong_relation_pairs (weight : D → ℝ≥0) (lines : H → Finset D)
    (p : ℕ) (hp : 0 < p) (B P : ℝ) (hP : 0 ≤ P)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)*
        a i^200 ≤ B^2*Real.exp (P/50))
    (hpoly : shiftOverhead p T.card ≤ Real.exp (2*P/25)) :
    (Fintype.card (RelatedPair (overlapRelation weight lines (1/(100*p)))) : ℝ) ≤
      B^2*Real.exp (P/10) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpne : (100*(p : ℝ)) ≠ 0 := by positivity
  have hmoment := DyadicMoments.moment_le_of_cover (strength lines weight) a T 200
    (by decide) (B^2*Real.exp (P/50)) (by positivity)
    (strength_nonneg lines weight) ha hcover hcount
  have hmarkov := strong_pairs_markov (strength lines weight) (strength_nonneg lines weight)
    (1/(100*(p : ℝ))) (by positivity) 200
  have hm := mul_le_mul_of_nonneg_right (hmarkov.trans hmoment)
    (pow_nonneg (show 0 ≤ 100*(p : ℝ) by positivity) 200)
  have hcancel : (1/(100*(p : ℝ)))^200*(100*(p : ℝ))^200 = 1 := by
    rw [← mul_pow, one_div_mul_cancel hpne, one_pow]
  have hdistinct : ((Finset.univ.filter (fun z : DistinctPairs H =>
      1/(100*(p : ℝ)) < strength lines weight z)).card : ℝ) ≤
      (T.card : ℝ)*(B^2)*Real.exp (P/50)*(200*(p : ℝ))^200 := by
    rw [mul_assoc, hcancel, mul_one] at hm
    apply hm.trans_eq
    rw [show 200*(p : ℝ) = 2*(100*(p : ℝ)) by ring, mul_pow]
    ring
  have hh := relation_pairs_card (overlapRelation weight lines (1/(100*(p : ℝ))))
  apply hh.trans
  have hn : ((Finset.univ.filter (fun z : DistinctPairs H =>
      overlapRelation weight lines (1/(100*(p : ℝ))) z.1 z.2)).card : ℝ) ≤
      (T.card : ℝ)*B^2*Real.exp (P/50)*(200*(p : ℝ))^200 := by
    convert hdistinct using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
  calc
    _ ≤ 4*B^2+(T.card : ℝ)*B^2*Real.exp (P/50)*(200*(p : ℝ))^200 := add_le_add hH hn
    _ ≤ _ := strong_dyadic_budget p T.card P (B^2) hP (sq_nonneg B) hpoly

omit [Fintype D] in

theorem strong_relation_degree (weight : D → ℝ≥0) (lines : H → Finset D)
    (p : ℕ) (B P : ℝ) (hP : 1 ≤ P) (hB : Real.exp (3*P) ≤ B)
    (hstrong : ∀ y,
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        1/(100*(p : ℝ)) ≤ mass weight (lines x ∩ lines y))).card : ℝ) ≤ B*Real.exp (-3*P)) :
    ∃ Δ : ℕ,
      (∀ y, Fintype.card {x : H // overlapRelation weight lines (1/(100*p)) y x} ≤ Δ) ∧
      (Δ : ℝ) ≤ B*Real.exp (-P) := by
  have hB0 : 0 ≤ B := (Real.exp_pos _).le.trans hB
  refine ⟨⌊B*Real.exp (-P)⌋₊, ?_, Nat.floor_le (by positivity)⟩
  intro y
  apply Nat.le_floor
  have hh := relation_row_card (overlapRelation weight lines (1/(100*(p : ℝ)))) y
  have hm : ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
      overlapRelation weight lines (1/(100*(p : ℝ))) y x)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
          1/(100*(p : ℝ)) ≤ mass weight (lines x ∩ lines y))).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have ht := hx.le
    simpa only [overlapRelation, Finset.inter_comm] using ht
  apply hh.trans
  calc
    _ ≤ 1+B*Real.exp (-3*P) := by linarith only [hm, hstrong y]
    _ ≤ _ := strong_degree_budget B P hP hB

omit [DecidableEq I] in

theorem prepared_pencil_high_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (24/25 : ℝ) ≤ base)
    (hlower : ∀ x, (3/4 : ℝ) ≤ mass weight (lines x))
    (hupper : ∀ x, mass weight (lines x) ≤ 2)
    (hdelta : ∀ x, |mass weight (lines x)-base| ≤ (17/100 : ℝ))
    (hB : Real.exp (3*((L : ℝ)*R)) ≤ B)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (N : ℕ) (hN : (N : ℝ) ≤ 4*B)
    (hone : ∀ d, (Finset.univ.filter (fun x => d ∈ lines x)).card ≤ N)
    (htwo : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun x => d ∈ lines x ∧ e ∈ lines x)).card ≤ 1)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)*
        a i^200 ≤ B^2*Real.exp (((L : ℝ)*R)/50))
    (hrow : ∀ y i, i ∈ T →
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        a i ≤ mass weight (lines x ∩ lines y))).card : ℝ)*a i^200 ≤
          B*Real.exp (((L : ℝ)*R)/50))
    (hstrong : ∀ y,
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        1/(100*(p : ℝ)) ≤ mass weight (lines x ∩ lines y))).card : ℝ) ≤
          B*Real.exp (-3*((L : ℝ)*R)))
    (hsq : (∑ x, (mass weight (lines x)-base)^2) ≤ B*Real.exp (((L : ℝ)*R)/100))
    (hpoly : certificateOverhead p T.card ((L : ℝ)*R) ≤ Real.exp (2*((L : ℝ)*R)/25))
    (hshift : shiftOverhead p T.card ≤ Real.exp (2*((L : ℝ)*R)/25))
    (hp2 : (p : ℝ)^2 ≤ Real.exp (((L : ℝ)*R)/10))
    (hps : 2*(p : ℝ)+3 ≤ Real.exp (((L : ℝ)*R)/10))
    (h : ℕ) (hh : 0 < h) (hR : 400 ≤ R)
    (hsize : h ≤ (R/2)/400)
    (herr : (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2) :
    (∫ ω, (∑ x : H, scoreTerm (lines x) (Real.exp (-(L : ℝ)*base)) (own x)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R × D => L*weight i.2)) ≤
        B^p*Real.exp (-(1/10 : ℝ)*(p*((L : ℝ)*R))) := by
  have hP0 : 0 ≤ (L : ℝ)*R := by positivity
  have hP : 1 ≤ (L : ℝ)*R := by
    have hR' : (400 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  have hB1 : 1 ≤ B := (Real.one_le_exp_iff.mpr (by positivity)).trans hB
  have hB0 : 0 ≤ B := by linarith
  have hbranch := full_branching_bound weight lines p R N L B hB1 hH hN hupper
    T a ha hcover hcount hpoly
  obtain ⟨hrows, hpairs⟩ := dyadic_shift_bounds weight lines p B ((L : ℝ)*R)
    hB1 hP0 hH T a ha hcover hcount hrow hshift
  obtain ⟨Δ, hΔ, hdeg⟩ := strong_relation_degree weight lines p B ((L : ℝ)*R) hP hB hstrong
  have hrel := strong_relation_pairs weight lines p hp B ((L : ℝ)*R) hP0 hH
    T a ha hcover hcount hshift
  have hmass x : ∑ d ∈ lines x, ((L*weight d : ℝ≥0) : ℝ) ≤ 2*(L : ℝ) := by
    simp only [NNReal.coe_mul, ← Finset.mul_sum]
    have ht := mul_le_mul_of_nonneg_left (hupper x) L.coe_nonneg
    simpa only [mass, mul_comm] using ht
  exact ambient_untruncated_moment weight lines hp R own L B B (2*(L : ℝ))
    (B*Real.exp (((L : ℝ)*R)/10)) (B*Real.exp (((L : ℝ)*R)/100)) base B
    hL (by linarith) hlower hdelta (by linarith) hB1 (by positivity)
    (by positivity) (by positivity) hB0 hmass 200 h N 1 (by decide) (by omega)
    hh hsize herr hone htwo hbranch hrows hpairs
    (deviation_sum weight lines base R (by omega) hdelta _ hsq)
    (singleton_budget p B ((L : ℝ)*R) hB0 hP0 hps) hp2 Δ hΔ hdeg hrel

end SharpLogRamsey.HighMoment

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TestSecondMomentBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.SecondMoment

open SharpRamseyFive.PoissonScore SharpRamseyFive.DyadicMoments

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]

lemma abs_pairMean_self_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hbase0 : 0 ≤ base)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    |pairMean rate s s (Real.exp (-L * base))| ≤ 2 * Real.exp (-L * c) := by
  rw [pairMean, ← integral_centeredFactor_mul]
  have hb : Real.exp (-L * base) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hn : 0 ≤ ∫ ω, centeredFactor s (Real.exp (-L * base)) ω *
      centeredFactor s (Real.exp (-L * base)) ω ∂batchMeasure rate :=
    integral_nonneg (fun ω => mul_self_nonneg _)
  rw [abs_of_nonneg hn]
  refine (integral_mono (integrable_centeredFactor_mul rate s s _)
    (integrable_centeredFactor rate s _).abs ?_).trans
    (integral_abs_centeredFactor_exp_le rate s hL hmass hlam hbase)
  intro ω
  have ha := abs_centeredFactor_le_one s _ hb ω
  have he := sq_abs (centeredFactor s (Real.exp (-L * base)) ω)
  nlinarith [abs_nonneg (centeredFactor s (Real.exp (-L * base)) ω)]

theorem second_moment_finite (rate : ι → ℝ≥0) (directions : H → Finset ι)
    (R : ℕ) (own : H → Fin R → Bool) (L base : ℝ)
    (lam : H → ℝ) (θ : H → H → ℝ)
    (hL : 1 ≤ L) (hbase : 3/4 ≤ base)
    (hmass : ∀ h, mass rate (directions h) = L * lam h)
    (hlam : ∀ h, 3/4 ≤ lam h)
    (hθ : ∀ h k, 0 ≤ θ h k)
    (hinter : ∀ h k, h ≠ k → mass rate (directions h ∩ directions k) = L * θ h k) :
    (∫ ω, (typicalScore Finset.univ directions (Real.exp (-L * base)) own ω)^2
      ∂scheduleMeasure rate R) ≤
    (Fintype.card H : ℝ) * (2 * Real.exp (-L * (3/4)))^R +
    (L^2 * Real.exp (-L * (3/4)))^R * 2^(R-1) *
      ((∑ h, |lam h - base|^R)^2 + ∑ h, ∑ k, (θ h k)^R) := by
  classical
  let A := L^2 * Real.exp (-L * (3/4))
  let d := (2 * Real.exp (-L * (3/4)))^R
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hp (h k : H) : |pairMean rate (directions h) (directions k)
      (Real.exp (-L * base))|^R ≤
    (if h = k then d else 0) + A^R * 2^(R-1) *
      (|lam h - base|^R * |lam k - base|^R + (θ h k)^R) := by
    by_cases hk : h = k
    · subst k
      have hg := pow_le_pow_left₀ (abs_nonneg _) (abs_pairMean_self_le rate
        (directions h) (by linarith : 0 ≤ L) (by linarith : 0 ≤ base)
        (hmass h) (hlam h) hbase) R
      rw [ite_eq_left rfl]
      exact hg.trans (le_add_of_nonneg_right (by positivity [hθ h h]))
    · have hi := abs_integral_centeredFactor_mul_exp_le rate (directions h)
        (directions k) hL (by norm_num : (0 : ℝ) ≤ 3/4) (hmass h) (hmass k)
        (hinter h k hk) (hlam h) (hlam k) hbase
      rw [integral_centeredFactor_mul] at hi
      change |pairMean rate (directions h) (directions k) (Real.exp (-L * base))| ≤
        A * (|lam h - base| * |lam k - base| + θ h k) at hi
      simp only [ite_eq_right hk, zero_add]
      calc
        _ ≤ (A * (|lam h - base| * |lam k - base| + θ h k))^R :=
          pow_le_pow_left₀ (abs_nonneg _) hi R
        _ = A^R * (|lam h - base| * |lam k - base| + θ h k)^R := mul_pow _ _ _
        _ ≤ A^R * (2^(R-1) * ((|lam h - base| * |lam k - base|)^R + (θ h k)^R)) :=
          mul_le_mul_of_nonneg_left (add_pow_le (by positivity) (hθ h k) R)
            (pow_nonneg hA R)
        _ = _ := by rw [mul_pow]; ring
  have hs := (integral_typicalScore_sq_le rate Finset.univ directions
    (Real.exp (-L * base)) own).trans (Finset.sum_le_sum (fun h _ =>
      Finset.sum_le_sum (fun k _ => hp h k)))
  apply hs.trans_eq
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two]
  rfl

theorem second_moment_dyadic {J : Type*} (rate : ι → ℝ≥0)
    (directions : H → Finset ι) (R : ℕ) (own : H → Fin R → Bool)
    (L base B C : ℝ) (lam : H → ℝ) (θ : H → H → ℝ)
    (T : Finset J) (a : J → ℝ)
    (hL : 1 ≤ L) (hbase : 3/4 ≤ base) (_hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hR : 200 ≤ R)
    (hmass : ∀ h, mass rate (directions h) = L * lam h)
    (hlam : ∀ h, 3/4 ≤ lam h)
    (hδ : ∀ h, |lam h - base| ≤ 1)
    (hδsum : (∑ h, |lam h - base|^2) ≤ C*B*Real.exp (L/100))
    (hcard : (Fintype.card H : ℝ) ≤ C*B^2)
    (hθ : ∀ h k, 0 ≤ θ h k) (hθmax : ∀ h k, θ h k ≤ 2)
    (hinter : ∀ h k, h ≠ k → mass rate (directions h ∩ directions k) = L * θ h k)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ h k, 0 < θ h k → ∃ i ∈ T, a i ≤ θ h k ∧ θ h k ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : H × H => a i ≤ θ z.1 z.2)).card : ℝ) *
        a i^200 ≤ B^2*Real.exp (L*R/50)) :
    (∫ ω, (typicalScore Finset.univ directions (Real.exp (-L * base)) own ω)^2
      ∂scheduleMeasure rate R) ≤ B^2 *
    (C * (2 * Real.exp (-L * (3/4)))^R +
      (L^2 * Real.exp (-L * (3/4)))^R * 2^(R-1) *
        (C^2 * Real.exp (L/50) + (T.card : ℝ) * 2^R * Real.exp (L*R/50))) := by
  have hs : (∑ h, |lam h - base|^R) ≤ C*B*Real.exp (L/100) := by
    refine (Finset.sum_le_sum (fun h _ =>
      pow_le_pow_of_le_one (abs_nonneg _) (hδ h) (by omega : 2 ≤ R))).trans hδsum
  have hs2 : (∑ h, |lam h - base|^R)^2 ≤ B^2 * (C^2 * Real.exp (L/50)) := by
    calc
      _ ≤ (C*B*Real.exp (L/100))^2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun h _ => by positivity)) hs 2
      _ = _ := by rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; ring_nf
  have ht := higher_moment_le_of_cover (fun z : H × H => θ z.1 z.2) a T
    200 R (by decide) hR (B^2*Real.exp (L*R/50)) 2 (by positivity) (by norm_num)
    (fun z => hθ z.1 z.2) (fun z => hθmax z.1 z.2) ha
    (fun z => hcover z.1 z.2) hcount
  have ht' : (∑ h, ∑ k, (θ h k)^R) ≤ B^2 * ((T.card : ℝ)*2^R*Real.exp (L*R/50)) := by
    calc
      _ ≤ (T.card : ℝ)*2^200*(B^2*Real.exp (L*R/50))*2^(R-200) := by
        simpa only [Fintype.sum_prod_type] using ht
      _ = _ := by
        have hp : (2 : ℝ)^200*2^(R-200) = 2^R := by
          rw [← pow_add, Nat.add_sub_of_le hR]
        calc
          _ = B^2*((T.card : ℝ)*((2 : ℝ)^200*2^(R-200))*Real.exp (L*R/50)) := by ring
          _ = _ := by rw [hp]
  have hd := mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (by positivity : 0 ≤ 2*Real.exp (-L*(3/4))) R)
  have hb := add_le_add hs2 ht'
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (L^2*Real.exp (-L*(3/4)))^R*2^(R-1))
  exact (second_moment_finite rate directions R own L base lam θ hL hbase
    hmass hlam hθ hinter).trans ((add_le_add hd hm).trans_eq (by ring))

lemma second_moment_exponent (L C N : ℝ) (R : ℕ) (hL : 0 ≤ L)
    (_hC : 0 ≤ C) (hN : 0 ≤ N)
    (hd : C*2^R ≤ Real.exp (L*R/20))
    (hp : (2*L^2)^R ≤ Real.exp (L*R/25))
    (hb : C^2*Real.exp (L/50) + N*2^R*Real.exp (L*R/50) ≤ Real.exp (L*R/20))
    (h2 : 2 ≤ Real.exp (L*R/20)) :
    C*(2*Real.exp (-L*(3/4)))^R +
      (L^2*Real.exp (-L*(3/4)))^R*2^(R-1)*
        (C^2*Real.exp (L/50)+N*2^R*Real.exp (L*R/50)) ≤ Real.exp (-(3/5)*(L*R)) := by
  have hP : 0 ≤ L*(R : ℝ) := mul_nonneg hL (Nat.cast_nonneg R)
  have he : (Real.exp (-L*(3/4)))^R = Real.exp (-(3/4)*(L*R)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hd' : C*(2*Real.exp (-L*(3/4)))^R ≤ Real.exp (-(13/20)*(L*R)) := by
    rw [mul_pow, he, ← mul_assoc]
    calc
      _ ≤ Real.exp (L*R/20)*Real.exp (-(3/4)*(L*R)) :=
        mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
      _ = Real.exp (-(7/10)*(L*R)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have ho : (L^2*Real.exp (-L*(3/4)))^R*2^(R-1) ≤
      (2*L^2)^R*Real.exp (-(3/4)*(L*R)) := by
    rw [mul_pow, he, mul_pow]
    have hh : (2 : ℝ)^(R-1) ≤ 2^R :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le R 1)
    nlinarith [mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (L^2)^R*Real.exp (-(3/4)*(L*R)) by positivity)]
  have ht : (L^2*Real.exp (-L*(3/4)))^R*2^(R-1)*
      (C^2*Real.exp (L/50)+N*2^R*Real.exp (L*R/50)) ≤ Real.exp (-(13/20)*(L*R)) := by
    calc
      _ ≤ ((2*L^2)^R*Real.exp (-(3/4)*(L*R)))*Real.exp (L*R/20) :=
        mul_le_mul ho hb (by positivity) (by positivity)
      _ ≤ (Real.exp (L*R/25)*Real.exp (-(3/4)*(L*R)))*Real.exp (L*R/20) := by
        gcongr
      _ = Real.exp (-(33/50)*(L*R)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ 2*Real.exp (-(13/20)*(L*R)) := by linarith
    _ ≤ Real.exp (L*R/20)*Real.exp (-(13/20)*(L*R)) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SharpLogRamsey.SecondMoment

namespace SharpLogRamsey.SecondMoment
open MeasureTheory SharpRamseyFive.PoissonScore
open scoped BigOperators NNReal
variable {ι H J : Type*} [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in

theorem prepared_pencil_second_moment (rate : ι → ℝ≥0) (directions : H → Finset ι)
    (R : ℕ) (own : H → Fin R → Bool) (L base B C : ℝ)
    (lam : H → ℝ) (θ : H → H → ℝ) (T : Finset J) (a : J → ℝ)
    (hL : 1 ≤ L) (hbase : 3/4 ≤ base) (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 200 ≤ R)
    (hmass : ∀ h, mass rate (directions h) = L * lam h)
    (hlam : ∀ h, 3/4 ≤ lam h) (hδ : ∀ h, |lam h - base| ≤ 1)
    (hδsum : (∑ h, |lam h - base|^2) ≤ C*B*Real.exp (L/100))
    (hcard : (Fintype.card H : ℝ) ≤ C*B^2)
    (hθ : ∀ h k, 0 ≤ θ h k) (hθmax : ∀ h k, θ h k ≤ 2)
    (hinter : ∀ h k, h ≠ k → mass rate (directions h ∩ directions k) = L * θ h k)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ h k, 0 < θ h k → ∃ i ∈ T, a i ≤ θ h k ∧ θ h k ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : H × H => a i ≤ θ z.1 z.2)).card : ℝ)*a i^200 ≤
        B^2*Real.exp (L*R/50))
    (hd : C*2^R ≤ Real.exp (L*R/20))
    (hp : (2*L^2)^R ≤ Real.exp (L*R/25))
    (hb : C^2*Real.exp (L/50)+(T.card : ℝ)*2^R*Real.exp (L*R/50) ≤ Real.exp (L*R/20))
    (h2 : 2 ≤ Real.exp (L*R/20)) :
    (∫ ω, (typicalScore Finset.univ directions (Real.exp (-L * base)) own ω)^2
      ∂scheduleMeasure rate R) ≤ B^2*Real.exp (-(3/5)*(L*R)) := by
  exact (second_moment_dyadic rate directions R own L base B C lam θ T a
    hL hbase hB hC hR hmass hlam hδ hδsum hcard hθ hθmax hinter ha hcover hcount).trans
    (mul_le_mul_of_nonneg_left (second_moment_exponent L C T.card R (by linarith)
      hC (Nat.cast_nonneg _) hd hp hb h2) (sq_nonneg B))

end SharpLogRamsey.SecondMoment

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PencilGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in

lemma radialFiber_disjoint (S : Finset (Projectivization K V)) (x : Projectivization K V)
    {W U : RadialLine x} (hne : W ≠ U) : Disjoint (radialFiber S x W) (radialFiber S x U) := by
  apply Finset.disjoint_left.mpr
  intro y hyW hyU
  obtain ⟨_, hyx, hyW⟩ := (mem_radialFiber S x y W).mp hyW
  have hyU := ((mem_radialFiber S x y U).mp hyU).2.2
  exact hne (Subtype.ext ((radial_unique x y hyx.symm W hyW).symm.trans
    (radial_unique x y hyx.symm U hyU)))

lemma radial_biUnion (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    (Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U)).biUnion (radialFiber S x) =
      S.filter (fun y => y ≠ x ∧ y.submodule ≤ U) := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_radialFiber]
  constructor
  · rintro ⟨W, hWU, hyS, hyx, hyW⟩
    exact ⟨hyS, hyx, hyW.trans hWU⟩
  · rintro ⟨hyS, hyx, hyU⟩
    refine ⟨⟨x.submodule ⊔ y.submodule, finrank_join x y hyx.symm, le_sup_left⟩,
      sup_le hx hyU, hyS, hyx, le_sup_right⟩

theorem radial_count (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), (radialFiber S x W).card =
      (S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.card_biUnion, radial_biUnion S x U hx]
  intro W _ U _ hne
  exact radialFiber_disjoint S x hne

theorem radial_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) (c : ℝ) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.mul_sum, ← Nat.cast_sum, radial_count S x U hx]

theorem hyperplane_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (hx : x.submodule ≤ LinearMap.ker H.rep) (c : ℝ) :
    ∑ W ∈ lines x H, c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep)).card :=
  radial_mass S x (LinearMap.ker H.rep) hx c

theorem intersection_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (H J : Projectivization K (Module.Dual K V))
    (hxH : x.submodule ≤ LinearMap.ker H.rep) (hxJ : x.submodule ≤ LinearMap.ker J.rep)
    (c : ℝ) :
    ∑ W ∈ lines x H ∩ lines x J, c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep)).card := by
  have he : lines x H ∩ lines x J =
      Finset.univ.filter (fun W : RadialLine x => W.1 ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep) := by
    ext W
    simp only [Finset.mem_inter, mem_lines, Finset.mem_filter, Finset.mem_univ, true_and, le_inf_iff]
  rw [he]
  exact radial_mass S x _ (le_inf hxH hxJ) c

end
end SharpLogRamsey.PreparedProjectiveGeometry

open Finset Classical
namespace SharpLogRamsey.CertificateGeometry
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
noncomputable section
omit [Finite K] [FiniteDimensional K V] in

lemma through_iff (W : Submodule K V) (H : Projectivization K (Module.Dual K V)) :
    W ≤ LinearMap.ker H.rep ↔ H.submodule ≤ W.dualAnnihilator := by
  rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

attribute [local instance] OAI.SharpLogRamsey.CertificateGeometry.flat_JoinedPencilGeometry_4
theorem card_through (W : Submodule K V) :
    Fintype.card {H : Projectivization K (Module.Dual K V) // W ≤ LinearMap.ker H.rep} =
      ∑ i ∈ range (Module.finrank K W.dualAnnihilator), Nat.card K^i := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeEquivRight (through_iff W)),
    ← Nat.card_congr (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W.dualAnnihilator)]
  exact Projectivization.card_of_finrank K W.dualAnnihilator rfl

end
end SharpLogRamsey.CertificateGeometry

namespace SharpLogRamsey.PreparedProjectiveGeometry
open SharpLogRamsey.CertificateGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma point_dualCoannihilator (H : Projectivization K (Module.Dual K V)) :
    H.submodule.dualCoannihilator = LinearMap.ker H.rep := by
  apply SetLike.coe_injective
  rw [H.submodule_eq, Submodule.coe_dualCoannihilator_span]
  ext v
  simp

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpLogRamsey.CertificateGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem two_directions_card (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (D E : RadialLine x) (hne : D≠E) :
    (A.filter (fun H => D∈lines x H ∧ E∈lines x H)).card≤1 := by
  apply card_le_one.mpr
  intro H hH J hJ
  by_contra hHJ
  have hr := finrank_join H J hHJ
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (H.submodule⊔J.submodule : Submodule K (Module.Dual K V))
  rw [Submodule.dualCoannihilator_sup_eq,point_dualCoannihilator,point_dualCoannihilator] at hd
  have hdimdual : Module.finrank K (Module.Dual K V)=Module.finrank K V := by simp
  have hi : Module.finrank K (LinearMap.ker H.rep⊓LinearMap.ker J.rep : Submodule K V)≤2 := by omega
  have hD : D.1≤LinearMap.ker H.rep⊓LinearMap.ker J.rep :=
    le_inf ((mem_lines _ _ _).mp (mem_filter.mp hH).2.1)
      ((mem_lines _ _ _).mp (mem_filter.mp hJ).2.1)
  have hE : E.1≤LinearMap.ker H.rep⊓LinearMap.ker J.rep :=
    le_inf ((mem_lines _ _ _).mp (mem_filter.mp hH).2.2)
      ((mem_lines _ _ _).mp (mem_filter.mp hJ).2.2)
  have hi2 : Module.finrank K (LinearMap.ker H.rep⊓LinearMap.ker J.rep : Submodule K V)=2 :=
    le_antisymm hi (D.2.1 ▸ Submodule.finrank_mono hD)
  have heD := Submodule.eq_of_le_of_finrank_eq hD (D.2.1.trans hi2.symm)
  have heE := Submodule.eq_of_le_of_finrank_eq hE (E.2.1.trans hi2.symm)
  exact hne (Subtype.ext (heD.trans heE.symm))

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TestRadialWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpRamseyFive.PoissonScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma radialWeight_coe (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (W : RadialLine x) :
    (radialWeight S x c W : ℝ)=strength S x c W := by
  simp only [radialWeight,strength,NNReal.coe_mul,NNReal.coe_natCast]

lemma radialWeight_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H : Projectivization K (Module.Dual K V))
    (hxH : x.submodule≤LinearMap.ker H.rep) :
    mass (radialWeight S x c) (lines x H)=
      (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule≤LinearMap.ker H.rep)).card := by
  simp only [mass,radialWeight_coe,strength]
  exact hyperplane_mass S x H hxH c

lemma radialWeight_intersection (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V))
    (hxH : x.submodule≤LinearMap.ker H.rep) (hxJ : x.submodule≤LinearMap.ker J.rep) :
    mass (radialWeight S x c) (lines x H∩lines x J)=overlap S x c H J := by
  simp only [mass,radialWeight_coe,strength,overlap]
  exact intersection_mass S x H J hxH hxJ c

lemma family_two_directions (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (D E : RadialLine x) (hne : D≠E) :
    (univ.filter (fun H : A => D∈lines x H ∧ E∈lines x H)).card≤1 := by
  have hh := two_directions_card (K:=K) (V:=V) hdim A x D E hne
  refine Nat.le_trans ?_ hh
  apply Finset.card_le_card_of_injOn (fun H : A => H.val)
  · intro H hH
    exact mem_filter.mpr ⟨H.2,(mem_filter.mp hH).2⟩
  · intro H hH J hJ he
    exact Subtype.ext he

lemma family_pair_card (A : Finset (Projectivization K (Module.Dual K V)))
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0) (a : ℝ)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    (univ.filter (fun z : SharpRamseyFive.WeightedPrograms.DistinctPairs A =>
      a ≤ mass (radialWeight S x c) (lines x z.1∩lines x z.2))).card=
      (largePairs S x c a A).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun z => ⟨(z.1.1.1,z.1.2.1.1),?_⟩
    invFun := fun z => ⟨⟨⟨z.1.1,?_⟩,⟨⟨z.1.2,?_⟩,?_⟩⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨z.1.1.2,z.1.2.1.2⟩,?_,?_⟩
    · intro he
      exact z.1.2.2 (Subtype.ext he.symm)
    · rw [←radialWeight_intersection S x c _ _ (hA _ z.1.1.2) (hA _ z.1.2.1.2)]
      exact (mem_filter.mp z.2).2
  · exact (mem_product.mp (mem_filter.mp z.2).1).1
  · exact (mem_product.mp (mem_filter.mp z.2).1).2
  · intro he
    exact (mem_filter.mp z.2).2.1 (congrArg Subtype.val he).symm
  · apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [radialWeight_intersection S x c _ _
      (hA _ (mem_product.mp (mem_filter.mp z.2).1).1)
      (hA _ (mem_product.mp (mem_filter.mp z.2).1).2)]
    exact (mem_filter.mp z.2).2.2
  · intro z
    rfl
  · intro z
    rfl

lemma family_neighbor_card (A : Finset (Projectivization K (Module.Dual K V)))
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0) (a : ℝ)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) (H : A) :
    (univ.filter (fun J : {J : A // J≠H} =>
      a ≤ mass (radialWeight S x c) (lines x J∩lines x H))).card=
      (largeNeighbors S x c a A H).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun J => ⟨J.1.1.1,?_⟩
    invFun := fun J => ⟨⟨⟨J.1,?_⟩,?_⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply mem_filter.mpr
    refine ⟨J.1.1.2,?_,?_⟩
    · intro he
      exact J.1.2 (Subtype.ext he.symm)
    · rw [←radialWeight_intersection S x c _ _ (hA _ H.2) (hA _ J.1.1.2),inter_comm]
      exact (mem_filter.mp J.2).2
  · exact (mem_filter.mp J.2).1
  · intro he
    exact (mem_filter.mp J.2).2.1 (congrArg Subtype.val he).symm
  · apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [inter_comm,radialWeight_intersection S x c _ _ (hA _ H.2) (hA _ (mem_filter.mp J.2).1)]
    exact (mem_filter.mp J.2).2.2
  · intro J
    rfl
  · intro J
    rfl

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestActualMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpLogRamsey.CertificateGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedTestActualMoment_2
theorem one_direction_rank_card (m : ℕ) (hdim : Module.finrank K V ≤ m+2)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (A.filter (fun H => W∈lines x H)).card ≤ ∑ i∈range m,Nat.card K^i := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W.1
  have hw := W.2.1
  have hm : Module.finrank K W.1.dualAnnihilator ≤ m := by omega
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // W.1≤LinearMap.ker H.rep} := by
      rw [←Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : {H // H∈A.filter (fun H => W∈lines x H)} =>
        (⟨H.1,(mem_lines _ _ _).mp (mem_filter.mp H.2).2⟩ :
          {H : Projectivization K (Module.Dual K V) // W.1≤LinearMap.ker H.rep}))
      intro H J he
      apply Subtype.ext
      exact congrArg (fun z => z.1) he
    _ = ∑ i∈range (Module.finrank K W.1.dualAnnihilator),Nat.card K^i := card_through _
    _ ≤ _ := sum_le_sum_of_subset (range_mono hm)

theorem pencil_rank_card (m : ℕ) (hdim : Module.finrank K V ≤ m+1)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    A.card ≤ ∑ i∈range m,Nat.card K^i := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq x.submodule
  have hx := x.finrank_submodule
  have hm : Module.finrank K x.submodule.dualAnnihilator ≤ m := by omega
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // x.submodule≤LinearMap.ker H.rep} := by
      rw [←Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : A =>
        (⟨H.1,hA H H.2⟩ : {H : Projectivization K (Module.Dual K V) // x.submodule≤LinearMap.ker H.rep}))
      intro H J he
      apply Subtype.ext
      exact congrArg (fun z => z.1) he
    _ = ∑ i∈range (Module.finrank K x.submodule.dualAnnihilator),Nat.card K^i := card_through _
    _ ≤ _ := sum_le_sum_of_subset (range_mono hm)

end
end SharpLogRamsey.PreparedProjectiveGeometry
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore
open SharpRamseyFive.WeightedPrograms (DistinctPairs)
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma family_one_direction_rank (m : ℕ) (hdim : Module.finrank K V ≤ m+2)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (univ.filter (fun H : A => W∈lines x H)).card ≤ ∑ i∈range m,Nat.card K^i := by
  have hh := one_direction_rank_card (K:=K) (V:=V) m hdim A x W
  refine Nat.le_trans ?_ hh
  apply Finset.card_le_card_of_injOn (fun H : A => H.val)
  · intro H hH
    exact mem_filter.mpr ⟨H.2,(mem_filter.mp hH).2⟩
  · intro H hH J hJ he
    exact Subtype.ext he

theorem actual_projective_high_moment
    (j : ℕ) (hj : 2 ≤ j) (hj3 : j ≤ 3) (hdim : Module.finrank K V ≤ j+1)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B : ℝ) (hf : f ≤ 1/25) {p : ℕ} (hp : 0<p) (R : ℕ)
    (own : A → Fin R → Bool)
    (hL : 10000 ≤ (L:ℝ))
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 13/100)
    (hB : Real.exp (3*((L:ℝ)*R)) ≤ B)
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ 4*B^2)
    (hdir : ((∑ i∈range (j-1),Nat.card K^i):ℝ) ≤ 4*B)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap S x c H J →
      ∃ i∈T,a i ≤ overlap S x c H J ∧ overlap S x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs S x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hrow : ∀ H∈A,∀ i∈T,((largeNeighbors S x c (a i) A H).card:ℝ)*a i^200 ≤ B*Real.exp (((L:ℝ)*R)/50))
    (hstrong : ∀ H∈A,((largeNeighbors S x c (1/(100*(p:ℝ))) A H).card:ℝ) ≤ B*Real.exp (-3*((L:ℝ)*R)))
    (hsq : (∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ B*Real.exp (((L:ℝ)*R)/100))
    (hpoly : SharpLogRamsey.MomentBudgetBridge.certificateOverhead p T.card ((L:ℝ)*R) ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hshift : SharpLogRamsey.MomentBudgetBridge.shiftOverhead p T.card ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3 ≤ Real.exp (((L:ℝ)*R)/10))
    (h : ℕ) (hh : 0<h) (hR : 400 ≤ R) (hsize : h ≤ (R/2)/400)
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2) :
    (∫ ω,(∑ H : A,scoreTerm (lines x H) (Real.exp (-(L:ℝ)*(1-f))) (own H)
      (fun r d => ω (r,d)))^p ∂batchMeasure (fun i : Fin R × RadialLine x => L*radialWeight S x c i.2))
      ≤ B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hm H (hH : H∈A) := radialWeight_mass S x c H (hA H hH)
  have hi H (hH : H∈A) J (hJ : J∈A) := radialWeight_intersection S x c H J (hA H hH) (hA J hJ)
  apply SharpLogRamsey.HighMoment.prepared_pencil_high_moment
    (radialWeight S x c) (fun H : A => lines x H) hp R own L (1-f) B
    hL (by linarith) _ _ _ hB _ (∑ i∈range (j-1),Nat.card K^i) (by exact_mod_cast hdir) _ _
    T a ha _ _ _ _ _ hpoly hshift hp2 hps h hh hR hsize herr
  · intro H
    rw [hm H H.2]
    exact hlow H H.2
  · intro H
    rw [hm H H.2]
    exact hupp H H.2
  · intro H
    rw [hm H H.2]
    exact (hdelta H H.2).trans (by norm_num)
  · rw [Fintype.card_coe]
    exact (Nat.cast_le.mpr (pencil_rank_card j hdim A x hA)).trans (by exact_mod_cast hcard)
  · intro W
    exact family_one_direction_rank (j-1) (by omega) A x W
  · intro D E hne
    exact family_two_directions (by omega) A x D E hne
  · intro z hz
    have he : SharpRamseyFive.WeightedPrograms.strength (fun H : A => lines x H)
        (radialWeight S x c) z=overlap S x c z.1 z.2 := hi z.1 z.1.2 z.2 z.2.1.2
    rw [he] at hz ⊢
    exact hcover z.1 z.1.2 z.2 z.2.1.2 (fun he => z.2.2 (Subtype.ext he.symm)) hz
  · intro i hiT
    have hc := family_pair_card A S x c (a i) hA
    change ((univ.filter (fun z : DistinctPairs A =>
      a i ≤ mass (radialWeight S x c) (lines x z.1∩lines x z.2))).card:ℝ)*a i^200 ≤ _
    rw [hc]
    exact hcount i hiT
  · intro H i hiT
    rw [family_neighbor_card A S x c (a i) hA H]
    exact hrow H H.2 i hiT
  · intro H
    rw [family_neighbor_card A S x c (1/(100*(p:ℝ))) hA H]
    exact hstrong H H.2
  · calc
      _ = ∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2 := by
        rw [←Finset.sum_coe_sort A (fun H => ((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2)]
        apply sum_congr rfl
        intro H _
        rw [hm H H.2]
      _ ≤ _ := hsq

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TestActualSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma family_all_pairs_card (A : Finset (Projectivization K (Module.Dual K V)))
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0)
    (a : ℝ) (ha : 0<a) :
    (univ.filter (fun z : A×A => a ≤ pencilTheta S x c z.1 z.2)).card=
      (largePairs S x c a A).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun z => ⟨(z.1.1.1,z.1.2.1),?_⟩
    invFun := fun z => ⟨(⟨z.1.1,?_⟩,⟨z.1.2,?_⟩),?_⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl }
  · have hc := (mem_filter.mp z.2).2
    have hn : z.1.1.1≠z.1.2.1 := by
      intro he
      simp only [pencilTheta,ite_eq_left he] at hc
      linarith
    exact mem_filter.mpr ⟨mem_product.mpr ⟨z.1.1.2,z.1.2.2⟩,hn,
      by simpa only [pencilTheta,ite_eq_right hn] using hc⟩
  · exact (mem_product.mp (mem_filter.mp z.2).1).1
  · exact (mem_product.mp (mem_filter.mp z.2).1).2
  · apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    simpa only [pencilTheta,ite_eq_right (mem_filter.mp z.2).2.1] using (mem_filter.mp z.2).2.2

omit [Finite K] [FiniteDimensional K V] in
lemma pencilTheta_nonneg (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V)) :
    0 ≤ pencilTheta S x c H J := by
  unfold pencilTheta overlap
  split_ifs <;> positivity

lemma pencilTheta_le_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V))
    (hH : x.submodule ≤ LinearMap.ker H.rep) (hJ : x.submodule ≤ LinearMap.ker J.rep) :
    pencilTheta S x c H J ≤ mass (radialWeight S x c) (lines x H) := by
  unfold pencilTheta
  split_ifs with he
  · exact mass_nonneg _ _
  · rw [←radialWeight_intersection S x c H J hH hJ]
    exact mass_mono _ inter_subset_left

theorem actual_projective_second_moment
    (j : ℕ) (hdim : Module.finrank K V ≤ j+1)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B C : ℝ) (hf : f ≤ 1/4) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (R : ℕ) (own : A → Fin R → Bool) (hL : 1 ≤ (L:ℝ)) (hR : 200 ≤ R)
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 1)
    (hsq : (∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ C*B*Real.exp ((L:ℝ)/100))
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ C*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap S x c H J →
      ∃ i∈T,a i ≤ overlap S x c H J ∧ overlap S x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs S x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hd : C*2^R ≤ Real.exp ((L:ℝ)*R/20))
    (hp : (2*(L:ℝ)^2)^R ≤ Real.exp ((L:ℝ)*R/25))
    (hb : C^2*Real.exp ((L:ℝ)/50)+(T.card:ℝ)*2^R*Real.exp ((L:ℝ)*R/50) ≤ Real.exp ((L:ℝ)*R/20))
    (h2 : 2 ≤ Real.exp ((L:ℝ)*R/20)) :
    (∫ ω,(∑ H : A,scoreTerm (lines x H) (Real.exp (-(L:ℝ)*(1-f))) (own H)
      (fun r d => ω (r,d)))^2 ∂batchMeasure (fun i : Fin R × RadialLine x => L*radialWeight S x c i.2))
      ≤ B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R)) := by
  let lam : A → ℝ := fun H => (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.1.rep)).card
  let θ : A → A → ℝ := fun H J => pencilTheta S x c H J
  have hm (H : A) : mass (radialWeight S x c) (lines x H)=lam H :=
    radialWeight_mass S x c H (hA H H.2)
  have hscaled (D : Finset (RadialLine x)) :
      mass (fun d => L*radialWeight S x c d) D=(L:ℝ)*mass (radialWeight S x c) D := by
    simp only [mass,NNReal.coe_mul,Finset.mul_sum]
  have hs := SharpLogRamsey.SecondMoment.prepared_pencil_second_moment
    (fun d => L*radialWeight S x c d) (fun H : A => lines x H) R own
    (L:ℝ) (1-f) B C lam θ T a hL (by linarith) hB hC hR
    (fun H => by rw [hscaled,hm]) (fun H => hlow H H.2) (fun H => hdelta H H.2)
    (by
      simp only [sq_abs]
      calc
        _ = ∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2 := by
          rw [←Finset.sum_coe_sort A (fun H => ((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2)]
        _ ≤ _ := hsq)
    (by
      rw [Fintype.card_coe]
      exact (Nat.cast_le.mpr (pencil_rank_card j hdim A x hA)).trans (by exact_mod_cast hcard))
    (fun H J => pencilTheta_nonneg S x c H J)
    (fun H J => (pencilTheta_le_mass S x c H J (hA H H.2) (hA J J.2)).trans
      (by rw [hm]; exact hupp H H.2))
    (fun H J hne => by
      rw [hscaled,radialWeight_intersection S x c H J (hA H H.2) (hA J J.2)]
      dsimp [θ,pencilTheta]
      rw [ite_eq_right (fun he => hne (Subtype.ext he))])
    (fun i hi => (ha i hi).le)
    (fun H J hθ => by
      have hne : H.1≠J.1 := by
        intro he
        simp only [θ,pencilTheta,ite_eq_left he] at hθ
        linarith
      simp only [θ,pencilTheta,ite_eq_right hne] at hθ ⊢
      exact hcover H H.2 J J.2 hne hθ)
    (fun i hi => by
      rw [family_all_pairs_card A S x c (a i) (ha i hi)]
      exact hcount i hi)
    hd hp hb h2
  have he := (measurePreserving_uncurry_schedule
    (fun d => L*radialWeight S x c d) R).integral_comp
    (MeasurableEquiv.curry (Fin R) (RadialLine x) ℕ).symm.measurableEmbedding
    (fun ω => (∑ H : A,scoreTerm (lines x H) (Real.exp (-(L:ℝ)*(1-f))) (own H)
      (fun r d => ω (r,d)))^2)
  rw [←he]
  exact hs

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestPointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.PoissonGrouping
open Classical
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma sum_hasLaw (rate : ι → ℝ≥0) (S : Finset ι) :
    HasLaw (fun ω : ι → ℕ => ∑ i ∈ S, ω i) (poissonMeasure (∑ i ∈ S, rate i)) (law rate) := by
  have hi : iIndepFun (fun i (ω : ι → ℕ) => ω i) (law rate) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he (i : ι) : HasLaw (fun ω : ι → ℕ => ω i) (poissonMeasure (rate i)) (law rate) :=
    (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_const, measure_univ, one_smul]
    symm
    apply Measure.ext_of_singleton
    intro n
    rw [poissonMeasure_singleton]
    cases n <;> simp
  | @insert i S hiS ih =>
    have ih' : HasLaw (∑ j ∈ S, fun ω : ι → ℕ => ω j)
        (poissonMeasure (∑ j ∈ S, rate j)) (law rate) := by
      convert ih using 1
      all_goals try with_reducible_and_instances rfl
      ext ω
      simp
    simp only [Finset.sum_insert hiS]
    convert (hi.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) hiS).symm.hasLaw_add_poissonMeasure
        (he i) ih' using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp

lemma regroup_hasLaw (rate : ι → ℝ≥0) (g : ι → κ) :
    HasLaw (regroup g) (Measure.pi fun k => law (fun i : {i // g i = k} => rate i)) (law rate) := by
  refine ⟨by exact (measurable_of_countable _).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
  have hpre : regroup g ⁻¹' {z} = {fun i => z (g i) ⟨i, rfl⟩} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      exact congrFun (congrFun h (g i)) ⟨i, rfl⟩
    · rintro rfl
      funext k i
      obtain ⟨i, rfl⟩ := i
      rfl
  rw [hpre]
  simp only [law, Measure.pi_singleton]
  have hf := Fintype.prod_fiberwise g (fun i => (poissonMeasure (rate i)) {z (g i) ⟨i, rfl⟩})
  convert hf.symm using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨i, rfl⟩ := i
  rfl

theorem groupedCount_hasLaw (rate : ι → ℝ≥0) (g : ι → κ) :
    HasLaw (groupedCount g)
      (law (fun k => ∑ i : {i // g i = k}, rate i)) (law rate) := by
  have hs (k : κ) : HasLaw (fun ω : {i // g i = k} → ℕ => ∑ i, ω i)
      (poissonMeasure (∑ i : {i // g i = k}, rate i))
      (law (fun i : {i // g i = k} => rate i)) := sum_hasLaw _ Finset.univ
  have hp := measurePreserving_pi _ _ (fun k => (hs k).measurePreserving (by fun_prop))
  exact hp.hasLaw.comp (regroup_hasLaw rate g)

end
end SharpLogRamsey.PoissonGrouping

namespace SharpLogRamsey.PoissonGrouping
open Finset MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
lemma groupedCount_eq_zero (g : ι → κ) (ω : ι → ℕ) (k : κ) :
    groupedCount g ω k=0 ↔ ∀ i,g i=k → ω i=0 := by
  simp only [groupedCount,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies]
  exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.2⟩

theorem grouped_moment (rate : ι → ℝ≥0) (g : ι → κ) (f : (κ → ℕ) → ℝ) (p : ℕ) :
    (∫ ω,f (groupedCount g ω)^p ∂law rate) =
      ∫ ω,f ω^p ∂law (fun k => ∑ i : {i // g i=k},rate i) := by
  exact (groupedCount_hasLaw rate g).integral_comp
    (measurable_of_countable (fun ω => f ω^p)).aestronglyMeasurable

end
end SharpLogRamsey.PoissonGrouping

namespace SharpLogRamsey.PointScore
open Finset MeasureTheory ProbabilityTheory
open SharpRamseyFive.PoissonScore SharpLogRamsey.PoissonGrouping
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D H : Type*} [Fintype A] [Fintype D] [Fintype H]

omit [Fintype D] [Fintype H] in
lemma grouped_empty {R : ℕ} (own center : A → Prop) (g : {y // ¬(own y ∨ center y)} → D)
    (T : Finset D) (a : {i : Fin R × A // ¬held own center i} → ℕ) (r : Fin R) :
    (∀ d∈T,groupedCount (outsideGroup own center g) a (r,d)=0) ↔
      ∀ y : {y // ¬(own y ∨ center y)},g y∈T → a ⟨(r,y),y.2⟩=0 := by
  classical
  simp only [PoissonGrouping.groupedCount_eq_zero]
  constructor
  · intro hh y hy
    exact hh (g y) hy ⟨(r,y),y.2⟩ rfl
  · intro hh d hd i hi
    have hr : i.1.1=r := congrArg Prod.fst hi
    have hg : g ⟨i.1.2,i.2⟩=d := congrArg Prod.snd hi
    have hh' := hh ⟨i.1.2,i.2⟩ (hg ▸ hd)
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg a
    apply Subtype.ext
    exact Prod.ext hr rfl

omit [Fintype D] in
lemma source_score_eq_grouped {R : ℕ} (own center : A → Prop) (inc : H → A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (lines : H → Finset D)
    (hinc : ∀ h y,inc h y.1 ↔ g y∈lines h) (b : ℝ) (ω : Fin R × A → ℕ)
    (hcenter : ∀ r y,center y → ω (r,y)=0) :
    pointScore own inc b ω =
      ∑ h,scoreTerm (lines h) b (ownBit own center inc (fun i => ω i.1) h)
        (fun r d => groupedCount (outsideGroup own center g) (fun i => ω i.1) (r,d)) := by
  classical
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  have ho : pointEmpty (fun y => own y ∧ inc h y) ω r =
      if ownBit own center inc (fun i => ω i.1) h r then (1:ℝ) else 0 := by
    simp only [pointEmpty,ownBit]
    congr 1
    exact propext (by aesop)
  have he : (∀ y,¬own y ∧ inc h y → ω (r,y)=0) ↔
      ∀ d∈lines h,groupedCount (outsideGroup own center g) (fun i => ω i.1) (r,d)=0 := by
    rw [grouped_empty]
    constructor
    · intro hh y hy
      exact hh y ⟨fun ho => y.2 (Or.inl ho),(hinc h y).mpr hy⟩
    · intro hh y hy
      by_cases hc : center y
      · exact hcenter r y hc
      · have hn : ¬(own y ∨ center y) := by tauto
        exact hh ⟨y,hn⟩ ((hinc h ⟨y,hn⟩).mp hy.2)
  have hx : pointEmpty (fun y => ¬own y ∧ inc h y) ω r =
      emptyIndicator (lines h) (fun d => groupedCount (outsideGroup own center g) (fun i => ω i.1) (r,d)) := by
    simp only [pointEmpty,emptyIndicator,emptyEvent,Set.indicator_apply,Set.mem_pi,
      Finset.mem_coe,Set.mem_singleton_iff,he]
  change _ = if ownBit own center inc (fun i => ω i.1) h r then _ else 0
  rw [ho,hx]
  unfold centeredFactor
  split_ifs <;> simp

end
end SharpLogRamsey.PointScore

open MeasureTheory
open scoped BigOperators Classical
namespace SharpLogRamsey.BoundedProbability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem mass_above_half (Y : Ω → ℝ) (hY : Integrable Y μ)
    (m a : ℝ) (hm : 0  <  m) (ha : 0  ≤  a)
    (hupper : ∀ ω,Y ω ≤ m) (hlower : m*a ≤ ∫ ω,Y ω ∂μ)
    (hE : MeasurableSet {ω | m*a/2 ≤ Y ω}) :
    a/2  ≤  μ.real {ω | m*a/2 ≤ Y ω} := by
  let E := {ω | m*a/2 ≤ Y ω}
  have hi : Integrable (E.indicator (fun _ : Ω =>  m)) μ := (integrable_const _).indicator hE
  have hp : ∀ ω,Y ω  ≤  m*a/2+E.indicator (fun _ : Ω =>  m) ω := by
    intro ω
    by_cases he : ω∈E
    · rw [Set.indicator_of_mem he]
      nlinarith [hupper ω]
    · rw [Set.indicator_of_notMem he]
      exact le_trans (le_of_lt (not_le.mp he)) (by simp)
  have hh := integral_mono hY ((integrable_const _).add hi) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hi,integral_const,
    integral_indicator_const _ hE] at hh
  simp only [probReal_univ,smul_eq_mul] at hh
  apply (le_of_mul_le_mul_left ?_ hm)
  nlinarith

theorem real_markov (Y : Ω → ℝ) (hY : Integrable Y μ) (hy : ∀ ω,0 ≤ Y ω)
    (t : ℝ) (_ht : 0  ≤  t) (hE : MeasurableSet {ω | t ≤ Y ω}) :
    t*μ.real {ω | t ≤ Y ω}  ≤  ∫ ω,Y ω ∂μ := by
  have hi := (integrable_const t).indicator hE (μ:=μ)
  have hp : ∀ ω,({ω | t ≤ Y ω}.indicator (fun _ : Ω =>  t)) ω  ≤  Y ω := by
    intro ω
    by_cases he : t ≤ Y ω
    · simp [he]
    · simpa [he] using hy ω
  have hh := integral_mono hi hY hp
  rw [integral_indicator_const _ hE] at hh
  simpa only [smul_eq_mul,mul_comm] using hh

lemma good_minus_bad (E B : Set Ω) : μ.real E-μ.real B  ≤  μ.real (E\B) := by
  have hh : μ.real E  ≤  μ.real (E\B)+μ.real B := by
    apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) (measureReal_union_le _ _)
    intro ω hω
    by_cases hB : ω∈B
    · exact Or.inr hB
    · exact Or.inl ⟨hω,hB⟩
  linarith

end
end SharpLogRamsey.BoundedProbability

namespace SharpLogRamsey.BoundedProbability
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω A B I : Type*} [MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]

theorem product_event_le (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (A×B)) (hE : MeasurableSet E) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ a,ν.real (Prod.mk a ⁻¹' E) ≤ ε) : (μ.prod ν).real E ≤ ε := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mp
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ _a,ENNReal.ofReal ε ∂μ := lintegral_mono (fun a =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mpr (h a))
    _ = _ := by simp

theorem even_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0 < t)
    (hi : Integrable (fun ω => f ω^p) μ)
    (hE : MeasurableSet {ω | t ≤ |f ω|})
    (hm : (∫ ω,f ω^p ∂μ) ≤ M) :
    μ.real {ω | t ≤ |f ω|} ≤ M/t^p := by
  have hh : t^p*μ.real {ω | t ≤ |f ω|} ≤ ∫ ω,f ω^p ∂μ := by
    have hi' := (integrable_const (t^p)).indicator hE (μ:=μ)
    have hpt : ∀ ω,({ω | t ≤ |f ω|}.indicator (fun _ => t^p)) ω ≤ f ω^p := by
      intro ω
      by_cases he : t ≤ |f ω|
      · rw [Set.indicator_of_mem (show ω∈{ω | t ≤ |f ω|} from he),←hp.pow_abs (f ω)]
        exact pow_le_pow_left₀ ht.le he p
      · rw [Set.indicator_of_notMem (show ω∉{ω | t ≤ |f ω|} from he)]
        exact hp.pow_nonneg (f ω)
    have hle := integral_mono hi' hi hpt
    rw [integral_indicator_const _ hE,smul_eq_mul] at hle
    simpa only [mul_comm] using hle
  exact (le_div_iff₀ (pow_pos ht p)).mpr (by simpa only [mul_comm] using hh.trans hm)

omit [MeasurableSpace Ω] in
lemma eventCount_nonneg (S : Finset I) (E : I → Set Ω) (ω : Ω) :
    0 ≤ eventCount S E ω := sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma integrable_eventCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset I) (E : I → Set Ω) (hE : ∀ i∈S,MeasurableSet (E i)) :
    Integrable (eventCount S E) μ := by
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const 1).indicator (hE i hi)

lemma integral_eventCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset I) (E : I → Set Ω) (hE : ∀ i∈S,MeasurableSet (E i)) :
    (∫ ω,eventCount S E ω ∂μ) = ∑ i∈S,μ.real (E i) := by
  unfold eventCount
  rw [integral_finsetSum _ (fun i hi => (integrable_const 1).indicator (hE i hi))]
  apply sum_congr rfl
  intro i hi
  have he : (fun ω : Ω => if ω∈E i then (1:ℝ) else 0) = (E i).indicator (fun _ => 1) := rfl
  rw [he,integral_indicator_const _ (hE i hi)]
  simp

theorem eventCount_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset I) (E : I → Set Ω) (hE : ∀ i∈S,MeasurableSet (E i))
    (ε t : ℝ) (ht : 0 < t) (he : ∀ i∈S,μ.real (E i) ≤ ε) :
    μ.real {ω | t ≤ eventCount S E ω} ≤ (S.card:ℝ)*ε/t := by
  have hi := integrable_eventCount μ S E hE
  have hme : Measurable (eventCount S E) := by
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.indicator (hE i hi)
  have hm := real_markov μ (eventCount S E) hi (eventCount_nonneg S E) t ht.le
    (measurableSet_le measurable_const hme)
  rw [integral_eventCount μ S E hE] at hm
  have hs : (∑ i∈S,μ.real (E i)) ≤ (S.card:ℝ)*ε := by
    calc
      _ ≤ ∑ _i∈S,ε := sum_le_sum he
      _ = _ := by simp
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hm.trans hs)

end
end SharpLogRamsey.BoundedProbability

namespace SharpLogRamsey.PoissonConditioning
open MeasureTheory ProbabilityTheory
open SharpLogRamsey.BoundedProbability
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem own_outside_tail (rate : ι → ℝ≥0) (own : ι → Prop)
    (f : ({i // own i} → ℕ) → ({i // ¬own i} → ℕ) → ℝ)
    (score : (ι → ℕ) → ℝ) (unsampled : (ι → ℕ) → Prop)
    (heq : ∀ ω,unsampled ω → score ω=f (fun i => ω i) (fun i => ω i))
    (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0 < t) (hM : 0 ≤ M)
    (hi : ∀ a,Integrable (fun b => f a b^p)
      (Measure.pi (fun i : {i // ¬own i} => poissonMeasure (rate i))))
    (hm : ∀ a,(∫ b,f a b^p ∂Measure.pi (fun i : {i // ¬own i} => poissonMeasure (rate i))) ≤ M) :
    (Measure.pi (fun i => poissonMeasure (rate i))).real
      {ω | unsampled ω ∧ t ≤ |score ω|} ≤ M/t^p := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℕ) own
  let ν₁ := Measure.pi (fun i : {i // own i} => poissonMeasure (rate i))
  let ν₂ := Measure.pi (fun i : {i // ¬own i} => poissonMeasure (rate i))
  let E : Set (({i // own i} → ℕ) × ({i // ¬own i} → ℕ)) := {ab | t ≤ |f ab.1 ab.2|}
  have hE : MeasurableSet E := Set.to_countable _ |>.measurableSet
  have hp' := measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) own
  have hh : (ν₁.prod ν₂).real E ≤ M/t^p := by
    apply product_event_le ν₁ ν₂ E hE (M/t^p) (by positivity)
    intro a
    exact even_moment_tail ν₂ (f a) p hp t M ht (hi a)
      (Set.to_countable _ |>.measurableSet) (hm a)
  have hsub : {ω | unsampled ω ∧ t ≤ |score ω|} ⊆ e ⁻¹' E := by
    intro ω hω
    change t ≤ |f (fun i => ω i) (fun i => ω i)|
    rw [←heq ω hω.1]
    exact hω.2
  apply (measureReal_mono (h₂:=measure_ne_top _ _) hsub).trans
  have he : (Measure.pi (fun i => poissonMeasure (rate i))).real (e ⁻¹' E) =
      (ν₁.prod ν₂).real E := by
    unfold Measure.real
    rw [hp'.measure_preimage hE.nullMeasurableSet]
  rw [he]
  exact hh

end
end SharpLogRamsey.PoissonConditioning

namespace SharpLogRamsey.PointScore
open Finset MeasureTheory ProbabilityTheory
open SharpRamseyFive.PoissonScore SharpLogRamsey.PoissonGrouping
open SharpLogRamsey.PoissonConditioning
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D H : Type*} [Fintype A] [Fintype D] [Fintype H]

omit [Fintype A] [Fintype D] [Fintype H] in
lemma centeredFactor_abs (T : Finset D) (b : ℝ) (ω : D → ℕ) :
    |centeredFactor T b ω|≤1+|b| := by
  unfold centeredFactor emptyIndicator
  rw [Set.indicator_apply]
  split_ifs
  · exact (abs_sub _ _).trans (by simp)
  · simp only [zero_sub,abs_neg]
    linarith [abs_nonneg b]

omit [Fintype A] [Fintype D] in
lemma radial_score_abs {R : ℕ} (lines : H → Finset D) (b : ℝ)
    (own : H → Fin R → Bool) (ω : Fin R × D → ℕ) :
    |∑ h,scoreTerm (lines h) b (own h) (fun r d => ω (r,d))| ≤
      (Fintype.card H:ℝ)*(1+|b|)^R := by
  calc
    _ ≤ ∑ h,|scoreTerm (lines h) b (own h) (fun r d => ω (r,d))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _h : H,(1+|b|)^R := by
      apply sum_le_sum
      intro h _
      unfold scoreTerm
      rw [abs_prod]
      calc
        _ ≤ ∏ _r : Fin R,(1+|b|) := by
          apply prod_le_prod (fun _ _ => abs_nonneg _)
          intro r _
          split_ifs
          · exact centeredFactor_abs _ _ _
          · simp only [abs_zero]; positivity
        _ = _ := by simp
    _ = _ := by simp

omit [Fintype A] [Fintype D] in
lemma integrable_radial_power {R : ℕ} (lines : H → Finset D) (b : ℝ)
    (own : H → Fin R → Bool) (p : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    [Countable Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → Fin R × D → ℕ) :
    Integrable (fun ω => (∑ h,scoreTerm (lines h) b (own h) (fun r d => g ω (r,d)))^p) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (((Fintype.card H:ℝ)*(1+|b|)^R)^p)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (radial_score_abs lines b own (g ω)) p

theorem point_score_tail {R : ℕ} (rate : Fin R × A → ℝ≥0)
    (own center : A → Prop) (inc : H → A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (lines : H → Finset D)
    (hinc : ∀ h y,inc h y.1 ↔ g y∈lines h) (b : ℝ)
    (radialRate : Fin R × D → ℝ≥0)
    (hrate : ∀ k,(∑ i : {i : {i : Fin R × A // ¬held own center i} //
      outsideGroup own center g i=k},rate i.1.1)=radialRate k)
    (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0<t) (hM : 0≤M)
    (hm : ∀ bits : H → Fin R → Bool,
      (∫ ω,(∑ h,scoreTerm (lines h) b (bits h) (fun r d => ω (r,d)))^p
        ∂batchMeasure radialRate)≤M) :
    (batchMeasure rate).real {ω | (∀ r y,center y → ω (r,y)=0) ∧
      t≤|pointScore own inc b ω|} ≤ M/t^p := by
  let f := fun (a : {i : Fin R × A // held own center i} → ℕ)
      (c : {i : Fin R × A // ¬held own center i} → ℕ) =>
    ∑ h,scoreTerm (lines h) b (ownBit own center inc a h)
      (fun r d => groupedCount (outsideGroup own center g) c (r,d))
  apply own_outside_tail rate (held own center) f (pointScore own inc b)
    (fun ω => ∀ r y,center y → ω (r,y)=0)
    (fun ω hc => source_score_eq_grouped own center inc g lines hinc b ω hc)
    p hp t M ht hM
  · intro a
    exact integrable_radial_power lines b (ownBit own center inc a) p _
      (groupedCount (outsideGroup own center g))
  · intro a
    have hh := grouped_moment (fun i : {i : Fin R × A // ¬held own center i} => rate i.1)
      (outsideGroup own center g)
      (fun ω => ∑ h,scoreTerm (lines h) b (ownBit own center inc a h) (fun r d => ω (r,d))) p
    change (∫ c,(f a c)^p ∂law (fun i : {i : Fin R × A // ¬held own center i} => rate i.1))≤M
    apply hh.le.trans
    convert! hm (ownBit own center inc a) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    funext k
    convert! hrate k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext i
    simp only [mem_univ]

end
end SharpLogRamsey.PointScore

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma direction_mem_lines (x : Projectivization K V)
    (y : {y : Projectivization K V // y≠x}) (H : Projectivization K (Module.Dual K V))
    (hx : x.submodule ≤ LinearMap.ker H.rep) :
    direction x y∈lines x H ↔ y.1.submodule ≤ LinearMap.ker H.rep := by
  rw [mem_lines]
  change x.submodule ⊔ y.1.submodule ≤ LinearMap.ker H.rep ↔ _
  simp only [sup_le_iff,hx,true_and]

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PointScore
open Finset
open SharpLogRamsey.PoissonGrouping
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D : Type*} [Fintype A] [Fintype D]

omit [Fintype D] in
lemma outside_uniform_rate {R : ℕ} (own center : A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (u : ℝ≥0) (k : Fin R × D) :
    (∑ _i : {i : {i : Fin R × A // ¬held own center i} // outsideGroup own center g i=k},u)=
      u*Fintype.card {y : {y // ¬(own y ∨ center y)} // g y=k.2} := by
  simp only [sum_const,card_univ,nsmul_eq_mul]
  rw [Fintype.card_congr (outsideBatchFiber own center g k.1 k.2)]
  exact mul_comm _ _

end
end SharpLogRamsey.PointScore

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in
lemma outsideDirection_card (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) :
    Fintype.card {y : {y : S // ¬(y.1∈O ∨ y.1=x)} // outsideDirection S O x y=W}=
      (radialFiber (S\(O∪{x})) x W).card :=
  (Fintype.card_congr (outsideDirectionFiber S O x W)).trans (Fintype.card_coe _)

lemma outsideDirection_incidence (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (hxH : x.submodule≤LinearMap.ker H.rep)
    (y : {y : S // ¬(y.1∈O ∨ y.1=x)}) :
    y.1.1.submodule≤LinearMap.ker H.rep ↔ outsideDirection S O x y∈lines x H :=
  by
    exact (direction_mem_lines x ⟨y.1.1,fun h => y.2 (Or.inr h)⟩ H hxH).symm

omit [Finite K] in
theorem actual_radial_rate (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    {R : ℕ} (L c : ℝ≥0) (k : Fin R × RadialLine x) :
    (∑ _i : {i : {i : Fin R × S // ¬held (fun y : S => y.1∈O) (fun y : S => y.1=x) i} //
      outsideGroup (fun y : S => y.1∈O) (fun y : S => y.1=x) (outsideDirection S O x) i=k},L*c)=
      L*(c*(radialFiber (S\(O∪{x})) x k.2).card) := by
  rw [outside_uniform_rate,mul_assoc]
  congr 2
  have hc := outsideDirection_card S O x k.2
  simp only [←Nat.card_eq_fintype_card] at hc ⊢
  exact_mod_cast hc

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TestProjectiveTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem projective_point_tail
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (R : ℕ) (b : ℝ) (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0<t) (hM : 0≤M)
    (hm : ∀ bits : A → Fin R → Bool,
      (∫ ω,(∑ H : A,scoreTerm (lines x H) b (bits H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R × RadialLine x => L*radialWeight (S\(O∪{x})) x c i.2))≤M) :
    (batchMeasure (fun _ : Fin R × S => L*c)).real
      {ω | (∀ r (y : S),y.1=x → ω (r,y)=0) ∧
        t ≤ |pointScore (fun y : S => y.1∈O)
          (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep) b ω|}
      ≤ M/t^p := by
  apply point_score_tail (fun _ : Fin R × S => L*c)
    (fun y : S => y.1∈O) (fun y : S => y.1=x)
    (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep)
    (outsideDirection S O x) (fun H : A => lines x H)
    (fun H y => outsideDirection_incidence S O x H (hA H H.2) y) b
    (fun k => L*radialWeight (S\(O∪{x})) x c k.2) _ p hp t M ht hM hm
  intro k
  exact actual_radial_rate S O x L c k

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TestPointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem actual_point_high_tail
    (j : ℕ) (hj : 2 ≤ j) (hj3 : j ≤ 3) (hdim : Module.finrank K V ≤ j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B : ℝ) (hf : f ≤ 1/25) {p : ℕ} (hp : 0<p) (hpe : Even p) (R : ℕ)
    (hL : 10000 ≤ (L:ℝ))
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 13/100)
    (hB : Real.exp (3*((L:ℝ)*R)) ≤ B)
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ 4*B^2)
    (hdir : ((∑ i∈range (j-1),Nat.card K^i):ℝ) ≤ 4*B)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
      ∃ i∈T,a i ≤ overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hrow : ∀ H∈A,∀ i∈T,((largeNeighbors (S\(O∪{x})) x c (a i) A H).card:ℝ)*a i^200 ≤ B*Real.exp (((L:ℝ)*R)/50))
    (hstrong : ∀ H∈A,((largeNeighbors (S\(O∪{x})) x c (1/(100*(p:ℝ))) A H).card:ℝ) ≤ B*Real.exp (-3*((L:ℝ)*R)))
    (hsq : (∑ H∈A,((c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ B*Real.exp (((L:ℝ)*R)/100))
    (hpoly : SharpLogRamsey.MomentBudgetBridge.certificateOverhead p T.card ((L:ℝ)*R) ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hshift : SharpLogRamsey.MomentBudgetBridge.shiftOverhead p T.card ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3 ≤ Real.exp (((L:ℝ)*R)/10))
    (h : ℕ) (hh : 0<h) (hR : 400 ≤ R) (hsize : h ≤ (R/2)/400)
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (t : ℝ) (ht : 0<t) :
    (batchMeasure (fun _ : Fin R × S => L*c)).real
      {ω | (∀ r (y : S),y.1=x → ω (r,y)=0) ∧
        t ≤ |pointScore (fun y : S => y.1∈O)
          (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep)
          (Real.exp (-(L:ℝ)*(1-f))) ω|}
      ≤ (B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))))/t^p := by
  have hB0 : 0≤B := (Real.exp_pos _).le.trans hB
  apply projective_point_tail S O x c L A hA R _ p hpe t _ ht (by positivity)
  intro bits
  exact actual_projective_high_moment j hj hj3 hdim (S\(O∪{x})) x c L A hA f B hf hp R bits
    hL hlow hupp hdelta hB hcard hdir T a ha hcover hcount hrow hstrong hsq
    hpoly hshift hp2 hps h hh hR hsize herr

theorem actual_point_second_tail
    (j : ℕ) (hdim : Module.finrank K V ≤ j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B C : ℝ) (hf : f ≤ 1/4) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (R : ℕ) (hL : 1 ≤ (L:ℝ)) (hR : 200 ≤ R)
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 1)
    (hsq : (∑ H∈A,((c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ C*B*Real.exp ((L:ℝ)/100))
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ C*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
      ∃ i∈T,a i ≤ overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hd : C*2^R ≤ Real.exp ((L:ℝ)*R/20))
    (hp : (2*(L:ℝ)^2)^R ≤ Real.exp ((L:ℝ)*R/25))
    (hb : C^2*Real.exp ((L:ℝ)/50)+(T.card:ℝ)*2^R*Real.exp ((L:ℝ)*R/50) ≤ Real.exp ((L:ℝ)*R/20))
    (h2 : 2 ≤ Real.exp ((L:ℝ)*R/20))
    (t : ℝ) (ht : 0<t) :
    (batchMeasure (fun _ : Fin R × S => L*c)).real
      {ω | (∀ r (y : S),y.1=x → ω (r,y)=0) ∧
        t ≤ |pointScore (fun y : S => y.1∈O)
          (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep)
          (Real.exp (-(L:ℝ)*(1-f))) ω|}
      ≤ (B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R)))/t^2 := by
  apply projective_point_tail S O x c L A hA R _ 2 (by decide) t _ ht (by positivity)
  intro bits
  exact actual_projective_second_moment j hdim (S\(O∪{x})) x c L A hA f B C hf hB hC R bits
    hL hR hlow hupp hdelta hsq hcard T a ha hcover hcount hd hp hb h2

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

attribute [local instance] OAI.SharpLogRamsey.ProjectiveDuality.flat_JoinedTestLearningIncidence_1
theorem dual_variance_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ) :
    (∑ x : Projectivization K V,
      ((∑ H, if SharpLogRamsey.Incidence.Incident x H then w H else 0) -
        (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i) * ∑ H, w H)^2) ≤
      (Nat.card K:ℝ)^(n+1) * ∑ H,w H^2 := by
  have hh := projective_variance_le
    (show Module.finrank K (Module.Dual K V)=n+3 from Subspace.dual_finrank_eq.trans hdim) w
  rw [← (bidual (K:=K) (V:=V)).sum_comp] at hh
  simpa only [weightedIncidences,incident_bidual] using hh

end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.PencilContrast
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality
noncomputable section
variable {A B : Type*}

lemma sum_degree (R : A → B → Prop) (S : Finset A) (Z : Finset B) :
    (∑ x∈S,degree R Z x) = ∑ H∈Z,∑ x∈S,if R x H then (1:ℝ) else 0 := by
  exact sum_comm

theorem support_large_degree (R : A → B → Prop) (S : Finset A) (Z : Finset B)
    (q N z a b : ℝ) (hq : 0 < q) (hN : 0 < N) (hz : 0 < z) (hb : 0 < b)
    (hh : (∑ H∈Z,(q/N)*∑ x∈S,if R x H then (1:ℝ) else 0) ≤ a*z) :
    ((S.filter (fun x => b*z/q ≤ degree R Z x)).card:ℝ) ≤ (a/b)*N := by
  have hid : (∑ H∈Z,(q/N)*∑ x∈S,if R x H then (1:ℝ) else 0) =
      (q/N)*∑ x∈S,degree R Z x := by rw [←mul_sum,sum_degree]
  rw [hid] at hh
  have hsum : (∑ x∈S,degree R Z x) ≤ a*z*N/q := by
    apply (le_div_iff₀ hq).mpr
    have ht := (div_le_iff₀ hN).mp (show q*(∑ x∈S,degree R Z x)/N ≤ a*z from by
      simpa only [div_mul_eq_mul_div] using hh)
    nlinarith
  have hmark : ((S.filter (fun x => b*z/q ≤ degree R Z x)).card:ℝ)*(b*z/q) ≤
      ∑ x∈S,degree R Z x := by
    calc
      _ = ∑ x∈S.filter (fun x => b*z/q ≤ degree R Z x),b*z/q := by simp
      _ ≤ ∑ x∈S.filter (fun x => b*z/q ≤ degree R Z x),degree R Z x :=
        sum_le_sum (fun _ hx => (mem_filter.mp hx).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun x _ _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  have hfin := hmark.trans hsum
  apply (le_of_mul_le_mul_right ?_ (show 0 < b*z/q by positivity))
  calc
    _ ≤ a*z*N/q := hfin
    _ = ((a/b)*N)*(b*z/q) := by field_simp

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem ambient_small_degree {n : ℕ} (hdim : Module.finrank K V=n+3)
    (Z : Finset (Projectivization K (Module.Dual K V))) (hZ : Z.Nonempty)
    (hQ : (10:ℝ) ≤ ∑ i∈range (n+3),(Nat.card K:ℝ)^i) :
    ((univ.filter (fun x : Projectivization K V =>
      degree SharpLogRamsey.Incidence.Incident Z x < (4/5:ℝ)*(Z.card:ℝ)/(Nat.card K:ℝ))).card:ℝ) ≤
        100*(Nat.card K:ℝ)^(n+3)/(Z.card:ℝ) := by
  let q : ℝ := Nat.card K
  let Q : ℝ := ∑ i∈range (n+3),q^i
  let u : ℝ := ∑ i∈range (n+2),q^i
  let z : ℝ := Z.card
  let μ : ℝ := u/Q*z
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hz : 0 < z := by dsimp [z]; exact_mod_cast card_pos.mpr hZ
  have hQ0 : 0 < Q := by dsimp [Q,q]; linarith
  have hgeom : Q=q*u+1 := by dsimp [Q,u]; rw [geom_sum_succ]
  have hmean : (9/10:ℝ)*z/q ≤ μ := by
    apply (div_le_iff₀ hq).mpr
    change (9/10:ℝ)*z ≤ u/Q*z*q
    rw [show u/Q*z*q=(u*z*q)/Q by ring,le_div_iff₀ hQ0]
    change (10:ℝ) ≤ Q at hQ
    have hh : 9*Q ≤ 10*(Q-1) := by linarith
    have ht := mul_le_mul_of_nonneg_right hh hz.le
    have hgz := congrArg (fun a : ℝ => a*z) hgeom
    nlinarith
  let w : Projectivization K (Module.Dual K V) → ℝ := fun H => if H∈Z then 1 else 0
  have hs : ∑ H,w H = z := by dsimp [w,z]; rw [←sum_filter]; simp
  have hs2 : ∑ H,w H^2 = z := by
    have hi : ∀ H,w H^2=w H := by intro H; dsimp [w]; split_ifs <;> norm_num
    simp_rw [hi]; exact hs
  have hdeg (x : Projectivization K V) :
      (∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0)=degree SharpLogRamsey.Incidence.Incident Z x := by
    dsimp [w,degree]
    calc
      _ = ∑ H,if H∈Z then (if SharpLogRamsey.Incidence.Incident x H then (1:ℝ) else 0) else 0 := by
        apply sum_congr rfl
        intro H _
        split_ifs <;> rfl
      _ = _ := by rw [←sum_filter]; simp
  have hv := dual_variance_le hdim w
  simp_rw [hdeg,hs,hs2] at hv
  change (∑ x,(degree SharpLogRamsey.Incidence.Incident Z x-μ)^2) ≤ q^(n+1)*z at hv
  let E := univ.filter (fun x : Projectivization K V => degree SharpLogRamsey.Incidence.Incident Z x<(4/5:ℝ)*z/q)
  have he : (E.card:ℝ)*(z/(10*q))^2 ≤ q^(n+1)*z := by
    calc
      _ = ∑ _x∈E,(z/(10*q))^2 := by simp
      _ ≤ ∑ x∈E,(degree SharpLogRamsey.Incidence.Incident Z x-μ)^2 := by
        apply sum_le_sum
        intro x hx
        have hh := (mem_filter.mp hx).2
        have hgap : z/(10*q) ≤ μ-degree SharpLogRamsey.Incidence.Incident Z x := by
          have hi : (9/10:ℝ)*z/q-(4/5:ℝ)*z/q=z/(10*q) := by ring
          linarith
        nlinarith [show 0 ≤ z/(10*q) by positivity]
      _ ≤ ∑ x,(degree SharpLogRamsey.Incidence.Incident Z x-μ)^2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hv
  change (E.card:ℝ) ≤ 100*q^(n+3)/z
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos (show 0 < z/(10*q) by positivity)))
  calc
    _ ≤ q^(n+1)*z := he
    _ = (100*q^(n+3)/z)*(z/(10*q))^2 := by
      rw [show n+3=(n+1)+2 by omega,pow_add]
      field_simp
      ring

end
end SharpLogRamsey.PencilContrast

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningRowBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace SharpLogRamsey.PoissonSchedules
variable {ι : Type*} [Fintype ι]

theorem measurable_emptyLedger (A : Finset ι) : MeasurableSet (emptyLedger A) := by
  exact (Set.to_countable (emptyLedger A)).measurableSet

theorem poisson_zero_real (r : ℝ≥0) : (poissonMeasure r).real {0} = Real.exp (-r) := by
  simpa using poissonMeasure_real_singleton r 0

theorem emptyLedger_probability (r : ι → ℝ≥0) (A : Finset ι) :
    (scheduleLaw r).real (emptyLedger A) = Real.exp (-(∑ i ∈ A, (r i : ℝ))) := by
  have he : emptyLedger A = (A : Set ι).pi (fun _ => ({0} : Set ℕ)) := by
    ext x; simp [emptyLedger,Set.mem_pi]
  rw [he,measureReal_def,scheduleLaw,Measure.pi_pi_finset,ENNReal.toReal_prod]
  calc
    _ = ∏ i ∈ A, Real.exp (-(r i : ℝ)) := prod_congr rfl (fun i hi => poisson_zero_real (r i))
    _ = _ := by rw [← Real.exp_sum,sum_neg_distrib]

end SharpLogRamsey.PoissonSchedules
namespace SharpLogRamsey.EmptyExceptional
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical NNReal
open SharpLogRamsey.PoissonSchedules SharpLogRamsey.BoundedProbability
noncomputable section
variable {ι H : Type*}

lemma emptySum_nonneg (E : Finset H) (D : H → Finset ι) (w : H → ℝ)
    (hw : ∀ h∈E,0 ≤ w h) (ω : ι → ℕ) : 0 ≤ emptySum E D w ω := by
  apply sum_nonneg
  intro h hh
  split_ifs
  · exact hw h hh
  · rfl

lemma emptySum_le_sum (E : Finset H) (D : H → Finset ι) (w : H → ℝ)
    (hw : ∀ h∈E,0 ≤ w h) (ω : ι → ℕ) : emptySum E D w ω  ≤  ∑ h∈E,w h := by
  apply sum_le_sum
  intro h hh
  split_ifs
  · rfl
  · exact hw h hh

variable [Fintype ι]

lemma integrable_emptySum (r : ι → ℝ≥0) (E : Finset H) (D : H → Finset ι) (w : H → ℝ) :
    Integrable (emptySum E D w) (scheduleLaw r) := by
  apply integrable_finsetSum
  intro h _
  exact (integrable_const (w h)).indicator (measurable_emptyLedger (D h))

lemma integral_emptySum (r : ι → ℝ≥0) (E : Finset H) (D : H → Finset ι) (w : H → ℝ) :
    (∫ ω,emptySum E D w ω ∂scheduleLaw r) =
      ∑ h∈E,w h*Real.exp (-(∑ i∈D h,(r i:ℝ))) := by
  simp only [emptySum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro h _
    change (∫ ω,(emptyLedger (D h)).indicator (fun _ =>  w h) ω ∂scheduleLaw r) = _
    rw [integral_indicator_const _ (measurable_emptyLedger _),smul_eq_mul,emptyLedger_probability]
    ring
  · intro h _
    exact (integrable_const (w h)).indicator (measurable_emptyLedger (D h))

theorem many_empty (r : ι → ℝ≥0) (E : Finset H) (hE : E.Nonempty)
    (D : H → Finset ι) (b : ℝ) (hb : ∀ h∈E,∑ i∈D h,(r i:ℝ) ≤ b) :
    Real.exp (-b)/2  ≤  (scheduleLaw r).real {ω |
      (E.card:ℝ)*Real.exp (-b)/2 ≤ emptySum E D (fun _ =>  1) ω} := by
  apply mass_above_half _ _ (integrable_emptySum r E D _) _ _
  · exact_mod_cast card_pos.mpr hE
  · exact (Real.exp_pos _).le
  · intro ω
    simpa using emptySum_le_sum E D (fun _ =>  1) (by intros; norm_num) ω
  · rw [integral_emptySum]
    calc
      _ = ∑ _h∈E,Real.exp (-b) := by simp
      _  ≤  _ := sum_le_sum (fun h hh =>  by simp only [one_mul]; exact Real.exp_le_exp.mpr (neg_le_neg (hb h hh)))
  · exact (Set.to_countable _).measurableSet

theorem heavy_empty_expectation (r : ι → ℝ≥0) (E : Finset H)
    (D : H → Finset ι) (l : H → ℝ) (P δ W : ℝ) (hP : 0 ≤ P)
    (hl : ∀ h∈E,0 ≤ l h) (hmass : ∀ h∈E,∑ i∈D h,(r i:ℝ)=P*l h)
    (hW : ∑ h∈E,l h ≤ W) :
    (∫ ω,emptySum (E.filter (fun h =>  δ ≤ l h)) D l ω ∂scheduleLaw r)  ≤
      W*Real.exp (-P*δ) := by
  rw [integral_emptySum]
  calc
    _  ≤  ∑ h∈E.filter (fun h =>  δ ≤ l h),l h*Real.exp (-P*δ) := by
      apply sum_le_sum
      intro h hh
      have hh' := mem_filter.mp hh
      apply mul_le_mul_of_nonneg_left _ (hl h hh'.1)
      apply Real.exp_le_exp.mpr
      rw [hmass h hh'.1]
      nlinarith [mul_le_mul_of_nonneg_left hh'.2 hP]
    _  ≤  ∑ h∈E,l h*Real.exp (-P*δ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun h hh _ =>
        mul_nonneg (hl h hh) (Real.exp_pos _).le)
    _  ≤  _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le

omit [Fintype ι] in

lemma empty_weight_split (E : Finset H) (D : H → Finset ι) (l : H → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (ω : ι → ℕ) :
    emptySum E D l ω  ≤  δ*emptySum E D (fun _ =>  1) ω+
      emptySum (E.filter (fun h =>  δ ≤ l h)) D l ω := by
  simp only [emptySum,sum_filter]
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro h _
  by_cases he : ω∈emptyLedger (D h)  <;>  by_cases hh : δ ≤ l h  <;>  simp [he,hh]
  · exact hδ
  · exact (lt_of_not_ge hh).le

end
end SharpLogRamsey.EmptyExceptional
namespace SharpLogRamsey.EmptyExceptional
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical NNReal
open SharpLogRamsey.PoissonSchedules SharpLogRamsey.BoundedProbability
noncomputable section
variable {ι H : Type*} [Fintype ι]

omit [Fintype ι] in
lemma emptySum_mono (D : H → Finset ι) (w : H → ℝ) {E F : Finset H}
    (hEF : E⊆F) (hw : ∀ h∈F,0 ≤ w h) (ω : ι → ℕ) :
    emptySum E D w ω ≤ emptySum F D w ω := by
  apply sum_le_sum_of_subset_of_nonneg hEF
  intro h hh _
  split_ifs
  · exact hw h hh
  · rfl

theorem empty_good_event (r : ι → ℝ≥0) (E E₀ : Finset H) (hE₀ : E₀.Nonempty)
    (hsub : E₀⊆E) (D : H → Finset ι) (l : H → ℝ) (P b δ u zmin W : ℝ)
    (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hu : 0 < u) (hz : 0 < zmin)
    (hl : ∀ h∈E,0 ≤ l h) (hmass : ∀ h∈E,∑ i∈D h,(r i:ℝ)=P*l h)
    (hb : ∀ h∈E₀,∑ i∈D h,(r i:ℝ) ≤ b)
    (hW : ∑ h∈E,l h ≤ W) (hzmin : zmin ≤ (E₀.card:ℝ)*Real.exp (-b)/2) :
    Real.exp (-b)/2 - W*Real.exp (-P*δ)/(u*zmin) ≤
      (scheduleLaw r).real {ω | zmin ≤ emptySum E D (fun _ => 1) ω ∧
        emptySum E D l ω ≤ (δ+u)*emptySum E D (fun _ => 1) ω} := by
  let Y := emptySum (E.filter (fun h => δ ≤ l h)) D l
  let G := {ω | (E₀.card:ℝ)*Real.exp (-b)/2 ≤ emptySum E₀ D (fun _ => 1) ω}
  let B := {ω | u*zmin ≤ Y ω}
  have hmany : Real.exp (-b)/2 ≤ (scheduleLaw r).real G := many_empty r E₀ hE₀ D b hb
  have hev := heavy_empty_expectation r E D l P δ W hP hl hmass hW
  have hmark := real_markov (scheduleLaw r) Y (integrable_emptySum r _ D l)
    (emptySum_nonneg _ D l (fun h hh => hl h (mem_filter.mp hh).1))
    (u*zmin) (mul_pos hu hz).le (Set.to_countable _).measurableSet
  have hbad : (scheduleLaw r).real B ≤ W*Real.exp (-P*δ)/(u*zmin) := by
    apply (le_div_iff₀ (mul_pos hu hz)).mpr
    simpa only [mul_comm] using hmark.trans hev
  have hcover : G\B ⊆ {ω | zmin ≤ emptySum E D (fun _ => 1) ω ∧
        emptySum E D l ω ≤ (δ+u)*emptySum E D (fun _ => 1) ω} := by
    intro ω hh
    have hn : Y ω < u*zmin := lt_of_not_ge hh.2
    have hc := emptySum_mono D (fun _ => (1:ℝ)) hsub (fun _ _ => by norm_num) ω
    have hsmall : zmin ≤ emptySum E D (fun _ => 1) ω := hzmin.trans (hh.1.trans hc)
    refine ⟨hsmall,?_⟩
    have hs := empty_weight_split E D l δ hδ ω
    have hh' := mul_le_mul_of_nonneg_left hsmall hu.le
    change emptySum E D l ω ≤ δ*emptySum E D (fun _ => 1) ω+Y ω at hs
    nlinarith
  have hdiff := good_minus_bad (scheduleLaw r) G B
  have hmono := measureReal_mono (h₂:=measure_ne_top (scheduleLaw r) _) hcover
  linarith

end
end SharpLogRamsey.EmptyExceptional
namespace SharpLogRamsey.LearningRow
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A : Type*} [Fintype A]

lemma capture_score (A T Z α z q : ℝ) (hq : 0<q) (hz : 0<z)
    (hZ : 0≤Z) (hZ1 : Z≤z/(10*q)) (_ha : 0≤α) (ha1 : α≤1)
    (he : |(A-T)-α*Z| ≤ z/(100*q)) (ht : |T|≤z/(10*q)) :
    A<z/(2*q) := by
  obtain ⟨_,he⟩ := abs_le.mp he
  obtain ⟨_,ht⟩ := abs_le.mp ht
  have ham : α*Z≤Z := by nlinarith
  have hh : 0<z/q := div_pos hz hq
  have hi : z/(100*q)= (z/q)/100 := by ring
  have hi1 : z/(10*q)= (z/q)/10 := by ring
  have hi2 : z/(2*q)= (z/q)/2 := by ring
  rw [hi] at he
  rw [hi1] at hZ1 ht
  rw [hi2]
  linarith

lemma exclude_score (A T Z α z q : ℝ) (hq : 0<q) (hz : 0<z)
    (hZ : (4/5)*z/q≤Z) (ha : 9/10≤α)
    (he : |(A-T)-α*Z| ≤ z/(100*q)) (ht : |T|≤z/(10*q)) :
    z/(2*q)<A := by
  obtain ⟨he,_⟩ := abs_le.mp he
  obtain ⟨ht,_⟩ := abs_le.mp ht
  have hh : 0<z/q := div_pos hz hq
  rw [mul_div_assoc] at hZ
  have hZ0 : 0≤Z := by nlinarith
  have ham : (9/10)*Z≤α*Z := mul_le_mul_of_nonneg_right ha hZ0
  have hi : z/(100*q)= (z/q)/100 := by ring
  have hi1 : z/(10*q)= (z/q)/10 := by ring
  have hi2 : z/(2*q)= (z/q)/2 := by ring
  rw [hi] at he
  rw [hi1] at ht
  rw [hi2]
  nlinarith

theorem capture_count (S sample D F E : Finset A) (score : A → ℝ) (z q : ℝ)
    (h : ∀ x∈S,x∉D → x∉F → x∉E → x∉sample → score x<z/(2*q)) :
    S.card ≤ (S∩test sample score z q).card+D.card+F.card+E.card := by
  have hs : S ⊆ ((S∩test sample score z q)∪D)∪F∪E := by
    intro x hx
    by_cases hd : x∈D
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hd))
    by_cases hf : x∈F
    · exact mem_union_left _ (mem_union_right _ hf)
    by_cases he : x∈E
    · exact mem_union_right _ he
    apply mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx,?_⟩)))
    simp only [test,mem_filter,mem_univ,true_and]
    by_cases hp : x∈sample
    · exact Or.inl hp
    · exact Or.inr (h x hx hd hf he hp)
  calc
    _ ≤ (((S∩test sample score z q)∪D)∪F∪E).card := card_le_card hs
    _ ≤ _ := by
      have h1 := card_union_le (S∩test sample score z q) D
      have h2 := card_union_le ((S∩test sample score z q)∪D) F
      have h3 := card_union_le (((S∩test sample score z q)∪D)∪F) E
      omega

theorem ambient_count (sample D F E : Finset A) (score : A → ℝ) (z q : ℝ)
    (h : ∀ x,x∉D → x∉F → x∉E → x∉sample → z/(2*q)≤ score x) :
    (test sample score z q).card ≤ sample.card+D.card+F.card+E.card := by
  have hs : test sample score z q ⊆ sample∪D∪F∪E := by
    intro x hx
    by_cases hd : x∈D
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hd))
    by_cases hf : x∈F
    · exact mem_union_left _ (mem_union_right _ hf)
    by_cases he : x∈E
    · exact mem_union_right _ he
    apply mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
    by_contra hp
    have ht := (mem_filter.mp hx).2.resolve_left hp
    exact (not_lt.mpr (h x hd hf he hp)) ht
  calc
    _ ≤ (sample∪D∪F∪E).card := card_le_card hs
    _ ≤ _ := by
      have h1 := card_union_le sample D
      have h2 := card_union_le (sample∪D) F
      have h3 := card_union_le (sample∪D∪F) E
      omega

end
end SharpLogRamsey.LearningRow

namespace SharpLogRamsey.LearningRow
open MeasureTheory Finset
open SharpLogRamsey.BoundedProbability
open scoped Classical BigOperators
noncomputable section
variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]

omit [MeasurableSpace Ω] [Fintype A] in
lemma eventCount_eq_card (S : Finset A) (E : A → Set Ω) (ω : Ω) :
    eventCount S E ω=(failures S E ω).card := by
  simp only [eventCount,failures,←sum_filter]
  simp

theorem row_success_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S Ds Da : Finset A) (sample : Ω → Finset A) (score typ zx : Ω → A → ℝ)
    (z : Ω → ℝ) (α : A → ℝ) (q tS tA eS eA M εS εA εM ρ : ℝ)
    (E : Set Ω) (FS FA : A → Set Ω)
    (hFS : ∀ x∈S,MeasurableSet (FS x)) (hFA : ∀ x,MeasurableSet (FA x))
    (hq : 0<q) (htS : 0<tS) (htA : 0<tA)
    (hE : ρ≤μ.real E)
    (hfS : ∀ x∈S,μ.real (FS x)≤εS) (hfA : ∀ x,μ.real (FA x)≤εA)
    (hM : μ.real {ω | M<(sample ω).card}≤εM)
    (hz : ∀ ω∈E,0<z ω) (hzx : ∀ ω∈E,∀ x,0≤zx ω x)
    (ha : ∀ x,9/10≤α x ∧ α x≤1)
    (herrors : ∀ ω∈E,∀ x,x∉Ds → x∉sample ω →
      |(score ω x-typ ω x)-α x*zx ω x|≤z ω/(100*q))
    (hs : ∀ ω∈E,∀ x∈S,x∉Ds → x∉sample ω → ω∉FS x → |typ ω x|≤z ω/(10*q))
    (hda : Ds⊆Da)
    (ht : ∀ ω∈E,∀ x,x∉Da → x∉sample ω → ω∉FA x → |typ ω x|≤z ω/(10*q))
    (hes : ∀ ω∈E,((S.filter (fun x => z ω/(10*q)<zx ω x)).card:ℝ)≤eS)
    (hea : ∀ ω∈E,((univ.filter (fun x => zx ω x<(4/5)*z ω/q)).card:ℝ)≤eA) :
    ρ-(S.card:ℝ)*εS/tS-(Fintype.card A:ℝ)*εA/tA-εM ≤
      μ.real {ω | (sample ω).card≤M ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-eS≤(S∩test (sample ω) (score ω) (z ω) q).card ∧
        ((test (sample ω) (score ω) (z ω) q).card:ℝ)≤M+(Da.card:ℝ)+tA+eA} := by
  let BS : Set Ω := {ω | tS≤eventCount S FS ω}
  let BA : Set Ω := {ω | tA≤eventCount univ FA ω}
  let BM : Set Ω := {ω | M<(sample ω).card}
  have hbs : μ.real BS≤(S.card:ℝ)*εS/tS := eventCount_tail μ S FS hFS εS tS htS hfS
  have hba : μ.real BA≤(Fintype.card A:ℝ)*εA/tA := by
    simpa using eventCount_tail μ univ FA (fun x _ => hFA x) εA tA htA (fun x _ => hfA x)
  have hb : μ.real (BS∪BA∪BM)≤(S.card:ℝ)*εS/tS+(Fintype.card A:ℝ)*εA/tA+εM := by
    have h1 := measureReal_union_le (μ:=μ) BS BA
    have h2 := measureReal_union_le (μ:=μ) (BS∪BA) BM
    linarith
  have hc : E\(BS∪BA∪BM) ⊆ {ω | (sample ω).card≤M ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-eS≤(S∩test (sample ω) (score ω) (z ω) q).card ∧
        ((test (sample ω) (score ω) (z ω) q).card:ℝ)≤M+(Da.card:ℝ)+tA+eA} := by
    intro ω hω
    have hnS : ω∉BS := fun h => hω.2 (Or.inl (Or.inl h))
    have hnA : ω∉BA := fun h => hω.2 (Or.inl (Or.inr h))
    have hnM : ω∉BM := fun h => hω.2 (Or.inr h)
    have hsmallS : ((failures S FS ω).card:ℝ)<tS := by
      rw [←eventCount_eq_card]
      exact lt_of_not_ge hnS
    have hsmallA : ((failures univ FA ω).card:ℝ)<tA := by
      rw [←eventCount_eq_card]
      exact lt_of_not_ge hnA
    have hm : ((sample ω).card:ℝ)≤M := le_of_not_gt hnM
    refine ⟨hm,?_,?_⟩
    · have hh := capture_count S (sample ω) Ds (failures S FS ω)
        (S.filter (fun x => z ω/(10*q)<zx ω x)) (score ω) (z ω) q (by
          intro x hx hds hfs hes hsample
          have htyp := hs ω hω.1 x hx hds hsample (fun hf => hfs (mem_filter.mpr ⟨hx,hf⟩))
          have hzx' : zx ω x≤z ω/(10*q) := by
            by_contra hh
            exact hes (mem_filter.mpr ⟨hx,lt_of_not_ge hh⟩)
          exact capture_score _ _ _ _ _ _ hq (hz ω hω.1) (hzx ω hω.1 x) hzx'
            (by linarith [(ha x).1]) (ha x).2 (herrors ω hω.1 x hds hsample) htyp)
      have hh' : (S.card:ℝ)≤(S∩test (sample ω) (score ω) (z ω) q).card+
          (Ds.card:ℝ)+(failures S FS ω).card+(S.filter (fun x => z ω/(10*q)<zx ω x)).card := by
        exact_mod_cast hh
      linarith [hes ω hω.1]
    · have hh := ambient_count (sample ω) Da (failures univ FA ω)
        (univ.filter (fun x => zx ω x<(4/5)*z ω/q)) (score ω) (z ω) q (by
          intro x hda' hfa hea hsample
          have hds : x∉Ds := fun hx => hda' (hda hx)
          have htyp := ht ω hω.1 x hda' hsample (fun hf => hfa (mem_filter.mpr ⟨mem_univ _,hf⟩))
          have hzx' : (4/5)*z ω/q≤zx ω x := by
            by_contra hh
            exact hea (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hh⟩)
          exact (exclude_score _ _ _ _ _ _ hq (hz ω hω.1) hzx' (ha x).1
            (herrors ω hω.1 x hds hsample) htyp).le)
      have hh' : ((test (sample ω) (score ω) (z ω) q).card:ℝ)≤(sample ω).card+
          (Da.card:ℝ)+(failures univ FA ω).card+
          (univ.filter (fun x => zx ω x<(4/5)*z ω/q)).card := by exact_mod_cast hh
      linarith [hea ω hω.1]
  have hg := good_minus_bad μ E (BS∪BA∪BM)
  have hh := measureReal_mono (h₂:=measure_ne_top μ _) hc
  linarith

end
end SharpLogRamsey.LearningRow
namespace SharpLogRamsey.PoissonTail
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.BoundedProbability SharpLogRamsey.PoissonGrouping
open scoped BigOperators NNReal Classical
noncomputable section

lemma weighted_power_hasSum (r : ℝ≥0) (a : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ))*(r:ℝ)^n/(n.factorial:ℝ)*a^n)
      (Real.exp ((r:ℝ)*(a-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*a)).mul_left (Real.exp (-(r:ℝ)))
  convert! h using 1
  · funext n
    rw [mul_pow]
    ring
  · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
    congr 1
    ring

lemma integrable_power (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => a^n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs,abs_pow] using (weighted_power_hasSum r |a|).summable

lemma integral_power (r : ℝ≥0) (a : ℝ) :
    (∫ n : ℕ,a^n ∂poissonMeasure r)=Real.exp ((r:ℝ)*(a-1)) := by
  rw [integral_poissonMeasure' (integrable_power r a)]
  simpa only [smul_eq_mul] using (weighted_power_hasSum r a).tsum_eq

theorem double_mean_tail (r : ℝ≥0) :
    (poissonMeasure r).real {n : ℕ | 2*(r:ℝ)≤n} ≤ Real.exp (-(r:ℝ)/3) := by
  have hlog : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hE : {n : ℕ | 2*(r:ℝ)≤n} ⊆
      {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n} := by
    intro n hn
    change Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n
    have he : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [he]
    change 2*(r:ℝ)≤(n:ℝ) at hn
    apply Real.exp_le_exp.mpr
    nlinarith
  have hm := real_markov (poissonMeasure r) (fun n : ℕ => (2:ℝ)^n)
    (integrable_power r 2) (fun _ => by positivity)
    (Real.exp (2*(r:ℝ)*Real.log 2)) (Real.exp_pos _).le
    (Set.to_countable _).measurableSet
  rw [integral_power] at hm
  have ht : (poissonMeasure r).real {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2)≤(2:ℝ)^n} ≤
      Real.exp ((r:ℝ)-2*(r:ℝ)*Real.log 2) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [sub_self, sub_zero,show (2:ℝ)-1=1 by norm_num,mul_one,mul_comm] using hm
  apply (measureReal_mono (h₂:=measure_ne_top _ _) hE).trans (ht.trans ?_)
  apply Real.exp_le_exp.mpr
  nlinarith [r.coe_nonneg]

theorem total_tail {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) :
    (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} ≤
      Real.exp (-(∑ i,(rate i:ℝ))/3) := by
  have h := sum_hasLaw rate univ
  have hm := h.measurePreserving (measurable_of_countable _)
  have he : (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} =
      (poissonMeasure (∑ i,rate i)).real {n : ℕ | 2*(∑ i,(rate i:ℝ))≤n} := by
    unfold Measure.real
    rw [←hm.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]
    rfl
  rw [he]
  simpa using double_mean_tail (∑ i,rate i)

end
end SharpLogRamsey.PoissonTail

namespace SharpLogRamsey.ExceptionalScore
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A H R : Type*} [Fintype R]

omit [Fintype R] in
lemma empty_mono {S T : Finset A} (h : S ⊆ T) (ω : R → A → ℕ) (r : R)
    (he : empty T ω r) : empty S ω r := fun x hx => he x (h hx)

omit [Fintype R] in
lemma factor_abs_le (O X : Finset A) (b : ℝ) (ω : R → A → ℕ) (r : R)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    |if empty O ω r then (if empty X ω r then 1-b else -b) else 0| ≤ 1 := by
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma term_empty (O X : Finset A) (b : ℝ) (ω : R → A → ℕ)
    (ho : fullyEmpty O ω) (hx : fullyEmpty X ω) :
    term O X b ω = (1-b)^(Fintype.card R) := by
  simp only [term,ite_eq_left (ho _),ite_eq_left (hx _),prod_const,card_univ]

lemma term_hit (O X : Finset A) (b : ℝ) (ω : R → A → ℕ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hh : ¬fullyEmpty (O∪X) ω) :
    |term O X b ω| ≤ b := by
  classical
  have hw : ∃ r,¬empty (O∪X) ω r := by simpa only [fullyEmpty,not_forall] using hh
  obtain ⟨r,hr⟩ := hw
  have hr' : ¬empty O ω r ∨ ¬empty X ω r := by
    by_contra h
    push Not at h
    apply hr
    intro x hx
    rcases mem_union.mp hx with hx|hx
    · exact h.1 x hx
    · exact h.2 x hx
  have hf : |if empty O ω r then (if empty X ω r then 1-b else -b) else 0| ≤ b := by
    rcases hr' with ho|hx
    · simp only [ite_eq_right ho,abs_zero]; exact hb
    · split_ifs <;> simp_all only [abs_neg,abs_of_nonneg hb,le_refl,abs_zero]
  rw [term,abs_prod]
  calc
    _ = |if empty O ω r then (if empty X ω r then 1-b else -b) else 0| *
        ∏ j∈univ.erase r,|if empty O ω j then (if empty X ω j then 1-b else -b) else 0| :=
      (mul_prod_erase _ _ (mem_univ r)).symm
    _ ≤ b*1 := mul_le_mul hf (prod_le_one (fun _ _ => abs_nonneg _)
      (fun j _ => factor_abs_le O X b ω j hb hb1)) (prod_nonneg (fun _ _ => abs_nonneg _)) hb
    _ = b := mul_one _

theorem exceptional_error (E : Finset H) (S O X : H → Finset A)
    (b : ℝ) (ω : R → A → ℕ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hdec : ∀ H∈E,fullyEmpty (S H) ω ↔ fullyEmpty (O H∪X H) ω) :
    |(∑ H∈E,term (O H) (X H) b ω) -
      (1-b)^(Fintype.card R)*(E.filter (fun H => fullyEmpty (S H) ω)).card| ≤
      b*(E.card:ℝ) := by
  have heq : (1-b)^(Fintype.card R)*(E.filter (fun H => fullyEmpty (S H) ω)).card =
      ∑ H∈E,if fullyEmpty (S H) ω then (1-b)^(Fintype.card R) else 0 := by
    rw [←sum_filter]; simp [mul_comm]
  rw [heq,←sum_sub_distrib]
  calc
    _ ≤ ∑ H∈E,|term (O H) (X H) b ω-
      (if fullyEmpty (S H) ω then (1-b)^(Fintype.card R) else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _H∈E,b := by
      apply sum_le_sum
      intro H hH
      by_cases he : fullyEmpty (S H) ω
      · have hu := (hdec H hH).mp he
        have ho : fullyEmpty (O H) ω := fun r => empty_mono (subset_union_left) ω r (hu r)
        have hx : fullyEmpty (X H) ω := fun r => empty_mono (subset_union_right) ω r (hu r)
        rw [ite_eq_left he,term_empty _ _ _ _ ho hx,sub_self,abs_zero]
        exact hb
      · rw [ite_eq_right he,sub_zero]
        exact term_hit _ _ _ _ hb hb1 (fun h => he ((hdec H hH).mpr h))
    _ = _ := by simp [mul_comm]

end
end SharpLogRamsey.ExceptionalScore

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PointScore
open scoped BigOperators Classical
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

omit [Fintype A] [Fintype H] in
lemma unsampled (S : Finset A) {R : ℕ} (ω : Schedule S R) (x : A)
    (hx : x∉sample S ω) : ∀ r (y : S),y.1=x → ω (r,y)=0 := by
  intro r y hy
  subst x
  have hn : ¬∃ r,extend S ω r y.1≠0 := fun h => hx (mem_filter.mpr ⟨y.2,h⟩)
  have hh : extend S ω r y.1=0 := Classical.not_not.mp (fun h => hn ⟨r,h⟩)
  simpa only [extend,dite_eq_left y.2] using hh

omit [Fintype A] [Fintype H] in
lemma sample_subset (S : Finset A) {R : ℕ} (ω : Schedule S R) : sample S ω⊆S := filter_subset _ _

omit [Fintype A] [Fintype H] in
lemma score_eq (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = ∑ h∈T, ∏ r,
      pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
        (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b) := by
  exact sum_coe_sort T (fun h : H => ∏ r,
    pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
      (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b))

omit [Fintype A] [Fintype H] in
lemma score_partition (S O : Finset A) (T E : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = score S O (T\E) inc b ω+score S O (T∩E) inc b ω := by
  simp only [score_eq]
  have hh := (sum_sdiff (inter_subset_left (s₁:=T) (s₂:=E)) (f:=fun h => ∏ r,
    pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
      (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b)))
  have he : T \ (T∩E)=T\E := by ext h; simp only [mem_sdiff,mem_inter]; tauto
  simpa only [he] using hh.symm

omit [Fintype A] [Fintype H] in
lemma empty_iff (S : Finset A) {R : ℕ} (inc : H → A → Prop)
    (ω : Schedule S R) (h : H) :
    empty S inc ω h ↔ SharpLogRamsey.ExceptionalScore.fullyEmpty
      (univ.filter (fun y : S => inc h y.1)) (fun r y => ω (r,y)) := by
  simp only [empty,ExceptionalScore.fullyEmpty,ExceptionalScore.empty,mem_filter,mem_univ,true_and]

omit [Fintype A] [Fintype H] in

lemma score_exceptional_term (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = ∑ h∈T,ExceptionalScore.term
      (univ.filter (fun y : S => y.1∈O ∧ inc h y.1))
      (univ.filter (fun y : S => y.1∉O ∧ inc h y.1)) b (fun r y => ω (r,y)) := by
  rw [score_eq]
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  simp only [pointEmpty,ExceptionalScore.empty,mem_filter,mem_univ,true_and]
  split_ifs <;> simp_all

omit [Fintype A] [Fintype H] in

theorem exceptional_error (S O : Finset A) (T E : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) (hb : 0≤b) (hb1 : b≤1) :
    |(score S O T inc b ω-score S O (T\E) inc b ω)-
      (1-b)^R*((T∩emptySet S E inc ω).card:ℝ)|≤b*((T∩E).card:ℝ) := by
  classical
  have hp := score_partition S O T E inc b ω
  have hcard : (T∩emptySet S E inc ω)=(T∩E).filter (empty S inc ω) := by
    ext h
    simp only [emptySet,mem_inter,mem_filter]
    tauto
  have hh := ExceptionalScore.exceptional_error (T∩E)
    (fun h => univ.filter (fun y : S => inc h y.1))
    (fun h => univ.filter (fun y : S => y.1∈O ∧ inc h y.1))
    (fun h => univ.filter (fun y : S => y.1∉O ∧ inc h y.1)) b (fun r y => ω (r,y)) hb hb1 (by
      intro h _
      simp only [ExceptionalScore.fullyEmpty,ExceptionalScore.empty,mem_union,
        mem_filter,mem_univ,true_and]
      constructor
      · intro he r y hy
        exact he r y (hy.elim And.right And.right)
      · intro he r y hy
        by_cases ho : y.1∈O
        · exact he r y (Or.inl ⟨ho,hy⟩)
        · exact he r y (Or.inr ⟨ho,hy⟩))
  rw [←score_exceptional_term S O (T∩E) inc b ω] at hh
  simp only [Fintype.card_fin,←empty_iff] at hh
  rw [hp,add_sub_cancel_left,hcard]
  exact hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open SharpLogRamsey.EmptyExceptional
open scoped BigOperators Classical NNReal
noncomputable section
variable {A H : Type*}

lemma coordinates_empty (S : Finset A) (R : ℕ) (inc : H → A → Prop)
    (ω : Schedule S R) (h : H) :
    ω∈emptyLedger (coordinates S R inc h) ↔ empty S inc ω h := by
  simp only [emptyLedger,coordinates,empty,mem_product,mem_univ,mem_filter,true_and]
  constructor
  · intro he r y hy
    exact he (r,y) hy
  · intro he i hi
    exact he i.1 i.2 hi

lemma sub_inc_card (S : Finset A) (inc : H → A → Prop) (h : H) :
    (univ.filter (fun y : S => inc h y.1)).card=(S.filter (inc h)).card := by
  apply card_bij (fun y _ => y.1)
  · intro y hy
    exact mem_filter.mpr ⟨y.2,(mem_filter.mp hy).2⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    exact ⟨⟨y,(mem_filter.mp hy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩,rfl⟩

lemma coordinates_mass (S : Finset A) (R : ℕ) (inc : H → A → Prop) (h : H)
    (γ : ℝ≥0) :
    (∑ _i∈coordinates S R inc h,(γ:ℝ))=(γ:ℝ)*R*((S.filter (inc h)).card:ℝ) := by
  simp only [sum_const,nsmul_eq_mul,coordinates,card_product,card_univ,Fintype.card_fin,
    sub_inc_card,Nat.cast_mul]
  ring

lemma empty_count (S : Finset A) (E : Finset H) (R : ℕ) (inc : H → A → Prop)
    (ω : Schedule S R) :
    emptySum E (coordinates S R inc) (fun _ => 1) ω=(emptySet S E inc ω).card := by
  simp only [emptySum,coordinates_empty,emptySet,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

lemma empty_weight (S : Finset A) (E : Finset H) (R : ℕ) (inc : H → A → Prop)
    (l : H → ℝ) (ω : Schedule S R) :
    emptySum E (coordinates S R inc) l ω=∑ h∈emptySet S E inc ω,l h := by
  simp only [emptySum,coordinates_empty,emptySet,sum_filter]

theorem actual_empty_good (S : Finset A) (E E₀ : Finset H) (R : ℕ)
    (inc : H → A → Prop) (γ : ℝ≥0) (l : H → ℝ) (P b δ u zmin W : ℝ)
    (hE₀ : E₀.Nonempty) (hsub : E₀⊆E) (hP : 0≤P) (hδ : 0≤δ)
    (hu : 0<u) (hz : 0<zmin) (hl : ∀ h∈E,0≤l h)
    (hmass : ∀ h∈E,(γ:ℝ)*R*((S.filter (inc h)).card:ℝ)=P*l h)
    (hb : ∀ h∈E₀,(γ:ℝ)*R*((S.filter (inc h)).card:ℝ)≤b)
    (hW : ∑ h∈E,l h≤W) (hzmin : zmin≤(E₀.card:ℝ)*Real.exp (-b)/2) :
    Real.exp (-b)/2-W*Real.exp (-P*δ)/(u*zmin)≤
      (scheduleLaw (fun _ : Fin R×S => γ)).real {ω |
        zmin≤(emptySet S E inc ω).card ∧
        (∑ h∈emptySet S E inc ω,l h)≤(δ+u)*(emptySet S E inc ω).card} := by
  have he := empty_good_event (fun _ : Fin R×S => γ) E E₀ hE₀ hsub
    (coordinates S R inc) l P b δ u zmin W hP hδ hu hz hl
    (fun h hh => (coordinates_mass S R inc h γ).trans (hmass h hh))
    (fun h hh => (coordinates_mass S R inc h γ).trans_le (hb h hh)) hW hzmin
  simpa only [empty_count,empty_weight,sum_const,nsmul_eq_mul,mul_one] using he

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open scoped BigOperators Classical NNReal
noncomputable section
variable {A : Type*}

lemma sample_card_le_total (S : Finset A) (R : ℕ) (ω : Schedule S R) :
    (sample S ω).card≤∑ i : Fin R×S,ω i := by
  have hs (x : A) (hx : x∈sample S ω) : 1≤∑ r,extend S ω r x := by
    obtain ⟨r,hr⟩ := (mem_filter.mp hx).2
    have hh := single_le_sum (fun r _ => Nat.zero_le (extend S ω r x)) (mem_univ r)
    exact (Nat.one_le_iff_ne_zero.mpr hr).trans hh
  calc
    _ = ∑ x∈sample S ω,1 := by simp
    _ ≤ ∑ x∈sample S ω,∑ r,extend S ω r x := sum_le_sum hs
    _ ≤ ∑ x∈S,∑ r,extend S ω r x :=
      sum_le_sum_of_subset_of_nonneg (sample_subset S ω) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ x : S,∑ r,ω (r,x) := by
      rw [←sum_coe_sort S (fun x : A => ∑ r,extend S ω r x)]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro r _
      exact dite_eq_left x.2
    _ = ∑ i : Fin R×S,ω i := by rw [Fintype.sum_prod_type,sum_comm]

lemma constant_mean (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    (∑ _i : Fin R×S,(γ:ℝ))=(R:ℝ)*S.card*γ := by
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,
    nsmul_eq_mul,Nat.cast_mul]

theorem sample_size_tail (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    (scheduleLaw (fun _ : Fin R×S => γ)).real
      {ω | 2*((R:ℝ)*S.card*γ)<((sample S ω).card:ℝ)}≤
        Real.exp (-((R:ℝ)*S.card*γ)/3) := by
  have hh := SharpLogRamsey.PoissonTail.total_tail (fun _ : Fin R×S => γ)
  rw [constant_mean S R γ] at hh
  apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) hh
  intro ω hω
  change 2*((R:ℝ)*S.card*γ)<((sample S ω).card:ℝ) at hω
  change 2*((R:ℝ)*S.card*γ)≤((∑ i : Fin R×S,ω i : ℕ):ℝ)
  exact hω.le.trans (Nat.cast_le.mpr (sample_card_le_total S R ω))

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TestRowPencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory PreparedProjectiveGeometry
open SharpLogRamsey.PointScore SharpLogRamsey.Incidence
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestRowPencils_2
local instance flat_JoinedTestRowPencils_3_r588b34_1 : Fintype (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
lemma score_second_tail
    (j R : ℕ) (hdim : Module.finrank K V≤j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (E : Finset (Projectivization K (Module.Dual K V))) (f B C : ℝ)
    (hf : f≤1/4) (hB : 0≤B) (hC : 0≤C) (hL : 1≤(L:ℝ)) (hR : 200≤R)
    (T : Finset I) (a : I→ℝ) (hc : SecondPencil j R S O x c L (pencil x\E) f B C T a)
    (t : ℝ) (ht : 0<t) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real
      {ω | x∉sample S ω ∧ t≤|score S O (pencil x\E)
        (fun H y => y.submodule≤LinearMap.ker H.rep) (Real.exp (-(L:ℝ)*(1-f))) ω|}≤
          B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2 := by
  have hh := actual_point_second_tail j hdim S O x c L (pencil x\E)
    (fun H hH => (mem_filter.mp (mem_sdiff.mp hH).1).2) f B C hf hB hC R hL hR
    hc.low hc.upp hc.deviation hc.squares hc.cardinal T a hc.positive hc.cover hc.pairs
    hc.diagonalBudget hc.powerBudget hc.sumBudget hc.twoBudget t ht
  apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) hh
  intro ω hω
  exact ⟨unsampled S ω x hω.1,hω.2⟩

lemma score_high_tail
    (j R p h : ℕ) (hj : 2≤j) (hj3 : j≤3) (hdim : Module.finrank K V≤j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (E : Finset (Projectivization K (Module.Dual K V))) (f B : ℝ)
    (hf : f≤1/25) (hp : 0<p) (hpe : Even p) (hL : 10000≤(L:ℝ)) (hR : 400≤R)
    (hB : Real.exp (3*((L:ℝ)*R))≤B)
    (T : Finset I) (a : I→ℝ) (hc : HighPencil j R p h S O x c L (pencil x\E) f B T a)
    (t : ℝ) (ht : 0<t) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real
      {ω | x∉sample S ω ∧ t≤|score S O (pencil x\E)
        (fun H y => y.submodule≤LinearMap.ker H.rep) (Real.exp (-(L:ℝ)*(1-f))) ω|}≤
          B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p := by
  have hh := actual_point_high_tail j hj hj3 hdim S O x c L (pencil x\E)
    (fun H hH => (mem_filter.mp (mem_sdiff.mp hH).1).2) f B hf hp hpe R hL
    hc.low hc.upp hc.deviation hB hc.cardinal hc.directions T a hc.nonnegative
    hc.cover hc.pairs hc.neighbors hc.strong hc.squares hc.certificateBudget hc.shiftBudget
    hc.pBudget hc.pSumBudget h hc.hPositive hR hc.hSize hc.hError t ht
  apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) hh
  intro ω hω
  exact ⟨unsampled S ω x hω.1,hω.2⟩

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

omit [Fintype A] [Fintype H] in
lemma degree_eq_card (inc : H→A→Prop) (Z : Finset H) (x : A) :
    PencilContrast.degree (fun x H => inc H x) Z x=(Z.filter (fun H => inc H x)).card := by
  simp only [PencilContrast.degree,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

omit [Fintype A] [Fintype H] in
lemma support_empty_large (S : Finset A) (Z : Finset H) (inc : H→A→Prop)
    (q a : ℝ) (hq : 0<q) (hS : S.Nonempty) (hZ : Z.Nonempty)
    (hb : (∑ H∈Z,(q/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤a*(Z.card:ℝ)) :
    ((S.filter (fun x => (Z.card:ℝ)/(10*q)<((Z.filter (fun H => inc H x)).card:ℝ))).card:ℝ)≤
      (10*a)*(S.card:ℝ) := by
  have hSc : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hZc : (0:ℝ)<Z.card := by exact_mod_cast card_pos.mpr hZ
  have hh := PencilContrast.support_large_degree (fun x H => inc H x) S Z q S.card Z.card a
    (1/10) hq hSc hZc (by norm_num) (by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero])
  have hs : S.filter (fun x => (Z.card:ℝ)/(10*q)<((Z.filter (fun H => inc H x)).card:ℝ))⊆
      S.filter (fun x => (1/10:ℝ)*(Z.card:ℝ)/q≤PencilContrast.degree (fun x H => inc H x) Z x) := by
    intro x hx
    refine mem_filter.mpr ⟨(mem_filter.mp hx).1,?_⟩
    rw [degree_eq_card]
    convert (mem_filter.mp hx).2.le using 1
    all_goals try with_reducible_and_instances rfl
    first | with_unfolding_all rfl | ring
  have hc : ((S.filter (fun x => (Z.card:ℝ)/(10*q)<((Z.filter (fun H => inc H x)).card:ℝ))).card:ℝ)≤
      (S.filter (fun x => (1/10:ℝ)*(Z.card:ℝ)/q≤PencilContrast.degree (fun x H => inc H x) Z x)).card := by
    exact_mod_cast card_le_card hs
  convert hc.trans hh using 1
  all_goals try with_reducible_and_instances rfl
  first | with_unfolding_all rfl | ring

lemma alpha_bounds (L f : ℝ) (R : ℕ) (hL : 0≤L) (hf : f≤1/25)
    (hR : (R:ℝ)*Real.exp (-(24/25:ℝ)*L)≤1/10) :
    0≤Real.exp (-L*(1-f)) ∧ Real.exp (-L*(1-f))≤1 ∧
      9/10≤(1-Real.exp (-L*(1-f)))^R ∧ (1-Real.exp (-L*(1-f)))^R≤1 := by
  let b := Real.exp (-L*(1-f))
  have hb : 0≤b := (Real.exp_pos _).le
  have hb1 : b≤1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hbe : b≤Real.exp (-(24/25:ℝ)*L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbR : (R:ℝ)*b≤1/10 :=
    (mul_le_mul_of_nonneg_left hbe (Nat.cast_nonneg R)).trans hR
  have hber : 1-(R:ℝ)*b≤(1-b)^R := by
    have hh := one_add_mul_sub_le_pow (show (-1:ℝ)≤1-b by linarith) R
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    first | with_unfolding_all rfl | ring
  exact ⟨hb,hb1,by linarith,pow_le_one₀ (by linarith) (by linarith)⟩

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestActualRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory LearningRow
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_2
attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_3
lemma pencil_inter_count (Z : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V) :
    (pencil x∩Z).card=(Z.filter (fun H => inc H x)).card := by
  congr 1
  ext H
  simp only [pencil,inc,mem_filter,mem_univ,true_and,mem_inter]
  tauto

lemma pencil_degree (Z : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V) :
    PencilContrast.degree Incidence.Incident Z x=((pencil x∩Z).card:ℝ) := by
  rw [pencil_inter_count]
  simp only [PencilContrast.degree,Incidence.incident_iff_submodule,inc,card_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem geometric_row_probability_oai
    (n R p h : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty) (hDa : Ds⊆Da)
    (O : Projectivization K V→Finset (Projectivization K V))
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (f : Projectivization K V→ℝ) (hf : ∀ x,f x≤1/25)
    (B C bE δ u zmin W tS tA : ℝ)
    (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : Real.exp (3*((L:ℝ)*R))≤B)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
    (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
    (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-f x))*((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (O x) x c L (pencil x\E) (f x) B C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (O x) x c L (pencil x\E) (f x) B T a) :
    let q : ℝ := Nat.card K
    let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
    let t := zmin/(10*q)
    let εs := B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
    let εa := B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
    Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
        (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-Real.exp (-μmean/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω |
        ((sample S ω).card:ℝ)≤2*μmean ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤
          (S∩rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card ∧
        ((rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card:ℝ)≤
          2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin} := by
  dsimp only
  let q : ℝ := Nat.card K
  let b : Projectivization K V→ℝ := fun x => Real.exp (-(L:ℝ)*(1-f x))
  let μ := PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)
  let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
  let z := fun ω : Schedule S R => ((emptySet S E inc ω).card:ℝ)
  let zx := fun (ω : Schedule S R) x => ((pencil x∩emptySet S E inc ω).card:ℝ)
  let typ := fun (ω : Schedule S R) x => score S (O x) (pencil x\E) inc (b x) ω
  let full := fun (ω : Schedule S R) x => score S (O x) (pencil x) inc (b x) ω
  let t := zmin/(10*q)
  let εs := B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
  let εa := B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
  let FS := fun x => {ω : Schedule S R | x∉Ds ∧ x∉sample S ω ∧ t≤|typ ω x|}
  let FA := fun x => {ω : Schedule S R | x∉Da ∧ x∉sample S ω ∧ t≤|typ ω x|}
  let G := {ω : Schedule S R | zmin≤z ω ∧
    (∑ H∈emptySet S E inc ω,(q/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤(δ+u)*z ω}
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have ht : 0<t := by dsimp [t]; positivity
  have hB0 : 0≤B := (Real.exp_pos _).le.trans hB
  have hd : Module.finrank K V≤n+2+1 := by omega
  have hgood := actual_empty_good S E E₀ R inc (L*c)
    (fun H => (q/(S.card:ℝ))*((S.filter (inc H)).card:ℝ)) ((L:ℝ)*R) bE δ u zmin W
    hE₀ hE₀E (by positivity) hδ hu hzmin (by intro H _; positivity)
    (by intro H _; rw [NNReal.coe_mul,hc]; ring) hsmall hW hZ
  have hfs : ∀ x∈S,μ.real (FS x)≤εs := by
    intro x _
    by_cases hx : x∈Ds
    · have he : FS x=∅ := by ext ω; simp [FS,hx]
      rw [he,measureReal_empty]
      dsimp [εs]
      positivity
    · have hh := score_second_tail (n+2) R hd S (O x) x c L E (f x) B C
        (by linarith [hf x]) hB0 hC (by linarith) (by omega) T a (hs x hx) t ht
      exact (measureReal_mono (h₂:=measure_ne_top μ _) (fun ω hω => hω.2)).trans hh
  have hfa : ∀ x,μ.real (FA x)≤εa := by
    intro x
    by_cases hx : x∈Da
    · have he : FA x=∅ := by ext ω; simp [FA,hx]
      rw [he,measureReal_empty]
      dsimp [εa]
      have hBp : 0≤B^p := pow_nonneg hB0 p
      positivity
    · have hh := score_high_tail (n+2) R p h (by omega) (by omega) hd S (O x) x c L E
        (f x) B (hf x) hp hpe hL hR hB T a (ha x hx) t ht
      exact (measureReal_mono (h₂:=measure_ne_top μ _) (fun ω hω => hω.2)).trans hh
  have halpha (x : Projectivization K V) := alpha_bounds (L:ℝ) (f x) R L.coe_nonneg (hf x) hα
  have herrors : ∀ ω∈G,∀ x,x∉Ds → x∉sample S ω →
      |(full ω x-typ ω x)-(1-b x)^R*zx ω x|≤z ω/(100*q) := by
    intro ω hω x hx _
    exact (exceptional_error S (O x) (pencil x) E inc (b x) ω
      (halpha x).1 (halpha x).2.1).trans ((herror x hx).trans
      (div_le_div_of_nonneg_right hω.1 (by positivity)))
  have htypS : ∀ ω∈G,∀ x∈S,x∉Ds → x∉sample S ω → ω∉FS x → |typ ω x|≤z ω/(10*q) := by
    intro ω hω x _ hx hsample hFS
    have hh : |typ ω x|<t := lt_of_not_ge (fun hh => hFS ⟨hx,hsample,hh⟩)
    exact hh.le.trans (div_le_div_of_nonneg_right hω.1 (by positivity))
  have htypA : ∀ ω∈G,∀ x,x∉Da → x∉sample S ω → ω∉FA x → |typ ω x|≤z ω/(10*q) := by
    intro ω hω x hx hsample hFA
    have hh : |typ ω x|<t := lt_of_not_ge (fun hh => hFA ⟨hx,hsample,hh⟩)
    exact hh.le.trans (div_le_div_of_nonneg_right hω.1 (by positivity))
  have hZnonempty (ω : Schedule S R) (hω : ω∈G) : (emptySet S E inc ω).Nonempty := by
    apply card_pos.mp
    have hh : (0:ℝ)<(emptySet S E inc ω).card := hzmin.trans_le hω.1
    exact_mod_cast hh
  have hes : ∀ ω∈G,((S.filter (fun x => z ω/(10*q)<zx ω x)).card:ℝ)≤10*(δ+u)*(S.card:ℝ) := by
    intro ω hω
    have hh := support_empty_large S (emptySet S E inc ω) inc q (δ+u) hq hS (hZnonempty ω hω) hω.2
    simpa only [z,zx,pencil_inter_count] using hh
  have hea : ∀ ω∈G,((univ.filter (fun x => zx ω x<(4/5)*z ω/q)).card:ℝ)≤100*q^(n+3)/zmin := by
    intro ω hω
    have hh := PencilContrast.ambient_small_degree hdim (emptySet S E inc ω) (hZnonempty ω hω) hQ
    simp only [pencil_degree] at hh
    apply hh.trans
    exact div_le_div_of_nonneg_left (by positivity) hzmin hω.1
  have hh := row_success_probability μ S Ds Da (sample S) full typ zx z
    (fun x => (1-b x)^R) q tS tA (10*(δ+u)*(S.card:ℝ)) (100*q^(n+3)/zmin)
    (2*μmean) εs εa (Real.exp (-μmean/3))
    (Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)) G FS FA
    (fun x _ => (Set.to_countable _).measurableSet) (fun x => (Set.to_countable _).measurableSet)
    hq htS htA hgood hfs hfa (sample_size_tail S R (L*c))
    (fun ω hω => hzmin.trans_le hω.1) (fun ω _ x => Nat.cast_nonneg _)
    (fun x => (halpha x).2.2) herrors htypS hDa htypA hes hea
  exact hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.PreparedRow.geometric_row_probability_oai := @OAI.SharpLogRamsey.PreparedRow.geometric_row_probability_oai
