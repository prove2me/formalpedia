-- Prove2me | solution 1 for OAI.Balanced.pencil_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:24:13.666558+00:00
-- url     : https://prove2.me/submissions/ef44c370-577f-4a9f-bad5-e0458d38e48a

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br004
import Theorems.Thm_OAI_Balanced_Local_injectiveUsedEventsEstimate_proof
import Theorems.Thm_OAI_Balanced_Local_pencilSmallReuse_proof
import Theorems.Thm_OAI_Balanced_pencilReuse_proof

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

@[simp] theorem covers_empty_iff (H : PartiteHypergraph r n) :
    H.Covers ∅ ↔ H.edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases h e he with ⟨i, hi⟩
    exact Finset.notMem_empty _ hi
  · intro h e he
    simp [h] at he

end Balanced.PartiteHypergraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionFieldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

omit [DecidableEq F] [DecidableEq G] in
@[simp] theorem cardinal_field (e : F ≃+* G) : Fintype.card G = Fintype.card F :=
  (Fintype.card_congr e.toEquiv).symm

end Balanced.FieldTransport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem eq_of_onLine_same_direction (p : Point F) (l m : Line F)
    (hdir : l.1 = m.1) (hl : OnLine p l) (hm : OnLine p m) : l = m := by
  rw [line_eq_lineThrough p l hl, line_eq_lineThrough p m hm, hdir]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_LogTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace BalancedRyser

theorem polynomial_mul_ratio_pow_le_inv
    (q r B : ℕ) (C : ℝ) (hq : 0 < q) (hBpos : 0 < B)
    (hC : 0 ≤ C) (hlog : Real.log (q : ℝ) ≤ (B : ℝ))
    (hlarge : C * Real.exp ((r : ℝ) + 1) ≤ (B : ℝ)) :
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B ≤ (q : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hbase : C / (B : ℝ) ≤ Real.exp (-((r : ℝ) + 1)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hBR).2
    simpa [div_eq_mul_inv, mul_comm] using
      ((le_div_iff₀ (Real.exp_pos ((r : ℝ) + 1))).2 hlarge)
  have hpow : (C / (B : ℝ)) ^ B ≤
      Real.exp (-((r : ℝ) + 1)) ^ B :=
    pow_le_pow_left₀ (div_nonneg hC hBR.le) hbase B
  calc
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B
        ≤ (q : ℝ) ^ r * Real.exp (-((r : ℝ) + 1)) ^ B :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hqR.le _)
    _ = Real.exp ((r : ℝ) * Real.log (q : ℝ) - ((r : ℝ) + 1) * B) := by
      have hqpow : (q : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hqR]
      rw [hqpow, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log (q : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    _ = (q : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hqR]

theorem tendsto_log_cutoff_atTop :
    Tendsto (fun q : ℕ => Nat.ceil (Real.log (q : ℝ))) atTop atTop :=
  tendsto_nat_ceil_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_polynomial_mul_cutoff_tail
    (B : ℕ → ℕ)
    (hlog : ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (B q : ℝ))
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r * (C / (B q : ℝ)) ^ B q)
      atTop (𝓝 0) := by
  have hcut : Tendsto (fun q : ℕ => (B q : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ hlog
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun q =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg q) r)
        (pow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _))
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
      hcut.eventually (eventually_gt_atTop 0),
      hcut.eventually (eventually_ge_atTop (C * Real.exp ((r : ℝ) + 1)))]
      with q hq hlogq hB hlarge
    exact polynomial_mul_ratio_pow_le_inv q r _ C hq
      (by exact_mod_cast hB) hC hlogq hlarge
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem tendsto_polynomial_mul_log_cutoff_tail
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (C / (Nat.ceil (Real.log (q : ℝ)) : ℝ)) ^
          Nat.ceil (Real.log (q : ℝ))) atTop (𝓝 0) :=
  tendsto_polynomial_mul_cutoff_tail _
    (Filter.Eventually.of_forall (fun _ => Nat.le_ceil _)) r C hC

theorem choose_le_exp_mul_div_pow (n B : ℕ) (hB : 0 < B) :
    (n.choose B : ℝ) ≤ (Real.exp 1 * n / B) ^ B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hf : (0 : ℝ) < B.factorial := by
    exact_mod_cast Nat.factorial_pos B
  have hseries := Real.pow_div_factorial_le_exp (B : ℝ) hBR.le B
  have hinv : 1 / (B.factorial : ℝ) ≤ (Real.exp 1 / B) ^ B := by
    rw [div_pow, Real.exp_one_pow]
    apply (div_le_div_iff₀ hf (pow_pos hBR B)).2
    simpa using (div_le_iff₀ hf).1 hseries
  calc
    (n.choose B : ℝ) ≤ (n : ℝ) ^ B / B.factorial := Nat.choose_le_pow_div B n
    _ = (n : ℝ) ^ B * (1 / (B.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ B * (Real.exp 1 / B) ^ B :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg (Nat.cast_nonneg n) B)
    _ = (Real.exp 1 * n / B) ^ B := by rw [← mul_pow]; congr 1; ring

theorem slot_choose_mul_pow_le
    (q B : ℕ) (K : ℝ) (hq : 0 < q) (hB : 0 < B) (hK : 0 ≤ K) :
    ((2 * (q + 1)).choose B : ℝ) * (K / (q : ℝ)) ^ B ≤
      (4 * Real.exp 1 * K / (B : ℝ)) ^ B := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    ((2 * (q + 1)).choose B : ℝ) * (K / (q : ℝ)) ^ B
        ≤ (Real.exp 1 * (2 * (q + 1) : ℕ) / B) ^ B * (K / (q : ℝ)) ^ B :=
      mul_le_mul_of_nonneg_right (choose_le_exp_mul_div_pow _ B hB)
        (pow_nonneg (div_nonneg hK hqR.le) B)
    _ = (Real.exp 1 * (2 * (q + 1) : ℕ) / B * (K / (q : ℝ))) ^ B := by
      rw [mul_pow]
    _ ≤ (4 * Real.exp 1 * K / (B : ℝ)) ^ B := by
      apply pow_le_pow_left₀ (by positivity)
      have hratio : (2 * (q + 1) : ℕ) / (q : ℝ) ≤ 4 := by
        apply (div_le_iff₀ hqR).2
        push_cast
        linarith
      have hmul := mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (Real.exp_pos 1).le hK)
      have hdiv := div_le_div_of_nonneg_right hmul hBR.le
      convert hdiv using 1 <;> ring

theorem tendsto_polynomial_mul_slot_choose_tail
    (r : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (((2 * (q + 1)).choose (Nat.ceil (Real.log (q : ℝ))) : ℝ) *
          (K / (q : ℝ)) ^ Nat.ceil (Real.log (q : ℝ))))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_polynomial_mul_log_cutoff_tail r (4 * Real.exp 1 * K) (by positivity))
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      tendsto_log_cutoff_atTop.eventually (eventually_gt_atTop 0)] with q hq hB
    exact mul_le_mul_of_nonneg_left (slot_choose_mul_pow_le q _ K hq hB hK)
      (pow_nonneg (Nat.cast_nonneg q) r)

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_LocalLargePencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace Balanced.Local

noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_event_union_le {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] :
    (∑ ω, if ∃ i ∈ s, E i ω then w ω else 0) ≤
      ∑ i ∈ s, ∑ ω, if E i ω then w ω else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ i ∈ s, E i ω
  · obtain ⟨i, hi, hEi⟩ := h
    rw [ite_eq_left ⟨i, hi, hEi⟩]
    have hterm := Finset.single_le_sum
      (s := s) (f := fun i => if E i ω then w ω else 0)
      (fun i _ => by split_ifs; exact hw ω; exact le_rfl) hi
    simpa only [ite_eq_left hEi] using hterm
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hw ω; exact le_rfl)

lemma sum_event_mono_of_pos {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (E G : Ω → Prop)
    [DecidablePred E] [DecidablePred G]
    (hEG : ∀ ω, 0 < w ω → E ω → G ω) :
    (∑ ω, if E ω then w ω else 0) ≤ ∑ ω, if G ω then w ω else 0 := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · by_cases hp : 0 < w ω
    · simp only [ite_eq_left hE, ite_eq_left (hEG ω hp hE), le_refl]
    · have hz : w ω = 0 := le_antisymm (le_of_not_gt hp) (hw ω)
      simp [hz]
  · simp only [ite_eq_right hE]
    split_ifs; exact hw ω; exact le_rfl

lemma sum_event_at_least_le {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s : Finset ι)
    (E : ι → Ω → Prop) [∀ i, DecidablePred (E i)] (m : ℕ) (δ : ℝ)
    (hcyl : ∀ t ∈ s.powersetCard m,
      (∑ ω, if ∀ i ∈ t, E i ω then w ω else 0) ≤ δ ^ m) :
    (∑ ω, if m ≤ (s.filter (fun i => E i ω)).card then w ω else 0) ≤
      (s.card.choose m : ℝ) * δ ^ m := by
  have hsub : ∀ ω : Ω, 0 < w ω →
      m ≤ (s.filter (fun i => E i ω)).card →
      ∃ t ∈ s.powersetCard m, ∀ i ∈ t, E i ω := by
    intro ω _ hω
    obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hω
    refine ⟨t, Finset.mem_powersetCard.mpr ⟨ht.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (ht hi)).2
  calc
    (∑ ω, if m ≤ (s.filter (fun i => E i ω)).card then w ω else 0)
        ≤ ∑ ω, if ∃ t ∈ s.powersetCard m, ∀ i ∈ t, E i ω then w ω else 0 :=
      sum_event_mono_of_pos w hw _ _ hsub
    _ ≤ ∑ t ∈ s.powersetCard m, ∑ ω, if ∀ i ∈ t, E i ω then w ω else 0 :=
      sum_event_union_le w hw (s.powersetCard m) (fun t ω => ∀ i ∈ t, E i ω)
    _ ≤ ∑ _t ∈ s.powersetCard m, δ ^ m := Finset.sum_le_sum hcyl
    _ = (s.card.choose m : ℝ) * δ ^ m := by
      simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma retained_choice_eq_of_onLine (Q : RetentionRule F)
    (M : MergedPairs F) (g : Direction F) (p : Point F)
    (c d : ChoiceCode F) (hc : c ∈ Q.candidates M g) (hd : d ∈ Q.candidates M g)
    (hpc : OnLine p c.1) (hpd : OnLine p d.1) : c = d := by
  have hcdir : c.1.1 = g := (Q.valid M g c hc).1
  have hddir : d.1.1 = g := (Q.valid M g d hd).1
  apply Q.uniqueLine M g c d hc hd
  apply Prod.ext
  · exact hcdir.trans hddir.symm
  · unfold OnLine at hpc hpd
    rw [hcdir] at hpc
    rw [hddir] at hpd
    exact hpc.symm.trans hpd

theorem fixed_offset_incident_cylinder_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (M : MergedPairs F)
    (p : Point F) (S : Finset (Slot F)) :
    (∑ v : Output F, if (∀ s ∈ S, OnLine p (v s).1) then w M v else 0) ≤
      (K / Fintype.card F) ^ S.card := by
  by_cases hex : ∃ v : Output F, 0 < w M v ∧ ∀ s ∈ S, OnLine p (v s).1
  · obtain ⟨v₀, hv₀, hp₀⟩ := hex
    have hv₀mem := (hw.2.2.1 M v₀ hv₀).2.2.1
    have hsub : ∀ v : Output F, 0 < w M v →
        (∀ s ∈ S, OnLine p (v s).1) → ∀ s ∈ S, (v s).2 = (v₀ s).2 := by
      intro v hv hp s hs
      have hvmem := (hw.2.2.1 M v hv).2.2.1
      have heq := retained_choice_eq_of_onLine Q M s.1 p
        (v s) (v₀ s) (hvmem s) (hv₀mem s) (hp s hs) (hp₀ s hs)
      exact congrArg Prod.snd heq
    have hmono := sum_event_mono_of_pos (w M) (hw.1 M)
      (fun v : Output F => ∀ s ∈ S, OnLine p (v s).1)
      (fun v : Output F => ∀ s ∈ S, (v s).2 = (v₀ s).2) hsub
    have hcyl := hw.2.2.2 M S (fun s => (v₀ s).2)
    exact le_trans hmono hcyl
  · have hz : (∑ v : Output F,
        if (∀ s ∈ S, OnLine p (v s).1) then w M v else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      split_ifs with hv
      · have hnp : ¬ 0 < w M v := fun hp => hex ⟨v, hp, hv⟩
        exact le_antisymm (le_of_not_gt hnp) (hw.1 M v)
      · rfl
    rw [hz]
    exact pow_nonneg (div_nonneg hK (Nat.cast_nonneg _)) _

omit [Field F] [DecidableEq F] in

lemma card_slot : Fintype.card (Slot F) = 2 * (Fintype.card F + 1) := by
  simp only [Slot, Direction, Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
  omega

lemma splitMultiplicity_le_incident_slots (M : MergedPairs F) (v : Output F)
    (p : Point F) :
    (configuration M v).splitMultiplicity p ≤
      (Finset.univ.filter (fun s : Slot F => OnLine p (v s).1)).card := by
  change ((Finset.univ.image (fun s : Slot F => (v s).1)).filter (OnLine p)).card ≤ _
  rw [Finset.filter_image]
  exact Finset.card_image_le

theorem fixed_offset_large_pencil_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (M : MergedPairs F) (p : Point F) (m : ℕ) :
    (∑ v : Output F, if m ≤ (configuration M v).splitMultiplicity p then w M v else 0) ≤
      ((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m := by
  have hmono := sum_event_mono_of_pos (w M) (hw.1 M)
    (fun v : Output F => m ≤ (configuration M v).splitMultiplicity p)
    (fun v : Output F => m ≤ (Finset.univ.filter (fun s : Slot F => OnLine p (v s).1)).card)
    (fun v _ hv => hv.trans (splitMultiplicity_le_incident_slots M v p))
  have hcount := sum_event_at_least_le (w M) (hw.1 M) Finset.univ
    (fun s v => OnLine p (v s).1) m (K / Fintype.card F) (by
      intro S hS
      have hc := fixed_offset_incident_cylinder_le Q w K hK hw M p S
      rw [(Finset.mem_powersetCard.mp hS).2] at hc
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro v _
      simp only [ite_eq_ite])
  rw [Finset.card_univ, card_slot] at hcount
  exact hmono.trans hcount

theorem fixed_offset_some_large_pencil_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (M : MergedPairs F) (m : ℕ) :
    (∑ v : Output F, if ∃ p : Point F, m ≤ (configuration M v).splitMultiplicity p
      then w M v else 0) ≤
      (Fintype.card F : ℝ) ^ 2 *
        (((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m) := by
  have hu := sum_event_union_le (w M) (hw.1 M) (Finset.univ : Finset (Point F))
    (fun p v => m ≤ (configuration M v).splitMultiplicity p)
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ?_
  calc
    (∑ p : Point F, ∑ v : Output F,
        if m ≤ (configuration M v).splitMultiplicity p then w M v else 0)
        ≤ ∑ _p : Point F,
          ((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m :=
      Finset.sum_le_sum (fun p _ => fixed_offset_large_pencil_le Q w K hK hw M p m)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Point, Fintype.card_prod,
        Nat.cast_mul, nsmul_eq_mul, pow_two]

omit [Field F] in

lemma selectedProbability_eq_sum (w : Kernel F) (E : Configuration F → Prop)
    [DecidablePred E] :
    selectedProbability w E =
      (∑ M : MergedPairs F, ∑ v : Output F,
        if E (configuration M v) then w M v else 0) / Fintype.card (MergedPairs F) := by
  unfold selectedProbability
  apply congrArg (fun x : ℝ => x / Fintype.card (MergedPairs F))
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro v _
  simp only [ite_eq_ite]

theorem selected_some_large_pencil_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (m : ℕ) :
    selectedProbability w (fun C => ∃ p : Point F, m ≤ C.splitMultiplicity p) ≤
      (Fintype.card F : ℝ) ^ 2 *
        (((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m) := by
  rw [selectedProbability_eq_sum]
  have hcard : (0 : ℝ) < Fintype.card (MergedPairs F) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  calc
    (∑ M : MergedPairs F, ∑ v : Output F,
        if ∃ p : Point F, m ≤ (configuration M v).splitMultiplicity p then w M v else 0)
        ≤ ∑ _M : MergedPairs F, (Fintype.card F : ℝ) ^ 2 *
          (((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m) :=
      Finset.sum_le_sum (fun M _ => fixed_offset_some_large_pencil_le Q w K hK hw M m)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem large_pencil_uniform_error (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F]
        (Q : RetentionRule F) (w : Kernel F), KernelConditions Q w K →
        selectedProbability w (fun C => ∃ p : Point F, logBudget F ≤ C.splitMultiplicity p) ≤
          ε (Fintype.card F) := by
  refine ⟨fun q => (q : ℝ) ^ 2 *
      (((2 * (q + 1)).choose (Nat.ceil (Real.log (q : ℝ))) : ℝ) *
        (K / q) ^ Nat.ceil (Real.log (q : ℝ))), ?_, ?_, ?_⟩
  · exact BalancedRyser.tendsto_polynomial_mul_slot_choose_tail 2 K hK
  · intro q
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (div_nonneg hK (Nat.cast_nonneg _)) _))
  · intro F _ _ _ Q w hw
    exact selected_some_large_pencil_le Q w K hK hw (logBudget F)

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConfigurationStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConfigurationStructure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in

theorem choice_line_mem_split (s : Slot F) : (C.choice s).line ∈ C.splitLines := by
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩

theorem split_multiplicity_le_one_of_designated (hC : C.Compatible)
    {s : Slot F} {p : Point F} (hp : p ∈ designated C.merged (C.choice s)) :
    C.splitMultiplicity p ≤ 1 := by
  have hsub : C.splitLinesAt p ⊆ {(C.choice s).line} := by
    intro l hl
    obtain ⟨hlS, hpl⟩ := Finset.mem_filter.mp hl
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hlS
    have hst := designated_slot_unique C hC hp hpl
    simp only [Finset.mem_singleton]
    rw [hst]
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_singleton, Configuration.splitMultiplicity] using hc

theorem center_not_designated (hC : C.Compatible) {p : Point F}
    (hb : 2 ≤ C.splitMultiplicity p) (s : Slot F) :
    p ∉ designated C.merged (C.choice s) := by
  intro hp
  have hle := split_multiplicity_le_one_of_designated C hC hp
  omega

end ConfigurationStructure
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConfigurationPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConfigurationPattern
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F) (hV : C.Valid) (hC : C.Compatible) (p : Point F)

theorem slot_direction_injective :
    Function.Injective (fun i => (slot C hV hC p i).1) := by
  intro i j hij
  apply slot_injective C hV hC p
  apply ConfigurationStructure.choice_line_injective C hV hC
  apply eq_of_onLine_same_direction p
  · exact (hV.2 _).1.trans (hij.trans (hV.2 _).1.symm)
  · exact slot_onLine C hV hC p i
  · exact slot_onLine C hV hC p j

theorem slot_line_eq (i : Fin (C.splitMultiplicity p)) :
    (C.choice (slot C hV hC p i)).line =
      lineThrough (slot C hV hC p i).1 p := by
  apply eq_of_onLine_same_direction p
  · exact (hV.2 _).1
  · exact slot_onLine C hV hC p i
  · exact onLine_lineThrough _ _

theorem point_injective : Function.Injective (point C hV hC p) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hi : slot C hV hC p i = slot C hV hC p j := by
    apply ConfigurationStructure.designated_slot_unique C hC
      (p := point C hV hC p (i, a))
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    · rw [he]
      exact (hV.2 _).2.2.2.2.2.1 b
  have hij := slot_injective C hV hC p hi
  subst j
  have hab : a = b := (hV.2 _).2.2.2.2.1 he
  exact Prod.ext rfl hab

theorem point_ne_center (hb : 2 ≤ C.splitMultiplicity p)
    (ij : Fin (C.splitMultiplicity p) × Fin 4) : point C hV hC p ij ≠ p := by
  intro he
  apply ConfigurationStructure.center_not_designated C hC hb (slot C hV hC p ij.1)
  have hx : point C hV hC p ij ∈
      designated C.merged (C.choice (slot C hV hC p ij.1)) :=
    Finset.mem_image.mpr ⟨ij.2, Finset.mem_univ _, rfl⟩
  simpa only [he] using hx

theorem point_image : Finset.univ.image (point C hV hC p) = C.designatedAt p := by
  ext x
  constructor
  · rintro hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨slot C hV hC p i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, slot_onLine C hV hC p i⟩,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, rfl⟩ := exists_slot C hV hC p (Finset.mem_filter.mp hs).2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(i, a), Finset.mem_univ _, rfl⟩

include hV hC

theorem assignment_eligible : Eligible (pattern C hV hC p) (assignment C hV hC p) := by
  refine ⟨slot_direction_injective C hV hC p, assignedGenerator_injective C hV hC p, ?_⟩
  intro i j
  change assignedGenerator C hV hC p (classOf C hV hC p i j) ≠ (slot C hV hC p i).1
  rw [assigned_class]
  exact (hV.2 _).2.2.2.1 j

theorem prescribedTuple_eq (i : Fin (C.splitMultiplicity p)) :
    prescribedTuple (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) i =
      (C.choice (slot C hV hC p i)).tuple := by
  apply (show ∀ s t : FourTuple F, s.generator = t.generator → s.side = t.side → s = t from by
    intro s t hg hs
    cases s
    cases t
    cases hg
    cases hs
    rfl)
  · funext j
    exact assigned_class C hV hC p i j
  · rfl

theorem prescribedPoint_eq (ij : Fin (C.splitMultiplicity p) × Fin 4) :
    prescribedPoint (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) C.merged ij =
      point C hV hC p ij := by
  unfold prescribedPoint
  rw [prescribedTuple_eq]
  rfl

theorem aligned :
    Aligned (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) p C.merged := by
  intro ij
  rw [prescribedPoint_eq]
  change OnLine (point C hV hC p ij) (lineThrough (slot C hV hC p ij.1).1 p)
  rw [← slot_line_eq C hV hC p ij.1]
  exact (hV.2 _).2.2.2.2.2.1 ij.2

theorem admissible (hb : 2 ≤ C.splitMultiplicity p)
    (hcap : ∀ x, constituentMultiplicity C.merged x ≤ logBudget F) :
    Admissible (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) p C.merged := by
  refine ⟨aligned C hV hC p, ?_, ?_, ?_, hcap⟩
  · intro ij kl h
    apply point_injective C hV hC p
    simpa only [prescribedPoint_eq] using h
  · intro ij
    rw [prescribedPoint_eq]
    exact point_ne_center C hV hC p hb ij
  · intro i
    change lineThrough (slot C hV hC p i).1 p ∉ constituentLines C.merged
    rw [← slot_line_eq C hV hC p i]
    exact (hV.2 _).2.1

theorem prescribedDesignated_eq :
    prescribedDesignated (pattern C hV hC p) (assignment C hV hC p)
      (bits C hV hC p) C.merged = C.designatedAt p := by
  have he : prescribedPoint (pattern C hV hC p) (assignment C hV hC p)
      (bits C hV hC p) C.merged = point C hV hC p :=
    funext (prescribedPoint_eq C hV hC p)
  unfold prescribedDesignated
  rw [he]
  exact point_image C hV hC p

theorem prescribedPartners_eq :
    prescribedPartners (pattern C hV hC p) (assignment C hV hC p)
      (bits C hV hC p) p C.merged = C.partnerSet p := by
  unfold prescribedPartners Configuration.partnerSet
  rw [prescribedDesignated_eq]

theorem target_line_image :
    (Finset.univ.image (fun i => lineThrough ((assignment C hV hC p).1 i) p)) =
      C.splitLinesAt p := by
  ext l
  constructor
  · intro hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
    change lineThrough (slot C hV hC p i).1 p ∈ C.splitLinesAt p
    rw [← slot_line_eq C hV hC p i]
    exact Finset.mem_filter.mpr ⟨ConfigurationStructure.choice_line_mem_split C _,
      slot_onLine C hV hC p i⟩
  · intro hl
    obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hl
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨i, rfl⟩ := exists_slot C hV hC p hp
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (slot_line_eq C hV hC p i).symm⟩

theorem allowedPiece_iff (A : LocalPiece F) :
    AllowedPiece (assignment C hV hC p) p C.merged A ↔ C.AllowedLocalPiece p A := by
  rcases A with U | l | d
  · rfl
  · change l ∉ (Finset.univ.image (fun i => lineThrough ((assignment C hV hC p).1 i) p)) ∪
      constituentLines C.merged ↔ l ∉ C.splitLinesAt p ∪ constituentLines C.merged
    rw [target_line_image]
  · rfl

theorem badCover_iff :
    BadCover (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) p C.merged ↔
      ∃ A : Finset (LocalPiece F), A.card ≤ C.splitMultiplicity p - 1 ∧
        (∀ a ∈ A, C.AllowedLocalPiece p a) ∧
        C.designatedAt p ⊆ C.partnerSet p ∪ A.biUnion C.localPiecePoints := by
  unfold BadCover
  rw [prescribedDesignated_eq, prescribedPartners_eq]
  simp only [allowedPiece_iff]
  rfl

end
end Balanced.Local.ConfigurationPattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTupleReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ) (σ : Equiv.Perm (Fin b))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem eligible_reindex (a : DirectionAssignment F b κ) :
    Eligible (P.reindex σ) (reindexAssignment σ a) ↔ Eligible P a := by
  constructor
  · rintro ⟨ht, hg, he⟩
    refine ⟨?_, hg, ?_⟩
    · intro i j hij
      have h := ht (a₁ := σ.symm i) (a₂ := σ.symm j) (by simpa [reindexAssignment] using hij)
      exact σ.symm.injective h
    · intro i j
      simpa [reindexAssignment, EqualityPattern.reindex] using he (σ.symm i) j
  · rintro ⟨ht, hg, he⟩
    exact ⟨ht.comp σ.injective, hg, fun i j => he (σ i) j⟩

omit [Fintype F] [DecidableEq F] in
theorem prescribedPoint_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) (ij : Fin b × Fin 4) :
    prescribedPoint (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) M ij =
      prescribedPoint P a bits M (reindexPositions σ ij) := rfl

omit [Fintype F] [DecidableEq F] in
theorem aligned_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Aligned (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      Aligned P a bits p M := by
  constructor
  · intro h ij
    have hh := h ((reindexPositions σ).symm ij)
    rw [prescribedPoint_reindex, Equiv.apply_symm_apply] at hh
    simpa [reindexPositions, reindexAssignment] using hh
  · intro h ij
    exact h (reindexPositions σ ij)

theorem admissible_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Admissible (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      Admissible P a bits p M := by
  constructor
  · rintro ⟨ha, hi, hp, hc, hm⟩
    refine ⟨(aligned_reindex P σ a bits p M).mp ha, ?_, ?_, ?_, hm⟩
    · intro ij kl h
      have hh := hi (a₁ := (reindexPositions σ).symm ij)
        (a₂ := (reindexPositions σ).symm kl) (by
          simpa only [prescribedPoint_reindex, Equiv.apply_symm_apply] using h)
      exact (reindexPositions σ).symm.injective hh
    · intro ij
      simpa only [prescribedPoint_reindex, Equiv.apply_symm_apply]
        using hp ((reindexPositions σ).symm ij)
    · intro i
      simpa [reindexAssignment] using hc (σ.symm i)
  · rintro ⟨ha, hi, hp, hc, hm⟩
    refine ⟨(aligned_reindex P σ a bits p M).mpr ha,
      hi.comp (reindexPositions σ).injective, ?_, ?_, hm⟩
    · intro ij
      exact hp (reindexPositions σ ij)
    · intro i
      exact hc (σ i)

omit [Fintype F] in
theorem prescribedDesignated_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) :
    prescribedDesignated (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) M =
      prescribedDesignated P a bits M := by
  unfold prescribedDesignated
  change Finset.univ.image (prescribedPoint P a bits M ∘ reindexPositions σ) = _
  rw [← Finset.image_image, Finset.image_univ_equiv]

theorem prescribedPartners_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    prescribedPartners (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M =
      prescribedPartners P a bits p M := by
  unfold prescribedPartners
  rw [prescribedDesignated_reindex]

omit P [Fintype F] in
theorem targetLines_reindex (a : DirectionAssignment F b κ) (p : Point F) :
    Finset.univ.image (fun i => lineThrough ((reindexAssignment σ a).1 i) p) =
      Finset.univ.image (fun i => lineThrough (a.1 i) p) := by
  change Finset.univ.image ((fun i => lineThrough (a.1 i) p) ∘ σ) = _
  rw [← Finset.image_image, Finset.image_univ_equiv]

omit P in
theorem allowedPiece_reindex (a : DirectionAssignment F b κ)
    (p : Point F) (M : MergedPairs F) (x : LocalPiece F) :
    AllowedPiece (reindexAssignment σ a) p M x ↔ AllowedPiece a p M x := by
  rcases x with U | l | d
  · rfl
  · change l ∉ _ ∪ constituentLines M ↔ l ∉ _ ∪ constituentLines M
    rw [targetLines_reindex]
  · rfl

theorem badCover_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    BadCover (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      BadCover P a bits p M := by
  simp only [BadCover, prescribedDesignated_reindex, prescribedPartners_reindex,
    allowedPiece_reindex]

theorem admissibleBadCover_reindex (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    AdmissibleBadCover (P.reindex σ) (reindexAssignment σ a) (reindexBits σ bits) p M ↔
      AdmissibleBadCover P a bits p M := by
  simp only [AdmissibleBadCover, admissible_reindex, badCover_reindex]

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_OrderedEventCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OrderedEventCounting

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in

theorem reorder_injective {b : ℕ} (f : Fin b → ι) (hf : Function.Injective f) :
    Function.Injective (fun σ : Equiv.Perm (Fin b) => f ∘ σ) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  exact hf (congrFun h i)

omit [Fintype ι] in

theorem factorial_le_sum_encoded_orders {J : Type*} [Fintype J] {b : ℕ}
    (R : J → Prop) (read : J → Fin b → ι)
    (f : Fin b → ι) (hf : Function.Injective f)
    (hR : ∀ σ : Equiv.Perm (Fin b), ∃ j, R j ∧ read j = f ∘ σ) :
    (b.factorial : ℝ) ≤ ∑ j, if R j then (1 : ℝ) else 0 := by
  classical
  choose pick hpick hread using hR
  let lift : Equiv.Perm (Fin b) → {j // R j} := fun σ => ⟨pick σ, hpick σ⟩
  have hi : Function.Injective lift := by
    intro σ τ h
    apply reorder_injective f hf
    change f ∘ σ = f ∘ τ
    rw [← hread σ, ← hread τ]
    exact congrArg read (congrArg Subtype.val h)
  have hc : b.factorial ≤ Fintype.card {j // R j} := by
    simpa only [Fintype.card_perm, Fintype.card_fin] using
      Fintype.card_le_of_injective lift hi
  have he : (Fintype.card {j // R j} : ℝ) =
      ∑ j, if R j then (1 : ℝ) else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [← he]
  exact_mod_cast hc

omit [Fintype ι] in

theorem weighted_encoded_order_bound {Ω J : Type*} [Fintype Ω] [Fintype J] {b : ℕ}
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (E : Ω → Prop)
    (R : J → Ω → Prop) (read : J → Fin b → ι)
    (hcover : ∀ ω, 0 < w ω → E ω →
      ∃ f : Fin b → ι, Function.Injective f ∧
        ∀ σ : Equiv.Perm (Fin b), ∃ j, R j ω ∧ read j = f ∘ σ) :
    (∑ ω, if E ω then w ω else 0) ≤
      (∑ j, ∑ ω, if R j ω then w ω else 0) / (b.factorial : ℝ) := by
  classical
  have hb : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  apply (le_div_iff₀ hb).mpr
  rw [Finset.sum_mul, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < w ω
  · by_cases he : E ω
    · obtain ⟨f, hf, hR⟩ := hcover ω hp he
      have hcount := factorial_le_sum_encoded_orders (fun j => R j ω) read f hf hR
      calc
        (if E ω then w ω else 0) * (b.factorial : ℝ) =
            (b.factorial : ℝ) * w ω := by rw [ite_eq_left he, mul_comm]
        _ ≤ (∑ j, if R j ω then (1 : ℝ) else 0) * w ω :=
          mul_le_mul_of_nonneg_right hcount (hw ω)
        _ = ∑ j, if R j ω then w ω else 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
    · simp only [ite_eq_right he, zero_mul]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp_all)
  · have hz : w ω = 0 := le_antisymm (le_of_not_gt hp) (hw ω)
    simp only [hz, ite_self, zero_mul, Finset.sum_const_zero, le_refl]

end
end Balanced.OrderedEventCounting

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_LocalOrderedPencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem bad_local_cover_all_orders (C : Configuration F)
    (hV : C.Valid) (hC : C.Compatible) (p : Point F)
    (hcap : ∀ x, constituentMultiplicity C.merged x ≤ logBudget F)
    {b κ : ℕ} (hb : C.splitMultiplicity p = b) (hb2 : 2 ≤ b)
    (hk : reuseCount C p = κ) (hbad : BadLocalCoverAt b p C) :
    ∃ f : Fin b → Slot F, Function.Injective f ∧
      ∀ σ : Equiv.Perm (Fin b), OrderedBadPencil b κ p (f ∘ σ) C := by
  subst b
  subst κ
  refine ⟨ConfigurationPattern.slot C hV hC p,
    ConfigurationPattern.slot_injective C hV hC p, ?_⟩
  intro σ
  let P := ConfigurationPattern.pattern C hV hC p
  let a := ConfigurationPattern.assignment C hV hC p
  let bits := ConfigurationPattern.bits C hV hC p
  have he : Eligible P a := ConfigurationPattern.assignment_eligible C hV hC p
  have ha : AdmissibleBadCover P a bits p C.merged :=
    ⟨ConfigurationPattern.admissible C hV hC p hb2 hcap,
      (ConfigurationPattern.badCover_iff C hV hC p).mpr hbad⟩
  refine ⟨(ConfigurationPattern.slot_injective C hV hC p).comp σ.injective,
    P.reindex σ, reindexAssignment σ a, reindexBits σ bits,
    (eligible_reindex P σ a).mpr he,
    (admissibleBadCover_reindex P σ a bits p C.merged).mpr ha, ?_⟩
  intro i
  refine ⟨rfl, ?_, ?_⟩
  · exact (ConfigurationPattern.prescribedTuple_eq C hV hC p (σ i)).symm
  · exact ConfigurationPattern.slot_line_eq C hV hC p (σ i)

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_UnusedOffsetIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical

namespace Balanced.UnusedOffsetIncidence

theorem probability_eq_pmf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    probability E = ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal := by
  classical
  rw [PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp [probability, ENNReal.toReal_div]

theorem probability_mono {Ω : Type*} [Fintype Ω] {E G : Ω → Prop}
    (h : ∀ ω, E ω → G ω) : probability E ≤ probability G := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro ω hω
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩

theorem probability_exists_le {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (E : ι → Ω → Prop) :
    probability (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, probability (E i) := by
  classical
  have heq : Finset.univ.filter (fun ω => ∃ i ∈ s, E i ω) =
      s.biUnion (fun i => Finset.univ.filter (E i)) := by
    ext ω
    simp
  have hb : (Finset.univ.filter (fun ω => ∃ i ∈ s, E i ω)).card ≤
      ∑ i ∈ s, (Finset.univ.filter (E i)).card := by
    rw [heq]
    exact Finset.card_biUnion_le
  unfold probability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hc := (Nat.cast_le (α := ℝ)).mpr hb
  push_cast at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1
  ext ω
  simp

theorem probability_exists_fintype_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (E : ι → Ω → Prop) :
    probability (fun ω => ∃ i, E i ω) ≤ ∑ i, probability (E i) := by
  simpa using probability_exists_le (Finset.univ : Finset ι) E

theorem probability_or_le {Ω : Type*} [Fintype Ω] (E G : Ω → Prop) :
    probability (fun ω => E ω ∨ G ω) ≤ probability E + probability G := by
  simpa [Bool.exists_bool, Fintype.sum_bool, add_comm, or_comm] using
    probability_exists_fintype_le (fun s : Bool => if s then E else G)

theorem probability_union3_bound {Ω : Type*} [Fintype Ω]
    {E A B C : Ω → Prop} {a b c : ℝ}
    (h : ∀ ω, E ω → A ω ∨ B ω ∨ C ω)
    (hA : probability A ≤ a) (hB : probability B ≤ b)
    (hC : probability C ≤ c) : probability E ≤ a + (b + c) := by
  have h₁ := probability_mono h
  have h₂ := probability_or_le A (fun ω => B ω ∨ C ω)
  have h₃ := probability_or_le B C
  exact h₁.trans (h₂.trans (add_le_add hA (h₃.trans (add_le_add hB hC))))

theorem uniform_map_eval {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [Nonempty A] (i : ι) :
    (PMF.uniformOfFintype (ι → A)).map (fun o => o i) =
      PMF.uniformOfFintype A := by
  classical
  have h := congrArg (fun p => p.map Prod.fst)
    (TupleAlignment.uniform_map_equiv (Equiv.funSplitAt i A))
  rw [PMF.map_comp, TupleAlignment.uniform_map_fst] at h
  exact h

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem pair_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (s : Bool) (a b : F) :
    probability (fun o : ι → Bool → F => o i s = a ∧ o i (!s) = b) =
      1 / (Fintype.card F : ℝ) ^ 2 := by
  classical
  let v : Bool → F := fun t => if t = s then a else b
  have heq : {o : ι → Bool → F | o i s = a ∧ o i (!s) = b} =
      (fun o : ι → Bool → F => o i) ⁻¹' {v} := by
    ext o
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, hb⟩
      funext t
      cases s <;> cases t <;> simpa [v] using (by assumption)
    · intro h
      constructor
      · simpa [v] using congrFun h s
      · simpa [v] using congrFun h (!s)
  rw [probability_eq_pmf, heq, ← PMF.toOuterMeasure_map_apply,
    uniform_map_eval, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply]
  simp [ENNReal.toReal_inv, one_div]

omit [Fintype F] in
theorem Noncollinear.pairwise_ne {x y z : Point F} (h : Noncollinear x y z) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨?_, ?_, ?_⟩
  · intro hxy
    subst y
    exact h ⟨joiningLine x z, onLine_joiningLine_left x z,
      onLine_joiningLine_left x z, onLine_joiningLine_right x z⟩
  · intro hxz
    subst z
    exact h ⟨joiningLine x y, onLine_joiningLine_left x y,
      onLine_joiningLine_right x y, onLine_joiningLine_left x y⟩
  · intro hyz
    subst z
    exact h ⟨joiningLine x y, onLine_joiningLine_left x y,
      onLine_joiningLine_right x y, onLine_joiningLine_right x y⟩

omit [Fintype F] in
private theorem direction_eq_joining (D : Finset (Direction F))
    (o : Offsets D) (d : D) (s : Bool) (x y : Point F) (hne : x ≠ y)
    (hx : OnLine x (constituent D o d s))
    (hy : OnLine y (constituent D o d s)) : d.1 = (joiningLine x y).1 := by
  exact congrArg Prod.fst (eq_of_two_common_points x y hne
    (constituent D o d s) (joiningLine x y) hx hy
    (onLine_joiningLine_left x y) (onLine_joiningLine_right x y))

theorem pairCover_probability_le (D : Finset (Direction F))
    (x y z : Point F) (hne : x ≠ y) (s : Bool) :
    probability (PairCover D x y z s) ≤ 1 / (Fintype.card F : ℝ) ^ 2 := by
  classical
  by_cases hd : (joiningLine x y).1 ∈ D
  · let d₀ : D := ⟨(joiningLine x y).1, hd⟩
    calc
      probability (PairCover D x y z s) ≤
          probability (fun o : Offsets D =>
            o d₀ s = lineEval d₀.1 x ∧ o d₀ (!s) = lineEval d₀.1 z) := by
        apply probability_mono
        rintro o ⟨d, hx, hy, hz⟩
        have hdd : d = d₀ := Subtype.ext (direction_eq_joining D o d s x y hne hx hy)
        subst d
        exact ⟨hx.symm, hz.symm⟩
      _ = _ := pair_probability d₀ s _ _
  · have hzero : probability (PairCover D x y z s) ≤ probability (fun _ : Offsets D => False) := by
      apply probability_mono
      rintro o ⟨d, hx, hy, _⟩
      exact hd ((direction_eq_joining D o d s x y hne hx hy) ▸ d.2)
    have hfalse : probability (fun _ : Offsets D => False) = 0 := by
      simp [probability]
    rw [hfalse] at hzero
    exact hzero.trans (div_nonneg zero_le_one (sq_nonneg (Fintype.card F : ℝ)))

theorem twoOneCover_probability_le (D : Finset (Direction F))
    (x y z : Point F) (hne : x ≠ y) :
    probability (TwoOneCover D x y z) ≤ 2 / (Fintype.card F : ℝ) ^ 2 := by
  calc
    probability (TwoOneCover D x y z) ≤ ∑ s : Bool, probability (PairCover D x y z s) :=
      probability_exists_fintype_le _
    _ ≤ ∑ _s : Bool, 1 / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun s _ => pairCover_probability_le D x y z hne s)
    _ = _ := by simp; ring

omit [Fintype F] [DecidableEq F] in
theorem tripleCovered_split (D : Finset (Direction F))
    (x y z : Point F) (hn : Noncollinear x y z) (o : Offsets D)
    (h : TripleCovered D x y z o) :
    TwoOneCover D x y z o ∨ TwoOneCover D x z y o ∨ TwoOneCover D y z x o := by
  obtain ⟨d, ⟨sx, hx⟩, ⟨sy, hy⟩, ⟨sz, hz⟩⟩ := h
  cases sx <;> cases sy <;> cases sz
  · exact (hn ⟨constituent D o d false, hx, hy, hz⟩).elim
  · exact Or.inl ⟨false, d, hx, hy, hz⟩
  · exact Or.inr (Or.inl ⟨false, d, hx, hz, hy⟩)
  · exact Or.inr (Or.inr ⟨true, d, hy, hz, hx⟩)
  · exact Or.inr (Or.inr ⟨false, d, hy, hz, hx⟩)
  · exact Or.inr (Or.inl ⟨true, d, hx, hz, hy⟩)
  · exact Or.inl ⟨true, d, hx, hy, hz⟩
  · exact (hn ⟨constituent D o d true, hx, hy, hz⟩).elim

theorem tripleCovered_probability_le (D : Finset (Direction F))
    (x y z : Point F) (hn : Noncollinear x y z) :
    probability (TripleCovered D x y z) ≤ 6 / (Fintype.card F : ℝ) ^ 2 := by
  obtain ⟨hxy, hxz, hyz⟩ := hn.pairwise_ne
  have h := probability_union3_bound (tripleCovered_split D x y z hn)
    (twoOneCover_probability_le D x y z hxy)
    (twoOneCover_probability_le D x z y hxz)
    (twoOneCover_probability_le D y z x hyz)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem noncollinearTripleInPair_probability_le (D : Finset (Direction F))
    (P : Finset (Point F)) :
    probability (NoncollinearTripleInPair D P) ≤
      6 * (P.card : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  have hsingle (x y z : Point F) :
      probability (fun o : Offsets D => Noncollinear x y z ∧ TripleCovered D x y z o) ≤
        6 / (Fintype.card F : ℝ) ^ 2 := by
    by_cases hn : Noncollinear x y z
    · exact (probability_mono (fun _ h => h.2)).trans
        (tripleCovered_probability_le D x y z hn)
    · simp only [hn, false_and, probability, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero, zero_div]
      exact div_nonneg (by norm_num) (sq_nonneg _)
  calc
    probability (NoncollinearTripleInPair D P) ≤
        ∑ x ∈ P, probability (fun o : Offsets D => ∃ y ∈ P, ∃ z ∈ P,
          Noncollinear x y z ∧ TripleCovered D x y z o) := probability_exists_le P _
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, probability (fun o : Offsets D => ∃ z ∈ P,
          Noncollinear x y z ∧ TripleCovered D x y z o) :=
      Finset.sum_le_sum (fun x _ => probability_exists_le P _)
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, ∑ z ∈ P, probability (fun o : Offsets D =>
          Noncollinear x y z ∧ TripleCovered D x y z o) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => probability_exists_le P _))
    _ ≤ ∑ _x ∈ P, ∑ _y ∈ P, ∑ _z ∈ P, 6 / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        Finset.sum_le_sum (fun z _ => hsingle x y z)))
    _ = _ := by simp; ring

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignmentNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

open AlignedListProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem alignmentNormalization_proof : AlignmentNormalizationResult.{u} := by
  intro F _ _ _ b κ _ _ hκ P a ha bits p
  exact alignment_probability P hκ a ha bits p

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformConditionalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.UniformConditionalProduct

open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_filter_split {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B] [Nonempty X] [Nonempty B]
    (e : X ≃ A × B) (E : A → Prop) [Nonempty {a : A // E a}]
    (h : ∃ x ∈ {x : X | E (e x).1},
      x ∈ (PMF.uniformOfFintype X).support) :
    (PMF.uniformOfFintype X).filter {x | E (e x).1} h =
      (PMF.uniformOfFintype ({a : A // E a} × B)).map
        (fun z => e.symm (z.1.1, z.2)) := by
  let : Nonempty {x : X // E (e x).1} :=
    ⟨(conditionedSplitEquiv e E).symm (Classical.choice inferInstance)⟩
  let : Nonempty ({x : X | E (e x).1} : Set X) :=
    ⟨(conditionedSplitEquiv e E).symm (Classical.choice inferInstance)⟩
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype {x : X // E (e x).1}).map Subtype.val = _
  have hlaw := uniform_map_equiv (conditionedSplitEquiv e E).symm
  rw [← hlaw, PMF.map_comp]
  rfl

theorem uniform_product_eq_bind {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).map (fun b => (a, b))) := by
  classical
  ext z
  rcases z with ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_fintype, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv,
    ite_and]

end
end Balanced.UniformConditionalProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUnusedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedUnused

open UniformConditionalProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem alignedLaw_eq_uniform_pair {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    letI := usedAligned_nonempty P hκ a ha bits p
    alignedLaw P hκ a ha bits p =
      (PMF.uniformOfFintype
        ({u : UsedArray P a // usedAligned P a bits p u} × UnusedArray P a)).map
        (fun z => (split P a).symm (z.1.1, z.2)) := by
  let := usedAligned_nonempty P hκ a ha bits p
  have hs : ∃ M ∈ {M | usedAligned P a bits p (split P a M).1},
      M ∈ (PMF.uniformOfFintype (MergedPairs F)).support := by
    obtain ⟨M, hM, hs⟩ := alignment_supported P hκ a ha bits p
    exact ⟨M, (aligned_iff_usedAligned P a bits p M).mp hM, hs⟩
  have h := uniform_filter_split (split P a) (usedAligned P a bits p) hs
  simpa only [← aligned_iff_usedAligned, alignedLaw] using h

theorem alignedLaw_eq_bind {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    alignedLaw P hκ a ha bits p =
      (usedLaw P hκ a ha bits p).bind (fun u =>
        (PMF.uniformOfFintype (UnusedArray P a)).map
          (fun v => (split P a).symm (u, v))) := by
  let := usedAligned_nonempty P hκ a ha bits p
  rw [alignedLaw_eq_uniform_pair, uniform_product_eq_bind, PMF.map_bind]
  unfold usedLaw
  rw [PMF.bind_map]
  congr 1
  funext u
  rw [PMF.map_comp]
  rfl

theorem conditionedOffsetProbability_eq_alignedLaw {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((alignedLaw P hκ a ha bits p).toOuterMeasure {M | E M}).toReal := by
  let A : MergedPairs F → Prop := Aligned P a bits p
  let : Nonempty {M : MergedPairs F // A M} := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  let : Nonempty ({M : MergedPairs F | A M} : Set (MergedPairs F)) := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  have hcard (H : MergedPairs F → Prop) :
      offsetProbability H = (Fintype.card {M // H M} : ℝ) / Fintype.card (MergedPairs F) := by
    unfold offsetProbability
    rw [← FiniteUniformFibers.probability_eq_sum H,
      PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
    simp [Fintype.card_subtype]
  have hnum : Fintype.card {M : {M : MergedPairs F // A M} // E M} =
      Fintype.card {M : MergedPairs F // A M ∧ E M} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter A E)
  change offsetProbability (fun M => A M ∧ E M) / offsetProbability A = _
  rw [hcard, hcard]
  change _ = (((PMF.uniformOfFintype (MergedPairs F)).filter {M | A M}
    (alignment_supported P hκ a ha bits p)).toOuterMeasure {M | E M}).toReal
  rw [Balanced.uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  change _ = (Fintype.card {M : {M : MergedPairs F // A M} // E M} : ℝ) /
    Fintype.card {M : MergedPairs F // A M}
  rw [hnum]
  have htotal : (Fintype.card (MergedPairs F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  have hcardinst (f g : Fintype {M : MergedPairs F // A M ∧ E M}) :
      @Fintype.card _ f = @Fintype.card _ g := by
    cases Subsingleton.elim f g
    rfl
  exact congrArg (Nat.cast : ℕ → ℝ) (hcardinst _ _)

end
end Balanced.Local.AlignedUnused

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrescribedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M : MergedPairs F}

omit [Fintype F] [DecidableEq F] in

theorem exists_prescribedPoint_on_constituent (hE : Eligible P a)
    (c : Fin (4 * b - κ)) (s : Bool) :
    ∃ ij : Fin b × Fin 4,
      OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s) := by
  obtain ⟨⟨i, j⟩, hc⟩ := P.everyClass c
  change P.classOf i j = c at hc
  by_cases hs : s = bits i j
  · refine ⟨(i, j), ?_⟩
    simpa only [hc, hs] using prescribedPoint_on_left (M := M) hE i j
  · have hs' : s = !(bits i j) := by
      cases s <;> cases h : bits i j <;> simp_all
    refine ⟨(i, j + 3), ?_⟩
    have hj : (j + 3) + 1 = j := by fin_cases j <;> decide
    simpa only [hj, hc, hs'] using prescribedPoint_on_right (M := M) hE i (j + 3)

theorem not_onLine_used_constituent (hE : Eligible P a)
    (hA : Admissible P a bits p M) (c : Fin (4 * b - κ)) (s : Bool) :
    ¬ OnLine p (constituent M (a.2 c) s) := by
  obtain ⟨⟨i, j⟩, hpoint⟩ := exists_prescribedPoint_on_constituent hE c s
  intro hp
  have hline : constituent M (a.2 c) s ≠ lineThrough (a.1 i) p := by
    intro heq
    exact hA.2.2.2.1 i (heq ▸
      Finset.mem_image.mpr ⟨(a.2 c, s), Finset.mem_univ _, rfl⟩)
  exact hA.2.2.1 (i, j)
    (common_point_eq_of_lines_ne _ _ hline _ p hpoint (hA.1 (i, j)) hp
      (onLine_lineThrough _ _))

theorem direction_unused_of_onLine (hE : Eligible P a)
    (hA : Admissible P a bits p M) {d : Direction F} {s : Bool}
    (hp : OnLine p (constituent M d s)) :
    d ∉ Finset.univ.image a.2 := by
  intro hd
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
  exact not_onLine_used_constituent hE hA c s hp

theorem mem_prescribedPartners_iff_unused (hE : Eligible P a)
    (hA : Admissible P a bits p M) (x : Point F) :
    x ∈ prescribedPartners P a bits p M ↔
      x ∈ prescribedDesignated P a bits M ∧
      ∃ ds : Direction F × Bool,
        ds.1 ∉ Finset.univ.image a.2 ∧
        OnLine p (constituent M ds.1 ds.2) ∧
        OnLine x (constituent M ds.1 (!ds.2)) := by
  constructor
  · intro hx
    obtain ⟨hF, ds, hp, hx⟩ := Finset.mem_filter.mp hx
    exact ⟨hF, ds, direction_unused_of_onLine hE hA hp, hp, hx⟩
  · rintro ⟨hF, ds, _, hp, hx⟩
    exact Finset.mem_filter.mpr ⟨hF, ds, hp, hx⟩

end
end Balanced.Local.PrescribedGeometry

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFourEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem classUseCount_pos (P : EqualityPattern b κ) (c : Fin (4 * b - κ)) :
    0 < classUseCount P c := by
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass c
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hij⟩⟩⟩

theorem sum_classUseCount (P : EqualityPattern b κ) :
    ∑ c, classUseCount P c = 4 * b := by
  simp only [classUseCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hi (i : Fin b) :
      (∑ c : Fin (4 * b - κ), if ∃ j, P.classOf i j = c then 1 else 0) = 4 := by
    have hs : (Finset.univ.filter (fun c => ∃ j, P.classOf i j = c)) =
        Finset.univ.image (P.classOf i) := by
      ext c
      simp
    have hc := Finset.card_image_of_injective (Finset.univ : Finset (Fin 4))
      (P.withinTuple i)
    rw [← hs] at hc
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  simp_rw [hi]
  simp [Nat.mul_comm]

theorem sum_class_excess (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    ∑ c, (classUseCount P c - 1) = κ := by
  rw [Finset.sum_tsub_distrib]
  · rw [sum_classUseCount]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    omega
  · intro c _
    exact classUseCount_pos P c

omit [Field F] [Fintype F] in
theorem usingTuples_eq_empty_of_not_used (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (d : Direction F)
    (hd : d ∉ usedDirections a) : usingTuples P a d = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
  exact hd (Finset.mem_image.mpr ⟨P.classOf i j, Finset.mem_univ _, hj⟩)

omit [Field F] in

theorem sum_direction_excess (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (hκ : κ ≤ 4 * b) :
    ∑ d : Direction F, ((usingTuples P a d).card - 1) = κ := by
  have hrestrict :
      (∑ d : Direction F, ((usingTuples P a d).card - 1)) =
        ∑ d ∈ usedDirections a, ((usingTuples P a d).card - 1) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro d _ hd
    simp [usingTuples_eq_empty_of_not_used P a d hd]
  rw [hrestrict, usedDirections, Finset.sum_image]
  · simp_rw [usingTuples_class_card P a ha]
    exact sum_class_excess P hκ
  · intro c _ e _ hce
    exact ha hce

theorem prescribedDesignated_card (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M) :
    (prescribedDesignated P a bits M).card = 4 * b := by
  rw [prescribedDesignated, Finset.card_image_of_injective _ hadm.2.1]
  simp [Nat.mul_comm]

theorem tuplePoints_subset_target (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M) (i : Fin b) :
    tuplePoints P a bits M i ⊆ linePoints (lineThrough (a.1 i) p) := by
  intro x hx
  obtain ⟨j, rfl⟩ := (mem_tuplePoints P a bits M i x).mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hal (i,j)⟩

theorem tuplePoints_inter_merged_card_le_two (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M)
    (i : Fin b) (d : Direction F) :
    (tuplePoints P a bits M i ∩ mergedPoints M d).card ≤ 2 := by
  have hne (s : Bool) : lineThrough (a.1 i) p ≠ constituent M d s := by
    intro he
    apply hadm.2.2.2.1 i
    rw [he]
    exact Finset.mem_image.mpr ⟨(d,s), Finset.mem_univ _, rfl⟩
  have hone (s : Bool) :
      (tuplePoints P a bits M i ∩ linePoints (constituent M d s)).card ≤ 1 := by
    apply (Finset.card_le_card ?_).trans
      (linePoints_inter_card_le_one _ _ (hne s))
    exact Finset.inter_subset_inter_right
      (tuplePoints_subset_target P a bits p M hadm.1 i)
  rw [mergedPoints, Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (by have h0 := hone false; have h1 := hone true; omega)

theorem line_inter_merged_card_le_two (M : MergedPairs F) (d : Direction F)
    (l : Line F) (hne : ∀ s, l ≠ constituent M d s) :
    (linePoints l ∩ mergedPoints M d).card ≤ 2 := by
  rw [mergedPoints, Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (by
    have h0 := linePoints_inter_card_le_one l _ (hne false)
    have h1 := linePoints_inter_card_le_one l _ (hne true)
    omega)

theorem used_pair_trace_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M)
    (hno : ¬ UsedPairExtra P a bits M) (d : Direction F)
    (hd : d ∈ usedDirections a) :
    (prescribedDesignated P a bits M ∩ mergedPoints M d).card ≤
      2 * (usingTuples P a d).card := by
  have hsub : prescribedDesignated P a bits M ∩ mergedPoints M d ⊆
      (usingTuples P a d).biUnion (fun i =>
        tuplePoints P a bits M i ∩ mergedPoints M d) := by
    intro x hx
    obtain ⟨⟨i,j⟩, _, hpoint⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
    have hxt : x ∈ tuplePoints P a bits M i :=
      (mem_tuplePoints P a bits M i x).mpr ⟨j, hpoint⟩
    have hi : i ∈ usingTuples P a d := by
      by_contra hn
      exact hno ⟨d, hd, i, hn, x, hxt, (Finset.mem_inter.mp hx).2⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr
      ⟨hxt, (Finset.mem_inter.mp hx).2⟩⟩
  exact (Finset.card_le_card hsub).trans (by
    have h := Finset.card_biUnion_le_card_mul (usingTuples P a d)
      (fun i => tuplePoints P a bits M i ∩ mergedPoints M d) 2
      (fun i _ => tuplePoints_inter_merged_card_le_two P a bits p M hadm i d)
    simpa [Nat.mul_comm] using h)

theorem unused_pair_trace_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hadm : Admissible P a bits p M)
    (hcol : ¬ ForbiddenCollinearTriple P a bits p M)
    (hnoncol : ¬ UnusedNoncollinearTriple P a bits M)
    (d : Direction F) (hd : d ∉ usedDirections a) :
    (prescribedDesignated P a bits M ∩ mergedPoints M d).card ≤ 2 := by
  by_contra hbig
  have hthree : 3 ≤ (prescribedDesignated P a bits M ∩ mergedPoints M d).card := by omega
  obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq hthree
  have hline : ∃ l : Line F, U ⊆ linePoints l := by
    by_contra hn
    exact hnoncol ⟨d, hd, U, hcard, hU, hn⟩
  obtain ⟨l, hl⟩ := hline
  have htrace : 3 ≤ (prescribedDesignated P a bits M ∩ linePoints l).card := by
    rw [← hcard]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hU hx)).1, hl hx⟩
  have heq : ∃ s, l = constituent M d s := by
    by_contra hn
    have hne : ∀ s, l ≠ constituent M d s := by simpa using hn
    have hle := line_inter_merged_card_le_two M d l hne
    have hcap : U.card ≤ (linePoints l ∩ mergedPoints M d).card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_inter.mpr ⟨hl hx, (Finset.mem_inter.mp (hU hx)).2⟩
    omega
  obtain ⟨s, rfl⟩ := heq
  apply hcol
  refine ⟨constituent M d s, ?_, ?_, htrace⟩
  · intro i he
    apply hadm.2.2.2.1 i
    rw [← he]
    exact Finset.mem_image.mpr ⟨(d,s), Finset.mem_univ _, rfl⟩
  · intro c t he
    apply hd
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _,
      (congrArg Prod.fst he).symm⟩

theorem precoverage_iff_unused (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (ha : Eligible P a) (hadm : Admissible P a bits p M) :
    Precoverage P a bits p M ↔ UnusedPrecoverage P a bits p M := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hF, ⟨d,s⟩, hd, hp, hpoint⟩ :=
      (PrescribedGeometry.mem_prescribedPartners_iff_unused ha hadm x).mp hx
    exact ⟨d, hd, s, hp, x, hF, hpoint⟩
  · rintro ⟨d, hd, s, hp, x, hF, hpoint⟩
    exact ⟨x, (PrescribedGeometry.mem_prescribedPartners_iff_unused ha hadm x).mpr
      ⟨hF, (d,s), hd, hp, hpoint⟩⟩

omit [Field F] in
theorem sum_extraCapacity (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (hκ : κ ≤ 4 * b) :
    ∑ x : LocalPiece F, extraCapacity P a x = 2 * κ := by
  simp only [Fintype.sum_sum_type, extraCapacity, Finset.sum_const_zero, zero_add]
  rw [← Finset.mul_sum, sum_direction_excess P a ha hκ]

theorem allowed_piece_trace_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (hused : ¬ UsedPairExtra P a bits M)
    (hcol : ¬ ForbiddenCollinearTriple P a bits p M)
    (hnoncol : ¬ UnusedNoncollinearTriple P a bits M)
    (x : LocalPiece F) (hx : AllowedPiece a p M x) :
    (prescribedDesignated P a bits M ∩ piecePoints M x).card ≤
      2 + extraCapacity P a x := by
  rcases x with U | l | d
  · exact (Finset.card_le_card Finset.inter_subset_right).trans hx
  · change (prescribedDesignated P a bits M ∩ linePoints l).card ≤ 2
    by_contra hbig
    apply hcol
    refine ⟨l, ?_, ?_, by omega⟩
    · intro i he
      apply hx
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩
    · intro c s he
      apply hx
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a.2 c,s), Finset.mem_univ _, he.symm⟩
  · change (prescribedDesignated P a bits M ∩ mergedPoints M d).card ≤
      2 + 2 * ((usingTuples P a d).card - 1)
    by_cases hd : d ∈ usedDirections a
    · have hle := used_pair_trace_le P a bits p M hadm hused d hd
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
      have hpos : 0 < (usingTuples P a (a.2 c)).card := by
        rw [usingTuples_class_card P a ha.2.1]
        exact classUseCount_pos P c
      omega
    · have hle := unused_pair_trace_le P a bits p M hadm hcol hnoncol d hd
      omega

theorem cover_budget_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (hκ : κ ≤ 4 * b) (hcover : BadCover P a bits p M)
    (hpre : ¬ Precoverage P a bits p M) (hused : ¬ UsedPairExtra P a bits M)
    (hcol : ¬ ForbiddenCollinearTriple P a bits p M)
    (hnoncol : ¬ UnusedNoncollinearTriple P a bits M) :
    4 * b ≤ 2 * (b - 1) + 2 * κ := by
  obtain ⟨A, hA, hallowed, hcover⟩ := hcover
  have hsub : prescribedDesignated P a bits M ⊆
      A.biUnion (fun x => prescribedDesignated P a bits M ∩ piecePoints M x) := by
    intro y hy
    rcases Finset.mem_union.mp (hcover hy) with hp | hp
    · exact False.elim (hpre ⟨y, hp⟩)
    · obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_inter.mpr ⟨hy, hyx⟩⟩
  have hbonus : (∑ x ∈ A, extraCapacity P a x) ≤ 2 * κ := by
    rw [← sum_extraCapacity P a ha.2.1 hκ]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  calc
    4 * b = (prescribedDesignated P a bits M).card :=
      (prescribedDesignated_card P a bits p M hadm).symm
    _ ≤ ∑ x ∈ A, (prescribedDesignated P a bits M ∩ piecePoints M x).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ x ∈ A, (2 + extraCapacity P a x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact allowed_piece_trace_le P a bits p M ha hadm hused hcol hnoncol x (hallowed x hx)
    _ = 2 * A.card + ∑ x ∈ A, extraCapacity P a x := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ ≤ 2 * A.card + 2 * κ := Nat.add_le_add_left hbonus _
    _ ≤ 2 * (b - 1) + 2 * κ := by omega

theorem admissibleBadCover_four_events (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (ha : Eligible P a) (hbad : AdmissibleBadCover P a bits p M) :
    UnusedPrecoverage P a bits p M ∨ UsedPairExtra P a bits M ∨
      ForbiddenCollinearTriple P a bits p M ∨ UnusedNoncollinearTriple P a bits M := by
  by_contra hnone
  push Not at hnone
  have hpre : ¬ Precoverage P a bits p M := by
    intro hp
    exact hnone.1 ((precoverage_iff_unused P a bits p M ha hbad.1).mp hp)
  have hbound := cover_budget_le P a bits p M ha hbad.1 (by omega) hbad.2
    hpre hnone.2.1 hnone.2.2.1 hnone.2.2.2
  omega

end
end Balanced.Local.FourEvents

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_AcyclicProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.DependencyExtraction

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

theorem expect_coordinate_refresh (i : α) (f : (α → β) → ℝ) :
    (𝔼 x, 𝔼 y, f (Function.update x i y)) = 𝔼 x, f x := by
  classical
  have hswap := Fintype.expect_equiv (coordinateSwap (β := β) i)
    (fun z : (α → β) × β => f (Function.update z.1 i z.2))
    (fun z : (α → β) × β => f z.1) (fun _ => rfl)
  have hprod₁ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x y => f (Function.update x i y))
  have hprod₂ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x (_ : β) => f x)
  simpa only [Finset.univ_product_univ, Fintype.expect_const] using
    hprod₁.symm.trans (hswap.trans hprod₂)

end Balanced.DependencyExtraction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedOffsetProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem offsetProbability_eq_expect (E : MergedPairs F → Prop) :
    offsetProbability E = 𝔼 M, if E M then (1 : ℝ) else 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  rfl

omit [Field F] in

theorem bool_pair_expect (s : Bool) (v w : F) :
    (𝔼 o : Bool → F, if o s = v ∧ o (!s) = w then (1 : ℝ) else 0) =
      (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  let f : Bool → F := fun t => if t = s then v else w
  have hiff (o : Bool → F) : (o s = v ∧ o (!s) = w) ↔ o = f := by
    constructor
    · intro h
      funext t
      cases s <;> cases t <;> simp_all [f]
    · rintro rfl
      cases s <;> simp [f]
  simp_rw [hiff]
  rw [Fintype.expect_eq_sum_div_card]
  simp [one_div, inv_pow]

theorem two_offset_factorization (d : Direction F) (s : Bool)
    (A : MergedPairs F → Prop) (v w : MergedPairs F → F)
    (hA : ∀ M o, A (Function.update M d o) ↔ A M)
    (hv : ∀ M o, v (Function.update M d o) = v M)
    (hw : ∀ M o, w (Function.update M d o) = w M) :
    offsetProbability (fun M => A M ∧ M d s = v M ∧ M d (!s) = w M) =
      offsetProbability A * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  rw [offsetProbability_eq_expect, offsetProbability_eq_expect]
  trans (𝔼 M : MergedPairs F, 𝔼 o : Bool → F,
    if A (Function.update M d o) ∧
      (Function.update M d o) d s = v (Function.update M d o) ∧
      (Function.update M d o) d (!s) = w (Function.update M d o) then (1 : ℝ) else 0)
  · convert (DependencyExtraction.expect_coordinate_refresh
      (α := Direction F) (β := Bool → F) d
      (fun M => if A M ∧ M d s = v M ∧ M d (!s) = w M then (1 : ℝ) else 0)).symm using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.expect_congr rfl
    intro M _
    split_ifs <;> rfl
  calc
    (𝔼 M, 𝔼 o, if A (Function.update M d o) ∧
        (Function.update M d o) d s = v (Function.update M d o) ∧
        (Function.update M d o) d (!s) = w (Function.update M d o) then (1 : ℝ) else 0) =
        𝔼 M, (if A M then (1 : ℝ) else 0) * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
      apply Finset.expect_congr rfl
      intro M _
      simp_rw [hA, hv, hw, Function.update_self]
      by_cases h : A M
      · simp only [h, true_and, ite_true, one_mul]
        exact bool_pair_expect s (v M) (w M)
      · simp [h]
    _ = _ := (Finset.expect_mul _ _ _).symm

variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

omit [Fintype F] in

theorem prescribedPoint_eq_of_used_agreement (M N : MergedPairs F)
    (hMN : ∀ d ∈ Finset.univ.image a.2, M d = N d) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M ij = prescribedPoint P a bits N ij := by
  have hleft := hMN (a.2 (P.classOf ij.1 ij.2))
    (Finset.mem_image.mpr ⟨P.classOf ij.1 ij.2, Finset.mem_univ _, rfl⟩)
  have hright := hMN (a.2 (P.classOf ij.1 (ij.2 + 1)))
    (Finset.mem_image.mpr ⟨P.classOf ij.1 (ij.2 + 1), Finset.mem_univ _, rfl⟩)
  simp only [prescribedPoint, tuplePoint, prescribedTuple, constituent, hleft, hright]

theorem prescribedPoint_refresh_unused (d : Direction F)
    (hd : d ∈ unusedDirections a) (M : MergedPairs F) (o : Bool → F)
    (ij : Fin b × Fin 4) :
    prescribedPoint P a bits (Function.update M d o) ij = prescribedPoint P a bits M ij := by
  apply prescribedPoint_eq_of_used_agreement
  intro e he
  apply Function.update_of_ne
  intro hed
  exact (mem_unusedDirections d).mp hd (hed ▸ he)

theorem aligned_refresh_unused (d : Direction F) (hd : d ∈ unusedDirections a)
    (M : MergedPairs F) (o : Bool → F) :
    Aligned P a bits p (Function.update M d o) ↔ Aligned P a bits p M := by
  simp only [Aligned, prescribedPoint_refresh_unused d hd M o]

theorem aligned_partner_incidence_probability (d : Direction F)
    (hd : d ∈ unusedDirections a) (s : Bool) (ij : Fin b × Fin 4) :
    offsetProbability (fun M => Aligned P a bits p M ∧
      OnLine p (constituent M d s) ∧
      OnLine (prescribedPoint P a bits M ij) (constituent M d (!s))) =
      offsetProbability (Aligned P a bits p) * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
  have h := two_offset_factorization d s (Aligned P a bits p)
    (fun _ => lineEval d p) (fun M => lineEval d (prescribedPoint P a bits M ij))
    (aligned_refresh_unused d hd) (fun _ _ => rfl)
    (fun M o => congrArg (lineEval d) (prescribedPoint_refresh_unused d hd M o ij))
  simpa only [OnLine, constituent, eq_comm] using h

theorem offsetProbability_nonneg (E : MergedPairs F → Prop) :
    0 ≤ offsetProbability E := by
  unfold offsetProbability
  positivity

omit [Field F] in

theorem offsetProbability_exists_le_sum {ι : Type*} [Fintype ι]
    (E : ι → MergedPairs F → Prop) :
    offsetProbability (fun M => ∃ i, E i M) ≤ ∑ i, offsetProbability (E i) := by
  simp_rw [offsetProbability_eq_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro M _
  by_cases h : ∃ i, E i M
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    calc
      (1 : ℝ) = if E i M then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if E j M then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if E j M then (1 : ℝ) else 0)
          (fun _ _ => by positivity) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    positivity

theorem aligned_unusedPrecoverage_probability_le :
    offsetProbability (fun M => Aligned P a bits p M ∧ unusedPrecoverage P a bits p M) ≤
      offsetProbability (Aligned P a bits p) *
        (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  let E : ((Fin b × Fin 4) × (Direction F × Bool)) → MergedPairs F → Prop :=
    fun z M => Aligned P a bits p M ∧ z.2.1 ∈ unusedDirections a ∧
      OnLine p (constituent M z.2.1 z.2.2) ∧
      OnLine (prescribedPoint P a bits M z.1) (constituent M z.2.1 (!z.2.2))
  have heq : (fun M => Aligned P a bits p M ∧ unusedPrecoverage P a bits p M) =
      (fun M => ∃ z, E z M) := by
    funext M
    apply propext
    constructor
    · rintro ⟨hA, ij, d, hd, s, hp, hx⟩
      exact ⟨(ij, d, s), hA, hd, hp, hx⟩
    · rintro ⟨⟨ij, d, s⟩, hA, hd, hp, hx⟩
      exact ⟨hA, ij, d, hd, s, hp, hx⟩
  rw [heq]
  apply (offsetProbability_exists_le_sum E).trans
  calc
    (∑ z, offsetProbability (E z)) ≤
        ∑ _z : ((Fin b × Fin 4) × (Direction F × Bool)),
          offsetProbability (Aligned P a bits p) * (Fintype.card F : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      rintro ⟨ij, d, s⟩ _
      by_cases hd : d ∈ unusedDirections a
      · have heqE : E (ij, d, s) = (fun M => Aligned P a bits p M ∧
            OnLine p (constituent M d s) ∧
            OnLine (prescribedPoint P a bits M ij) (constituent M d (!s))) := by
          funext M
          simp only [E, hd, true_and]
        rw [heqE, aligned_partner_incidence_probability d hd s ij]
      · have hzero : offsetProbability (E (ij, d, s)) = 0 := by
          simp only [offsetProbability, E, hd, false_and, and_false, ite_false,
            Finset.sum_const_zero, zero_div]
        rw [hzero]
        exact mul_nonneg (offsetProbability_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_option, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [inv_pow, ← one_div]
      ring

theorem conditioned_unusedPrecoverage_probability_le :
    conditionedOffsetProbability (Aligned P a bits p) (unusedPrecoverage P a bits p) ≤
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  unfold conditionedOffsetProbability
  by_cases hzero : offsetProbability (Aligned P a bits p) = 0
  · rw [hzero, div_zero]
    positivity
  · have hpos := lt_of_le_of_ne (offsetProbability_nonneg (Aligned P a bits p))
      (Ne.symm hzero)
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ offsetProbability (Aligned P a bits p) *
          (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 :=
        aligned_unusedPrecoverage_probability_le
      _ = _ := by ring

end
end Balanced.Local.UnusedOffsetProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedEventBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

theorem unusedPrecoverage_iff_fourEvents (M : MergedPairs F) :
    unusedPrecoverage P a bits p M ↔ FourEvents.UnusedPrecoverage P a bits p M := by
  constructor
  · rintro ⟨ij, d, hd, s, hp, hx⟩
    refine ⟨d, (PrescribedGeometry.mem_unusedDirections d).mp hd, s, hp,
      prescribedPoint P a bits M ij, ?_, hx⟩
    exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
  · rintro ⟨d, hd, s, hp, x, hxF, hx⟩
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hxF
    exact ⟨ij, d, (PrescribedGeometry.mem_unusedDirections d).mpr hd, s, hp, hx⟩

omit [Field F] in
theorem offsetProbability_mono {E G : MergedPairs F → Prop}
    (h : ∀ M, E M → G M) : offsetProbability E ≤ offsetProbability G := by
  unfold offsetProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro M _
  by_cases hE : E M
  · simp only [hE, h M hE, ite_true]
    exact le_rfl
  · simp only [hE, ite_false]
    positivity

theorem conditionedOffsetProbability_mono (A : MergedPairs F → Prop)
    {E G : MergedPairs F → Prop} (h : ∀ M, E M → G M) :
    conditionedOffsetProbability A E ≤ conditionedOffsetProbability A G := by
  unfold conditionedOffsetProbability
  exact div_le_div_of_nonneg_right
    (offsetProbability_mono (fun M hM => ⟨hM.1, h M hM.2⟩))
    (offsetProbability_nonneg A)

theorem conditioned_fourEvents_unusedPrecoverage_le :
    conditionedOffsetProbability (Aligned P a bits p)
      (FourEvents.UnusedPrecoverage P a bits p) ≤
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  have heq : FourEvents.UnusedPrecoverage P a bits p = unusedPrecoverage P a bits p := by
    funext M
    exact propext (unusedPrecoverage_iff_fourEvents M).symm
  rw [heq]
  exact conditioned_unusedPrecoverage_probability_le

end
end Balanced.Local.UnusedOffsetProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFourEventProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem offsetProbability_or_le (E G : MergedPairs F → Prop) :
    offsetProbability (fun M => E M ∨ G M) ≤
      offsetProbability E + offsetProbability G := by
  unfold offsetProbability
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro M _
  by_cases hE : E M <;> by_cases hG : G M <;> simp [hE, hG]

theorem conditionedOffsetProbability_or_le (A E G : MergedPairs F → Prop) :
    conditionedOffsetProbability A (fun M => E M ∨ G M) ≤
      conditionedOffsetProbability A E + conditionedOffsetProbability A G := by
  unfold conditionedOffsetProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (offsetProbability_nonneg A)
  have heq : (fun M => A M ∧ (E M ∨ G M)) =
      (fun M => (A M ∧ E M) ∨ (A M ∧ G M)) := by
    funext M
    exact propext and_or_left
  rw [heq]
  exact offsetProbability_or_le _ _

variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)

theorem conditioned_badCover_four_events_le (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (ha : Eligible P a) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      conditionedOffsetProbability (Aligned P a bits p)
        (FourEvents.UnusedPrecoverage P a bits p) +
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧
          FourEvents.ForbiddenCollinearTriple P a bits p M) +
      conditionedOffsetProbability (Aligned P a bits p)
        (FourEvents.UnusedNoncollinearTriple P a bits) := by
  let E₁ := FourEvents.UnusedPrecoverage P a bits p
  let E₂ := fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M
  let E₃ := fun M => Admissible P a bits p M ∧
    FourEvents.ForbiddenCollinearTriple P a bits p M
  let E₄ := FourEvents.UnusedNoncollinearTriple P a bits
  have hsub : ∀ M, AdmissibleBadCover P a bits p M →
      E₁ M ∨ E₂ M ∨ E₃ M ∨ E₄ M := by
    intro M hM
    rcases FourEvents.admissibleBadCover_four_events P a bits p M hb hκ ha hM with
      h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hM.1, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hM.1, h⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  have h₁ := conditionedOffsetProbability_or_le (Aligned P a bits p) E₁
    (fun M => E₂ M ∨ E₃ M ∨ E₄ M)
  have h₂ := conditionedOffsetProbability_or_le (Aligned P a bits p) E₂
    (fun M => E₃ M ∨ E₄ M)
  have h₃ := conditionedOffsetProbability_or_le (Aligned P a bits p) E₃ E₄
  have hm := conditionedOffsetProbability_mono (Aligned P a bits p) hsub
  change conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
    conditionedOffsetProbability (Aligned P a bits p) E₁ +
    conditionedOffsetProbability (Aligned P a bits p) E₂ +
    conditionedOffsetProbability (Aligned P a bits p) E₃ +
    conditionedOffsetProbability (Aligned P a bits p) E₄
  linarith

end
end Balanced.Local.UnusedOffsetProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFourEventWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem unusedNoncollinearTriple_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (h : UnusedNoncollinearTriple P a bits M) :
    ∃ (d : Direction F) (i j k : Fin b × Fin 4), d ∉ usedDirections a ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M i ∈ mergedPoints M d ∧
      prescribedPoint P a bits M j ∈ mergedPoints M d ∧
      prescribedPoint P a bits M k ∈ mergedPoints M d ∧
      ¬ ∃ l : Line F, OnLine (prescribedPoint P a bits M i) l ∧
        OnLine (prescribedPoint P a bits M j) l ∧
        OnLine (prescribedPoint P a bits M k) l := by
  obtain ⟨d,hd,U,hcard,hU,hnline⟩ := h
  obtain ⟨x,y,z,hxy,hxz,hyz,hUeq⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ U := by rw [hUeq]; simp
  have hy : y ∈ U := by rw [hUeq]; simp
  have hz : z ∈ U := by rw [hUeq]; simp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hU hx)).1
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hU hy)).1
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hU hz)).1
  refine ⟨d,i,j,k,hd,hxy,hxz,hyz,(Finset.mem_inter.mp (hU hx)).2,
    (Finset.mem_inter.mp (hU hy)).2,(Finset.mem_inter.mp (hU hz)).2,?_⟩
  rintro ⟨l,hi,hj,hk⟩
  apply hnline
  refine ⟨l,?_⟩
  intro x hxU
  rw [hUeq] at hxU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxU
  rcases hxU with rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩

end
end Balanced.Local.FourEvents

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UnusedOffsetAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Balanced.UnusedOffsetIncidence

theorem pmf_sum_real {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ a, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => μ.apply_ne_top a)]
  have h : ∑ a, μ a = 1 := by simpa only [tsum_fintype] using μ.tsum_coe
  rw [h]
  simp

theorem pmf_outer_ne_top {α : Type*} (μ : PMF α) (E : Set α) :
    μ.toOuterMeasure E ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]
  exact μ.tsum_coe_indicator_ne_top E

theorem bind_probability_le {α β : Type*} [Fintype α]
    (μ : PMF α) (ν : α → PMF β) (E : Set β) (r : ℝ)
    (h : ∀ a, ((ν a).toOuterMeasure E).toReal ≤ r) :
    ((μ.bind ν).toOuterMeasure E).toReal ≤ r := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
      (μ.apply_ne_top a) (pmf_outer_ne_top (ν a) E))]
  simp_rw [ENNReal.toReal_mul]
  calc
    (∑ a, (μ a).toReal * ((ν a).toOuterMeasure E).toReal) ≤
        ∑ a, (μ a).toReal * r :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = r := by rw [← Finset.sum_mul, pmf_sum_real μ, one_mul]

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedTripleProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Balanced.Local.UnusedTripleProbability

open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] in
theorem prescribedDesignated_card_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    (prescribedDesignated P a bits M).card ≤ 4 * b := by
  apply Finset.card_image_le.trans
  simp [Nat.mul_comm]

omit [Fintype F] in
theorem prescribedDesignated_eq_of_used_agreement (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M N : MergedPairs F)
    (h : ∀ d ∈ Finset.univ.image a.2, M d = N d) :
    prescribedDesignated P a bits M = prescribedDesignated P a bits N := by
  unfold prescribedDesignated
  congr 1
  funext ij
  exact UnusedOffsetProbability.prescribedPoint_eq_of_used_agreement M N h ij

theorem unusedNoncollinearTriple_imp (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (h : FourEvents.UnusedNoncollinearTriple P a bits M) :
    UnusedOffsetIncidence.NoncollinearTripleInPair (unusedDirections a)
      (prescribedDesignated P a bits M) (unusedOffsets a M) := by
  obtain ⟨d, i, j, k, hd, _, _, _, hi, hj, hk, hn⟩ :=
    FourEvents.unusedNoncollinearTriple_indices P a bits M h
  have hdu : d ∈ unusedDirections a := (mem_unusedDirections d).mpr hd
  refine ⟨prescribedPoint P a bits M i, ?_, prescribedPoint P a bits M j, ?_,
    prescribedPoint P a bits M k, ?_, hn, ⟨⟨d,hdu⟩, ?_, ?_, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · rcases Finset.mem_union.mp hi with hfalse | htrue
    · exact ⟨false, (Finset.mem_filter.mp hfalse).2⟩
    · exact ⟨true, (Finset.mem_filter.mp htrue).2⟩
  · rcases Finset.mem_union.mp hj with hfalse | htrue
    · exact ⟨false, (Finset.mem_filter.mp hfalse).2⟩
    · exact ⟨true, (Finset.mem_filter.mp htrue).2⟩
  · rcases Finset.mem_union.mp hk with hfalse | htrue
    · exact ⟨false, (Finset.mem_filter.mp hfalse).2⟩
    · exact ⟨true, (Finset.mem_filter.mp htrue).2⟩

theorem refreshed_unusedNoncollinearTriple_probability_le (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (N : MergedPairs F)
    (Ms : UnusedOffsetIncidence.Offsets (unusedDirections a) → MergedPairs F)
    (hused : ∀ o d, d ∈ Finset.univ.image a.2 → Ms o d = N d)
    (hunused : ∀ o (d : unusedDirections a), Ms o d.1 = o d) :
    UnusedOffsetIncidence.probability
      (fun o => FourEvents.UnusedNoncollinearTriple P a bits (Ms o)) ≤
      6 * (4 * (b : ℝ)) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  have hmono : UnusedOffsetIncidence.probability
      (fun o => FourEvents.UnusedNoncollinearTriple P a bits (Ms o)) ≤
      UnusedOffsetIncidence.probability
        (UnusedOffsetIncidence.NoncollinearTripleInPair (unusedDirections a)
          (prescribedDesignated P a bits N)) := by
    apply UnusedOffsetIncidence.probability_mono
    intro o ho
    have h := unusedNoncollinearTriple_imp P a bits (Ms o) ho
    have hpoints := prescribedDesignated_eq_of_used_agreement P a bits
      (Ms o) N (hused o)
    have hoff : unusedOffsets a (Ms o) = o := by
      funext d
      exact hunused o d
    rwa [hpoints, hoff] at h
  apply hmono.trans
  apply (UnusedOffsetIncidence.noncollinearTripleInPair_probability_le
    (unusedDirections a) (prescribedDesignated P a bits N)).trans
  gcongr
  exact_mod_cast prescribedDesignated_card_le P a bits N

end Balanced.Local.UnusedTripleProbability

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUnusedTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Balanced.Local.UnusedTripleProbability

open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem conditioned_unusedNoncollinearTriple_le
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned P a bits p)
      (FourEvents.UnusedNoncollinearTriple P a bits) ≤
        384 * (b : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  rw [AlignedUnused.conditionedOffsetProbability_eq_alignedLaw P hκ a ha bits p,
    AlignedUnused.alignedLaw_eq_bind]
  apply UnusedOffsetIncidence.bind_probability_le
  intro u
  have hlaw := TupleAlignment.uniform_map_equiv (unusedArrayEquiv P a).symm
  rw [← hlaw, PMF.map_comp, PMF.toOuterMeasure_map_apply]
  change ((PMF.uniformOfFintype
    (UnusedOffsetIncidence.Offsets (unusedDirections a))).toOuterMeasure
    {o | FourEvents.UnusedNoncollinearTriple P a bits
      ((AlignedUnused.split P a).symm (u, (unusedArrayEquiv P a).symm o))}).toReal ≤ _
  rw [← UnusedOffsetIncidence.probability_eq_pmf]
  have h := refreshed_unusedNoncollinearTriple_probability_le P a bits
    ((AlignedUnused.split P a).symm (u, fun _ _ => 0))
    (fun o => (AlignedUnused.split P a).symm (u, (unusedArrayEquiv P a).symm o))
    (fun o d hd => ?_) (fun o d => ?_)
  · convert h using 1; ring
  · have ho := congrFun (congrArg Prod.fst
      ((AlignedUnused.split P a).apply_symm_apply (u, (unusedArrayEquiv P a).symm o)))
      ⟨d, hd⟩
    have hn := congrFun (congrArg Prod.fst
      ((AlignedUnused.split P a).apply_symm_apply (u, fun _ _ => 0))) ⟨d, hd⟩
    exact ho.trans hn.symm
  · exact congrFun (congrArg Prod.snd
      ((AlignedUnused.split P a).apply_symm_apply (u, (unusedArrayEquiv P a).symm o)))
      ⟨d.1, (mem_unusedDirections d.1).mp d.2⟩

theorem conditioned_badCover_le_used_events
    (P : EqualityPattern b κ) (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M) +
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 +
      384 * (b : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  have h := UnusedOffsetProbability.conditioned_badCover_four_events_le
    P a bits p hb hκ ha
  have h₁ := UnusedOffsetProbability.conditioned_fourEvents_unusedPrecoverage_le
    (P := P) (a := a) (bits := bits) (p := p)
  have h₄ := conditioned_unusedNoncollinearTriple_le P hκ a ha bits p
  linarith

end Balanced.Local.UnusedTripleProbability

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*}

variable [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem offsetProbability_eq_card (E : MergedPairs F → Prop) :
    offsetProbability E =
      ((Finset.univ.filter E).card : ℝ) / Fintype.card (MergedPairs F) := by
  classical
  simp [offsetProbability]

theorem offsetProbability_mono {E G : MergedPairs F → Prop}
    (h : ∀ M, E M → G M) : offsetProbability E ≤ offsetProbability G := by
  classical
  rw [offsetProbability_eq_card, offsetProbability_eq_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (Finset.univ.filter E).card ≤ (Finset.univ.filter G).card := by
    apply Finset.card_le_card
    intro M hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h M (Finset.mem_filter.mp hM).2⟩
  exact_mod_cast hc

theorem selectedProbability_mono (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    {E G : Configuration F → Prop} (h : ∀ C, E C → G C) :
    selectedProbability w E ≤ selectedProbability w G := by
  unfold selectedProbability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro M _
  apply Finset.sum_le_sum
  intro v _
  by_cases hE : E (configuration M v)
  · simp only [hE, h _ hE, ite_true]
    exact le_rfl
  · simp only [hE, ite_false]
    split_ifs
    · exact hw M v
    · exact le_rfl

theorem selected_prescription_and_offset_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (S : Finset (Slot F))
    (t : MergedPairs F → Slot F → TupleCode F) (E : MergedPairs F → Prop) :
    selectedProbability w (fun C => E C.merged ∧
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) ≤
      (K / Fintype.card F) ^ S.card * offsetProbability E := by
  let r : ℝ := (K / Fintype.card F) ^ S.card
  have hpoint : ∀ M : MergedPairs F,
      (∑ v : Output F, if E M ∧ (∀ s ∈ S, (v s).2 = t M s)
        then w M v else 0) ≤ if E M then r else 0 := by
    intro M
    by_cases hE : E M
    · simpa only [hE, true_and, ite_true] using hw.2.2.2 M S (t M)
    · simp [hE]
  have hsum : (∑ M : MergedPairs F, if E M then r else 0) =
      r * ∑ M : MergedPairs F, if E M then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    split_ifs <;> simp
  have hform : selectedProbability w (fun C => E C.merged ∧
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) =
      (∑ M : MergedPairs F, ∑ v : Output F,
        if E M ∧ (∀ s ∈ S, (v s).2 = t M s) then w M v else 0) /
          Fintype.card (MergedPairs F) := by
    unfold selectedProbability
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro v _
    simp [configuration, decodeChoice, encodeTuple, decodeTuple]
  rw [hform]
  calc
    _ ≤ (∑ M : MergedPairs F, if E M then r else 0) /
        Fintype.card (MergedPairs F) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun M _ => hpoint M)) (by positivity)
    _ = r * offsetProbability E := by rw [hsum]; simp [offsetProbability, div_eq_mul_inv, mul_assoc]

end
end Balanced.Local.KernelBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology BigOperators

namespace Balanced.LocalAsymptotics

theorem summable_polynomial_mul_pow_div_factorial (a : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Summable (fun b : ℕ => (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) := by
  apply (Real.summable_pow_div_factorial (2 * C)).of_norm_bounded_eventually_nat
  have h := (tendsto_pow_const_div_const_pow_of_one_lt a (by norm_num : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with b hb
  have hb' : (b : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
    exact le_of_lt ((div_lt_one (by positivity : (0 : ℝ) < 2 ^ b)).mp hb)
  rw [Real.norm_of_nonneg (by positivity), mul_pow]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb' (pow_nonneg hC b))
    (by positivity)

theorem tendsto_log_pow_div (a : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ a / x) atTop (𝓝 0) := by
  have h := isLittleO_log_rpow_rpow_atTop (a : ℝ) (by norm_num : (0 : ℝ) < 1)
  simpa only [Real.rpow_natCast, Real.rpow_one] using h.tendsto_div_nhds_zero

theorem tendsto_ceil_log_pow_div (a : ℕ) :
    Tendsto (fun x : ℝ => (⌈Real.log x⌉₊ : ℝ) ^ a / x) atTop (𝓝 0) := by
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hx : ∀ᶠ x : ℝ in atTop, 0 ≤ x := eventually_ge_atTop 0
  apply squeeze_zero' (hx.mono fun x hx => by positivity)
    (g := fun x : ℝ => (2 : ℝ) ^ a * ((Real.log x) ^ a / x))
  · filter_upwards [hlog, hx] with x hlog hx
    have hceil : (⌈Real.log x⌉₊ : ℝ) ≤ 2 * Real.log x := by
      have h := Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
      linarith
    calc
      (⌈Real.log x⌉₊ : ℝ) ^ a / x ≤ (2 * Real.log x) ^ a / x := by gcongr
      _ = (2 : ℝ) ^ a * ((Real.log x) ^ a / x) := by rw [mul_pow]; ring
  · simpa using (tendsto_log_pow_div a).const_mul ((2 : ℝ) ^ a)

theorem tendsto_ceil_log_cube_div_nat :
    Tendsto (fun q : ℕ => (⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ))
      atTop (𝓝 0) :=
  (tendsto_ceil_log_pow_div 3).comp tendsto_natCast_atTop_atTop

theorem sum_polynomial_mul_pow_div_factorial_le (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (s : Finset ℕ) :
    (∑ b ∈ s, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) ≤
      ∑' b : ℕ, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ) := by
  exact (summable_polynomial_mul_pow_div_factorial a C hC).sum_le_tsum s
    (fun b _ => by positivity)

theorem tendsto_weighted_log_bound (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (s : ℕ → Finset ℕ) :
    Tendsto (fun q : ℕ =>
      (∑ b ∈ s q, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) *
      ((⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero (fun q => by positivity)
    (g := fun q : ℕ => (∑' b : ℕ, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) *
      ((⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ)))
  · intro q
    apply mul_le_mul_of_nonneg_right
      (sum_polynomial_mul_pow_div_factorial_le a C hC (s q))
    positivity
  · simpa using tendsto_ceil_log_cube_div_nat.const_mul
      (∑' b : ℕ, (b : ℝ) ^ a * C ^ b / (b.factorial : ℝ))

theorem tendsto_plane_weighted_pencil_sum (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (s : ℕ → Finset ℕ) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 2 *
      ∑ b ∈ s q, ((b : ℝ) ^ a * C ^ b / (b.factorial : ℝ)) *
        ((⌈Real.log (q : ℝ)⌉₊ : ℝ) ^ 3 / (q : ℝ) ^ 3)) atTop (𝓝 0) := by
  apply (tendsto_weighted_log_bound a C hC s).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [← Finset.sum_mul]
  field_simp

theorem pencil_common_factor_le (q K : ℝ) (b κ : ℕ)
    (hq : 1 ≤ q) (hK : 0 ≤ K) (hκ : κ ≤ 5 * b) :
    (32 : ℝ) ^ b * (q + 1) ^ (5 * b - κ) * (K / q) ^ b / q ^ (4 * b) ≤
      (1024 * K) ^ b / q ^ κ := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hp : (q + 1) ^ (5 * b - κ) ≤ (2 : ℝ) ^ (5 * b) * q ^ (5 * b - κ) := by
    calc
      (q + 1) ^ (5 * b - κ) ≤ (2 * q) ^ (5 * b - κ) := by gcongr; linarith
      _ = (2 : ℝ) ^ (5 * b - κ) * q ^ (5 * b - κ) := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ (5 * b) * q ^ (5 * b - κ) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
          (pow_nonneg hqpos.le _)
  have hqp : q ^ (5 * b) = q ^ b * q ^ (4 * b) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : (32 : ℝ) ^ b * (2 : ℝ) ^ (5 * b) * K ^ b = (1024 * K) ^ b := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    norm_num
  calc
    (32 : ℝ) ^ b * (q + 1) ^ (5 * b - κ) * (K / q) ^ b / q ^ (4 * b)
        ≤ (32 : ℝ) ^ b * ((2 : ℝ) ^ (5 * b) * q ^ (5 * b - κ)) *
          (K / q) ^ b / q ^ (4 * b) := by gcongr
    _ = (1024 * K) ^ b / q ^ κ := by
      rw [div_pow, pow_sub₀ q hqne hκ, hqp]
      field_simp
      nlinarith [hc]

end Balanced.LocalAsymptotics

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePatternCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.ReusePatternCounting

noncomputable section
open scoped Classical

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem changedSet_fillOn_subset (base : α → β) (s : Finset α) (v : s → β) :
    changedSet base (fillOn base s v) ⊆ s := by
  intro i hi
  by_contra his
  exact (Finset.mem_filter.mp hi).2 (by simp [fillOn, his])

theorem card_sparse_maps_le (base : α → β) (k : ℕ) (hk : k ≤ Fintype.card α) :
    Fintype.card {f : α → β // (changedSet base f).card ≤ k} ≤
      (Fintype.card α).choose k * Fintype.card β ^ k := by
  let fill : (Σ s : {s : Finset α // s.card = k}, (s.1 → β)) →
      {f : α → β // (changedSet base f).card ≤ k} := fun sv =>
    ⟨fillOn base sv.1.1 sv.2,
      (Finset.card_le_card (changedSet_fillOn_subset base sv.1.1 sv.2)).trans_eq sv.1.2⟩
  have hsurj : Function.Surjective fill := by
    intro f
    obtain ⟨s, hsub, hcard⟩ := Finset.exists_superset_card_eq f.2 hk
    refine ⟨⟨⟨s, hcard⟩, fun i => f.1 i.1⟩, ?_⟩
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [fill, fillOn, hi]
    · have heq : f.1 i = base i := by
        by_contra hne
        exact hi (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩))
      simp [fill, fillOn, hi, heq]
  calc
    Fintype.card {f : α → β // (changedSet base f).card ≤ k}
        ≤ Fintype.card (Σ s : {s : Finset α // s.card = k}, (s.1 → β)) :=
          Fintype.card_le_of_surjective fill hsurj
    _ = ∑ s : {s : Finset α // s.card = k}, Fintype.card β ^ k := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.card_fun, Fintype.card_coe, s.2]
    _ = (Fintype.card α).choose k * Fintype.card β ^ k := by
      simp [Fintype.card_finset_len]

theorem card_sparse_endomaps_le (k : ℕ) (hk : k ≤ Fintype.card α) :
    Fintype.card {f : α → α // (changedSet id f).card ≤ k} ≤
      Fintype.card α ^ (2 * k) := by
  calc
    Fintype.card {f : α → α // (changedSet id f).card ≤ k}
        ≤ (Fintype.card α).choose k * Fintype.card α ^ k := card_sparse_maps_le id k hk
    _ ≤ Fintype.card α ^ k * Fintype.card α ^ k :=
      Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
    _ = Fintype.card α ^ (2 * k) := by rw [← pow_add]; congr 1; omega

section Representatives

variable {ι γ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq γ]

theorem firstRepresentative_eq_iff (f : ι → γ) (i j : ι) :
    firstRepresentative f i = firstRepresentative f j ↔ f i = f j := by
  constructor
  · intro h
    have hv := congrArg f h
    simpa only [value_firstRepresentative] using hv
  · exact firstRepresentative_eq_of_value_eq f

theorem firstRepresentative_eq_of_same_equalities {δ : Type*} [DecidableEq δ]
    (f : ι → γ) (g : ι → δ)
    (h : ∀ i j, f i = f j ↔ g i = g j) :
    firstRepresentative f = firstRepresentative g := by
  funext i
  have hs : Finset.univ.filter (fun j => f j = f i) =
      Finset.univ.filter (fun j => g j = g i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
  unfold firstRepresentative
  congr 1

theorem card_canonical_patterns_le (κ : ℕ) (hκ : κ ≤ Fintype.card ι) :
    Nat.card (CanonicalPattern ι κ) ≤ Fintype.card ι ^ (2 * κ) := by
  rw [Nat.card_eq_fintype_card]
  let forget : CanonicalPattern ι κ →
      {r : ι → ι // (changedSet id r).card ≤ κ} :=
    fun r => ⟨r.1, Nat.le_of_eq r.2.2⟩
  have hinj : Function.Injective forget := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : {r : ι → ι // (changedSet id r).card ≤ κ} => z.1) hab
  exact (Fintype.card_le_of_injective forget hinj).trans (card_sparse_endomaps_le κ hκ)

theorem card_four_point_patterns_le (b κ : ℕ) (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    Nat.card (CanonicalPattern (Fin (4 * b)) κ) ≤ (4 * b) ^ 4 := by
  have hκn : κ ≤ Fintype.card (Fin (4 * b)) := by simp; omega
  have h := card_canonical_patterns_le (ι := Fin (4 * b)) κ hκn
  simp only [Fintype.card_fin] at h
  apply h.trans
  exact Nat.pow_le_pow_right (by omega) (by omega)

end Representatives

end
end Balanced.ReusePatternCounting

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPatternCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PatternCodes

open ReusePatternCounting
open scoped Classical
noncomputable section

variable {b κ : ℕ}

theorem canonicalCode_equalities (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b)
    (ij kl : Fin b × Fin 4) :
    (canonicalCode P hκ).1 (occurrenceEquiv b ij) =
      (canonicalCode P hκ).1 (occurrenceEquiv b kl) ↔
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 := by
  simpa only [canonicalCode, flatClasses, Equiv.symm_apply_apply] using
    firstRepresentative_eq_iff (flatClasses P)
      (occurrenceEquiv b ij) (occurrenceEquiv b kl)

theorem canonicalCode_eq_iff (P Q : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    canonicalCode P hκ = canonicalCode Q hκ ↔
      ∀ (ij kl : Fin b × Fin 4),
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2 := by
  constructor
  · intro h ij kl
    rw [← canonicalCode_equalities P hκ, ← canonicalCode_equalities Q hκ, h]
  · intro h
    apply Subtype.ext
    exact firstRepresentative_eq_of_same_equalities (flatClasses P) (flatClasses Q)
      (fun i j => h ((occurrenceEquiv b).symm i) ((occurrenceEquiv b).symm j))

attribute [local instance] OAI.Balanced.Local.PatternCodes.instFintypeEqualityPattern
theorem card_actual_pattern_codes_le (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    (Finset.univ.image (fun P : EqualityPattern b κ =>
      canonicalCode P (by omega))).card ≤ (4 * b) ^ 4 := by
  have h := card_four_point_patterns_le b κ hb hκ
  rw [Nat.card_eq_fintype_card] at h
  exact (Finset.card_le_univ _).trans h

theorem exists_pattern_representatives (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (EqualityPattern b κ), R.card ≤ (4 * b) ^ 4 ∧
      ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
        ∀ (ij kl : Fin b × Fin 4),
          P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
            Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2 := by
  let hk : κ ≤ 4 * b := by omega
  let S := Finset.univ.image (fun P : EqualityPattern b κ => canonicalCode P hk)
  have hex : ∀ c : S, ∃ P : EqualityPattern b κ, canonicalCode P hk = c.1 := by
    intro c
    obtain ⟨P, _, hP⟩ := Finset.mem_image.mp c.2
    exact ⟨P, hP⟩
  let rep : S → EqualityPattern b κ := fun c => Classical.choose (hex c)
  have hrep (c : S) : canonicalCode (rep c) hk = c.1 := Classical.choose_spec (hex c)
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · calc
      (Finset.univ.image rep).card ≤ (Finset.univ : Finset S).card := Finset.card_image_le
      _ = S.card := by simp
      _ ≤ (4 * b) ^ 4 := card_actual_pattern_codes_le hb hκ
  · intro P
    let c : S := ⟨canonicalCode P hk, Finset.mem_image.mpr ⟨P, Finset.mem_univ P, rfl⟩⟩
    refine ⟨rep c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩, ?_⟩
    exact (canonicalCode_eq_iff P (rep c) hk).mp (hrep c).symm

end
end Balanced.Local.PatternCodes

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SparsePatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.SparsePatterns

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I A : Type*} [Fintype I] [Fintype A]

section Relabeling

variable {X Y Z D : Type*}

theorem exists_relabeling_of_same_pattern (f : X → Y) (g : X → Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpattern : ∀ i j, (f i = f j ↔ g i = g j)) :
    ∃ e : Y ≃ Z, ∀ i, e (f i) = g i := by
  let r : Y → X := fun y => Classical.choose (hf y)
  have hr : ∀ y, f (r y) = y := fun y => Classical.choose_spec (hf y)
  let e : Y → Z := fun y => g (r y)
  have hfactor : ∀ i, e (f i) = g i := fun i =>
    (hpattern (r (f i)) i).mp (hr (f i))
  have hinj : Function.Injective e := by
    intro y z hyz
    have h := (hpattern (r y) (r z)).mpr hyz
    simpa only [hr] using h
  have hsurj : Function.Surjective e := by
    intro z
    obtain ⟨i, rfl⟩ := hg z
    exact ⟨f i, hfactor i⟩
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, hfactor⟩

end Relabeling

end
end Balanced.SparsePatterns

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPatternTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.Local

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P Q : EqualityPattern b κ}

theorem exists_classRelabeling
    (h : ∀ i j : Fin b × Fin 4,
      (P.classOf i.1 i.2 = P.classOf j.1 j.2 ↔
        Q.classOf i.1 i.2 = Q.classOf j.1 j.2)) :
    ∃ e : Fin (4 * b - κ) ≃ Fin (4 * b - κ),
      ∀ i j, e (P.classOf i j) = Q.classOf i j := by
  obtain ⟨e, he⟩ := SparsePatterns.exists_relabeling_of_same_pattern
    (fun i : Fin b × Fin 4 => P.classOf i.1 i.2)
    (fun i : Fin b × Fin 4 => Q.classOf i.1 i.2)
    P.everyClass Q.everyClass h
  exact ⟨e, fun i j => he (i, j)⟩

variable (e : Fin (4 * b - κ) ≃ Fin (4 * b - κ))
variable (he : ∀ i j, e (P.classOf i j) = Q.classOf i j)

include he

omit [Field F] [Fintype F] [DecidableEq F] in
theorem relabelAssignment_generator (a : DirectionAssignment F b κ)
    (i : Fin b) (j : Fin 4) :
    (relabelAssignment e a).2 (Q.classOf i j) = a.2 (P.classOf i j) := by
  change a.2 (e.symm (Q.classOf i j)) = a.2 (P.classOf i j)
  rw [← he i j, e.symm_apply_apply]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem eligible_relabelAssignment (a : DirectionAssignment F b κ) :
    Eligible Q (relabelAssignment e a) ↔ Eligible P a := by
  have hinj : Function.Injective (relabelAssignment e a).2 ↔
      Function.Injective a.2 := by
    change Function.Injective (a.2 ∘ e.symm) ↔ Function.Injective a.2
    constructor
    · intro h x y hxy
      have hh : e x = e y := h (by simpa using hxy)
      exact e.injective hh
    · intro h
      exact h.comp e.symm.injective
  simp only [Eligible, relabelAssignment_target, hinj,
    relabelAssignment_generator e he]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem prescribedTuple_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (i : Fin b) :
    prescribedTuple Q (relabelAssignment e a) bits i =
      prescribedTuple P a bits i := by
  unfold prescribedTuple
  congr 1
  funext j
  exact relabelAssignment_generator e he a i j

omit [Fintype F] [DecidableEq F] in
theorem prescribedPoint_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) :
    prescribedPoint Q (relabelAssignment e a) bits M =
      prescribedPoint P a bits M := by
  funext ij
  simp only [prescribedPoint, prescribedTuple_relabelAssignment e he]

omit [Fintype F] [DecidableEq F] in
theorem aligned_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Aligned Q (relabelAssignment e a) bits p M ↔ Aligned P a bits p M := by
  simp only [Aligned, prescribedPoint_relabelAssignment e he,
    relabelAssignment_target]

theorem admissible_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Admissible Q (relabelAssignment e a) bits p M ↔ Admissible P a bits p M := by
  simp only [Admissible, aligned_relabelAssignment e he,
    prescribedPoint_relabelAssignment e he, relabelAssignment_target]

omit [Fintype F] in
theorem prescribedDesignated_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) :
    prescribedDesignated Q (relabelAssignment e a) bits M =
      prescribedDesignated P a bits M := by
  simp only [prescribedDesignated, prescribedPoint_relabelAssignment e he]

theorem prescribedPartners_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    prescribedPartners Q (relabelAssignment e a) bits p M =
      prescribedPartners P a bits p M := by
  simp only [prescribedPartners, prescribedDesignated_relabelAssignment e he]

omit he in
theorem allowedPiece_relabelAssignment (a : DirectionAssignment F b κ)
    (p : Point F) (M : MergedPairs F) (x : LocalPiece F) :
    AllowedPiece (relabelAssignment e a) p M x ↔ AllowedPiece a p M x := by
  cases x with
  | inl U => rfl
  | inr x =>
      cases x <;> rfl

theorem badCover_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    BadCover Q (relabelAssignment e a) bits p M ↔ BadCover P a bits p M := by
  simp only [BadCover, prescribedDesignated_relabelAssignment e he,
    prescribedPartners_relabelAssignment e he, allowedPiece_relabelAssignment]

theorem admissibleBadCover_relabelAssignment (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    AdmissibleBadCover Q (relabelAssignment e a) bits p M ↔
      AdmissibleBadCover P a bits p M := by
  simp only [AdmissibleBadCover, admissible_relabelAssignment e he,
    badCover_relabelAssignment e he]

end Balanced.Local

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrescriptionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem orderedBadPencil_has_representative
    (R : Finset (EqualityPattern b κ))
    (hR : ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
      ∀ ij kl : Fin b × Fin 4,
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (p : Point F) (used : Fin b → Slot F) (C : Configuration F)
    (h : OrderedBadPencil b κ p used C) :
    ∃ j : PencilPrescriptions (F := F) R,
      prescriptionOccurs R p j C ∧ prescriptionRead R j = used := by
  obtain ⟨_, P, a, bits, he, hg, hm⟩ := h
  obtain ⟨Q, hQ, hPQ⟩ := hR P
  obtain ⟨e, heq⟩ := exists_classRelabeling hPQ
  let a' := relabelAssignment e a
  let side : Fin b → Bool := fun i => (used i).2
  have hs : prescriptionSlots a' side = used := by
    funext i
    apply Prod.ext
    · exact (hm i).1.symm
    · rfl
  refine ⟨(⟨Q, hQ⟩, a', bits, side), ?_, hs⟩
  change Eligible Q a' ∧ AdmissibleBadCover Q a' bits p C.merged ∧ _
  refine ⟨(eligible_relabelAssignment e heq a).mpr he,
    (admissibleBadCover_relabelAssignment e heq a bits p C.merged).mpr hg, ?_⟩
  intro i
  rw [hs]
  exact (hm i).2.1.trans (prescribedTuple_relabelAssignment e heq a bits i).symm

theorem selectedProbability_le_encodedOrder_sum
    {J : Type*} [Fintype J] (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E : Configuration F → Prop) (R : J → Configuration F → Prop)
    (read : J → Fin b → Slot F)
    (hcover : ∀ M v, 0 < w M v → E (configuration M v) →
      ∃ f : Fin b → Slot F, Function.Injective f ∧
        ∀ σ : Equiv.Perm (Fin b), ∃ j,
          R j (configuration M v) ∧ read j = f ∘ σ) :
    selectedProbability w E ≤
      (∑ j, selectedProbability w (R j)) / (b.factorial : ℝ) := by
  have h := OrderedEventCounting.weighted_encoded_order_bound
    (fun z : MergedPairs F × Output F => w z.1 z.2)
    (fun z => hw z.1 z.2) (fun z => E (configuration z.1 z.2))
    (fun j z => R j (configuration z.1 z.2)) read (fun z => hcover z.1 z.2)
  simp only [Fintype.sum_prod_type] at h
  have hd := div_le_div_of_nonneg_right h
    (show (0 : ℝ) ≤ Fintype.card (MergedPairs F) by positivity)
  simpa only [selectedProbability, Finset.sum_div, div_div, mul_comm] using hd

theorem bad_pencil_probability_le_canonical_sum
    (R : Finset (EqualityPattern b κ))
    (hR : ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
      ∀ ij kl : Fin b × Fin 4,
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (∑ j : PencilPrescriptions (F := F) R,
        selectedProbability w (prescriptionOccurs R p j)) / (b.factorial : ℝ) := by
  apply selectedProbability_le_encodedOrder_sum w hK.1 _ _ (prescriptionRead R)
  intro M v hv hbad
  obtain ⟨hV, hC, _, hcap⟩ := hK.2.2.1 M v hv
  obtain ⟨f, hf, hall⟩ := bad_local_cover_all_orders (configuration M v) hV hC p hcap
    hbad.1 hb hbad.2.1 hbad.2.2
  exact ⟨f, hf, fun σ => orderedBadPencil_has_representative R hR p (f ∘ σ)
    (configuration M v) (hall σ)⟩

theorem pencilPrescription_probability_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (side : Fin b → Bool)
    (p : Point F) :
    selectedProbability w (PencilPrescriptionOccurs P a bits side p) ≤
      if Eligible P a then (K / Fintype.card F) ^ b *
        offsetProbability (AdmissibleBadCover P a bits p) else 0 := by
  by_cases he : Eligible P a
  · rw [ite_eq_left he]
    have hi : Function.Injective (prescriptionSlots a side) := by
      intro i j hij
      exact he.1 (congrArg Prod.fst hij)
    let S : Finset (Slot F) := Finset.univ.image (prescriptionSlots a side)
    let t : Slot F → TupleCode F := Function.extend (prescriptionSlots a side)
      (fun i => KernelBridge.encodeTuple (prescribedTuple P a bits i))
      (fun _ => (fun _ => none, fun _ => false))
    have hcard : S.card = b := by
      rw [Finset.card_image_of_injective _ hi]
      simp
    have hp := KernelBridge.selected_prescription_and_offset_le Q w K hK S
      (fun _ => t) (AdmissibleBadCover P a bits p)
    rw [hcard] at hp
    refine (KernelBridge.selectedProbability_mono w hK.1 ?_).trans hp
    intro C hC
    refine ⟨hC.2.1, ?_⟩
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    change KernelBridge.encodeTuple (C.choice (prescriptionSlots a side i)).tuple =
      Function.extend (prescriptionSlots a side)
        (fun i => KernelBridge.encodeTuple (prescribedTuple P a bits i))
        (fun _ => (fun _ => none, fun _ => false)) (prescriptionSlots a side i)
    rw [hi.extend_apply, hC.2.2 i]
  · simp only [ite_eq_right he]
    simp only [selectedProbability, PencilPrescriptionOccurs, he, false_and,
      ite_false, Finset.sum_const_zero, zero_div, le_refl]

theorem bad_pencil_probability_le_canonical_offset_sum
    (R : Finset (EqualityPattern b κ))
    (hR : ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
      ∀ ij kl : Fin b × Fin 4,
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (∑ j : PencilPrescriptions (F := F) R,
        if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
          offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) /
        (b.factorial : ℝ) := by
  refine (bad_pencil_probability_le_canonical_sum R hR Q w K hK p hb).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  exact pencilPrescription_probability_le Q w K hK j.1.1 j.2.1 j.2.2.1 j.2.2.2 p

theorem canonical_offset_sum_eq (R : Finset (EqualityPattern b κ))
    (K : ℝ) (p : Point F) :
    (∑ j : PencilPrescriptions (F := F) R,
      if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
        offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) =
      (2 : ℝ) ^ b * (K / Fintype.card F) ^ b *
        ∑ P : R, ∑ bits : Bits b, directionBadCoverMass P.1 bits p := by
  have hgeom (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
      (bits : Bits b) :
      (fun M => Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) =
        AdmissibleBadCover P a bits p := by
    funext M
    apply propext
    exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩
  have hprod : (∑ j : PencilPrescriptions (F := F) R,
      if Eligible j.1.1 j.2.1 then (K / Fintype.card F) ^ b *
        offsetProbability (AdmissibleBadCover j.1.1 j.2.1 j.2.2.1 p) else 0) =
      ∑ P : R, ∑ a : DirectionAssignment F b κ, ∑ bits : Bits b,
        ∑ _side : Fin b → Bool, if Eligible P.1 a then (K / Fintype.card F) ^ b *
          offsetProbability (AdmissibleBadCover P.1 a bits p) else 0 := by
    simp only [PencilPrescriptions, Fintype.sum_prod_type]
  rw [hprod]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [directionBadCoverMass, hgeom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem bad_pencil_probability_le_direction_bound
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) (hk : κ ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hgeom : ∀ (P : EqualityPattern b κ) (bits : Bits b),
      directionBadCoverMass P bits p ≤ D) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (4 * (b : ℝ)) ^ 4 * (32 : ℝ) ^ b * (K / Fintype.card F) ^ b * D /
        (b.factorial : ℝ) := by
  obtain ⟨R, hcard, hR⟩ := PatternCodes.exists_pattern_representatives (by omega : 1 ≤ b) hk
  have hbound := bad_pencil_probability_le_canonical_offset_sum R hR Q w K hK p hb
  rw [canonical_offset_sum_eq] at hbound
  have hbits : Fintype.card (Bits b) = 16 ^ b := by
    simp [Bits]
  have hsum : (∑ P : R, ∑ bits : Bits b, directionBadCoverMass P.1 bits p) ≤
      (R.card : ℝ) * (16 : ℝ) ^ b * D := by
    calc
      _ ≤ ∑ _P : R, ∑ _bits : Bits b, D := by
        apply Finset.sum_le_sum
        intro P _
        exact Finset.sum_le_sum (fun bits _ => hgeom P.1 bits)
      _ = _ := by simp [hbits, mul_assoc]
  have hcard' : (R.card : ℝ) ≤ (4 * (b : ℝ)) ^ 4 := by exact_mod_cast hcard
  refine hbound.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
  calc
    _ ≤ (2 : ℝ) ^ b * (K / Fintype.card F) ^ b *
        ((R.card : ℝ) * (16 : ℝ) ^ b * D) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 : ℝ) ^ b * (K / Fintype.card F) ^ b *
        ((4 * (b : ℝ)) ^ 4 * (16 : ℝ) ^ b * D) := by gcongr
    _ = _ := by
      have hp : (2 : ℝ) ^ b * (16 : ℝ) ^ b = (32 : ℝ) ^ b := by
        rw [← mul_pow]
        norm_num
      rw [← hp]
      ring

theorem bad_pencil_probability_le_common_factor
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) (hk : κ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t)
    (hgeom : ∀ (P : EqualityPattern b κ) (bits : Bits b),
      directionBadCoverMass P bits p ≤
        ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - κ) /
          (Fintype.card F : ℝ) ^ (4 * b) * t) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (4 * (b : ℝ)) ^ 4 * (1024 * K) ^ b / (b.factorial : ℝ) *
        (t / (Fintype.card F : ℝ) ^ κ) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty F)
  have hraw := bad_pencil_probability_le_direction_bound Q w K hK0 hK p hb hk
    (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - κ) /
      (Fintype.card F : ℝ) ^ (4 * b) * t) (by positivity) hgeom
  have hc := LocalAsymptotics.pencil_common_factor_le (Fintype.card F : ℝ) K b κ
    hq hK0 (by omega)
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ (4 * (b : ℝ)) ^ 4 * t / (b.factorial : ℝ) by positivity)
  refine hraw.trans ?_
  convert hm using 1 <;> push_cast <;> ring

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalAlignedReuseCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem alignment_and_badCover_probability (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) :
    offsetProbability (fun M => Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) =
      offsetProbability (AdmissibleBadCover P a bits p) := by
  congr 1
  funext M
  apply propext
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

theorem badCover_probability_le_of_conditioned (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) (t : ℝ)
    (hnorm : offsetProbability (Aligned P a bits p) =
      1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hcond : conditionedOffsetProbability (Aligned P a bits p)
      (AdmissibleBadCover P a bits p) ≤ t) :
    offsetProbability (AdmissibleBadCover P a bits p) ≤
      1 / (Fintype.card F : ℝ) ^ (4 * b) * t := by
  unfold conditionedOffsetProbability at hcond
  rw [alignment_and_badCover_probability, hnorm] at hcond
  have hp : (0 : ℝ) < 1 / (Fintype.card F : ℝ) ^ (4 * b) := by positivity
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hcond

omit [Field F] [DecidableEq F] in

theorem card_directionAssignment (hk : κ ≤ 4 * b) :
    Fintype.card (DirectionAssignment F b κ) =
      (Fintype.card F + 1) ^ (5 * b - κ) := by
  simp only [DirectionAssignment, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Direction, Fintype.card_option]
  rw [← pow_add]
  congr 1
  omega

theorem directionBadCoverMass_le_of_conditioned
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (hk : κ ≤ 4 * b) (t : ℝ) (ht : 0 ≤ t)
    (hnorm : ∀ a : DirectionAssignment F b κ, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hcond : ∀ a : DirectionAssignment F b κ, Eligible P a →
      conditionedOffsetProbability (Aligned P a bits p)
        (AdmissibleBadCover P a bits p) ≤ t) :
    directionBadCoverMass P bits p ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - κ) /
        (Fintype.card F : ℝ) ^ (4 * b) * t := by
  unfold directionBadCoverMass
  simp only [alignment_and_badCover_probability]
  calc
    _ ≤ ∑ _a : DirectionAssignment F b κ,
        1 / (Fintype.card F : ℝ) ^ (4 * b) * t := by
      apply Finset.sum_le_sum
      intro a _
      by_cases he : Eligible P a
      · rw [ite_eq_left he]
        exact badCover_probability_le_of_conditioned P a bits p t (hnorm a he) (hcond a he)
      · rw [ite_eq_right he]
        positivity
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_directionAssignment hk]
      push_cast
      ring

theorem bad_pencil_probability_le_of_conditioned
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) (hk : κ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t)
    (hnorm : ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
      ∀ bits : Bits b, offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hcond : ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
      ∀ bits : Bits b, conditionedOffsetProbability (Aligned P a bits p)
        (AdmissibleBadCover P a bits p) ≤ t) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (4 * (b : ℝ)) ^ 4 * (1024 * K) ^ b / (b.factorial : ℝ) *
        (t / (Fintype.card F : ℝ) ^ κ) := by
  apply bad_pencil_probability_le_common_factor Q w K hK0 hK p hb hk t ht
  intro P bits
  exact directionBadCoverMass_le_of_conditioned P bits p (by omega) t ht
    (fun a ha => hnorm P a ha bits) (fun a ha => hcond P a ha bits)

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPatternEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem selectedProbability_le_three_of_positive_imp
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E A B D : Configuration F → Prop)
    (himp : ∀ M v, 0 < w M v → E (configuration M v) →
      A (configuration M v) ∨ B (configuration M v) ∨ D (configuration M v)) :
    selectedProbability w E ≤ selectedProbability w A +
      selectedProbability w B + selectedProbability w D := by
  unfold selectedProbability
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro M _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  by_cases hp : 0 < w M v
  · have hnonneg := hw M v
    by_cases he : E (configuration M v)
    · rcases himp M v hp he with ha | hb | hd
      · simp only [ite_eq_left he, ite_eq_left ha]
        split_ifs <;> linarith
      · simp only [ite_eq_left he, ite_eq_left hb]
        split_ifs <;> linarith
      · simp only [ite_eq_left he, ite_eq_left hd]
        split_ifs <;> linarith
    · simp only [ite_eq_right he]
      positivity
  · have hz : w M v = 0 := le_antisymm (le_of_not_gt hp) (hw M v)
    simp only [hz, ite_self, add_zero, le_refl]

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFailureSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem selectedProbability_exists_finset_le {ι : Type*} [DecidableEq ι]
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v) (s : Finset ι)
    (E : ι → Configuration F → Prop) :
    selectedProbability w (fun C => ∃ i ∈ s, E i C) ≤
      ∑ i ∈ s, selectedProbability w (E i) := by
  have h := sum_event_union_le
    (fun z : MergedPairs F × Output F => w z.1 z.2)
    (fun z => hw z.1 z.2) s (fun i z => E i (configuration z.1 z.2))
  have hd := div_le_div_of_nonneg_right h
    (show (0 : ℝ) ≤ Fintype.card (MergedPairs F) by positivity)
  calc
    selectedProbability w (fun C => ∃ i ∈ s, E i C) =
        (∑ z : MergedPairs F × Output F,
          if ∃ i ∈ s, E i (configuration z.1 z.2) then w z.1 z.2 else 0) /
            Fintype.card (MergedPairs F) := by
      unfold selectedProbability
      apply congrArg (fun x : ℝ => x / Fintype.card (MergedPairs F))
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    _ ≤ (∑ i ∈ s, ∑ z : MergedPairs F × Output F,
        if E i (configuration z.1 z.2) then w z.1 z.2 else 0) /
          Fintype.card (MergedPairs F) := hd
    _ = _ := by simp only [Finset.sum_div, Fintype.sum_prod_type, selectedProbability]

theorem local_failure_cases (C : Configuration F) (hbad : ¬ C.LocalCondition) :
    LargePencilEvent C ∨ HighReuseEvent C ∨ SmallBadLocalEvent C := by
  unfold Configuration.LocalCondition at hbad
  push Not at hbad
  obtain ⟨p, hb, hbad⟩ := hbad
  by_cases hlarge : logBudget F < C.splitMultiplicity p
  · exact Or.inl ⟨p, hlarge⟩
  by_cases hhigh : 3 ≤ reuseCount C p
  · exact Or.inr (Or.inl ⟨p, by omega, hhigh⟩)
  refine Or.inr (Or.inr ⟨p, C.splitMultiplicity p,
    Finset.mem_Icc.mpr ⟨hb, by omega⟩, reuseCount C p,
    Finset.mem_range.mpr (by omega), rfl, rfl, hbad⟩)

theorem small_bad_local_probability_le_sum
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v) :
    selectedProbability w SmallBadLocalEvent ≤
      ∑ p : Point F, ∑ b ∈ Finset.Icc 3 (logBudget F), ∑ κ ∈ Finset.range 3,
        selectedProbability w (fun C => C.splitMultiplicity p = b ∧
          reuseCount C p = κ ∧ BadLocalCoverAt b p C) := by
  have hp := selectedProbability_exists_finset_le w hw (Finset.univ : Finset (Point F))
    (fun p C => ∃ b ∈ Finset.Icc 3 (logBudget F), ∃ κ ∈ Finset.range 3,
      C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C)
  simp only [Finset.mem_univ, true_and] at hp
  refine hp.trans (Finset.sum_le_sum fun p _ => ?_)
  refine (selectedProbability_exists_finset_le w hw (Finset.Icc 3 (logBudget F))
    (fun b C => ∃ κ ∈ Finset.range 3,
      C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C)).trans ?_
  apply Finset.sum_le_sum
  intro b _
  exact selectedProbability_exists_finset_le w hw (Finset.range 3)
    (fun κ C => C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C)

theorem small_bad_local_probability_le_envelope
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (L : ℝ) (f : ℕ → ℝ)
    (hsmall : ∀ (p : Point F) b, b ∈ Finset.Icc 3 (logBudget F) →
      ∀ κ ∈ Finset.range 3,
        selectedProbability w (fun C => C.splitMultiplicity p = b ∧
          reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤ L * f b) :
    selectedProbability w SmallBadLocalEvent ≤
      3 * L * ((Fintype.card F : ℝ) ^ 2 * ∑ b ∈ Finset.Icc 3 (logBudget F), f b) := by
  refine (small_bad_local_probability_le_sum w hw).trans ?_
  calc
    _ ≤ ∑ _p : Point F, ∑ b ∈ Finset.Icc 3 (logBudget F),
        ∑ _κ ∈ Finset.range 3, L * f b := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum (fun κ hk => hsmall p b hb κ hk)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.card_univ, Point, Fintype.card_prod, Nat.cast_mul]
      simp_rw [← mul_assoc, ← Finset.mul_sum]
      ring

theorem high_reuse_probability_le (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (C : ℝ)
    (hpoint : ∀ p : Point F,
      selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3) :
    selectedProbability w HighReuseEvent ≤ C / Fintype.card F := by
  have hu := selectedProbability_exists_finset_le w hw (Finset.univ : Finset (Point F))
    (fun p X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p)
  simp only [Finset.mem_univ, true_and] at hu
  calc
    _ ≤ ∑ p : Point F,
        selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) := hu
    _ ≤ ∑ _p : Point F, C / (Fintype.card F : ℝ) ^ 3 :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Point, Fintype.card_prod,
        Nat.cast_mul, nsmul_eq_mul]
      have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
      field_simp

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSummationArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section

theorem small_reuse_cost_le (q B x C : ℝ) (d κ : ℕ)
    (hq : 0 < q) (hB : 1 ≤ B) (hx : 0 ≤ x) (hC : 0 ≤ C) (hk : κ ≤ 3) :
    (C * x ^ d * (2 * B / q) ^ (3 - κ)) / q ^ κ ≤
      8 * C * x ^ d * (B ^ 3 / q ^ 3) := by
  have hpow : (2 * B) ^ (3 - κ) ≤ 8 * B ^ 3 := by
    calc
      (2 * B) ^ (3 - κ) ≤ (2 * B) ^ 3 :=
        pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
      _ = 8 * B ^ 3 := by ring
  calc
    (C * x ^ d * (2 * B / q) ^ (3 - κ)) / q ^ κ =
        C * x ^ d * (2 * B) ^ (3 - κ) / q ^ 3 := by
      rw [div_pow, mul_div_assoc, div_div, ← pow_add, Nat.sub_add_cancel hk]
      ring
    _ ≤ C * x ^ d * (8 * B ^ 3) / q ^ 3 := by gcongr
    _ = _ := by ring

theorem small_reuse_envelope_le (q B C A : ℝ) (b d a κ : ℕ)
    (hq : 0 < q) (hB : 1 ≤ B) (hb : 1 ≤ b) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hk : κ ≤ 3) (ha : d + 4 ≤ a) :
    (4 * (b : ℝ)) ^ 4 * A ^ b / (b.factorial : ℝ) *
      ((C * (b : ℝ) ^ d * (2 * B / q) ^ (3 - κ)) / q ^ κ) ≤
      (2048 * C) * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) * (B ^ 3 / q ^ 3)) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hcost := small_reuse_cost_le q B (b : ℝ) C d κ hq hB (Nat.cast_nonneg _) hC hk
  calc
    _ ≤ (4 * (b : ℝ)) ^ 4 * A ^ b / (b.factorial : ℝ) *
        (8 * C * (b : ℝ) ^ d * (B ^ 3 / q ^ 3)) := by gcongr
    _ = (2048 * C) * (((b : ℝ) ^ (d + 4) * A ^ b / (b.factorial : ℝ)) *
        (B ^ 3 / q ^ 3)) := by rw [pow_add]; ring
    _ ≤ _ := by
      have hp := pow_le_pow_right₀ hbR ha
      gcongr

theorem two_reuse_envelope_le (q B D A : ℝ) (b a : ℕ)
    (hq : 0 < q) (hB : 1 ≤ B) (hb : 1 ≤ b) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (ha : 7 ≤ a) :
    (4 * (b : ℝ)) ^ 4 * A ^ b / (b.factorial : ℝ) *
      ((D * (b : ℝ) ^ 3 / q) / q ^ 2) ≤
      (256 * D) * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) * (B ^ 3 / q ^ 3)) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hB3 : (1 : ℝ) ≤ B ^ 3 := one_le_pow₀ hB
  calc
    _ = (256 * D) * (((b : ℝ) ^ 7 * A ^ b / (b.factorial : ℝ)) *
        (1 / q ^ 3)) := by ring
    _ ≤ _ := by
      have hp := pow_le_pow_right₀ hbR ha
      gcongr

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalEndpointAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators Topology
universe u

theorem pencilLocal_of_reuse_and_size_bounds
    (hReuse : PencilReuseResult.{u})
    (hSmall : ∀ K : ℝ, 0 < K → ∃ a : ℕ, ∃ A L : ℝ,
      0 ≤ A ∧ 0 ≤ L ∧ ∃ q₀ : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
          KernelConditions Q w K → ∀ (p : Point F) (b κ : ℕ),
            3 ≤ b → b ≤ logBudget F → κ ≤ 2 →
            selectedProbability w (fun C => C.splitMultiplicity p = b ∧
              reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
              L * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
                ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))) :
    PencilLocalResult.{u} := by
  intro K hK
  obtain ⟨C, hC, qR, hR⟩ := hReuse K hK
  obtain ⟨a, A, L, hA, hL, qS, hS⟩ := hSmall K hK
  obtain ⟨εL, hεL, hεL0, hlarge⟩ := large_pencil_uniform_error K hK.le
  let εS : ℕ → ℝ := fun q => (q : ℝ) ^ 2 *
    ∑ b ∈ Finset.Icc 3 (Nat.ceil (Real.log (q : ℝ))),
      ((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
        ((Nat.ceil (Real.log (q : ℝ)) : ℝ) ^ 3 / (q : ℝ) ^ 3)
  have hεS : Tendsto εS atTop (𝓝 0) :=
    LocalAsymptotics.tendsto_plane_weighted_pencil_sum a A hA
      (fun q => Finset.Icc 3 (Nat.ceil (Real.log (q : ℝ))))
  have hinv : Tendsto (fun q : ℕ => C / (q : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  refine ⟨fun q => εL q + C / (q : ℝ) + 3 * L * εS q, ?_, ?_, max qR qS, ?_⟩
  · simpa using (hεL.add hinv).add (hεS.const_mul (3 * L))
  · intro q
    have hs : 0 ≤ εS q := by dsimp [εS]; positivity
    exact add_nonneg (add_nonneg (hεL0 q) (by positivity)) (by positivity)
  · intro F _ _ _ hq Q w hw
    have hR' := hR F ((le_max_left _ _).trans hq) Q w hw
    have hS' := hS F ((le_max_right _ _).trans hq) Q w hw
    have hlarge' : selectedProbability w LargePencilEvent ≤ εL (Fintype.card F) := by
      refine (KernelBridge.selectedProbability_mono w hw.1 ?_).trans (hlarge F Q w hw)
      intro X hX
      obtain ⟨p, hp⟩ := hX
      exact ⟨p, hp.le⟩
    have hhigh := high_reuse_probability_le w hw.1 C hR'
    have hsmall : selectedProbability w SmallBadLocalEvent ≤
        3 * L * εS (Fintype.card F) := by
      apply small_bad_local_probability_le_envelope w hw.1 L
        (fun b => ((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
          ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))
      intro p b hb κ hk
      exact hS' p b κ (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
        (by have := Finset.mem_range.mp hk; omega)
    have hcases := selectedProbability_le_three_of_positive_imp w hw.1
      (fun X => ¬ X.LocalCondition) LargePencilEvent HighReuseEvent SmallBadLocalEvent
      (fun _ _ _ hbad => local_failure_cases _ hbad)
    exact hcases.trans (add_le_add (add_le_add hlarge' hhigh) hsmall)

theorem pencilLocal_of_three_reuse_estimates
    (hReuse : PencilReuseResult.{u}) (hSmall : PencilSmallReuseResult.{u})
    (hTwo : PencilTwoReusesResult.{u}) : PencilLocalResult.{u} := by
  apply pencilLocal_of_reuse_and_size_bounds hReuse
  intro K hK
  obtain ⟨hnorm, C, hC, d, qS, hS⟩ := hSmall
  obtain ⟨D, hD, qT, hT⟩ := hTwo
  refine ⟨d + 7, 1024 * K, 2048 * C + 256 * D,
    by positivity, by positivity, max qS qT, ?_⟩
  intro F _ _ _ hq Q w hw p b κ hb hB hk
  have hqR : (0 : ℝ) < Fintype.card F := by positivity
  have hBR : (1 : ℝ) ≤ logBudget F := by
    exact_mod_cast (show 1 ≤ logBudget F by omega)
  let W : ℝ := (((b : ℝ) ^ (d + 7) * (1024 * K) ^ b / (b.factorial : ℝ)) *
    ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  by_cases hk2 : κ = 2
  · subst κ
    have hraw := bad_pencil_probability_le_common_factor Q w K hK.le hw p
      (by omega : 2 ≤ b) (by omega : 2 ≤ 2)
      (D * (b : ℝ) ^ 3 / Fintype.card F) (by positivity) (by
        intro P bits
        exact hT F ((le_max_right _ _).trans hq) b hb hB P bits p)
    have harith := two_reuse_envelope_le (Fintype.card F : ℝ) (logBudget F : ℝ)
      D (1024 * K) b (d + 7) hqR hBR (by omega) hD.le (by positivity) (by omega)
    refine hraw.trans (harith.trans ?_)
    change (256 * D) * W ≤ (2048 * C + 256 * D) * W
    exact mul_le_mul_of_nonneg_right (by linarith) hW
  · have hk1 : κ ≤ 1 := by omega
    have hraw := bad_pencil_probability_le_of_conditioned Q w K hK.le hw p
      (by omega : 2 ≤ b) hk
      (C * (b : ℝ) ^ d * (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ))
      (by positivity)
      (fun P a ha bits => hnorm F b κ hb hB hk P a ha bits p)
      (fun P a ha bits => hS F ((le_max_left _ _).trans hq) b κ hb hB hk1 P a ha bits p)
    have harith := small_reuse_envelope_le (Fintype.card F : ℝ) (logBudget F : ℝ)
      C (1024 * K) b d (d + 7) κ hqR hBR (by omega) hC.le (by positivity)
      (by omega) (by omega)
    refine hraw.trans (harith.trans ?_)
    change (2048 * C) * W ≤ (2048 * C + 256 * D) * W
    exact mul_le_mul_of_nonneg_right (by linarith) hW

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalEndpointReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

universe u

theorem pencilLocal_of_small_and_two_reuse
    (hSmall : PencilSmallReuseResult.{u})
    (hTwo : PencilTwoReusesResult.{u}) : PencilLocalResult.{u} :=
  pencilLocal_of_three_reuse_estimates pencilReuse_proof hSmall hTwo

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalEndpointCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

universe u

theorem pencilLocal_of_two_reuses
    (hTwo : PencilTwoReusesResult.{u}) : PencilLocalResult.{u} :=
  pencilLocal_of_small_and_two_reuse pencilSmallReuse_proof hTwo

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalDirectionAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

theorem eligible_not_allTokensDistinct_iff {F : Type*} {b κ : ℕ}
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (ha : Eligible P a) :
    ¬ AllTokensDistinct a ↔ ∃ i j, a.1 i = a.2 j := by
  constructor
  · intro h
    by_contra hex
    apply h
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (ha.1 hxy)
        | inr j => exact False.elim (hex ⟨i, j, hxy⟩)
    | inr i =>
        cases y with
        | inl j => exact False.elim (hex ⟨j, i, hxy.symm⟩)
        | inr j => exact congrArg Sum.inr (ha.2.1 hxy)
  · rintro ⟨i, j, hij⟩ hd
    have h' : Sum.inl i = (Sum.inr j : DirectionToken b κ) := hd hij
    cases h'

theorem card_directionToken_two {b : ℕ} (hb : 1 ≤ b) :
    Fintype.card (DirectionToken b 2) = 5 * b - 2 := by
  simp only [DirectionToken, Fintype.card_sum, Fintype.card_fin]
  omega

section CrossEquality

variable {I G J : Type*} [Fintype I] [Fintype G] [Fintype J]
  [DecidableEq I] [DecidableEq G] [DecidableEq J]

theorem card_crossEquality (i : I) (j : G) :
    ((Finset.univ : Finset ((I → J) × (G → J))).filter
      (fun a => a.1 i = a.2 j)).card =
        Fintype.card J ^ (Fintype.card I - 1) * Fintype.card J ^ Fintype.card G := by
  have hsub : Fintype.card {k : I // k ≠ i} = Fintype.card I - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun k : I => k = i)
  have h := Fintype.card_congr (crossEqualityEquiv (J := J) i j)
  simpa only [Fintype.card_subtype, Fintype.card_prod, Fintype.card_fun, hsub] using h

theorem card_any_crossEquality_le :
    ((Finset.univ : Finset ((I → J) × (G → J))).filter
      (fun a => ∃ i j, a.1 i = a.2 j)).card ≤
        (Fintype.card I * Fintype.card G) *
          (Fintype.card J ^ (Fintype.card I - 1) * Fintype.card J ^ Fintype.card G) := by
  classical
  let E (ij : I × G) := (Finset.univ : Finset ((I → J) × (G → J))).filter
    (fun a => a.1 ij.1 = a.2 ij.2)
  calc
    _ ≤ (Finset.univ.biUnion E).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, j, hij⟩ := (Finset.mem_filter.mp ha).2
      exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, by simp [E, hij]⟩
    _ ≤ ∑ ij : I × G, (E ij).card := Finset.card_biUnion_le
    _ = _ := by
      simp only [E, card_crossEquality, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, smul_eq_mul]

end CrossEquality

section FiniteField

variable {F : Type*} [Fintype F]

open scoped Classical in

theorem card_eligible_not_allDistinct_two_le {b : ℕ} (hb : 1 ≤ b)
    (P : EqualityPattern b 2) :
    ((Finset.univ : Finset (DirectionAssignment F b 2)).filter
      (fun a => Eligible P a ∧ ¬ AllTokensDistinct a)).card ≤
        b * (4 * b - 2) * (Fintype.card F + 1) ^ (5 * b - 3) := by
  classical
  have hexp : (b - 1) + (4 * b - 2) = 5 * b - 3 := by omega
  calc
    _ ≤ ((Finset.univ : Finset (DirectionAssignment F b 2)).filter
        (fun a => ∃ i j, a.1 i = a.2 j)).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨_, ha, hnot⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (eligible_not_allTokensDistinct_iff P a ha).mp hnot⟩
    _ ≤ _ := by
      have h := card_any_crossEquality_le (I := Fin b) (G := Fin (4 * b - 2))
        (J := Direction F)
      simpa only [Fintype.card_fin, Direction, Fintype.card_option,
        ← pow_add, hexp] using h

theorem card_token_injections_two_le {b : ℕ} (hb : 1 ≤ b) :
    Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
      (Fintype.card F + 1) ^ (5 * b - 2) := by
  have h : Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
      Fintype.card (DirectionToken b 2 → Direction F) :=
    Fintype.card_le_of_injective _ Function.Embedding.coe_injective
  simpa only [Fintype.card_fun, card_directionToken_two hb,
    Direction, Fintype.card_option] using h

end FiniteField

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalNoninjectiveContribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem joint_alignment_probability_le {b κ : ℕ} (P : EqualityPattern b κ)
    (hκ : κ ≤ 2) (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (E : MergedPairs F → Prop) :
    offsetProbability (fun M => Aligned P a bits p M ∧ E M) ≤
      1 / (Fintype.card F : ℝ) ^ (4 * b) := by
  calc
    _ ≤ offsetProbability (Aligned P a bits p) :=
      KernelBridge.offsetProbability_mono (fun _ h => h.1)
    _ = _ := alignment_probability P hκ a ha bits p

theorem sum_noninjective_joint_le {b : ℕ} (hb : 1 ≤ b)
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b 2 → MergedPairs F → Prop) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a ∧ ¬ AllTokensDistinct a then
        offsetProbability (fun M => Aligned P a bits p M ∧ E a M) else 0) ≤
      (b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3) /
        (Fintype.card F : ℝ) ^ (4 * b) := by
  let S := (Finset.univ : Finset (DirectionAssignment F b 2)).filter
    (fun a => Eligible P a ∧ ¬ AllTokensDistinct a)
  have hsum : (∑ a ∈ S,
      offsetProbability (fun M => Aligned P a bits p M ∧ E a M)) ≤
      (S.card : ℝ) * (1 / (Fintype.card F : ℝ) ^ (4 * b)) := by
    calc
      _ ≤ ∑ _a ∈ S, (1 / (Fintype.card F : ℝ) ^ (4 * b)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact joint_alignment_probability_le P (by omega) a
          (Finset.mem_filter.mp ha).2.1 bits p (E a)
      _ = _ := by simp
  have hcard : (S.card : ℝ) ≤
      (b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3) := by
    exact_mod_cast card_eligible_not_allDistinct_two_le (F := F) hb P
  calc
    _ = ∑ a ∈ S, offsetProbability (fun M => Aligned P a bits p M ∧ E a M) := by
      simp only [S, Finset.sum_filter]
    _ ≤ (S.card : ℝ) * (1 / (Fintype.card F : ℝ) ^ (4 * b)) := hsum
    _ ≤ ((b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3)) *
        (1 / (Fintype.card F : ℝ) ^ (4 * b)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem noninjective_coefficient_le {b : ℕ} (hb : 1 ≤ b)
    {q : ℝ} (hq : 0 < q) :
    (b : ℝ) * (4 * b - 2 : ℕ) * (q + 1) ^ (5 * b - 3) / q ^ (4 * b) ≤
      (q + 1) ^ (5 * b - 2) / q ^ (4 * b) * (4 * (b : ℝ) ^ 3 / q) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hsub : ((4 * b - 2 : ℕ) : ℝ) ≤ 4 * (b : ℝ) := by
    exact_mod_cast (Nat.sub_le (4 * b) 2)
  have hbnonneg : (0 : ℝ) ≤ b := by positivity
  have hcoef : (b : ℝ) * (4 * b - 2 : ℕ) ≤ 4 * (b : ℝ) ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_left hsub hbnonneg
    have h₂ : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 3 := by
      nlinarith [sq_nonneg (b : ℝ)]
    nlinarith
  have hexp : 5 * b - 2 = (5 * b - 3) + 1 := by omega
  have hbase : (b : ℝ) * (4 * b - 2 : ℕ) * q ≤
      4 * (b : ℝ) ^ 3 * (q + 1) := by
    have h := mul_le_mul_of_nonneg_right hcoef hq.le
    nlinarith [pow_nonneg hbnonneg 3]
  have hbase' : (b : ℝ) * (4 * b - 2 : ℕ) ≤
      4 * (b : ℝ) ^ 3 * (q + 1) / q := (le_div_iff₀ hq).mpr hbase
  calc
    _ = ((q + 1) ^ (5 * b - 3) / q ^ (4 * b)) *
        ((b : ℝ) * (4 * b - 2 : ℕ)) := by ring
    _ ≤ ((q + 1) ^ (5 * b - 3) / q ^ (4 * b)) *
        (4 * (b : ℝ) ^ 3 * (q + 1) / q) :=
      mul_le_mul_of_nonneg_left hbase' (by positivity)
    _ = _ := by rw [hexp, pow_succ]; ring

theorem sum_noninjective_badCover_le {b : ℕ} (hb : 1 ≤ b)
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a ∧ ¬ AllTokensDistinct a then
        offsetProbability (fun M =>
          Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) * (4 * (b : ℝ) ^ 3 / Fintype.card F) := by
  apply (sum_noninjective_joint_le hb P bits p
    (fun a => AdmissibleBadCover P a bits p)).trans
  simpa only [Nat.cast_add, Nat.cast_one] using
    noninjective_coefficient_le hb (q := (Fintype.card F : ℝ)) (by positivity)

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem injective_joint_sum_le_of_conditional {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (C : ℝ)
    (halign : ∀ a : DirectionAssignment F b 2, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hbound : (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then
        conditionedOffsetProbability (Aligned P a bits p)
          (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F)) :
    (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then
        offsetProbability (fun M => Aligned P a bits p M ∧
          AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) *
          (C * (b : ℝ) ^ 3 / Fintype.card F) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have heq (a : DirectionAssignment F b 2) (ha : AllTokensDistinct a) :
      offsetProbability (fun M => Aligned P a bits p M ∧
        AdmissibleBadCover P a bits p M) =
      (1 / (Fintype.card F : ℝ) ^ (4 * b)) *
        conditionedOffsetProbability (Aligned P a bits p)
          (AdmissibleBadCover P a bits p) := by
    unfold conditionedOffsetProbability
    rw [halign a (allTokensDistinct_eligible P a ha)]
    field_simp
  calc
    _ = (1 / (Fintype.card F : ℝ) ^ (4 * b)) *
        ∑ a : DirectionAssignment F b 2,
          if AllTokensDistinct a then conditionedOffsetProbability
            (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : AllTokensDistinct a
      · simp only [ha, ite_true, heq a ha]
      · simp only [ha, ite_false, mul_zero]
    _ ≤ (1 / (Fintype.card F : ℝ) ^ (4 * b)) *
        (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
          (C * (b : ℝ) ^ 3 / Fintype.card F)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

theorem direction_sum_le_of_injective {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (hb : 1 ≤ b) (C : ℝ)
    (halign : ∀ a : DirectionAssignment F b 2, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hbound : (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then
        conditionedOffsetProbability (Aligned P a bits p)
          (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F)) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a then offsetProbability (fun M =>
        Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) *
          ((C + 4) * (b : ℝ) ^ 3 / Fintype.card F) := by
  let W : DirectionAssignment F b 2 → ℝ := fun a =>
    offsetProbability (fun M => Aligned P a bits p M ∧
      AdmissibleBadCover P a bits p M)
  have hsplit : (∑ a, if Eligible P a then W a else 0) =
      (∑ a, if AllTokensDistinct a then W a else 0) +
        ∑ a, if Eligible P a ∧ ¬ AllTokensDistinct a then W a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : AllTokensDistinct a
    · simp only [ha, allTokensDistinct_eligible P a ha, ite_true,
        not_true_eq_false, and_false, ite_false, add_zero]
    · by_cases he : Eligible P a <;> simp [ha, he]
  change (∑ a, if Eligible P a then W a else 0) ≤ _
  rw [hsplit]
  have hi := injective_joint_sum_le_of_conditional P bits p C halign hbound
  have hc := sum_noninjective_badCover_le hb P bits p
  calc
    _ ≤ (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) * (C * (b : ℝ) ^ 3 / Fintype.card F)) +
        (((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) * (4 * (b : ℝ) ^ 3 / Fintype.card F)) :=
      add_le_add hi hc
    _ = _ := by ring

universe u

theorem pencilTwoReuses_of_alignment_and_injective
    (halign : AlignmentNormalizationResult.{u})
    (hinjective : InjectiveTwoReuseEstimate.{u}) : PencilTwoReusesResult.{u} := by
  obtain ⟨C, hC, q₀, hbound⟩ := hinjective
  refine ⟨C + 4, by linarith, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  apply direction_sum_le_of_injective P bits p (by omega) C
  · intro a ha
    exact halign F b 2 hb hB (by omega) P a ha bits p
  · exact hbound F hq b hb hB P bits p

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped BigOperators Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
omit [Field F] [DecidableEq F] in
theorem sum_allTokensDistinct_eq {b κ : ℕ}
    (f : DirectionAssignment F b κ → ℝ) :
    (∑ a : DirectionAssignment F b κ, if AllTokensDistinct a then f a else 0) =
      ∑ e : DirectionToken b κ ↪ Direction F, f (tokenInjectionEquiv F b κ e).1 := by
  calc
    _ = ∑ a ∈ (Finset.univ.filter (fun a : DirectionAssignment F b κ => AllTokensDistinct a)), f a := by
      rw [Finset.sum_filter]
    _ = ∑ a : {a : DirectionAssignment F b κ // AllTokensDistinct a}, f a.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := (Equiv.sum_comp (tokenInjectionEquiv F b κ) (fun a => f a.1)).symm

theorem injective_conditional_sum_le_of_embedding_sum {b : ℕ}
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (hb : 1 ≤ b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : (∑ e : DirectionToken b 2 ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
        (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) ≤
      (Fintype.card (DirectionToken b 2 ↪ Direction F) : ℝ) *
        (C * (b : ℝ) ^ 3 / Fintype.card F)) :
    (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then conditionedOffsetProbability
        (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F) := by
  rw [sum_allTokensDistinct_eq]
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast card_token_injections_two_le (F := F) hb
theorem sum_le_card_mul_of_mean_le {I : Type*} [Fintype I]
    (f : I → ℝ) (B : ℝ) (h : (∑ i, f i) / Fintype.card I ≤ B) :
    (∑ i, f i) ≤ (Fintype.card I : ℝ) * B := by
  by_cases hc : Fintype.card I = 0
  · have : IsEmpty I := Fintype.card_eq_zero_iff.mp hc
    simp
  · have hp : (0 : ℝ) < Fintype.card I := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    simpa [mul_comm] using (div_le_iff₀ hp).mp h

theorem injective_conditional_sum_le_of_embedding_mean {b : ℕ}
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (hb : 1 ≤ b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : (∑ e : DirectionToken b 2 ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
        (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) /
        Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
      C * (b : ℝ) ^ 3 / Fintype.card F) :
    (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then conditionedOffsetProbability
        (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F) :=
  injective_conditional_sum_le_of_embedding_sum P bits p hb C hC
    (sum_le_card_mul_of_mean_le _ _ hbound)

universe u

theorem pencilTwoReuses_of_alignment_and_injective_mean
    (halign : AlignmentNormalizationResult.{u})
    (hmean : InjectiveTwoReuseMeanEstimate.{u}) : PencilTwoReusesResult.{u} := by
  apply pencilTwoReuses_of_alignment_and_injective halign
  obtain ⟨C, hC, q₀, hbound⟩ := hmean
  refine ⟨C, hC, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  exact injective_conditional_sum_le_of_embedding_mean P bits p (by omega) C hC.le
    (hbound F hq b hb hB P bits p)

theorem pencilTwoReuses_of_injective_mean
    (hmean : InjectiveTwoReuseMeanEstimate.{u}) : PencilTwoReusesResult.{u} :=
  pencilTwoReuses_of_alignment_and_injective_mean alignmentNormalization_proof hmean

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseUsedEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped Classical BigOperators

theorem unused_errors_le (q b : ℝ) (hq : 1 ≤ q) (hb : 1 ≤ b) :
    8 * b * (q + 1) / q ^ 2 + 384 * b ^ 3 / q ^ 2 ≤ 400 * b ^ 3 / q := by
  have hq0 : 0 < q := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  have hbb : b ≤ b ^ 3 := by nlinarith [sq_nonneg (b - 1)]
  have hfirst : 8 * b * (q + 1) ≤ 16 * b ^ 3 * q := by
    calc
      _ ≤ 8 * b ^ 3 * (q + 1) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hb3 (sub_nonneg.mpr hq)]
  have hlast : 384 * b ^ 3 ≤ 384 * b ^ 3 * q := by
    nlinarith [mul_nonneg hb3 (sub_nonneg.mpr hq)]
  calc
    _ = (8 * b * (q + 1) + 384 * b ^ 3) / q ^ 2 := by ring
    _ ≤ (400 * b ^ 3 * q) / q ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg q)
    _ = _ := by field_simp

theorem mean_le_mean_add {I : Type*} [Fintype I]
    (f g : I → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, f i ≤ g i + B) :
    (∑ i, f i) / Fintype.card I ≤ (∑ i, g i) / Fintype.card I + B := by
  by_cases hc : Fintype.card I = 0
  · simpa [hc] using hB
  have hcR : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hc
  calc
    _ ≤ (∑ i, (g i + B)) / Fintype.card I :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_add_distrib]; simp; field_simp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem badCover_mean_le_usedEventMean {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (hb : 3 ≤ b) :
    (∑ e : DirectionToken b 2 ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
        (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) /
      Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
        usedEventMean P bits p + 400 * (b : ℝ) ^ 3 / Fintype.card F := by
  apply mean_le_mean_add _ _ _ (by positivity)
  intro e
  let a := (tokenInjectionEquiv F b 2 e).1
  have ha : Eligible P a := allTokensDistinct_eligible P a (tokenInjectionEquiv F b 2 e).2
  have h := UnusedTripleProbability.conditioned_badCover_le_used_events
    P hb (by omega) a ha bits p
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hn := unused_errors_le (Fintype.card F : ℝ) (b : ℝ) hq hbR
  change conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
    usedEventConditionalMass P a bits p + _
  unfold usedEventConditionalMass
  linarith

universe u

theorem pencilTwoReuses_of_used_event_mean
    (hused : InjectiveUsedEventsEstimate.{u}) : PencilTwoReusesResult.{u} := by
  apply pencilTwoReuses_of_injective_mean
  obtain ⟨C, hC, q₀, hbound⟩ := hused
  refine ⟨C + 400, by linarith only [hC], q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  have h₁ := badCover_mean_le_usedEventMean P bits p hb
  have h₂ : usedEventMean P bits p + 400 * (b : ℝ) ^ 3 / Fintype.card F ≤
      C * (b : ℝ) ^ 3 / Fintype.card F + 400 * (b : ℝ) ^ 3 / Fintype.card F :=
    add_le_add (hbound F hq b hb hB P bits p) le_rfl
  have hn : C * (b : ℝ) ^ 3 / Fintype.card F +
      400 * (b : ℝ) ^ 3 / Fintype.card F =
      (C + 400) * (b : ℝ) ^ 3 / Fintype.card F := by ring
  exact h₁.trans (h₂.trans_eq hn)

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
open RootChildPartition AlignedGlobal UsedEventUnion Timing
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

universe u

theorem pencilTwoReuses_proof : PencilTwoReusesResult.{u} :=
  TwoReuseAssembly.pencilTwoReuses_of_used_event_mean injectiveUsedEventsEstimate_proof

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_FinalLocalEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

universe u

theorem pencilLocal_proof : PencilLocalResult.{u} :=
  pencilLocal_of_two_reuses pencilTwoReuses_proof

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DistinctRoleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal Classical

namespace Balanced.DistinctRole

variable {D F : Type*} [Field F]

variable [Fintype D] [Fintype F]

instance distinctNonempty :
    Nonempty {M : D → Bool → F // ∀ d, M d false ≠ M d true} :=
  ⟨⟨fun _ b => if b then 0 else 1, by simp⟩⟩

end Balanced.DistinctRole

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternExposureBoundary
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

@[simp] theorem count_eq_zero_of_isEmpty [IsEmpty P.Label] (ω : P.Sample) :
    P.count ω = 0 := by
  simp [count]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem pencil_local_oai : Local.PencilLocalResult.{u} := Local.pencilLocal_proof

end Balanced

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.pencil_local_oai.{u} := @OAI.Balanced.pencil_local_oai.{u}
