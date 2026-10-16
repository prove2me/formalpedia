-- Prove2me | solution 1 for OAI.RandomKSAT.hall_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:44:04.559104+00:00
-- url     : https://prove2.me/submissions/6c9fc4dd-2503-4b56-ae6a-d35f4ca0d3cb

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/HallSatisfiability.lean:L185-L228
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.hall_probability_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Theorems.Thm_OAI_RandomKSAT_killRatio_le_density_pow

-- ---- from OAI.Probability.SATVariance.ClauseCombinatorics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sum.{u_1, u_2} {α : Type u_1} {ι : Type u_2} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    favg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, favg (f i) := by
  simp only [favg, Finset.sum_div]
  exact Finset.sum_comm

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_pi_product.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℝ) :
    favg (fun x : ι → α => ∏ i, f i (x i)) = ∏ i, favg (f i) := by
  classical
  unfold favg
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.HallSatisfiability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma finiteSAT_of_hall {n k m : ℕ} (w : Fin m → Clause n k)
    (hh : ∀ I : Finset (Fin m), I.card ≤ (I.biUnion (fun j => (w j).1.1)).card) :
    finiteSAT w m := by
  obtain ⟨f,hf,hm⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun j => (w j).1.1)).mp hh
  let a : Assignment n := Function.extend f (fun j => (w j).2 ⟨f j,hm j⟩) (fun _ => false)
  refine ⟨a,fun j _ => ⟨⟨f j,hm j⟩,?_⟩⟩
  exact hf.extend_apply _ _ j

lemma deficient_witness {n k m : ℕ} (w : Fin m → Clause n k) (hw : ¬finiteSAT w m) :
    ∃ W : Finset (Fin n), ∃ I : Finset (Fin m), I.card = W.card+1 ∧
      ∀ j ∈ I, (w j).1.1 ⊆ W := by
  have hh : ¬∀ I : Finset (Fin m), I.card ≤ (I.biUnion (fun j => (w j).1.1)).card :=
    fun h => hw (finiteSAT_of_hall w h)
  push Not at hh
  obtain ⟨J,hJ⟩ := hh
  obtain ⟨I,hIJ,hI⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hJ)
  refine ⟨J.biUnion (fun j => (w j).1.1),I,hI,fun j hj v hv => ?_⟩
  exact Finset.mem_biUnion.mpr ⟨j,hIJ hj,hv⟩

lemma favg_support {n k : ℕ} (f : {s : Finset (Fin n) // s.card = k} → ℝ) :
    favg (fun c : Clause n k => f c.1) = favg f := by
  unfold favg
  change (∑ c : (s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool), f c.1) /
    Fintype.card (Clause n k) = _
  rw [Fintype.sum_sigma, clause_card, support_card]
  have he (s : {s : Finset (Fin n) // s.card = k}) : (∑ _ : s.1 → Bool, f s) = 2^k*f s := by
    simp [s.property]
  simp only [he, ← Finset.mul_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2:ℝ)^k ≠ 0 := by positivity
  field_simp

lemma containing_support_probability {n k : ℕ} (W : Finset (Fin n)) :
    favg (fun c : Clause n k => if c.1.1 ⊆ W then (1:ℝ) else 0) =
      (W.card.choose k : ℝ)/(n.choose k) := by
  have he0 := favg_support (fun s : {s : Finset (Fin n) // s.card = k} =>
    if s.val ⊆ W then (1:ℝ) else 0)
  rw [he0]
  unfold favg
  rw [support_card, Finset.sum_boole]
  congr 1
  have he : {s : {s : Finset (Fin n) // s.card = k} // s.1 ⊆ W} ≃
      {s : Finset (Fin n) // s ⊆ W ∧ s.card = k} :=
    { toFun := fun s => ⟨s.1.1,s.2,s.1.2⟩
      invFun := fun s => ⟨⟨s.1,s.2.2⟩,s.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr he
  rw [Fintype.card_of_subtype (W.powersetCard k) (by intro s; simp)] at hc
  simpa only [Fintype.card_subtype, Finset.card_powersetCard] using congrArg (fun x : ℕ => (x:ℝ)) hc

lemma containing_support_bound {n k : ℕ} (hkn : k ≤ n) (W : Finset (Fin n)) :
    favg (fun c : Clause n k => if c.1.1 ⊆ W then (1:ℝ) else 0) ≤
      ((W.card : ℝ)/n)^k := by
  rw [containing_support_probability]
  have hb : W.card ≤ n := (Finset.card_le_univ W).trans_eq (Fintype.card_fin n)
  have hh := mul_le_mul_of_nonneg_left (killRatio_le_density_pow hb hkn)
    (show (0:ℝ) ≤ 2^k by positivity)
  have he1 : (2:ℝ)^k*killRatio n W.card k = (W.card.choose k : ℝ)/(n.choose k) := by
    unfold killRatio
    field_simp
  have he2 : (2:ℝ)^k*((W.card:ℝ)/(2*n))^k = ((W.card:ℝ)/n)^k := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [he1,he2] at hh
  exact hh

lemma favg_pi_on.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (I : Finset ι) (f : α → ℝ) :
    favg (fun w : ι → α => ∏ i ∈ I, f (w i)) = (favg f)^I.card := by
  have he (w : ι → α) : (∏ i ∈ I, f (w i)) = ∏ i, if i ∈ I then f (w i) else 1 := by
    symm
    rw [← Finset.prod_filter]
    congr 1
    ext i
    simp
  simp only [he]
  change favg (fun w : ι → α => ∏ i, (fun i a => if i ∈ I then f a else 1) i (w i)) = _
  rw [favg_pi_product (fun i a => if i ∈ I then f a else 1)]
  have hh (i : ι) : favg (fun a => if i ∈ I then f a else 1) = if i ∈ I then favg f else 1 := by
    split_ifs <;> simp [favg_const]
  simp only [hh]
  rw [← Finset.prod_filter]
  have he' : Finset.univ.filter (fun i => i ∈ I) = I := by ext i; simp
  rw [he', Finset.prod_const]

lemma hall_union_pointwise {n k m : ℕ} (w : Fin m → Clause n k) :
    (if ¬finiteSAT w m then (1:ℝ) else 0) ≤
      ∑ W : Finset (Fin n), ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1),
        ∏ i ∈ I, if (w i).1.1 ⊆ W then (1:ℝ) else 0 := by
  have hn (W : Finset (Fin n)) (I : Finset (Fin m)) :
      0 ≤ ∏ i ∈ I, if (w i).1.1 ⊆ W then (1:ℝ) else 0 := by positivity
  by_cases hw : finiteSAT w m
  · rw [ite_eq_right (not_not.mpr hw)]
    exact Finset.sum_nonneg (fun W _ => Finset.sum_nonneg (fun I _ => hn W I))
  · rw [ite_eq_left hw]
    obtain ⟨W,I,hI,hwI⟩ := deficient_witness w hw
    have hi : I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1) := by simp [hI]
    calc
      1 = ∏ i ∈ I, if (w i).1.1 ⊆ W then (1:ℝ) else 0 := by
        symm
        apply Finset.prod_eq_one
        intro i hi
        simp [hwI i hi]
      _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1),
          ∏ i ∈ J, if (w i).1.1 ⊆ W then (1:ℝ) else 0 :=
        Finset.single_le_sum (fun J _ => hn W J) hi
      _ ≤ _ := Finset.single_le_sum
        (f := fun W : Finset (Fin n) => ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1),
          ∏ i ∈ I, if (w i).1.1 ⊆ W then (1:ℝ) else 0)
        (fun W _ => Finset.sum_nonneg (fun I _ => hn W I)) (Finset.mem_univ W)

lemma hall_term_bound {n m t : ℕ} (hn : 0 < n) (htn : t ≤ n) {a : ℝ}
    (ha : 0 ≤ a) (hm : (m:ℝ) ≤ a*n) :
    (n.choose t : ℝ)*(m.choose (t+1) : ℝ)*((t:ℝ)/n)^(2*(t+1)) ≤
      a*(Real.exp 2*a)^t := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hn'
  have ht : (0:ℝ) ≤ t := by positivity
  have htn' : (t:ℝ)/n ≤ 1 := (div_le_one hn').mpr (by exact_mod_cast htn)
  have hmn : (m:ℝ)/n ≤ a := (div_le_iff₀ hn').mpr hm
  have hfac : (0:ℝ) < t.factorial := by positivity
  have hfac' : (0:ℝ) < (t+1).factorial := by positivity
  calc
    _ ≤ ((n:ℝ)^t/t.factorial)*((m:ℝ)^(t+1)/(t+1).factorial)*((t:ℝ)/n)^(2*(t+1)) := by
      gcongr
      · exact Nat.choose_le_pow_div t n
      · exact Nat.choose_le_pow_div (t+1) m
    _ = ((m:ℝ)/n)^(t+1)*((t:ℝ)/n)*
        ((t:ℝ)^t/t.factorial)*((t:ℝ)^(t+1)/(t+1).factorial) := by
      rw [show 2*(t+1) = t+t+2 by omega]
      simp only [pow_add, pow_succ, div_pow]
      field_simp
    _ ≤ a^(t+1)*1*(Real.exp t)*(Real.exp t) := by
      gcongr
      · exact Real.pow_div_factorial_le_exp t ht t
      · exact Real.pow_div_factorial_le_exp t ht (t+1)
    _ = a*(Real.exp 2*a)^t := by
      rw [mul_one, mul_assoc, ← Real.exp_add,
        show (t:ℝ)+(t:ℝ) = (t:ℝ)*2 by ring, Real.exp_nat_mul, mul_pow, pow_succ]
      ring

lemma finite_geometric_half {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1/2) (N : ℕ) :
    (∑ t ∈ Finset.range N, r^t) ≤ 2 := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  calc
    _ ≤ ∑' t : ℕ, r^t := (summable_geometric_of_norm_lt_one hn).sum_le_tsum _
      (fun t _ => pow_nonneg hr t)
    _ = (1-r)⁻¹ := tsum_geometric_of_norm_lt_one hn
    _ ≤ 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (by linarith)).mpr
      linarith

lemma hall_sum_bound {n m : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a)
    (ha' : Real.exp 2*a ≤ 1/2) (hm : (m:ℝ) ≤ a*n) :
    (∑ t ∈ Finset.range (n+1), (n.choose t : ℝ)*(m.choose (t+1) : ℝ)*
      ((t:ℝ)/n)^(2*(t+1))) ≤ 2*a := by
  calc
    _ ≤ ∑ t ∈ Finset.range (n+1), a*(Real.exp 2*a)^t := by
      apply Finset.sum_le_sum
      intro t ht
      exact hall_term_bound hn (by have := Finset.mem_range.mp ht; omega) ha hm
    _ = a*(∑ t ∈ Finset.range (n+1), (Real.exp 2*a)^t) := by rw [Finset.mul_sum]
    _ ≤ a*2 := mul_le_mul_of_nonneg_left (finite_geometric_half (by positivity) ha' _) ha
    _ = _ := by ring

lemma hall_probability_bound {n k m : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {a : ℝ} (ha : 0 ≤ a) (ha' : Real.exp 2*a ≤ 1/2) (hm : (m:ℝ) ≤ a*n) :
    favg (fun w : Fin m → Clause n k => if ¬finiteSAT w m then (1:ℝ) else 0) ≤ 2*a := by
  let := clause_nonempty n k hkn
  have hn : 0 < n := by omega
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hi (W : Finset (Fin n)) (I : Finset (Fin m))
      (hI : I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1)) :
      favg (fun w : Fin m → Clause n k => ∏ i ∈ I,
        if (w i).1.1 ⊆ W then (1:ℝ) else 0) ≤ ((W.card:ℝ)/n)^(2*(W.card+1)) := by
    rw [favg_pi_on I (fun c : Clause n k => if c.1.1 ⊆ W then (1:ℝ) else 0)]
    have hic := (Finset.mem_powersetCard.mp hI).2
    rw [hic, pow_mul]
    apply pow_le_pow_left₀ (favg_nonneg (fun _ => by positivity))
    apply (containing_support_bound hkn W).trans
    have hr : (W.card:ℝ)/n ≤ 1 := (div_le_one hn').mpr (by exact_mod_cast (show W.card ≤ n by simpa using Finset.card_le_univ W))
    exact pow_le_pow_of_le_one (by positivity) hr hk
  calc
    _ ≤ favg (fun w : Fin m → Clause n k =>
        ∑ W : Finset (Fin n), ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1),
        ∏ i ∈ I, if (w i).1.1 ⊆ W then (1:ℝ) else 0) := favg_mono hall_union_pointwise
    _ = ∑ W : Finset (Fin n), ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1),
        favg (fun w : Fin m → Clause n k =>
          ∏ i ∈ I, if (w i).1.1 ⊆ W then (1:ℝ) else 0) := by
      rw [favg_sum]
      apply Finset.sum_congr rfl
      intro W _
      exact favg_sum _ _
    _ ≤ ∑ W : Finset (Fin n),
        (m.choose (W.card+1):ℝ)*((W.card:ℝ)/n)^(2*(W.card+1)) := by
      apply Finset.sum_le_sum
      intro W _
      calc
        _ ≤ ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard (W.card+1),
            ((W.card:ℝ)/n)^(2*(W.card+1)) := Finset.sum_le_sum (hi W)
        _ = _ := by simp
    _ = ∑ t ∈ Finset.range (n+1), (n.choose t:ℝ)*(m.choose (t+1):ℝ)*
          ((t:ℝ)/n)^(2*(t+1)) := by
      have he : (Finset.univ : Finset (Finset (Fin n))) =
          (Finset.univ : Finset (Fin n)).powerset := by ext W; simp
      rw [he,Finset.sum_powerset_apply_card (fun t : ℕ =>
        (m.choose (t+1):ℝ)*((t:ℝ)/n)^(2*(t+1)))]
      simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]
    _ ≤ 2*a := hall_sum_bound hn ha ha' hm

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.hall_probability_bound := @_root_.OAI.RandomKSAT.hall_probability_bound
