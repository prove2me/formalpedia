-- Prove2me | solution 1 for NestedCRP.level_conditional
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T00:09:25.37605+00:00
-- url     : https://prove2.me/submissions/237a7426-b050-4ff7-a465-c5e192e100ef

import Mathlib
import Definitions.Def_NestedCRP_levelWeight
import Definitions.Def_NestedCRP_sweep
import Definitions.Def_mm_countable
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_stickMass
import Definitions.Def_NestedCRP_dirichletMeasure
import Definitions.Def_NestedCRP_topicMass
import Definitions.Def_NestedCRP_posterior

section
namespace CarriedPrior
section
open MeasureTheory ProbabilityTheory

namespace BetaMoments

lemma pdf_nonneg (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 ≤ betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp [betaPDFReal, hx]

lemma integral_density (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    ∫ x, f x ∂betaMeasure a b = ∫ x, betaPDFReal a b x * f x := by
  unfold betaMeasure betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_betaPDFReal a b).ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  simp [betaPDF, ENNReal.toReal_ofReal (pdf_nonneg a b x ha hb)]

lemma integral_pdf (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ∫ x, betaPDFReal a b x = 1 := by
  letI := isProbabilityMeasureBeta ha hb
  have h := integral_density a b ha hb (fun _ => 1)
  simpa using h.symm

lemma pdf_tilt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : ℕ) (x : ℝ) :
    betaPDFReal a b x * (x^A * (1-x)^B) =
      (beta (a+A) (b+B) / beta a b) * betaPDFReal (a+A) (b+B) x := by
  have ha' : 0 < a + A := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
  have hb' : 0 < b + B := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg _)
  by_cases hx : 0 < x ∧ x < 1
  · have hx' : 0 < 1-x := by linarith [hx.2]
    simp only [betaPDFReal, if_pos hx]
    rw [show a+(A:ℝ)-1 = (a-1)+(A:ℝ) by ring,
      show b+(B:ℝ)-1 = (b-1)+(B:ℝ) by ring,
      Real.rpow_add hx.1, Real.rpow_add hx', Real.rpow_natCast, Real.rpow_natCast]
    field_simp [ne_of_gt (beta_pos ha hb),ne_of_gt (beta_pos ha' hb')]
  · simp [betaPDFReal, hx]

noncomputable def moment (a b : ℝ) (A B : ℕ) : ℝ :=
  ∫ x, x^A * (1-x)^B ∂betaMeasure a b

lemma moment_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : ℕ) :
    moment a b A B = beta (a+A) (b+B) / beta a b := by
  rw [moment, integral_density a b ha hb]
  simp_rw [pdf_tilt a b ha hb A B]
  rw [integral_const_mul, integral_pdf _ _
    (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _))
    (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg _)), mul_one]

lemma beta_succ_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    beta (a+1) b = a / (a+b) * beta a b := by
  unfold beta
  rw [show a+1+b = (a+b)+1 by ring, Real.Gamma_add_one ha.ne',
    Real.Gamma_add_one (add_pos ha hb).ne']
  field_simp

lemma beta_succ_right (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    beta a (b+1) = b / (a+b) * beta a b := by
  unfold beta
  rw [show a+(b+1) = (a+b)+1 by ring, Real.Gamma_add_one hb.ne',
    Real.Gamma_add_one (add_pos ha hb).ne']
  field_simp
  <;> ring

lemma moment_succ_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : ℕ) :
    moment a b (A+1) B = (a+A)/(a+b+A+B) * moment a b A B := by
  rw [moment_eq a b ha hb, moment_eq a b ha hb]
  push_cast
  rw [show a+((A:ℝ)+1) = (a+A)+1 by ring, beta_succ_left _ _
    (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _))
    (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg _))]
  congr 1 <;> ring

lemma moment_succ_right (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : ℕ) :
    moment a b A (B+1) = (b+B)/(a+b+A+B) * moment a b A B := by
  rw [moment_eq a b ha hb, moment_eq a b ha hb]
  push_cast
  rw [show b+((B:ℝ)+1) = (b+B)+1 by ring, beta_succ_right _ _
    (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _))
    (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg _))]
  congr 1 <;> ring

end BetaMoments

namespace StickFactorization
open Finset

lemma group_values {ι : Type*} [DecidableEq ι] (s : Finset ι) (ζ : ι → ℕ)
    (L : ℕ) (hL : ∀ i ∈ s, ζ i < L) (U : ℕ → ℝ) :
    ∏ i ∈ s, U (ζ i) = ∏ j ∈ range L, U j ^ (s.filter fun i => ζ i = j).card := by
  have h := Finset.prod_fiberwise_of_maps_to' (s := s) (t := range L)
    (g := ζ) (fun i hi => mem_range.mpr (hL i hi)) U
  simpa only [prod_const] using h.symm

lemma group_remainders {ι : Type*} [DecidableEq ι] (s : Finset ι) (ζ : ι → ℕ)
    (L : ℕ) (hL : ∀ i ∈ s, ζ i < L) (U : ℕ → ℝ) :
    ∏ i ∈ s, ∏ j ∈ range (ζ i), (1-U j) =
      ∏ j ∈ range L, (1-U j) ^ (s.filter fun i => j < ζ i).card := by
  have hf : ∀ i ∈ s, (range L).filter (fun j => j < ζ i) = range (ζ i) := by
    intro i hi
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans (hL i hi), h⟩
  calc
    _ = ∏ i ∈ s, ∏ j ∈ range L, if j < ζ i then 1-U j else 1 := by
      apply prod_congr rfl
      intro i hi
      rw [← prod_filter, hf i hi]
    _ = ∏ j ∈ range L, ∏ i ∈ s, if j < ζ i then 1-U j else 1 := prod_comm
    _ = _ := by simp_rw [← prod_filter, prod_const]

lemma group_sticks {ι : Type*} [DecidableEq ι] (s : Finset ι) (ζ : ι → ℕ)
    (L : ℕ) (hL : ∀ i ∈ s, ζ i < L) (U : ℕ → ℝ) :
    ∏ i ∈ s, NestedCRP.stick U (ζ i) =
      ∏ j ∈ range L, U j ^ (s.filter fun i => ζ i = j).card *
        (1-U j) ^ (s.filter fun i => j < ζ i).card := by
  simp only [NestedCRP.stick, prod_mul_distrib]
  rw [group_values s ζ L hL, group_remainders s ζ L hL]

lemma integral_product (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (L : ℕ) (A B : ℕ → ℕ) :
    (∫ U, ∏ j ∈ range L, U j ^ A j * (1-U j)^B j
      ∂Measure.infinitePi (fun _ : ℕ => betaMeasure a b)) =
      ∏ j ∈ range L, BetaMoments.moment a b (A j) (B j) := by
  letI := isProbabilityMeasureBeta ha hb
  have hh := integral_restrict_infinitePi (fun _ : ℕ => betaMeasure a b)
    (s := range L) (f := fun y => ∏ j, y j ^ A j * (1-y j)^B j)
    (by apply Continuous.aestronglyMeasurable; fun_prop)
  rw [integral_fintype_prod_eq_prod (f := fun (j : range L) (x : ℝ) => x ^ A j * (1-x)^B j)] at hh
  change (∫ U, ∏ j : range L, U j ^ A j * (1-U j)^B j
    ∂Measure.infinitePi (fun _ : ℕ => betaMeasure a b)) =
      ∏ j : range L, BetaMoments.moment a b (A j) (B j) at hh
  have he (U : ℕ → ℝ) := Finset.prod_coe_sort (range L) (fun j => U j ^ A j * (1-U j)^B j)
  simp_rw [he] at hh
  rw [Finset.prod_coe_sort (range L) (fun j => BetaMoments.moment a b (A j) (B j))] at hh
  exact hh

lemma mass_product {ι : Type*} [DecidableEq ι] (s : Finset ι) (ζ : ι → ℕ)
    (H : NestedCRP.Hyper) (L : ℕ) (hL : ∀ i ∈ s, ζ i < L) :
    (∫ U, ∏ i ∈ s, NestedCRP.stick U (ζ i) ∂NestedCRP.gemLaw H.m H.pi) =
      ∏ j ∈ range L, BetaMoments.moment (H.m*H.pi) ((1-H.m)*H.pi)
        (s.filter fun i => ζ i = j).card (s.filter fun i => j < ζ i).card := by
  simp_rw [group_sticks s ζ L hL]
  exact integral_product _ _ (mul_pos H.m_pos H.pi_pos)
    (mul_pos (sub_pos.mpr H.m_lt_one) H.pi_pos) L _ _

end StickFactorization

namespace StickFactorization
open Finset

lemma update_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℕ) (n : ι) (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun i => P (Function.update ζ n k i)).card =
      ((univ.erase n).filter fun i => P (ζ i)).card + if P k then 1 else 0 := by
  classical
  have he : (univ.filter fun i => P (Function.update ζ n k i)).erase n =
      (univ.erase n).filter fun i => P (ζ i) := by
    ext i
    by_cases hi : i = n
    · subst i; simp
    · simp [hi, Function.update_of_ne hi]
  by_cases hk : P k
  · have hn : n ∈ univ.filter fun i => P (Function.update ζ n k i) := by simp [hk]
    rw [← he, if_pos hk, card_erase_add_one hn]
  · have hn : n ∉ univ.filter fun i => P (Function.update ζ n k i) := by simp [hk]
    rw [← he, erase_eq_of_notMem hn, if_neg hk, add_zero]

lemma others_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℕ) (n : ι) (U : ℕ → ℝ) :
    (∏ i : {i // i ≠ n}, NestedCRP.stick U (ζ i)) =
      ∏ i ∈ univ.erase n, NestedCRP.stick U (ζ i) := by
  have h := Finset.prod_subtype_eq_prod_filter (s := (univ : Finset ι))
    (fun i => NestedCRP.stick U (ζ i)) (p := fun i => i ≠ n)
  have hs : (univ : Finset ι).subtype (fun i => i ≠ n) = univ := by ext i; simp
  simpa only [hs, Finset.filter_ne'] using h

lemma count_partition {ι : Type*} [DecidableEq ι] (s : Finset ι) (ζ : ι → ℕ) (j : ℕ) :
    (s.filter fun i => ζ i = j).card + (s.filter fun i => j < ζ i).card =
      (s.filter fun i => j ≤ ζ i).card := by
  have he : (s.filter fun i => j ≤ ζ i) =
      (s.filter fun i => ζ i = j) ∪ (s.filter fun i => j < ζ i) := by
    ext i; by_cases hi : i ∈ s <;> simp [hi] <;> omega
  rw [he, card_union_of_disjoint]
  exact disjoint_filter.mpr (fun i hi he ht => by omega)

lemma moment_update (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (A B : ℕ) (j k : ℕ) :
    BetaMoments.moment a b (A + if k = j then 1 else 0) (B + if j < k then 1 else 0) =
      (if j = k then (a+A)/(a+b+A+B) else if j < k then (b+B)/(a+b+A+B) else 1) *
      BetaMoments.moment a b A B := by
  by_cases he : j = k
  · subst j
    simpa using BetaMoments.moment_succ_left a b ha hb A B
  · by_cases hj : j < k
    · simpa [he,Ne.symm he,hj] using BetaMoments.moment_succ_right a b ha hb A B
    · simp [he,Ne.symm he,hj]

lemma factor_product (L k : ℕ) (hk : k < L) (a b : ℕ → ℝ) :
    (∏ j ∈ range L, if j = k then a j else if j < k then b j else 1) =
      a k * ∏ j ∈ range k, b j := by
  have he : (range L).filter (fun j => j < k) = range k := by
    ext j; simp only [mem_filter,mem_range]; omega
  rw [← Finset.mul_prod_erase (range L) _ (mem_range.mpr hk)]
  simp only [if_pos rfl]
  congr 1
  calc
    _ = ∏ j ∈ (range L).erase k, if j < k then b j else 1 := by
      apply prod_congr rfl
      intro j hj
      rw [if_neg (ne_of_mem_erase hj)]
    _ = ∏ j ∈ range L, if j < k then b j else 1 := by
      rw [← Finset.mul_prod_erase (range L) (fun j => if j < k then b j else 1) (mem_range.mpr hk)]
      simp
    _ = _ := by rw [← prod_filter,he]

end StickFactorization

namespace StickFactorization
open Finset NestedCRP

theorem level_prior_mass (H : Hyper) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℕ) (n : ι) (k : ℕ) :
    stickMass H.m H.pi (Function.update ζ n k) =
      levelPrior H.m H.pi ζ n k * stickMass H.m H.pi (fun i : {i // i ≠ n} => ζ i) := by
  classical
  let L := max (univ.sup ζ) k + 1
  let s := (univ : Finset ι).erase n
  let A (j : ℕ) := (s.filter fun i => ζ i = j).card
  let B (j : ℕ) := (s.filter fun i => j < ζ i).card
  let D (j : ℕ) := H.pi + ((s.filter fun i => j ≤ ζ i).card : ℝ)
  have hk : k < L := by dsimp [L]; omega
  have hz : ∀ i, ζ i < L := by
    intro i
    have hh : ζ i ≤ univ.sup ζ := le_sup (mem_univ i)
    dsimp [L]; omega
  have hup : ∀ i ∈ (univ : Finset ι), Function.update ζ n k i < L := by
    intro i hi
    by_cases he : i = n
    · subst i; simpa using hk
    · simpa [Function.update_of_ne he] using hz i
  have ha := mul_pos H.m_pos H.pi_pos
  have hb := mul_pos (sub_pos.mpr H.m_lt_one) H.pi_pos
  have hd (j : ℕ) : H.m*H.pi + (1-H.m)*H.pi + (A j : ℝ) + (B j : ℝ) = D j := by
    have hc : (A j : ℝ) + (B j : ℝ) = ((s.filter fun i => j ≤ ζ i).card : ℝ) := by
      exact_mod_cast count_partition s ζ j
    dsimp [D]
    nlinarith
  have hold : stickMass H.m H.pi (fun i : {i // i ≠ n} => ζ i) =
      ∏ j ∈ range L, BetaMoments.moment (H.m*H.pi) ((1-H.m)*H.pi) (A j) (B j) := by
    unfold stickMass
    simp_rw [others_product ζ n]
    exact mass_product s ζ H L (fun i _ => hz i)
  have hnew := mass_product (univ : Finset ι) (Function.update ζ n k) H L hup
  change stickMass H.m H.pi (Function.update ζ n k) = _ at hnew
  have he (j : ℕ) := update_count ζ n k (fun l => l = j)
  have hg (j : ℕ) := update_count ζ n k (fun l => j < l)
  simp_rw [he, hg] at hnew
  change stickMass H.m H.pi (Function.update ζ n k) =
    ∏ j ∈ range L, BetaMoments.moment (H.m*H.pi) ((1-H.m)*H.pi)
      (A j + if k = j then 1 else 0) (B j + if j < k then 1 else 0) at hnew
  simp_rw [moment_update _ _ ha hb, hd] at hnew
  rw [prod_mul_distrib, factor_product L k hk] at hnew
  rw [hnew,hold]
  rfl

end StickFactorization

namespace CarriedNormalization
section
open Filter
open scoped Topology
namespace LevelPriorNormalization
noncomputable section

/-- Finite count partition at the current level. -/
lemma count_partition {ι : Type*} (A : Finset ι) (ζ : ι → ℕ) (k : ℕ) :
    (A.filter (fun i => ζ i = k)).card + (A.filter (fun i => k < ζ i)).card =
      (A.filter (fun i => k ≤ ζ i)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := A.filter (fun i => k ≤ ζ i))
    (fun i => ζ i = k)
  have he : (A.filter (fun i => k ≤ ζ i)).filter (fun i => ζ i = k) =
      A.filter (fun i => ζ i = k) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter]
    constructor
    · intro hi
      exact ⟨hi.1.1,hi.2⟩
    · intro hi
      exact ⟨⟨hi.1,by omega⟩,hi.2⟩
  have hg : (A.filter (fun i => k ≤ ζ i)).filter (fun i => ¬ ζ i = k) =
      A.filter (fun i => k < ζ i) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter]
    constructor
    · intro hi
      exact ⟨hi.1.1,by omega⟩
    · intro hi
      exact ⟨⟨hi.1,by omega⟩,by omega⟩
  rw [he,hg] at h
  exact h

/-- Any uniformly positive sequence of stick fractions exhausts its mass. -/
lemma bounded_sticks (a : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ha : ∀ k, δ ≤ a k ∧ a k ≤ 1) :
    HasSum (fun k => a k * ∏ j ∈ Finset.range k, (1-a j)) 1 := by
  let R := fun n => ∏ j ∈ Finset.range n, (1-a j)
  have hδ1 : δ ≤ 1 := (ha 0).1.trans (ha 0).2
  have hR0 : ∀ n, 0 ≤ R n := fun n => Finset.prod_nonneg fun j _ => sub_nonneg.mpr (ha j).2
  have hRle : ∀ n, R n ≤ (1-δ)^n := by
    intro n
    calc R n ≤ ∏ _j ∈ Finset.range n, (1-δ) :=
           Finset.prod_le_prod (fun j _ => sub_nonneg.mpr (ha j).2)
             (fun j _ => by linarith [(ha j).1])
         _ = (1-δ)^n := by simp
  have hz : Tendsto R atTop (𝓝 0) :=
    squeeze_zero hR0 hRle (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))
  have hs : ∀ n, ∑ k ∈ Finset.range n, a k * ∏ j ∈ Finset.range k, (1-a j) = 1-R n := by
    intro n
    induction n with
    | zero => simp [R]
    | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [R,Finset.prod_range_succ]; ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k =>
    mul_nonneg (hδ.le.trans (ha k).1) (hR0 k)) 1).mpr
  change Tendsto (fun n => ∑ k ∈ Finset.range n, a k * ∏ j ∈ Finset.range k, (1-a j)) atTop (𝓝 1)
  simp_rw [hs]
  simpa using tendsto_const_nhds.sub hz

/-- Normalization of the full infinite predictive-level distribution. -/
theorem normalized (H : NestedCRP.Hyper) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℕ) (n : ι) : HasSum (NestedCRP.levelPrior H.m H.pi ζ n) 1 := by
  classical
  let A := Finset.univ.erase n
  let E := fun k => ((A.filter (fun i => ζ i = k)).card : ℝ)
  let G := fun k => ((A.filter (fun i => k < ζ i)).card : ℝ)
  let B := fun k => ((A.filter (fun i => k ≤ ζ i)).card : ℝ)
  let a := fun k => (H.m * H.pi + E k) / (H.pi + B k)
  let δ := H.m * H.pi / (H.pi + (A.card : ℝ))
  have hE : ∀ k, 0 ≤ E k := fun k => Nat.cast_nonneg _
  have hG : ∀ k, 0 ≤ G k := fun k => Nat.cast_nonneg _
  have hB : ∀ k, 0 ≤ B k := fun k => Nat.cast_nonneg _
  have hD : ∀ k, 0 < H.pi + B k := fun k => add_pos_of_pos_of_nonneg H.pi_pos (hB k)
  have hpart : ∀ k, E k + G k = B k := by
    intro k
    dsimp [E,G,B]
    exact_mod_cast count_partition A ζ k
  have hcap : ∀ k, B k ≤ (A.card : ℝ) := by
    intro k
    dsimp [B]
    exact_mod_cast Finset.card_filter_le A (fun i => k ≤ ζ i)
  have hmp : 0 < H.m * H.pi := mul_pos H.m_pos H.pi_pos
  have hδ : 0 < δ := div_pos hmp (add_pos_of_pos_of_nonneg H.pi_pos (Nat.cast_nonneg _))
  have ha : ∀ k, δ ≤ a k ∧ a k ≤ 1 := by
    intro k
    constructor
    · calc δ ≤ H.m * H.pi / (H.pi + B k) :=
             div_le_div_of_nonneg_left hmp.le (hD k) (by linarith [hcap k])
           _ ≤ a k := div_le_div_of_nonneg_right (by linarith [hE k]) (hD k).le
    · apply (div_le_one (hD k)).mpr
      have hm := mul_lt_mul_of_pos_right H.m_lt_one H.pi_pos
      linarith [hpart k,hG k]
  have hc : ∀ k, ((1-H.m)*H.pi+G k)/(H.pi+B k) = 1-a k := by
    intro k
    dsimp [a]
    apply (eq_sub_iff_add_eq).mpr
    rw [← add_div]
    apply (div_eq_one_iff_eq (hD k).ne').mpr
    nlinarith [hpart k]
  have he : NestedCRP.levelPrior H.m H.pi ζ n =
      (fun k => a k * ∏ j ∈ Finset.range k, (1-a j)) := by
    funext k
    unfold NestedCRP.levelPrior
    change a k * (∏ j ∈ Finset.range k, ((1-H.m)*H.pi+G j)/(H.pi+B j)) = _
    simp_rw [hc]
  rw [he]
  exact bounded_sticks a δ hδ ha
end
end LevelPriorNormalization

/-- The independently audited second conjunct of NestedCRP.level_prior. -/
theorem solution (H : NestedCRP.Hyper) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℕ) (n : ι) : HasSum (NestedCRP.levelPrior H.m H.pi ζ n) 1 :=
  LevelPriorNormalization.normalized H ζ n

/-- With no other words, the predictive distribution is geometric on all levels. -/
theorem empty_others_control (m pi : ℝ) (hpi : pi ≠ 0) (ζ : Fin 1 → ℕ) (k : ℕ) :
    NestedCRP.levelPrior m pi ζ 0 k = m * (1-m)^k := by
  have he : (Finset.univ.erase (0 : Fin 1)) = ∅ := by decide
  simp [NestedCRP.levelPrior,he,hpi]

/-- Two other words at level zero reinforce its probability from 1/2 to 3/4. -/
theorem two_zero_words_control :
    NestedCRP.levelPrior (1/2) 2 (fun _ : Fin 3 => 0) 0 0 = 3/4 ∧
    NestedCRP.levelPrior (1/2) 2 (fun _ : Fin 3 => 0) 0 1 = 1/8 := by
  have he : Finset.univ.erase (0 : Fin 3) = {1,2} := by decide
  have hc : ({1,2} : Finset (Fin 3)).card = 2 := by decide
  norm_num [NestedCRP.levelPrior,he,hc]

/-- Positivity of the hyperparameter m is essential even with no other words. -/
theorem zero_mean_control :
    ¬ HasSum (NestedCRP.levelPrior 0 2 (fun _ : Fin 1 => 0) 0) 1 := by
  have he : NestedCRP.levelPrior 0 2 (fun _ : Fin 1 => 0) 0 = (fun _ : ℕ => (0:ℝ)) := by
    funext k
    rw [empty_others_control 0 2 (by norm_num)]
    simp
  rw [he]
  intro h
  have hh := h.unique (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  norm_num at hh

end
end CarriedNormalization

theorem solution (H : NestedCRP.Hyper) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℕ) (n : ι) :
    (∀ k, NestedCRP.stickMass H.m H.pi (Function.update ζ n k) =
      NestedCRP.levelPrior H.m H.pi ζ n k *
        NestedCRP.stickMass H.m H.pi (fun i : {i // i ≠ n} => ζ i)) ∧
    HasSum (NestedCRP.levelPrior H.m H.pi ζ n) 1 :=
  ⟨StickFactorization.level_prior_mass H ζ n, CarriedNormalization.solution H ζ n⟩

theorem uniform_beta_mixed_moment_control : BetaMoments.moment 1 1 1 1 = (1/6 : ℝ) := by
  have h00 : BetaMoments.moment 1 1 0 0 = 1 := by
    letI := isProbabilityMeasureBeta (show (0:ℝ) < 1 by norm_num) (show (0:ℝ) < 1 by norm_num)
    simp [BetaMoments.moment]
  have h10 := BetaMoments.moment_succ_left 1 1 (by norm_num) (by norm_num) 0 0
  have h11 := BetaMoments.moment_succ_right 1 1 (by norm_num) (by norm_num) 1 0
  norm_num [h00] at h10 h11
  linarith

end
end CarriedPrior

open NestedCRP
open scoped BigOperators
namespace LevelWeightBounds
noncomputable section
open Classical
lemma prior_pos (H : Hyper) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℕ) (n : ι) (k : ℕ) : 0 < levelPrior H.m H.pi z n k := by
  have hp := H.pi_pos
  have hmp := H.m_pos
  unfold levelPrior
  apply mul_pos
  · apply div_pos <;> positivity
  · apply Finset.prod_pos
    intro j hj
    apply div_pos
    · have hm : 0 < 1 - H.m := sub_pos.mpr H.m_lt_one
      positivity
    · positivity

lemma likelihood_bounds {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State)
    (s : C.Site) (k : ℕ) : 0 < levelLik H.eta C x s k ∧ levelLik H.eta C x s k ≤ 1 := by
  have hV : 0 < V := (C.word s).isLt.trans_le (Nat.le_refl V) |>.trans_le' (Nat.zero_le _)
  have hVreal : (1:ℝ) ≤ V := by exact_mod_cast hV
  have hsum : (siteCount C x s k (C.word s) : ℝ) ≤ ∑ v, (siteCount C x s k v : ℝ) :=
    Finset.single_le_sum (fun v _ => Nat.cast_nonneg _) (Finset.mem_univ _)
  have hd : 0 < (∑ v, (siteCount C x s k v : ℝ)) + V * H.eta := by
    have hp : 0 < (V:ℝ)*H.eta := mul_pos (by exact_mod_cast hV) H.eta_pos
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hp
  unfold levelLik
  constructor
  · exact div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) H.eta_pos) hd
  · apply (div_le_one hd).mpr
    have he := mul_le_mul_of_nonneg_right hVreal H.eta_pos.le
    linarith

lemma weight_bounds {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State)
    (s : C.Site) (k : ℕ) : 0 < levelWeight H C x s k ∧
    levelWeight H C x s k ≤ levelPrior H.m H.pi (x.2 s.1) s.2 k := by
  have hp := prior_pos H (x.2 s.1) s.2 k
  have hl := likelihood_bounds H C x s k
  constructor
  · exact mul_pos hp hl.1
  · exact mul_le_of_le_one_right hp.le hl.2

lemma weight_summable {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State)
    (s : C.Site) : Summable (levelWeight H C x s) := by
  exact Summable.of_nonneg_of_le (fun k => (weight_bounds H C x s k).1.le)
    (fun k => (weight_bounds H C x s k).2)
    (CarriedPrior.CarriedNormalization.LevelPriorNormalization.normalized H (x.2 s.1) s.2).summable

lemma normalizer_bounds {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State)
    (s : C.Site) : 0 < ∑' k, levelWeight H C x s k ∧ ∑' k, levelWeight H C x s k ≤ 1 := by
  have hw := weight_summable H C x s
  constructor
  · exact lt_of_lt_of_le (weight_bounds H C x s 0).1
      (hw.le_tsum 0 (fun k _ => (weight_bounds H C x s k).1.le))
  · have h := Summable.tsum_le_tsum (fun k => (weight_bounds H C x s k).2) hw
      (CarriedPrior.CarriedNormalization.LevelPriorNormalization.normalized H (x.2 s.1) s.2).summable
    simpa only [(CarriedPrior.CarriedNormalization.LevelPriorNormalization.normalized H (x.2 s.1) s.2).tsum_eq] using h

theorem normalized_weights {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State)
    (s : C.Site) : HasSum (fun k => levelWeight H C x s k / ∑' j, levelWeight H C x s j) 1 := by
  have h := (weight_summable H C x s).hasSum.div_const (∑' j, levelWeight H C x s j)
  simpa only [div_self (normalizer_bounds H C x s).1.ne'] using h

lemma set_self {V D : ℕ} (C : Corpus V D) (z : C.Levels) (s : C.Site) (k : ℕ) :
    C.setLevel z s k s.1 s.2 = k := by simp [Corpus.setLevel]
lemma set_other {V D : ℕ} (C : Corpus V D) (z : C.Levels) (s t : C.Site)
    (ht : t ≠ s) (k : ℕ) : C.setLevel z s k t.1 t.2 = z t.1 t.2 := by
  simp [Corpus.setLevel,ht]
lemma update_injective {V D : ℕ} (C : Corpus V D) (x : C.State) (s : C.Site) :
    Function.Injective (fun k => (x.1,C.setLevel x.2 s k)) := by
  intro a b hab
  have h := congrArg (fun y : C.State => y.2 s.1 s.2) hab
  simpa only [set_self] using h
lemma update_range {V D : ℕ} (C : Corpus V D) (x y : C.State) (s : C.Site) :
    y ∈ Set.range (fun k => (x.1,C.setLevel x.2 s k)) ↔
      y.1 = x.1 ∧ ∀ t : C.Site, t ≠ s → y.2 t.1 t.2 = x.2 t.1 t.2 := by
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨rfl,fun t ht => set_other C x.2 s t ht k⟩
  · rintro ⟨hT,hz⟩
    refine ⟨y.2 s.1 s.2,?_⟩
    apply Prod.ext
    · exact hT.symm
    funext d n
    by_cases h : (⟨d,n⟩ : C.Site) = s
    · simp only [Corpus.setLevel,if_pos h]
      exact congrArg (fun t : C.Site => y.2 t.1 t.2) h.symm
    · simp only [Corpus.setLevel,if_neg h]
      exact (hz ⟨d,n⟩ h).symm

theorem level_kernel_stochastic {V D : ℕ} (H : Hyper) (C : Corpus V D) (s : C.Site) :
    MarkovMixing.IsStochasticC (levelKernel H C s) := by
  constructor
  · intro x y
    unfold levelKernel
    split_ifs
    · exact (div_pos (weight_bounds H C x s _).1 (normalizer_bounds H C x s).1).le
    · exact le_rfl
  · intro x
    apply (update_injective C x s).hasSum_iff ?_ |>.mp
    · have he : (levelKernel H C s x ∘ (fun k => (x.1,C.setLevel x.2 s k))) =
          (fun k => levelWeight H C x s k / ∑' j, levelWeight H C x s j) := by
        funext k
        have hr := (update_range C x (x.1,C.setLevel x.2 s k) s).mp ⟨k,rfl⟩
        dsimp only [Function.comp_apply]
        unfold levelKernel
        rw [if_pos hr]
        simp only [set_self]
      rw [he]
      exact normalized_weights H C x s
    · intro y hy
      have hr := mt (update_range C x y s).mpr hy
      simp only [levelKernel,if_neg hr]

theorem weight_well_defined {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State)
    (s : C.Site) : (∀ k, 0 < levelWeight H C x s k) ∧
    Summable (levelWeight H C x s) ∧ 0 < ∑' k, levelWeight H C x s k :=
  ⟨fun k => (weight_bounds H C x s k).1,weight_summable H C x s,(normalizer_bounds H C x s).1⟩

abbrev controlCorpus : Corpus 2 1 := ⟨fun _ => 2,fun _ n => n⟩
theorem normalized_likelihood_control (T : Tree 1) :
    levelLik (1/2) controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 0 = 1/4 ∧
    levelLik (1/2) controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 1 = 1/2 := by
  have hr : ∀ (ℓ : ℕ) (d e : Fin 1), T.Rel ℓ d e := by
    intro ℓ d e
    have he : d = e := Subsingleton.elim _ _
    subst e
    exact (T.part ℓ).refl d
  have hc : ∀ (k : Fin 2) (v : Fin 2),
      siteCount controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ k v =
        if k = 0 ∧ v = 1 then 1 else 0 := by
    intro k v
    unfold siteCount
    simp only [hr,and_true]
    fin_cases k <;> fin_cases v <;> decide
  have h00 : siteCount controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 0 0 = 0 := by simpa using hc 0 0
  have h01 : siteCount controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 0 1 = 1 := by simpa using hc 0 1
  have h10 : siteCount controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 1 0 = 0 := by simpa using hc 1 0
  have h11 : siteCount controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 1 1 = 0 := by simpa using hc 1 1
  have hw : controlCorpus.word ⟨0,0⟩ = (0 : Fin 2) := rfl
  constructor <;> norm_num [levelLik,hw,Fin.sum_univ_two,h00,h01,h10,h11]
end
end LevelWeightBounds

end

section
namespace CarriedMoments
section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace GeneralDirichlet
noncomputable section
lemma gamma_integral (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (a-1) * Real.exp (-(r*t))) =
      ENNReal.ofReal (Real.Gamma a / r^a) := by
  have hI : ∫ t in Ioi (0:ℝ), t ^ (a-1) * Real.exp (-(r*t)) = Real.Gamma a / r^a := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr,Real.div_rpow zero_le_one hr.le,Real.one_rpow]
    ring
  rw [← hI,ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_integral_ne_zero (by rw [hI]; positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
lemma gamma_nat (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^m * Real.exp (-(r*t))) =
      ENNReal.ofReal (m.factorial / r^(m+1)) := by
  have h := gamma_integral ((m:ℝ)+1) r (by positivity) hr
  simp only [add_sub_cancel_right,Real.rpow_natCast,Real.Gamma_nat_eq_factorial] at h
  rw [show (m:ℝ)+1 = ((m+1:ℕ):ℝ) by norm_num,Real.rpow_natCast] at h
  exact h
lemma gamma_pos (a : ℝ) : ∀ᵐ x ∂gammaMeasure a 1, (0:ℝ) < x := by
  have hf : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  rw [gammaMeasure,ae_withDensity_iff hf]
  have hn : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hn] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h
lemma gamma_laplace (a : ℝ) (ha : 0 < a) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (z^n * Real.exp (-(t*z))) ∂gammaMeasure a 1 =
      ENNReal.ofReal (Real.Gamma (a+n) / Real.Gamma a / (1+t)^(a+n)) := by
  have hf : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  have hg : Measurable fun z : ℝ => ENNReal.ofReal (z^n * Real.exp (-(t*z))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul _ hf hg]
  have hn : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by rw [ae_iff]; simp
  have he : (fun z => gammaPDF a 1 z * ENNReal.ofReal (z^n * Real.exp (-(t*z)))) =ᵐ[volume]
      (Ioi (0:ℝ)).indicator (fun z => ENNReal.ofReal ((Real.Gamma a)⁻¹) *
        ENNReal.ofReal (z^(a+n-1) * Real.exp (-((1+t)*z)))) := by
    filter_upwards [hn] with z hz
    rcases lt_or_gt_of_ne hz with hz | hz
    · rw [gammaPDF_of_neg hz,zero_mul,indicator_of_notMem (by simpa using hz.le)]
    · rw [gammaPDF_of_nonneg hz.le,indicator_of_mem (by simpa using hz),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [Real.one_rpow,one_mul]
      rw [show -((1+t)*z) = -z + -(t*z) by ring,Real.exp_add,
        show a+(n:ℝ)-1 = (a-1)+(n:ℝ) by ring,Real.rpow_add hz,Real.rpow_natCast]
      ring
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ioi,
    lintegral_const_mul _ (by fun_prop),gamma_integral (a+n) (1+t) (by positivity) (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
end
end GeneralDirichlet

namespace GeneralDirichlet
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
lemma beta_integral (n : ℕ) (d : ℝ) (hn : 1 ≤ n) (hd : 0 < d) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/(1+t)^((n:ℝ)+d)) =
      ENNReal.ofReal ((n-1).factorial * Real.Gamma d / Real.Gamma ((n:ℝ)+d)) := by
  let N : ℝ := (n:ℝ)+d
  have hN : 0 < N := by dsimp [N]; positivity
  have hG : 0 < Real.Gamma N := Real.Gamma_pos_of_pos hN
  have step1 : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/(1+t)^((n:ℝ)+d)) =
      ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/Real.Gamma N) *
        ENNReal.ofReal (u^(N-1)*Real.exp (-((1+t)*u))) := by
    intro t ht
    have ht' : 0 < 1+t := by linarith [mem_Ioi.mp ht]
    rw [lintegral_const_mul _ (by fun_prop),gamma_integral N (1+t) hN ht',
      ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (le_of_lt ht) _) hG.le)]
    congr 1
    dsimp [N] at *
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step1]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    exact (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.1^(n-1)/Real.Gamma N)).mul (ENNReal.measurable_ofReal.comp (by fun_prop :
      Measurable fun p : ℝ × ℝ => p.2^(N-1)*Real.exp (-((1+p.1)*p.2)))))]
  have step2 : ∀ u ∈ Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/Real.Gamma N) *
      ENNReal.ofReal (u^(N-1)*Real.exp (-((1+t)*u)))) =
      ENNReal.ofReal ((n-1).factorial/Real.Gamma N) *
        ENNReal.ofReal (u^(d-1)*Real.exp (-(1*u))) := by
    intro u hu
    have hu' : 0 < u := hu
    have e : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/Real.Gamma N) *
        ENNReal.ofReal (u^(N-1)*Real.exp (-((1+t)*u))) =
        ENNReal.ofReal (u^(N-1)*Real.exp (-u)/Real.Gamma N) *
          ENNReal.ofReal (t^(n-1)*Real.exp (-(u*t))) := by
      intro t ht
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (le_of_lt ht) _) hG.le),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -((1+t)*u) = -u + -(u*t) by ring,Real.exp_add]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi e,
      lintegral_const_mul _ (by fun_prop),gamma_nat (n-1) hu',
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.sub_add_cancel hn,one_mul,
      show N-1 = (d-1)+(n:ℝ) by dsimp [N]; ring,Real.rpow_add hu',Real.rpow_natCast]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step2,
    lintegral_const_mul _ (by fun_prop),gamma_integral d 1 hd one_pos,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Real.one_rpow,div_one]
  dsimp [N]
  ring
end GeneralDirichlet

namespace GeneralDirichlet
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
noncomputable section
lemma pi_pos {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i) :
    ∀ᵐ z ∂(Measure.pi fun i => gammaMeasure (α i) 1), ∀ i, (0:ℝ) < z i := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  exact eventually_all.2 fun i => Measure.tendsto_eval_ae_ae.eventually (gamma_pos (α i))
lemma product_laplace {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i)
    (a : ι → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (∏ i, (z i ^ a i * Real.exp (-(t*z i))))
      ∂(Measure.pi fun i => gammaMeasure (α i) 1) =
      ENNReal.ofReal (∏ i, (Real.Gamma (α i+a i)/Real.Gamma (α i)/(1+t)^(α i+a i))) := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  have h1 : ∀ i, ∫ x, x^a i * Real.exp (-(t*x)) ∂gammaMeasure (α i) 1 =
      Real.Gamma (α i+a i)/Real.Gamma (α i)/(1+t)^(α i+a i) := by
    intro i
    have hai := hα i
    rw [integral_eq_lintegral_of_nonneg_ae,gamma_laplace (α i) (hα i) (a i) ht,
      ENNReal.toReal_ofReal (by positivity)]
    · filter_upwards [gamma_pos (α i)] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le
    · exact (by fun_prop : Continuous fun x : ℝ => x^a i * Real.exp (-(t*x))).aestronglyMeasurable
  have hint : ∀ i, Integrable (fun x : ℝ => x^a i * Real.exp (-(t*x))) (gammaMeasure (α i) 1) :=
    fun i => Integrable.of_integral_ne_zero (by have hai := hα i; rw [h1]; positivity)
  have h2 := integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun (i : ι) (x : ℝ) => x^a i * Real.exp (-(t*x)))
    (μ := fun i => gammaMeasure (α i) 1)
  simp only [h1] at h2
  rw [← h2,ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.fintype_prod (f := fun (i : ι) (x : ℝ) => x^a i * Real.exp (-(t*x))) hint
  · filter_upwards [pi_pos α hα] with z hz
    exact Finset.prod_nonneg fun i _ => mul_nonneg (pow_nonneg (hz i).le _) (Real.exp_pos _).le
lemma reduce {ι : Type*} [Fintype ι] (α : ι → ℝ) (a : ι → ℕ) :
    (∫ p, ∏ i, p i ^ a i ∂NestedCRP.dirichletMeasure α) =
      ∫ z, (∏ i, z i ^ a i)/(∑ i, z i)^(∑ i, a i) ∂(Measure.pi fun i => gammaMeasure (α i) 1) := by
  rw [NestedCRP.dirichletMeasure,integral_map (by fun_prop : Measurable fun x : ι → ℝ => fun i => x i/∑ j,x j).aemeasurable
    (by fun_prop : Continuous fun p : ι → ℝ => ∏ i,p i^a i).aestronglyMeasurable]
  simp only [div_pow,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
lemma moment {ι : Type*} [Fintype ι] [Nonempty ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i) (a : ι → ℕ) :
    (∫ p, ∏ i,p i^a i ∂NestedCRP.dirichletMeasure α) =
      Real.Gamma (∑ i,α i)/(∏ i,Real.Gamma (α i)) *
        ((∏ i,Real.Gamma ((a i:ℝ)+α i))/Real.Gamma ((∑ i,(a i:ℝ))+∑ i,α i)) := by
  classical
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  set d := ∑ i,α i with hd
  have hdpos : 0 < d := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  set n := ∑ i,a i with hn
  have hg : (∏ i,Real.Gamma (α i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Real.Gamma_pos_of_pos (hα i)).ne'
  have hprod : 0 < ∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i) := Finset.prod_pos fun i _ => by
    have hi := hα i
    positivity
  rw [reduce]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have ha : ∀ i,a i=0 := fun i => (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)
    simp only [ha,pow_zero,Finset.prod_const_one,Finset.sum_const_zero,div_one,Nat.cast_zero,zero_add]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    field_simp [(Real.Gamma_pos_of_pos hdpos).ne']
  · set π := Measure.pi fun i => gammaMeasure (α i) 1
    have hnf : (0:ℝ) < (n-1).factorial := by positivity
    have hrep : ∀ᵐ z ∂π, ENNReal.ofReal ((∏ i,z i^a i)/(∑ i,z i)^n) =
        ENNReal.ofReal (1/(n-1).factorial) * ∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal ((∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1)) := by
      filter_upwards [pi_pos α hα] with z hz
      have hS : 0 < ∑ i,z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
      have hF : 0 ≤ ∏ i,z i^a i := Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _
      have e : ∀ t,(∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1) =
          (∏ i,z i^a i)*(t^(n-1)*Real.exp (-((∑ i,z i)*t))) := by
        intro t
        rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_mul]
        simp only [neg_mul,Finset.sum_neg_distrib,mul_comm t]
        ring
      simp_rw [e]
      have hm : Measurable fun t : ℝ => ENNReal.ofReal (t^(n-1)*Real.exp (-((∑ i,z i)*t))) := ENNReal.measurable_ofReal.comp (by fun_prop)
      simp_rw [ENNReal.ofReal_mul hF]
      rw [lintegral_const_mul _ hm,gamma_nat (n-1) hS,Nat.sub_add_cancel hpos,
        ← ENNReal.ofReal_mul hF,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hinner : ∀ t ∈ Ioi (0:ℝ), (∫⁻ z,ENNReal.ofReal
        ((∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1)) ∂π) =
        ENNReal.ofReal (∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i)) *
          ENNReal.ofReal (t^(n-1)/(1+t)^((n:ℝ)+d)) := by
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      simp_rw [ENNReal.ofReal_mul' (pow_nonneg ht0 (n-1))]
      have hm : Measurable fun z : ι → ℝ => ENNReal.ofReal (∏ i,(z i^a i*Real.exp (-(t*z i)))) := ENNReal.measurable_ofReal.comp (by fun_prop)
      have hpL : 0 < ∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i)/(1+t)^(α i+a i) :=
        Finset.prod_pos fun i _ => by
          have hi := hα i
          positivity
      rw [lintegral_mul_const _ hm,product_laplace α hα a ht0,
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Finset.prod_div_distrib,← Real.rpow_sum_of_pos (by linarith : 0 < 1+t)]
      have he : ∑ i,(α i+(a i:ℝ)) = (n:ℝ)+d := by simp only [Finset.sum_add_distrib,← Nat.cast_sum,← hn,← hd];ring
      rw [he]
      ring
    have hmeas : Measurable (Function.uncurry fun (z : ι → ℝ) (t : ℝ) => ENNReal.ofReal
      ((∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1))) := ENNReal.measurable_ofReal.comp (by fun_prop)
    have hL : (∫⁻ z,ENNReal.ofReal ((∏ i,z i^a i)/(∑ i,z i)^n) ∂π) =
        ENNReal.ofReal ((n-1).factorial*Real.Gamma d/Real.Gamma ((n:ℝ)+d)/(n-1).factorial *
          ∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i)) := by
      rw [lintegral_congr_ae hrep,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_lintegral_swap hmeas.aemeasurable,setLIntegral_congr_fun measurableSet_Ioi hinner,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,beta_integral n d hpos hdpos,
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [integral_eq_lintegral_of_nonneg_ae,hL,ENNReal.toReal_ofReal (by positivity)]
    · simp only [Finset.prod_div_distrib,add_comm (α _) _,Nat.cast_sum] at *
      dsimp [n,d]
      push_cast
      field_simp
    · filter_upwards [pi_pos α hα] with z hz
      exact div_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _)
        (pow_nonneg (Finset.sum_nonneg fun i _ => (hz i).le) _)
    · exact (by fun_prop : Measurable fun z : ι → ℝ => (∏ i,z i^a i)/(∑ i,z i)^n).aestronglyMeasurable
end
end GeneralDirichlet


open MeasureTheory ProbabilityTheory
 theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (α : ι → ℝ) (hα : ∀ i,0 < α i) (n : ι → ℕ) :
    ∫ U, ∏ i,U i^n i ∂NestedCRP.dirichletMeasure α =
      Real.Gamma (∑ i,α i)/(∏ i,Real.Gamma (α i)) *
        ((∏ i,Real.Gamma ((n i:ℝ)+α i))/Real.Gamma ((∑ i,(n i:ℝ))+∑ i,α i)) :=
  GeneralDirichlet.moment α hα n
namespace GeneralDirichlet
lemma zero_exponents_control {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i,0 < α i) :
    (∫ p, ∏ i,p i^(0:ℕ) ∂NestedCRP.dirichletMeasure α) = 1 := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  rw [reduce]
  simp [Measure.real]
lemma uniform_pair_control :
    (∫ p, p 0 * p 1 ∂NestedCRP.dirichletMeasure (fun _ : Fin 2 => (1:ℝ))) = (1/6:ℝ) := by
  have h := moment (fun _ : Fin 2 => (1:ℝ)) (by intro i; norm_num) (fun _ => 1)
  norm_num [Fin.prod_univ_two,Fin.sum_univ_two,Real.Gamma_nat_eq_factorial] at h
  exact h
lemma singleton_control (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ p, p 0^n ∂NestedCRP.dirichletMeasure (fun _ : Fin 1 => a)) = 1 := by
  have h := moment (fun _ : Fin 1 => a) (fun _ => ha) (fun _ => n)
  simpa [Real.Gamma_pos_of_pos ha |>.ne',Real.Gamma_pos_of_pos (show 0 < (n:ℝ)+a by positivity) |>.ne'] using h
end GeneralDirichlet

end
end CarriedMoments

open MeasureTheory ProbabilityTheory NestedCRP Finset
namespace TopicPredictive
noncomputable section
attribute [local instance] Classical.propDecidable
lemma dirichlet_probability {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i) :
    IsProbabilityMeasure (dirichletMeasure α) := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun x : ι → ℝ => fun i => x i/∑ j,x j).aemeasurable

lemma moment_step {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (α : ι → ℝ) (hα : ∀ i,0 < α i)
    (a : ι → ℕ) (i : ι) :
    (∫ p, ∏ j,p j ^ (Function.update a i (a i+1) j) ∂dirichletMeasure α) =
      ((a i:ℝ)+α i)/((∑ j,(a j:ℝ))+∑ j,α j) *
        (∫ p,∏ j,p j^a j ∂dirichletMeasure α) := by
  classical
  have hS : 0 < (∑ j,(a j:ℝ))+∑ j,α j := by
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _) (Finset.sum_pos (fun j _ => hα j) Finset.univ_nonempty)
  have hi : 0 < (a i:ℝ)+α i := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (hα i)
  have hs : (∑ j, ((Function.update a i (a i+1) j:ℕ):ℝ)) = (∑ j,(a j:ℝ))+1 := by
    have he : (fun j => ((Function.update a i (a i+1) j:ℕ):ℝ)) = Function.update (fun j => (a j:ℝ)) i ((a i:ℝ)+1) := by
      ext j
      by_cases hj : j=i <;> simp [Function.update_apply,hj]
    rw [he]
    have hx := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (a j:ℝ)) ((a i:ℝ)+1)
    rw [hx]
    have hy := Finset.sum_erase_add (Finset.univ : Finset ι) (fun j => (a j:ℝ)) (Finset.mem_univ i)
    simpa [Finset.sdiff_singleton_eq_erase] using (by linarith : (a i:ℝ)+1+∑ j ∈ Finset.univ.erase i,(a j:ℝ) = (∑ j,(a j:ℝ))+1)
  have hp : (∏ j,Real.Gamma ((Function.update a i (a i+1) j:ℕ)+α j)) =
      ((a i:ℝ)+α i)*(∏ j,Real.Gamma ((a j:ℝ)+α j)) := by
    have he : (fun j => Real.Gamma ((Function.update a i (a i+1) j:ℕ)+α j)) =
        fun j => (if j=i then ((a i:ℝ)+α i) else 1)*Real.Gamma ((a j:ℝ)+α j) := by
      ext j
      by_cases hj : j=i
      · subst j
        simp only [Function.update_self,if_pos rfl,Nat.cast_add,Nat.cast_one]
        rw [show (a i:ℝ)+1+α i=(a i:ℝ)+α i+1 by ring,Real.Gamma_add_one hi.ne']
        simp
      · simp [Function.update_apply,hj]
    rw [he,Finset.prod_mul_distrib]
    simp
  rw [CarriedMoments.GeneralDirichlet.moment α hα _,CarriedMoments.GeneralDirichlet.moment α hα _,hs,hp]
  rw [show (∑ j,(a j:ℝ))+1+∑ j,α j=((∑ j,(a j:ℝ))+∑ j,α j)+1 by ring,Real.Gamma_add_one hS.ne']
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma group_words {S V : Type*} [Fintype V] [DecidableEq V] (A : Finset S) (word : S → V) (p : V → ℝ) :
    (∏ s ∈ A,p (word s)) = ∏ v,p v ^ (A.filter fun s => word s=v).card := by
  classical
  symm
  simpa using (Finset.prod_fiberwise' A word p)

lemma topic_factorization {V D : ℕ} (η : ℝ) (hη : 0 < η) (C : Corpus V D)
    (T : Tree D) (z : C.Levels) (A : Finset C.Site) (I : Finset (Node D))
    (hI : ∀ s ∈ A,nodeOf C T z s ∈ I) :
    topicMassOn η C T z A =
      ∏ b ∈ I, ∫ p, ∏ s ∈ A.filter (fun s => nodeOf C T z s=b),p (C.word s)
        ∂dirichletMeasure (fun _ : Fin V => η) := by
  classical
  let μ := dirichletMeasure (fun _ : Fin V => η)
  letI : IsProbabilityMeasure μ := dirichlet_probability _ (fun _ => hη)
  let F : I → (Fin V → ℝ) → ℝ := fun b p => ∏ s ∈ A.filter (fun s => nodeOf C T z s=b),p (C.word s)
  have he (β : Node D → Fin V → ℝ) : (∏ s ∈ A,β (nodeOf C T z s) (C.word s)) = ∏ b : I,F b (β b) := by
    change (∏ s ∈ A,β (nodeOf C T z s) (C.word s)) = ∏ b : I,∏ s ∈ A.filter (fun s => nodeOf C T z s=b.val),β b.val (C.word s)
    rw [Finset.prod_coe_sort I (fun b : Node D => ∏ s ∈ A.filter (fun s => nodeOf C T z s=b),β b (C.word s))]
    symm
    calc (∏ b ∈ I,∏ s ∈ A.filter (fun s => nodeOf C T z s=b),β b (C.word s)) =
        ∏ b ∈ I,∏ s ∈ A.filter (fun s => nodeOf C T z s=b),β (nodeOf C T z s) (C.word s) := by
          apply Finset.prod_congr rfl
          intro b hb
          apply Finset.prod_congr rfl
          intro s hs
          rw [(Finset.mem_filter.mp hs).2]
      _ = _ := Finset.prod_fiberwise_of_maps_to hI _
  unfold topicMassOn topicLaw
  simp_rw [he]
  change (∫ β, (fun y : I → Fin V → ℝ => ∏ b,F b (y b)) (I.restrict β) ∂Measure.infinitePi (fun _ : Node D => μ)) = _
  have hmeas : AEStronglyMeasurable (fun y : I → Fin V → ℝ => ∏ b,F b (y b)) (Measure.pi (fun _ : I => μ)) := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hh := integral_restrict_infinitePi (μ := fun _ : Node D => μ) (s := I) hmeas
  rw [hh]
  rw [integral_fintype_prod_eq_prod]
  change (∏ b : I, ∫ p, ∏ s ∈ A.filter (fun s => nodeOf C T z s=b.val),p (C.word s) ∂dirichletMeasure (fun _ : Fin V => η)) = _
  exact Finset.prod_coe_sort I (fun b : Node D => ∫ p, ∏ s ∈ A.filter (fun s => nodeOf C T z s=b),p (C.word s) ∂dirichletMeasure (fun _ : Fin V => η))

lemma moment_word {S : Type*} {V : ℕ} (η : ℝ) (hη : 0 < η)
    (A : Finset S) (word : S → Fin V) (v : Fin V) :
    (∫ p, p v * ∏ s ∈ A,p (word s) ∂dirichletMeasure (fun _ : Fin V => η)) =
      (((A.filter fun s => word s=v).card:ℝ)+η) /
        ((∑ j : Fin V,((A.filter fun s => word s=j).card:ℝ))+V*η) *
        (∫ p, ∏ s ∈ A,p (word s) ∂dirichletMeasure (fun _ : Fin V => η)) := by
  classical
  letI : Nonempty (Fin V) := ⟨v⟩
  let a := fun j => (A.filter fun s => word s=j).card
  have he (p : Fin V → ℝ) : (∏ j,p j^(Function.update a v (a v+1) j)) = p v *∏ j,p j^a j := by
    have hx : (fun j => p j^(Function.update a v (a v+1) j)) = fun j => (if j=v then p v else 1)*p j^a j := by
      ext j
      by_cases h : j=v
      · subst j
        simp [pow_succ,mul_comm]
      · simp [Function.update_apply,h]
    rw [hx,Finset.prod_mul_distrib]
    simp
  have hh := moment_step (fun _ : Fin V => η) (fun _ => hη) a v
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  simp_rw [group_words]
  trans (∫ p, ∏ j,p j^(Function.update a v (a v+1) j) ∂dirichletMeasure (fun _ : Fin V => η))
  · apply integral_congr_ae
    filter_upwards [] with p
    exact (he p).symm
  · exact hh

lemma topic_insert {V D : ℕ} (η : ℝ) (hη : 0 < η) (C : Corpus V D)
    (T : Tree D) (z : C.Levels) (A : Finset C.Site) (s₀ : C.Site) (hs₀ : s₀ ∉ A) :
    topicMassOn η C T z (insert s₀ A) =
      (((A.filter fun s => nodeOf C T z s=nodeOf C T z s₀ ∧ C.word s=C.word s₀).card:ℝ)+η) /
      ((∑ v : Fin V,((A.filter fun s => nodeOf C T z s=nodeOf C T z s₀ ∧ C.word s=v).card:ℝ))+V*η) *
      topicMassOn η C T z A := by
  classical
  let b₀ := nodeOf C T z s₀
  let I := insert b₀ (A.image (nodeOf C T z))
  let B := A.filter (fun s => nodeOf C T z s=b₀)
  let R := (((B.filter fun s => C.word s=C.word s₀).card:ℝ)+η) /
      ((∑ v : Fin V,((B.filter fun s => C.word s=v).card:ℝ))+V*η)
  have hI : ∀ s ∈ A,nodeOf C T z s ∈ I := fun s hs => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs)
  have hI' : ∀ s ∈ insert s₀ A,nodeOf C T z s ∈ I := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hs
    · exact Finset.mem_insert_self _ _
    · exact hI s hs
  rw [topic_factorization η hη C T z _ I hI',topic_factorization η hη C T z _ I hI]
  have hfactor (b : Node D) :
      (∫ p,∏ s ∈ (insert s₀ A).filter (fun s => nodeOf C T z s=b),p (C.word s) ∂dirichletMeasure (fun _ : Fin V => η)) =
      (if b=b₀ then R else 1) * (∫ p,∏ s ∈ A.filter (fun s => nodeOf C T z s=b),p (C.word s) ∂dirichletMeasure (fun _ : Fin V => η)) := by
    by_cases hb : b=b₀
    · subst b
      have hnot : s₀ ∉ B := fun h => hs₀ (Finset.mem_filter.mp h).1
      simp only [if_pos rfl]
      have hf : (insert s₀ A).filter (fun s => nodeOf C T z s=b₀) = insert s₀ B := by
        ext s
        simp only [Finset.mem_filter,Finset.mem_insert,B]
        aesop
      rw [hf]
      simp_rw [Finset.prod_insert hnot]
      exact moment_word η hη B C.word (C.word s₀)
    · have hf : (insert s₀ A).filter (fun s => nodeOf C T z s=b) = A.filter (fun s => nodeOf C T z s=b) := by
        ext s
        simp only [Finset.mem_filter,Finset.mem_insert]
        constructor
        · rintro ⟨rfl|hs,he⟩
          · exact False.elim (hb he.symm)
          · exact ⟨hs,he⟩
        · rintro ⟨hs,he⟩;exact ⟨Or.inr hs,he⟩
      rw [hf,if_neg hb,one_mul]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ b ∈ I,if b=b₀ then R else 1)=R := by simp [I]
  rw [hprod]
  congr 1
  dsimp [R,B,b₀]
  simp only [Finset.filter_filter]

lemma block_eq_iff {D : ℕ} (T : Tree D) (k : ℕ) (e d : Fin D) :
    T.block k e=T.block k d ↔ T.Rel k e d := by
  classical
  constructor
  · intro h
    have hm : e ∈ T.block k e := by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(T.part k).refl e⟩
    rw [h] at hm
    simpa [Tree.block] using hm
  · intro h
    ext x
    simp only [Tree.block,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hx => (T.part k).trans hx h,fun hx => (T.part k).trans hx ((T.part k).symm h)⟩

lemma word_predictive {V D : ℕ} (H : Hyper) (C : Corpus V D) (T : Tree D) (z : C.Levels)
    (s₀ : C.Site) (k : ℕ) :
    topicMass H.eta C T (C.setLevel z s₀ k) = levelLik H.eta C (T,z) s₀ k *
      topicMassOn H.eta C T z (Finset.univ.erase s₀) := by
  classical
  let z' := C.setLevel z s₀ k
  let A := Finset.univ.erase s₀
  have ho (s : C.Site) (hs : s ∈ A) : nodeOf C T z' s=nodeOf C T z s := by
    have hne := (Finset.mem_erase.mp hs).1
    simp [nodeOf,z',Corpus.setLevel,hne]
  have hself : nodeOf C T z' s₀=(k,T.block k s₀.1) := by simp [nodeOf,z',Corpus.setLevel]
  have hc (v : Fin V) : (A.filter fun s => nodeOf C T z' s=nodeOf C T z' s₀ ∧ C.word s=v).card = siteCount C (T,z) s₀ k v := by
    unfold siteCount
    congr 1
    ext s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hs,hn,hw⟩
      rw [ho s hs,hself] at hn
      have hk := congrArg Prod.fst hn
      have hb := congrArg Prod.snd hn
      change z s.1 s.2=k at hk
      change T.block (z s.1 s.2) s.1=T.block k s₀.1 at hb
      rw [hk] at hb
      exact ⟨(Finset.mem_erase.mp hs).1,hk,(block_eq_iff T k _ _).mp hb,hw⟩
    · rintro ⟨hne,hk,hr,hw⟩
      have hs : s ∈ A := Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩
      refine ⟨hs,?_,hw⟩
      rw [ho s hs,hself]
      simp only [nodeOf,hk,Prod.mk.injEq,true_and]
      exact (block_eq_iff T k _ _).mpr hr
  have hm : topicMassOn H.eta C T z' A=topicMassOn H.eta C T z A := by
    unfold topicMassOn
    apply integral_congr_ae
    filter_upwards [] with β
    apply Finset.prod_congr rfl
    intro s hs
    rw [ho s hs]
  have hh := topic_insert H.eta H.eta_pos C T z' A s₀ (Finset.notMem_erase _ _)
  simp_rw [hc] at hh
  rw [hm] at hh
  simpa only [A,Finset.insert_erase (Finset.mem_univ s₀),topicMass,levelLik] using hh

end
end TopicPredictive

open MeasureTheory NestedCRP in
lemma distinct_word_control :
    (∫ p : Fin 2 → ℝ,p 1*p 0 ∂dirichletMeasure (fun _ : Fin 2 => (1/2:ℝ))) =
      (1/4:ℝ)*(∫ p : Fin 2 → ℝ,p 0 ∂dirichletMeasure (fun _ : Fin 2 => (1/2:ℝ))) := by
  have h := TopicPredictive.moment_word (1/2:ℝ) (by norm_num) ({0} : Finset (Fin 1)) (fun _ => (0 : Fin 2)) 1
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h
open MeasureTheory NestedCRP in
lemma repeated_word_control :
    (∫ p : Fin 2 → ℝ,p 0*p 0 ∂dirichletMeasure (fun _ : Fin 2 => (1/2:ℝ))) =
      (3/4:ℝ)*(∫ p : Fin 2 → ℝ,p 0 ∂dirichletMeasure (fun _ : Fin 2 => (1/2:ℝ))) := by
  have h := TopicPredictive.moment_word (1/2:ℝ) (by norm_num) ({0} : Finset (Fin 1)) (fun _ => (0 : Fin 2)) 0
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h
open NestedCRP in
theorem carried_word_solution {V D : ℕ} (H : Hyper) (C : Corpus V D) (T : Tree D) (z : C.Levels)
    (s₀ : C.Site) (k : ℕ) :
    topicMass H.eta C T (C.setLevel z s₀ k) = levelLik H.eta C (T,z) s₀ k *
      topicMassOn H.eta C T z (Finset.univ.erase s₀) := TopicPredictive.word_predictive H C T z s₀ k

end

open NestedCRP Finset
namespace LevelConditional
noncomputable section
lemma same_document {V D : ℕ} (C : Corpus V D) (z : C.Levels) (s : C.Site) (k : ℕ) :
    C.setLevel z s k s.1 = Function.update (z s.1) s.2 k := by
  classical
  funext n
  rcases s with ⟨d,j⟩
  simp [Corpus.setLevel,Function.update]
lemma other_document {V D : ℕ} (C : Corpus V D) (z : C.Levels) (s : C.Site) (k : ℕ)
    (d : Fin D) (hd : d ≠ s.1) : C.setLevel z s k d = z d := by
  funext n
  have hn : (⟨d,n⟩ : C.Site) ≠ s := fun h => hd (congrArg Sigma.fst h)
  simp [Corpus.setLevel,hn]
lemma document_product {V D : ℕ} (H : Hyper) (C : Corpus V D) (z : C.Levels)
    (s : C.Site) (k : ℕ) :
    (∏ d, stickMass H.m H.pi (C.setLevel z s k d)) =
      levelPrior H.m H.pi (z s.1) s.2 k *
      (stickMass H.m H.pi (fun i : {i // i ≠ s.2} => z s.1 i) *
        ∏ d ∈ Finset.univ.erase s.1,stickMass H.m H.pi (z d)) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun d => stickMass H.m H.pi (C.setLevel z s k d)) (Finset.mem_univ s.1),same_document,
    (CarriedPrior.solution H (z s.1) s.2).1 k]
  have ho : (∏ d ∈ Finset.univ.erase s.1,stickMass H.m H.pi (C.setLevel z s k d)) =
      ∏ d ∈ Finset.univ.erase s.1,stickMass H.m H.pi (z d) := by
    apply Finset.prod_congr rfl
    intro d hd
    rw [other_document C z s k d (Finset.mem_erase.mp hd).1]
  rw [ho,mul_assoc]
noncomputable def outsideFactor {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State) (s : C.Site) : ℝ :=
  ncrpMass H.gamma x.1 *
    (stickMass H.m H.pi (fun i : {i // i ≠ s.2} => x.2 s.1 i) *
      ∏ d ∈ Finset.univ.erase s.1,stickMass H.m H.pi (x.2 d)) *
    topicMassOn H.eta C x.1 x.2 (Finset.univ.erase s)
lemma joint_factor {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State) (s : C.Site) (k : ℕ) :
    joint H C (x.1,C.setLevel x.2 s k) = outsideFactor H C x s * levelWeight H C x s k := by
  rw [joint,document_product H C x.2 s k,TopicPredictive.word_predictive H C x.1 x.2 s k]
  simp only [outsideFactor,levelWeight]
  ring
end
end LevelConditional
open NestedCRP in
theorem solution {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State) (s₀ : C.Site) :
    (∀ k, 0 < levelWeight H C x s₀ k) ∧ Summable (levelWeight H C x s₀) ∧
      0 < ∑' k, levelWeight H C x s₀ k ∧
      ∀ k k', joint H C (x.1, C.setLevel x.2 s₀ k) * levelWeight H C x s₀ k' =
        joint H C (x.1, C.setLevel x.2 s₀ k') * levelWeight H C x s₀ k := by
  obtain ⟨hp,hs,ht⟩ := LevelWeightBounds.weight_well_defined H C x s₀
  refine ⟨hp,hs,ht,?_⟩
  intro k k'
  rw [LevelConditional.joint_factor,LevelConditional.joint_factor]
  ring

namespace LevelConditional
open NestedCRP
noncomputable def controlHyper : Hyper := ⟨1,1/2,1/2,2,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩
lemma two_level_weights_control (T : Tree 1) :
    levelWeight controlHyper LevelWeightBounds.controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 0 = 1/6 ∧
    levelWeight controlHyper LevelWeightBounds.controlCorpus (T,fun _ _ => 0) ⟨0,0⟩ 1 = 1/12 := by
  have he : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have hp : levelPrior (1/2) 2 (fun _ : Fin 2 => 0) 0 0 = 2/3 ∧
      levelPrior (1/2) 2 (fun _ : Fin 2 => 0) 0 1 = 1/6 := by
    norm_num [levelPrior,he]
  have hl := LevelWeightBounds.normalized_likelihood_control T
  constructor
  · change levelPrior (1/2) 2 (fun _ : Fin 2 => 0) 0 0 * _ = 1/6
    dsimp only [controlHyper]
    rw [hp.1,hl.1]
    norm_num
  · change levelPrior (1/2) 2 (fun _ : Fin 2 => 0) 0 1 * _ = 1/12
    dsimp only [controlHyper]
    rw [hp.2,hl.2]
    norm_num
lemma two_level_joint_control (T : Tree 1) :
    joint controlHyper LevelWeightBounds.controlCorpus
      (T,LevelWeightBounds.controlCorpus.setLevel (fun _ _ => 0) ⟨0,0⟩ 0) =
    2 * joint controlHyper LevelWeightBounds.controlCorpus
      (T,LevelWeightBounds.controlCorpus.setLevel (fun _ _ => 0) ⟨0,0⟩ 1) := by
  have h := (solution controlHyper LevelWeightBounds.controlCorpus (T,fun _ _ => 0) ⟨0,0⟩).2.2.2 0 1
  rw [(two_level_weights_control T).1,(two_level_weights_control T).2] at h
  linarith
end LevelConditional
