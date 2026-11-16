-- Prove2me | solution 1 for NestedCRP.level_prior
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T21:14:36.684393+00:00
-- url     : https://prove2.me/submissions/2ed758d9-2f14-433a-8432-d3e608abf3d0

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_stickMass
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
