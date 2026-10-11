-- Prove2me | solution 1 for LubyMIS.Derandomized.algorithmD_rounds
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T22:30:13.768339+00:00
-- url     : https://prove2.me/submissions/29c74dd0-e778-47ce-b96b-b2b3fba3e09f

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic
import Definitions.Def_LubyMIS_Derandomized_AlgorithmD

-- BEGIN COMPLETE MODULE FiniteAverage
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

noncomputable def avg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

lemma avg_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg (fun ω _ => hf ω)) (Nat.cast_nonneg _)

lemma avg_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

lemma avg_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    avg (fun ω => f ω + g ω) = avg f + avg g := by simp [avg, Finset.sum_add_distrib, add_div]

lemma avg_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    avg (fun ω => f ω - g ω) = avg f - avg g := by simp [avg, Finset.sum_sub_distrib, sub_div]

lemma avg_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    avg (fun ω => a * f ω) = a * avg f := by simp [avg, ← Finset.mul_sum, mul_div_assoc]

lemma avg_sum {Ω ι : Type*} [Fintype Ω] (J : Finset ι) (f : ι → Ω → ℝ) :
    avg (fun ω => ∑ i ∈ J, f i ω) = ∑ i ∈ J, avg (f i) := by
  simp only [avg, ← Finset.sum_div]
  rw [Finset.sum_comm]

lemma avg_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) : avg (fun _ : Ω => a) = a := by
  simp [avg, Fintype.card_ne_zero]

noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> norm_num [bit]
lemma bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> norm_num [bit]
lemma bit_sq (b : Bool) : bit b * bit b = bit b := by cases b <;> norm_num [bit]

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE FiniteAverage

-- BEGIN COMPLETE MODULE AffineSamples
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

variable {K : Type*} [Field K]

def affinePair (i j : K) (hij : i ≠ j) : (K × K) ≃ (K × K) where
  toFun p := (p.1 + p.2*i, p.1 + p.2*j)
  invFun p := ((j*p.1-i*p.2)/(j-i), (p.2-p.1)/(j-i))
  left_inv := by
    intro p
    have hn : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    ext <;> dsimp <;> field_simp <;> ring
  right_inv := by
    intro p
    have hn : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    ext <;> dsimp <;> field_simp <;> ring

def affineSingle (i : K) : (K × K) ≃ (K × K) where
  toFun p := (p.1 + p.2*i, p.2)
  invFun p := (p.1 - p.2*i, p.2)
  left_inv := by
    intro p
    apply Prod.ext
    · dsimp; ring
    · rfl
  right_inv := by
    intro p
    apply Prod.ext
    · dsimp; ring
    · rfl

lemma avg_affine_pair [Fintype K] (i j : K) (hij : i ≠ j) (f g : K → ℝ) :
    avg (fun p : K × K => f (p.1+p.2*i) * g (p.1+p.2*j)) = avg f * avg g := by
  have he := Equiv.sum_comp (affinePair i j hij) (fun p : K × K => f p.1 * g p.2)
  change (∑ p : K × K, f (p.1+p.2*i) * g (p.1+p.2*j)) = _ at he
  unfold avg
  rw [he, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp [Fintype.card_prod, Nat.cast_mul, div_mul_div_comm]

lemma avg_affine_single [Fintype K] (i : K) (f : K → ℝ) :
    avg (fun p : K × K => f (p.1+p.2*i)) = avg f := by
  have he := Equiv.sum_comp (affineSingle i) (fun p : K × K => f p.1)
  change (∑ p : K × K, f (p.1+p.2*i)) = _ at he
  unfold avg
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Fintype.card_prod, Nat.cast_mul]
  have hn : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE AffineSamples

-- BEGIN COMPLETE MODULE CoinMarginals
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

noncomputable def rounded (q d : ℕ) : ℝ := (q / (2*d) : ℕ) / (q : ℝ)

def thresholdEquiv (q k : ℕ) [NeZero q] (hk : k ≤ q) :
    {z : ZMod q // z.val < k} ≃ Fin k where
  toFun z := ⟨z.val.val, z.property⟩
  invFun i := ⟨(i.val : ZMod q), by simp [ZMod.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans_le hk)]⟩
  left_inv := by intro z; apply Subtype.ext; exact ZMod.natCast_zmod_val _
  right_inv := by intro i; apply Fin.ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans_le hk)]

lemma avg_threshold (q k : ℕ) [NeZero q] (hk : k ≤ q) :
    avg (fun z : ZMod q => bit (decide (z.val < k))) = (k : ℝ) / q := by
  have hc : (Finset.univ.filter (fun z : ZMod q => z.val < k)).card = k := by
    have he := Fintype.card_congr (thresholdEquiv q k hk)
    simpa [Fintype.card_subtype] using he
  simp only [avg, bit, Bool.decide_iff]
  simp [hc, ZMod.card]

lemma coin_average {n q : ℕ} [NeZero q] (hq : q.Prime)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i : Fin n) :
    avg (fun p : ZMod q × ZMod q => bit (coinD q H p.1 p.2 i)) = rounded q (H.degree i) := by
  let : Fact q.Prime := ⟨hq⟩
  unfold coinD
  rw [avg_affine_single (i.val : ZMod q) (fun z => bit (decide (z.val < q/(2*H.degree i))))]
  exact avg_threshold q _ (Nat.div_le_self _ _)

lemma coin_pair_average {n q : ℕ} [NeZero q] (hq : q.Prime) (hnq : n ≤ q)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i j : Fin n) (hij : i ≠ j) :
    avg (fun p : ZMod q × ZMod q => bit (coinD q H p.1 p.2 i) *
      bit (coinD q H p.1 p.2 j)) = rounded q (H.degree i) * rounded q (H.degree j) := by
  let : Fact q.Prime := ⟨hq⟩
  have hcast : (i.val : ZMod q) ≠ (j.val : ZMod q) := by
    intro he
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans_le hnq),
      Nat.mod_eq_of_lt (j.isLt.trans_le hnq)] at hv
    exact hij (Fin.ext hv)
  unfold coinD
  rw [avg_affine_pair _ _ hcast
    (fun z => bit (decide (z.val < q/(2*H.degree i))))
    (fun z => bit (decide (z.val < q/(2*H.degree j)))),
    avg_threshold q _ (Nat.div_le_self _ _), avg_threshold q _ (Nat.div_le_self _ _)]
  rfl

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE CoinMarginals

-- BEGIN COMPLETE MODULE RoundedBounds
section

namespace LubyMIS.Derandomized.Proof

lemma rounded_nonneg (q d : ℕ) : 0 ≤ rounded q d := by unfold rounded; positivity

lemma rounded_upper (q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    rounded q d ≤ 1 / (2 * (d : ℝ)) := by
  have hnat := Nat.div_mul_le_self q (2*d)
  have hreal : ((q/(2*d) : ℕ) : ℝ) * (2*(d : ℝ)) ≤ q := by exact_mod_cast hnat
  unfold rounded
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < q)).mpr
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*d)).mpr
  nlinarith

lemma rounded_lower (q d : ℕ) (hd : 0 < d) (hsmall : 16*d < q) :
    (8/9 : ℝ) / (2*(d : ℝ)) ≤ rounded q d := by
  have hq : 0 < q := by omega
  have hden : 0 < 2*d := by omega
  have hk : 8 ≤ q/(2*d) := (Nat.le_div_iff_mul_le hden).mpr (by omega)
  have hlt : q < (q/(2*d)+1)*(2*d) :=
    (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self _)
  have hb : 8*q ≤ 9*(q/(2*d))*(2*d) := by nlinarith
  have hr : (8 : ℝ)*q ≤ 9*((q/(2*d) : ℕ) : ℝ)*(2*d) := by exact_mod_cast hb
  unfold rounded
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*d)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < q)).mpr
  nlinarith

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE RoundedBounds

-- BEGIN COMPLETE MODULE BlockerBounds
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

variable {n : ℕ}

def blockers (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (j : Fin n) : Finset (Fin n) :=
  (H.neighborFinset j).filter (fun u => H.degree j ≤ H.degree u)

lemma blockers_self (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (j : Fin n) :
    j ∉ blockers H j := by simp [blockers]

lemma blocker_sum_bound (q : ℕ) (hq : 0 < q)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (j : Fin n) :
    (∑ u ∈ blockers H j, rounded q (H.degree u)) ≤ (1/2 : ℝ) := by
  by_cases hd : H.degree j = 0
  · have he : H.neighborFinset j = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hd
    simp [blockers, he]
  · have hdpos : 0 < H.degree j := Nat.pos_of_ne_zero hd
    have hreal : (0 : ℝ) < H.degree j := by exact_mod_cast hdpos
    calc
      _ ≤ ∑ u ∈ blockers H j, 1/(2*(H.degree j : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        have hle := (Finset.mem_filter.mp hu).2
        have huPos : 0 < H.degree u := hdpos.trans_le hle
        exact (rounded_upper q _ hq huPos).trans
          (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hle))
      _ ≤ (H.degree j : ℝ)*(1/(2*(H.degree j : ℝ))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (SimpleGraph.card_neighborFinset_eq_degree H j)
      _ = 1/2 := by field_simp

lemma survival_or_blocker (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (c : Fin n → Bool) (v j : Fin n) (hj : j ∈ H.neighborFinset v) (hc : c j = true) :
    v ∈ nbhd H (selectB H c) ∨ ∃ u ∈ blockers H j, c u = true := by
  classical
  by_cases hb : ∃ u ∈ blockers H j, c u = true
  · exact Or.inr hb
  left
  have hsel : j ∈ selectB H c := by
    simp only [selectB, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hc, ?_⟩
    intro u hju hcu
    apply lt_of_not_ge
    intro hle
    exact hb ⟨u, Finset.mem_filter.mpr ⟨by simpa using hju, hle⟩, hcu⟩
  simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, hsel, by simpa using hj⟩

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE BlockerBounds

-- BEGIN COMPLETE MODULE PairSums
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

lemma sum_offdiag {ι : Type*} [DecidableEq ι] (J : Finset ι) (p : ι → ℝ) :
    (∑ i ∈ J, ∑ j ∈ J.erase i, p i * p j) = (∑ i ∈ J, p i)^2 - ∑ i ∈ J, (p i)^2 := by
  calc
    _ = ∑ i ∈ J, p i * ((∑ j ∈ J, p j) - p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hi]
    _ = _ := by simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, ← Finset.sum_mul]; ring_nf

lemma bit_sum_card {ι : Type*} (J : Finset ι) (c : ι → Bool) :
    (∑ i ∈ J, bit (c i)) = ((J.filter (fun i => c i)).card : ℝ) := by
  simp [bit]

lemma bit_offdiag {ι : Type*} [DecidableEq ι] (J : Finset ι) (c : ι → Bool) :
    (∑ i ∈ J, ∑ j ∈ J.erase i, bit (c i)*bit (c j)) =
      (∑ i ∈ J, bit (c i)) * ((∑ i ∈ J, bit (c i)) - 1) := by
  rw [sum_offdiag]
  have hs : (∑ i ∈ J, (bit (c i))^2) = ∑ i ∈ J, bit (c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [pow_two] using bit_sq (c i)
  rw [hs]; ring

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE PairSums

-- BEGIN COMPLETE MODULE FractionalBonferroni
section

namespace LubyMIS.Derandomized.Proof

lemma fractional_count_bound (k : ℕ) (a : ℝ) (_ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a * k - a^2 * ((k : ℝ) * (k - 1) / 2) ≤ 1 := by
  rcases k with _ | k
  · norm_num
  rcases k with _ | k
  · norm_num; exact ha1
  have hk : (2 : ℝ) ≤ (k + 2 : ℕ) := by exact_mod_cast Nat.le_add_left 2 k
  have hsq := mul_nonneg (show (0 : ℝ) ≤ (k + 2 : ℕ) by positivity)
    (sq_nonneg ((((k + 2 : ℕ) : ℝ) - 1) * a - 1))
  have hid : 2 * (((k + 2 : ℕ) : ℝ) - 1) *
      (1 - (a * (k + 2 : ℕ) - a^2 * ((k + 2 : ℕ) * ((k + 2 : ℕ) - 1) / 2))) =
      (k + 2 : ℕ) * ((((k + 2 : ℕ) : ℝ) - 1) * a - 1)^2 + ((k + 2 : ℕ) - 2) := by ring
  have hprod : 0 ≤ 2 * (((k + 2 : ℕ) : ℝ) - 1) *
      (1 - (a * (k + 2 : ℕ) - a^2 * ((k + 2 : ℕ) * ((k + 2 : ℕ) - 1) / 2))) := by
    rw [hid]; linarith
  have hfactor : 0 < 2 * (((k + 2 : ℕ) : ℝ) - 1) := by linarith
  have := (mul_nonneg_iff_of_pos_left hfactor).mp hprod
  simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using (sub_nonneg.mp this)

lemma choose_fraction (a : ℝ) (ha : 0 ≤ a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 / 4 : ℝ) * min a (1 / 2) ≤ t*a/2 - t^2*a^2/2 := by
  by_cases h : a ≤ 1/2
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [min_eq_left h]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]
  · have hp : 0 < a := by linarith
    refine ⟨1/(2*a), by positivity, ?_, ?_⟩
    · apply (div_le_one (by positivity : 0 < 2*a)).mpr; linarith
    · rw [min_eq_right (by linarith)]
      have he : 1/(2*a)*a = (1/2 : ℝ) := by field_simp
      nlinarith [sq_nonneg (1/(2*a)*a - 1/2)]

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE FractionalBonferroni

-- BEGIN COMPLETE MODULE SurvivalPointwise
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

lemma survival_pointwise {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ι) (c : ι → Bool) (covered : Bool)
    (hfail : ∀ j ∈ J, c j = true → covered = true ∨ ∃ u ∈ B j, c u = true)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a*(∑ j ∈ J, bit (c j)) - a^2/2*(∑ j ∈ J, ∑ u ∈ J.erase j, bit (c j)*bit (c u)) -
      a*(∑ j ∈ J, bit (c j)*(∑ u ∈ B j, bit (c u))) ≤ bit covered := by
  have hpair : 0 ≤ ∑ j ∈ J, ∑ u ∈ J.erase j, bit (c j)*bit (c u) :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun u _ => mul_nonneg (bit_nonneg _) (bit_nonneg _)))
  have hblock : 0 ≤ ∑ j ∈ J, bit (c j)*(∑ u ∈ B j, bit (c u)) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (bit_nonneg _) (Finset.sum_nonneg (fun u _ => bit_nonneg _)))
  cases hc : covered with
  | true =>
    have hb := fractional_count_bound (J.filter (fun j => c j)).card a ha ha1
    rw [bit_offdiag, bit_sum_card]
    change _ ≤ (1 : ℝ)
    nlinarith [mul_nonneg ha hblock]
  | false =>
    have hdom : (∑ j ∈ J, bit (c j)) ≤ ∑ j ∈ J, bit (c j)*(∑ u ∈ B j, bit (c u)) := by
      apply Finset.sum_le_sum
      intro j hj
      cases hjc : c j with
      | false => simp [bit]
      | true =>
        obtain h | ⟨u, hu, huc⟩ := hfail j hj hjc
        · simp [hc] at h
        · have hs := Finset.single_le_sum (fun v _ => bit_nonneg (c v)) hu
          simp only [huc, bit, if_true] at hs
          simpa only [hjc, bit, if_true, one_mul] using hs
    change _ ≤ (0 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hdom ha,
      mul_nonneg (div_nonneg (sq_nonneg a) (by norm_num : (0 : ℝ) ≤ 2)) hpair]

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE SurvivalPointwise

-- BEGIN COMPLETE MODULE SurvivalAverage
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

lemma survival_average {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ι) (c : ι → Ω → Bool) (covered : Ω → Bool)
    (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hmarg : ∀ j, avg (fun ω => bit (c j ω)) = p j)
    (hpair : ∀ i j, i ≠ j → avg (fun ω => bit (c i ω)*bit (c j ω)) = p i*p j)
    (hself : ∀ j ∈ J, j ∉ B j)
    (hblock : ∀ j ∈ J, ∑ u ∈ B j, p u ≤ 1/2)
    (hfail : ∀ ω, ∀ j ∈ J, c j ω = true → covered ω = true ∨ ∃ u ∈ B j, c u ω = true) :
    (1/4 : ℝ) * min (∑ j ∈ J, p j) (1/2) ≤ avg (fun ω => bit (covered ω)) := by
  let A := ∑ j ∈ J, p j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => hp j)
  obtain ⟨a, ha, ha1, hchoose⟩ := choose_fraction A hA
  have hmain := avg_mono (fun ω => survival_pointwise J B (fun j => c j ω) (covered ω)
    (hfail ω) a ha ha1)
  have hfirst : avg (fun ω => ∑ j ∈ J, bit (c j ω)) = A := by
    rw [avg_sum]; simp_rw [hmarg]; rfl
  have hpairs : avg (fun ω => ∑ j ∈ J, ∑ u ∈ J.erase j, bit (c j ω)*bit (c u ω)) =
      A^2 - ∑ j ∈ J, (p j)^2 := by
    simp_rw [avg_sum]
    rw [← sum_offdiag]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro u hu
    exact hpair j u (Finset.ne_of_mem_erase hu).symm
  have hblocks : avg (fun ω => ∑ j ∈ J, bit (c j ω)*(∑ u ∈ B j, bit (c u ω))) ≤ A/2 := by
    rw [avg_sum]
    calc
      _ = ∑ j ∈ J, p j*(∑ u ∈ B j, p u) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp_rw [Finset.mul_sum]
        rw [avg_sum]
        apply Finset.sum_congr rfl
        intro u hu
        exact hpair j u (fun he => hself j hj (he ▸ hu))
      _ ≤ ∑ j ∈ J, p j*(1/2) := Finset.sum_le_sum
        (fun j hj => mul_le_mul_of_nonneg_left (hblock j hj) (hp j))
      _ = A/2 := by rw [← Finset.sum_mul]; dsimp [A]; ring
  simp only [avg_sub, avg_mul, hfirst, hpairs] at hmain
  have hsq : 0 ≤ ∑ j ∈ J, (p j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_left hblocks ha
  have he := mul_nonneg (div_nonneg (sq_nonneg a) (by norm_num : (0 : ℝ) ≤ 2)) hsq
  change (1/4 : ℝ)*min A (1/2) ≤ _
  nlinarith only [hmain, hb, he, hchoose]

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE SurvivalAverage

-- BEGIN COMPLETE MODULE NeighborhoodProbability
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

lemma quarter_min_transfer (a b : ℝ) (_hb : 0 ≤ b) (hab : (4/9 : ℝ)*b ≤ a) :
    (1/9 : ℝ)*min b 1 ≤ (1/4 : ℝ)*min a (1/2) := by
  by_cases ha : a ≤ 1/2 <;> by_cases hb1 : b ≤ 1
  · rw [min_eq_left ha, min_eq_left hb1]; linarith
  · rw [min_eq_left ha, min_eq_right (le_of_not_ge hb1)]; linarith
  · rw [min_eq_right (le_of_not_ge ha), min_eq_left hb1]; linarith
  · rw [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb1)]; norm_num

lemma neighborhood_probability {n q : ℕ} [NeZero q] (hq : q.Prime) (hnq : n ≤ q)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hsmall : ∀ i, 16*H.degree i < n) (v : Fin n) :
    (1/9 : ℝ)*min (sumInv H v) 1 ≤
      avg (fun p : ZMod q × ZMod q => bit (decide (v ∈ nbhd H (selectB H (coinD q H p.1 p.2))))) := by
  classical
  have hbase := survival_average (H.neighborFinset v) (blockers H)
    (fun j (p : ZMod q × ZMod q) => coinD q H p.1 p.2 j)
    (fun p => decide (v ∈ nbhd H (selectB H (coinD q H p.1 p.2))))
    (fun j => rounded q (H.degree j)) (fun j => rounded_nonneg q _)
    (fun j => coin_average hq H j) (fun i j hij => coin_pair_average hq hnq H i j hij)
    (fun j _ => blockers_self H j) (fun j _ => blocker_sum_bound q hq.pos H j) ?_
  · apply le_trans _ hbase
    apply quarter_min_transfer
    · exact Finset.sum_nonneg (fun j _ => by positivity)
    · unfold sumInv
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjv : H.Adj j v := (show H.Adj v j by simpa using hj).symm
      have hd : 0 < H.degree j := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨v, by simpa using hjv⟩
      have h := rounded_lower q (H.degree j) hd ((hsmall j).trans_le hnq)
      have he : (4/9 : ℝ)*(1/(H.degree j : ℝ)) = (8/9 : ℝ)/(2*(H.degree j : ℝ)) := by ring
      rw [he]
      exact h
  · intro p j hj hc
    rcases survival_or_blocker H (coinD q H p.1 p.2) v j hj hc with hh | hh
    · exact Or.inl (by simpa using hh)
    · exact Or.inr hh

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE NeighborhoodProbability

-- BEGIN COMPLETE MODULE DegreeWeight
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

variable {n : ℕ}

noncomputable def edgeCharge (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (u v : Fin n) : ℝ :=
  if H.Adj u v then if sumInv H u ≤ 1 then (H.degree u : ℝ) / H.degree v else 1 else 0

lemma degree_pos_adj (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] {u v : Fin n}
    (h : H.Adj u v) : 0 < H.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_pos.mpr ⟨v, by simpa using h⟩

lemma edgeCharge_pair (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (u v : Fin n) :
    (if H.Adj u v then (1 : ℝ) else 0) ≤ edgeCharge H u v + edgeCharge H v u := by
  by_cases huv : H.Adj u v
  · have hvu := huv.symm
    have hu : (0 : ℝ) < H.degree u := by exact_mod_cast degree_pos_adj H huv
    have hv : (0 : ℝ) < H.degree v := by exact_mod_cast degree_pos_adj H hvu
    simp only [edgeCharge, if_pos huv, if_pos hvu]
    split_ifs <;> try positivity
    · have hh : (2 : ℝ) ≤ (H.degree u : ℝ)/H.degree v + (H.degree v : ℝ)/H.degree u := by
        have hid : (H.degree u : ℝ)/H.degree v + (H.degree v : ℝ)/H.degree u =
            ((H.degree u : ℝ)^2+(H.degree v : ℝ)^2)/((H.degree u : ℝ)*H.degree v) := by
          field_simp
        rw [hid]
        apply (le_div_iff₀ (mul_pos hu hv)).mpr
        nlinarith [sq_nonneg ((H.degree u : ℝ) - H.degree v)]
      linarith
    · linarith [div_nonneg hu.le hv.le]
    · linarith [div_nonneg hv.le hu.le]
    · norm_num
  · have hvu : ¬H.Adj v u := fun h => huv h.symm
    simp [edgeCharge, huv, hvu]

lemma edgeCharge_sum (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (u : Fin n) :
    (∑ v, edgeCharge H u v) = (H.degree u : ℝ) * min (sumInv H u) 1 := by
  classical
  by_cases hu : sumInv H u ≤ 1
  · simp only [edgeCharge, if_pos hu, min_eq_left hu]
    rw [← Finset.sum_filter]
    rw [← H.neighborFinset_eq_filter]
    simp [sumInv, Finset.mul_sum, div_eq_mul_inv]
  · simp only [edgeCharge, if_neg hu, min_eq_right (le_of_not_ge hu), mul_one]
    simp only [Finset.sum_boole]
    rw [← H.neighborFinset_eq_filter, H.card_neighborFinset_eq_degree]

lemma degree_weight_ge_edges (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (H.edgeFinset.card : ℝ) ≤ ∑ u, (H.degree u : ℝ) * min (sumInv H u) 1 := by
  have hp := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (s := Finset.univ) (fun v _ => edgeCharge_pair H u v))
  simp_rw [Finset.sum_add_distrib] at hp
  rw [Finset.sum_comm (f := fun u v => edgeCharge H v u)] at hp
  simp_rw [edgeCharge_sum] at hp
  have hd : (∑ u, ∑ v, if H.Adj u v then (1 : ℝ) else 0) = 2*(H.edgeFinset.card : ℝ) := by
    have hh := H.sum_degrees_eq_twice_card_edges
    have he (u : Fin n) : (∑ v, if H.Adj u v then (1 : ℝ) else 0) = H.degree u := by
      simp only [Finset.sum_boole]
      rw [← H.neighborFinset_eq_filter, H.card_neighborFinset_eq_degree]
    simp_rw [he]
    exact_mod_cast hh
  rw [hd] at hp
  linarith

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE DegreeWeight

-- BEGIN COMPLETE MODULE EliminatedIncidence
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ}

def touchedGraph (H : SimpleGraph (Fin n)) (K : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := H.Adj a b ∧ (a ∈ K ∨ b ∈ K)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩

instance touchedGraphDecidable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (K : Finset (Fin n)) : DecidableRel (touchedGraph H K).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma touched_degree (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (K : Finset (Fin n)) {v : Fin n} (hv : v ∈ K) :
    (touchedGraph H K).degree v = H.degree v := by
  classical
  have he : (touchedGraph H K).neighborFinset v = H.neighborFinset v := by
    ext w
    rw [(touchedGraph H K).mem_neighborFinset, H.mem_neighborFinset]
    change H.Adj v w ∧ (v∈K ∨ w∈K) ↔ H.Adj v w
    exact and_iff_left (Or.inl hv)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using congrArg Finset.card he

lemma touched_edgeFinset (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (K : Finset (Fin n)) :
    (touchedGraph H K).edgeFinset = H.edgeFinset.filter (fun e => ∃v∈e, v∈K) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      change H.Adj a b ∧ (a∈K ∨ b∈K) ↔ H.Adj a b ∧ _
      simp

lemma degree_sum_neighborhood_le (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (J : Finset (Fin n)) :
    (∑ v ∈ nbhd H J, H.degree v) ≤ 2 * eliminated H J := by
  classical
  let K := J ∪ nbhd H J
  have he : (touchedGraph H K).edgeFinset.card = eliminated H J := by
    rw [touched_edgeFinset]
    unfold eliminated
    congr 1
    ext e
    simp only [Finset.mem_filter, K]
  rw [← he, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc
    (∑v∈nbhd H J, H.degree v) = ∑v∈nbhd H J, (touchedGraph H K).degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (touched_degree H K (Finset.mem_union_right J hv)).symm
    _ ≤ ∑v, (touchedGraph H K).degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE EliminatedIncidence

-- BEGIN COMPLETE MODULE BestSample
section

open scoped BigOperators
namespace LubyMIS.Derandomized.Proof

lemma expected_elimination {n q : ℕ} [NeZero q] (hq : q.Prime) (hnq : n ≤ q)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsmall : ∀ i, 16*H.degree i < n) :
    (H.edgeFinset.card : ℝ) ≤ 18 * avg (fun p : ZMod q × ZMod q =>
      (eliminated H (selectB H (coinD q H p.1 p.2)) : ℝ)) := by
  classical
  let cov (v : Fin n) (p : ZMod q × ZMod q) :=
    bit (decide (v ∈ nbhd H (selectB H (coinD q H p.1 p.2))))
  have hpoint (p : ZMod q × ZMod q) :
      (∑ v, (H.degree v : ℝ)*cov v p) ≤ 2*(eliminated H (selectB H (coinD q H p.1 p.2)) : ℝ) := by
    have hh := degree_sum_neighborhood_le H (selectB H (coinD q H p.1 p.2))
    have hr : (∑ v ∈ nbhd H (selectB H (coinD q H p.1 p.2)), (H.degree v : ℝ)) ≤
        2*(eliminated H (selectB H (coinD q H p.1 p.2)) : ℝ) := by exact_mod_cast hh
    simpa [cov, bit, Finset.sum_filter, mul_ite] using hr
  have hmean := avg_mono hpoint
  rw [avg_sum, avg_mul] at hmean
  simp_rw [avg_mul] at hmean
  have hcover : (∑ v, (H.degree v : ℝ)*((1/9 : ℝ)*min (sumInv H v) 1)) ≤
      ∑ v, (H.degree v : ℝ)*avg (cov v) := by
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left (neighborhood_probability hq hnq H hsmall v) (Nat.cast_nonneg _)
  have hid : (∑ v, (H.degree v : ℝ)*((1/9 : ℝ)*min (sumInv H v) 1)) =
      (1/9 : ℝ)*(∑ v, (H.degree v : ℝ)*min (sumInv H v) 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv; ring
  rw [hid] at hcover
  have hweight := degree_weight_ge_edges H
  nlinarith only [hmean, hcover, hweight]

lemma best_sample_bound {n q : ℕ} (hq : q.Prime) (hnq : n ≤ q)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsmall : ∀ i, 16*H.degree i < n)
    (x y : ZMod q)
    (hbest : ∀ x' y', eliminated H (selectB H (coinD q H x' y')) ≤
      eliminated H (selectB H (coinD q H x y))) :
    H.edgeFinset.card ≤ 18 * eliminated H (selectB H (coinD q H x y)) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have he := expected_elimination hq hnq H hsmall
  have hb := avg_mono (fun p : ZMod q × ZMod q =>
    (show (eliminated H (selectB H (coinD q H p.1 p.2)) : ℝ) ≤
      (eliminated H (selectB H (coinD q H x y)) : ℝ) by exact_mod_cast hbest p.1 p.2))
  rw [avg_const] at hb
  have hh := he.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 18))
  exact_mod_cast hh

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE BestSample

-- BEGIN COMPLETE MODULE RestrictionGeometry
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma restrict_adj {U : Finset (Fin n)} {a b : Fin n} :
    (restrict G U).Adj a b ↔ a ∈ U ∧ b ∈ U ∧ G.Adj a b := Iff.rfl

lemma degree_pos_mem {U : Finset (Fin n)} {v : Fin n}
    (h : 0 < (restrict G U).degree v) : v ∈ U := by
  obtain ⟨w, hw⟩ := ((restrict G U).degree_pos_iff_exists_adj v).mp h
  exact hw.1

lemma V1_subset (U : Finset (Fin n)) : V1 G U ⊆ U := Finset.sdiff_subset

lemma mem_V1_of_adj {U : Finset (Fin n)} {v w : Fin n}
    (h : (restrict G U).Adj v w) : v ∈ V1 G U := by
  apply Finset.mem_sdiff.mpr
  refine ⟨h.1, ?_⟩
  intro hz
  have hd := (Finset.mem_filter.mp hz).2
  have hp := h.degree_pos_left
  omega

lemma restrict_V1 (U : Finset (Fin n)) : restrict G (V1 G U) = restrict G U := by
  ext v w
  constructor
  · intro h
    exact ⟨V1_subset G U h.1, V1_subset G U h.2.1, h.2.2⟩
  · intro h
    exact ⟨mem_V1_of_adj G h, mem_V1_of_adj G h.symm, h.2.2⟩

lemma nbhd_subset {U J : Finset (Fin n)} : nbhd (restrict G U) J ⊆ U := by
  intro v hv
  obtain ⟨w, _, hw⟩ := (show ∃w∈J, (restrict G U).Adj v w from by simpa only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and] using hv)
  exact hw.1

lemma nbhd_singleton (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (v : Fin n) :
    nbhd H {v} = H.neighborFinset v := by
  ext w
  simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, exists_eq_left, SimpleGraph.mem_neighborFinset]
  exact H.adj_comm w v

lemma nbhd_zeroSet (U : Finset (Fin n)) : nbhd (restrict G U) (zeroSet G U) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨w, hw, h⟩ := (show ∃w∈zeroSet G U, (restrict G U).Adj v w from by simpa only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and] using hv)
  have hz := (Finset.mem_filter.mp hw).2
  have hp := h.degree_pos_right
  omega

lemma zeroSet_independent (U : Finset (Fin n)) :
    ∀ v ∈ zeroSet G U, ∀ w ∈ U, ¬ G.Adj v w := by
  intro v hv w hw h
  have hh : (restrict G U).Adj v w := ⟨(Finset.mem_filter.mp hv).1, hw, h⟩
  have hp := hh.degree_pos_left
  have hz := (Finset.mem_filter.mp hv).2
  omega

lemma selectB_independent (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (c : Fin n → Bool) : ∀ v ∈ selectB H c, ∀ w ∈ selectB H c, ¬ H.Adj v w := by
  intro v hv w hw h
  have hv' : c v = true ∧ ∀j, H.Adj v j → c j = true → H.degree j < H.degree v := by simpa only [selectB, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  have hw' : c w = true ∧ ∀j, H.Adj w j → c j = true → H.degree j < H.degree w := by simpa only [selectB, Finset.mem_filter, Finset.mem_univ, true_and] using hw
  have h1 := hv'.2 w h hw'.1
  have h2 := hw'.2 v h.symm hv'.1
  omega

lemma coinD_eq_false_of_degree_zero (q : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (x y : ZMod q) {v : Fin n} (hv : H.degree v = 0) : coinD q H x y v = false := by
  simp [coinD, hv]

lemma selectD_subset (q : ℕ) (U : Finset (Fin n)) (x y : ZMod q) :
    selectB (restrict G U) (coinD q (restrict G U) x y) ⊆ U := by
  intro v hv
  have hc : coinD q (restrict G U) x y v = true := (show coinD q (restrict G U) x y v = true ∧ _ from by simpa only [selectB, Finset.mem_filter, Finset.mem_univ, true_and] using hv).1
  apply degree_pos_mem G
  by_contra hh
  have hz : (restrict G U).degree v = 0 := by omega
  rw [coinD_eq_false_of_degree_zero q (restrict G U) x y hz] at hc
  contradiction

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE RestrictionGeometry

-- BEGIN COMPLETE MODULE EdgeDeletion
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma restrict_sdiff_edges (U K : Finset (Fin n)) :
    (restrict G (U \ K)).edgeFinset =
      (restrict G U).edgeFinset.filter (fun e => ¬ ∃v∈e, v∈K) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      change (a∈U\K ∧ b∈U\K ∧ G.Adj a b) ↔
        (a∈U ∧ b∈U ∧ G.Adj a b) ∧ ¬ ∃v∈s(a,b), v∈K
      simp only [Finset.mem_sdiff, Sym2.mem_iff, exists_eq_or_imp]
      simp only [exists_eq_left]
      tauto

lemma edge_delete_count (U J : Finset (Fin n)) :
    (restrict G (U \ (J ∪ nbhd (restrict G U) J))).edgeFinset.card +
      eliminated (restrict G U) J = (restrict G U).edgeFinset.card := by
  classical
  rw [restrict_sdiff_edges]
  unfold eliminated
  have h := Finset.card_filter_add_card_filter_not (s := (restrict G U).edgeFinset)
      (fun e => ∃v∈e, v∈J ∪ nbhd (restrict G U) J)
  rw [Nat.add_comm]
  convert h using 2
  congr 1
  ext e
  simp only [Finset.mem_filter]

lemma restrict_edge_mono {U V : Finset (Fin n)} (h : U ⊆ V) :
    (restrict G U).edgeFinset ⊆ (restrict G V).edgeFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      exact ⟨h he.1, h he.2.1, he.2.2⟩

lemma eliminated_le_edges (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (J : Finset (Fin n)) : eliminated H J ≤ H.edgeFinset.card := by
  classical
  unfold eliminated
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he
  exact he.1

lemma zero_edges_V1 {U : Finset (Fin n)} (he : (restrict G U).edgeFinset.card = 0) :
    V1 G U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hvU := (Finset.mem_sdiff.mp hv).1
  have hn := (Finset.mem_sdiff.mp hv).2
  have hd : (restrict G U).degree v ≠ 0 := by
    intro hd
    exact hn (Finset.mem_filter.mpr ⟨hvU, hd⟩)
  obtain ⟨w, hw⟩ := ((restrict G U).degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hd)
  have hm : s(v,w) ∈ (restrict G U).edgeFinset := by
    exact SimpleGraph.mem_edgeFinset.mpr hw
  have hemp := Finset.card_eq_zero.mp he
  simp only [hemp, Finset.notMem_empty] at hm

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE EdgeDeletion

-- BEGIN COMPLETE MODULE StateInvariant
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

structure GoodState (I U : Finset (Fin n)) : Prop where
  independent : ∀v∈I, ∀w∈I, ¬G.Adj v w
  disjoint : Disjoint I U
  separated : ∀v∈I, ∀w∈U, ¬G.Adj v w
  dominated : ∀v, v∉U → v∈I ∨ ∃w∈I, G.Adj v w

omit [DecidableRel G.Adj] in
lemma good_initial : GoodState G ∅ Finset.univ := by
  constructor <;> simp

lemma good_remove {I U J : Finset (Fin n)} (h : GoodState G I U) (hJU : J ⊆ U)
    (hJ : ∀v∈J, ∀w∈J, ¬G.Adj v w) :
    GoodState G (I ∪ J) (U \ (J ∪ nbhd (restrict G U) J)) := by
  classical
  constructor
  · intro v hv w hw
    rcases Finset.mem_union.mp hv with hv | hv <;> rcases Finset.mem_union.mp hw with hw | hw
    · exact h.independent v hv w hw
    · exact h.separated v hv w (hJU hw)
    · exact fun ha => h.separated w hw v (hJU hv) ha.symm
    · exact hJ v hv w hw
  · apply Finset.disjoint_left.mpr
    intro v hv hu
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.disjoint_left.mp h.disjoint hv (Finset.mem_sdiff.mp hu).1
    · exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_left _ hv)
  · intro v hv w hw ha
    rcases Finset.mem_union.mp hv with hv | hv
    · exact h.separated v hv w (Finset.mem_sdiff.mp hw).1 ha
    · apply (Finset.mem_sdiff.mp hw).2
      apply Finset.mem_union_right
      simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hv, (Finset.mem_sdiff.mp hw).1, hJU hv, ha.symm⟩
  · intro v hv
    by_cases hu : v∈U
    · have hx : v∈J ∪ nbhd (restrict G U) J := by
        by_contra hx
        exact hv (Finset.mem_sdiff.mpr ⟨hu, hx⟩)
      rcases Finset.mem_union.mp hx with hj | hn
      · exact Or.inl (Finset.mem_union_right _ hj)
      · obtain ⟨w, hw, ha⟩ := (show ∃w∈J, (restrict G U).Adj v w from by
          simpa only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and] using hn)
        exact Or.inr ⟨w, Finset.mem_union_right _ hw, ha.2.2⟩
    · rcases h.dominated v hu with hi | ⟨w, hw, ha⟩
      · exact Or.inl (Finset.mem_union_left _ hi)
      · exact Or.inr ⟨w, Finset.mem_union_left _ hw, ha⟩

lemma good_zero {I U : Finset (Fin n)} (h : GoodState G I U) :
    GoodState G (I ∪ zeroSet G U) (V1 G U) := by
  have hz : zeroSet G U ⊆ U := Finset.filter_subset _ _
  have hh := good_remove G h hz (fun v hv w hw => zeroSet_independent G U v hv w (hz hw))
  simpa only [nbhd_zeroSet, Finset.union_empty, V1] using hh

omit [DecidableRel G.Adj] in
lemma good_empty_maximal {I : Finset (Fin n)} (h : GoodState G I ∅) :
    Maximal G.IsIndepSet (I : Set (Fin n)) := by
  constructor
  · intro v hv w hw hne
    exact h.independent v hv w hw
  · intro J hJ hIJ v hv
    rcases h.dominated v (Finset.notMem_empty v) with hi | ⟨w, hw, ha⟩
    · exact hi
    · exact False.elim (hJ hv (hIJ hw) ha.ne ha)

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE StateInvariant

-- BEGIN COMPLETE MODULE StepInvariant
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma good_step {q : ℕ} {s t : Finset (Fin n) × Finset (Fin n)}
    (hs : GoodState G s.1 s.2) (hstep : DStep G q s t) : GoodState G t.1 t.2 := by
  classical
  have hz := good_zero G hs
  change (∃i∈V1 G s.2, _ ∧ _ ∧ _) ∨ (_ ∧ ∃x y, _ ∧ _) at hstep
  rcases hstep with ⟨i, hi, _, _, rfl⟩ | ⟨_, x, y, _, rfl⟩
  · have hj : ({i} : Finset (Fin n)) ⊆ V1 G s.2 := Finset.singleton_subset_iff.mpr hi
    have hh := good_remove G hz hj (by
      intro v hv w hw
      simp only [Finset.mem_singleton] at hv hw
      subst v
      subst w
      exact G.loopless.irrefl i)
    rw [nbhd_singleton] at hh
    have he : (restrict G (V1 G s.2)).neighborFinset i = (restrict G s.2).neighborFinset i := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      rw [restrict_V1]
    rw [he] at hh
    exact hh
  · apply good_remove G hz (selectD_subset G q (V1 G s.2) x y)
    intro v hv w hw ha
    have hvU := selectD_subset G q (V1 G s.2) x y hv
    have hwU := selectD_subset G q (V1 G s.2) x y hw
    exact selectB_independent (restrict G (V1 G s.2)) _ v hv w hw ⟨hvU, hwU, ha⟩

lemma step_subset {q : ℕ} {s t : Finset (Fin n) × Finset (Fin n)}
    (hstep : DStep G q s t) : t.2 ⊆ s.2 := by
  change (∃i∈V1 G s.2, _ ∧ _ ∧ _) ∨ (_ ∧ ∃x y, _ ∧ _) at hstep
  rcases hstep with ⟨i, hi, hm, hd, rfl⟩ | ⟨hm, x, y, hm', rfl⟩
  all_goals exact Finset.Subset.trans Finset.sdiff_subset (V1_subset G s.2)

lemma run_good_before {q : ℕ} {s : ℕ → Finset (Fin n) × Finset (Fin n)}
    (hs : IsRun G q s) (k : ℕ) (hk : ∀j<k, (s j).2.Nonempty) :
    GoodState G (s k).1 (s k).2 := by
  induction k with
  | zero => simpa only [hs.1] using good_initial G
  | succ k ih =>
      exact good_step G (ih (fun j hj => hk j (by omega))) (hs.2 k (hk k (by omega)))

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE StepInvariant

-- BEGIN COMPLETE MODULE StepEdges
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma step_edge_mono {q : ℕ} {s t : Finset (Fin n) × Finset (Fin n)}
    (hstep : DStep G q s t) :
    (restrict G t.2).edgeFinset.card ≤ (restrict G s.2).edgeFinset.card :=
  Finset.card_le_card (restrict_edge_mono G (step_subset G hstep))

lemma degree_zero_outside {U : Finset (Fin n)} {v : Fin n} (hv : v∉U) :
    (restrict G U).degree v = 0 := by
  by_contra hh
  exact hv (degree_pos_mem G (Nat.pos_of_ne_zero hh))

lemma step_zero_edges {q : ℕ} {s t : Finset (Fin n) × Finset (Fin n)}
    (hstep : DStep G q s t) (he : (restrict G s.2).edgeFinset.card = 0) : t.2 = ∅ := by
  have hz := zero_edges_V1 G he
  change (∃i∈V1 G s.2, _ ∧ _ ∧ _) ∨ (_ ∧ ∃x y, _ ∧ _) at hstep
  rcases hstep with ⟨i, hi, _⟩ | ⟨_, x, y, _, rfl⟩
  · simp only [hz, Finset.notMem_empty] at hi
  · simp only [hz, Finset.empty_sdiff]

lemma sampled_edge_shrink (U J : Finset (Fin n))
    (h : (restrict G U).edgeFinset.card ≤ 18 * eliminated (restrict G U) J) :
    18 * (restrict G (U \ (J ∪ nbhd (restrict G U) J))).edgeFinset.card ≤
      17 * (restrict G U).edgeFinset.card := by
  have he := edge_delete_count G U J
  omega

lemma restrict_V1_edge_card (U : Finset (Fin n)) :
    (restrict G (V1 G U)).edgeFinset.card = (restrict G U).edgeFinset.card := by
  have he : (restrict G (V1 G U)).edgeFinset = (restrict G U).edgeFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset, restrict_V1]
  exact congrArg Finset.card he

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE StepEdges

-- BEGIN COMPLETE MODULE StepShrink
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma restrict_V1_degree (U : Finset (Fin n)) (i : Fin n) :
    (restrict G (V1 G U)).degree i = (restrict G U).degree i := by
  have he : (restrict G (V1 G U)).neighborFinset i = (restrict G U).neighborFinset i := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset, restrict_V1]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using congrArg Finset.card he

lemma step_case2_shrink {q : ℕ} (hq : q.Prime) (hnq : n≤q) (hn : 0<n)
    {s t : Finset (Fin n) × Finset (Fin n)} (hstep : DStep G q s t) (hc : ¬Case1 G s) :
    18 * (restrict G t.2).edgeFinset.card ≤ 17 * (restrict G s.2).edgeFinset.card := by
  change (∃i∈V1 G s.2, _ ∧ _ ∧ _) ∨ (_ ∧ ∃x y, _ ∧ _) at hstep
  rcases hstep with ⟨i, hi, _, hd, _⟩ | ⟨hall, x, y, hbest, rfl⟩
  · exact False.elim (hc ⟨i,hi,hd⟩)
  · have hsmall : ∀i, 16*(restrict G (V1 G s.2)).degree i<n := by
      intro i
      by_cases hi : i∈V1 G s.2
      · rw [restrict_V1_degree]
        exact hall i hi
      · rw [degree_zero_outside G hi]
        simpa using hn
    have hb := best_sample_bound hq hnq (restrict G (V1 G s.2)) hsmall x y hbest
    have he := sampled_edge_shrink G (V1 G s.2)
      (selectB (restrict G (V1 G s.2)) (coinD q (restrict G (V1 G s.2)) x y)) hb
    rw [restrict_V1_edge_card] at he
    exact he

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE StepShrink

-- BEGIN COMPLETE MODULE CaseOneDrop
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma singleton_neighbor_card (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i : Fin n) :
    ({i} ∪ H.neighborFinset i).card = H.degree i + 1 := by
  classical
  have hi : i ∉ H.neighborFinset i := by simp
  simp [Finset.singleton_union, Finset.card_insert_of_notMem hi, SimpleGraph.card_neighborFinset_eq_degree]

lemma case_one_drop (U : Finset (Fin n)) {i : Fin n} (hi : i∈V1 G U) :
    (V1 G U \ ({i} ∪ (restrict G U).neighborFinset i)).card +
      (restrict G U).degree i + 1 ≤ U.card := by
  have hs : {i} ∪ (restrict G U).neighborFinset i ⊆ V1 G U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · simpa only [Finset.mem_singleton.mp hv] using hi
    · exact mem_V1_of_adj G ((show (restrict G U).Adj i v from by simpa only [SimpleGraph.mem_neighborFinset] using hv).symm)
  have hh := Finset.card_sdiff_add_card_eq_card hs
  rw [singleton_neighbor_card] at hh
  have hc := Finset.card_le_card (V1_subset G U)
  omega

lemma case1_step_drop {q : ℕ} {s t : Finset (Fin n) × Finset (Fin n)}
    (hstep : DStep G q s t) (hc : Case1 G s) :
    n < 16 * (s.2.card - t.2.card) := by
  change (∃i∈V1 G s.2, _ ∧ _ ∧ _) ∨ (_ ∧ ∃x y, _ ∧ _) at hstep
  rcases hstep with ⟨i, hi, _, hd, rfl⟩ | ⟨hall, _⟩
  · have h := case_one_drop G s.2 hi
    dsimp only
    omega
  · obtain ⟨i, hi, hd⟩ := hc
    have := hall i hi
    omega

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE CaseOneDrop

-- BEGIN COMPLETE MODULE RunTermination
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma step_card_strict {q : ℕ} {s t : Finset (Fin n) × Finset (Fin n)}
    (hstep : DStep G q s t) (hne : s.2.Nonempty)
    (hshrink : ¬Case1 G s →
      18 * (restrict G t.2).edgeFinset.card ≤ 17 * (restrict G s.2).edgeFinset.card) :
    t.2.card < s.2.card := by
  have hsub := step_subset G hstep
  have hle := Finset.card_le_card hsub
  by_cases hc : Case1 G s
  · have hd := case1_step_drop G hstep hc
    omega
  · by_cases he : (restrict G s.2).edgeFinset.card = 0
    · have ht := step_zero_edges G hstep he
      simpa only [ht, Finset.card_empty] using Finset.card_pos.mpr hne
    · have hh := hshrink hc
      by_contra hn
      have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
      have hec : (restrict G t.2).edgeFinset.card = (restrict G s.2).edgeFinset.card := by rw [heq]
      omega

lemma first_empty_of_strict {s : ℕ → Finset (Fin n) × Finset (Fin n)}
    (hstrict : ∀k, (s k).2.Nonempty → (s (k+1)).2.card < (s k).2.card) :
    ∃k≤n, (s k).2 = ∅ ∧ ∀j<k, (s j).2.Nonempty := by
  classical
  have hex : ∃k≤n, (s k).2 = ∅ := by
    by_contra hh
    have hn : ∀k≤n, (s k).2.Nonempty := by
      intro k hk
      apply Finset.nonempty_iff_ne_empty.mpr
      exact fun he => hh ⟨k,hk,he⟩
    have hbound : ∀k≤n, (s k).2.card + k ≤ n := by
      intro k hk
      induction k with
      | zero => simpa using Finset.card_le_univ (s 0).2
      | succ k ih =>
          have hi := ih (by omega)
          have hd := hstrict k (hn k (by omega))
          omega
    have h1 := hbound n le_rfl
    have h2 := Finset.card_pos.mpr (hn n le_rfl)
    omega
  have he : ∃k, (s k).2 = ∅ := by obtain ⟨k,_,hk⟩ := hex; exact ⟨k,hk⟩
  refine ⟨Nat.find he, ?_, Nat.find_spec he, ?_⟩
  · obtain ⟨k,hk,hke⟩ := hex
    exact (Nat.find_min' he hke).trans hk
  · intro j hj
    exact Finset.nonempty_iff_ne_empty.mpr (Nat.find_min he hj)

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE RunTermination

-- BEGIN COMPLETE MODULE CaseOneCount
section

namespace LubyMIS.Derandomized.Proof
open Classical

lemma sum_drops (v : ℕ → ℕ) (k : ℕ) (hv : ∀j<k, v (j+1) ≤ v j) :
    (∑j∈Finset.range k, (v j - v (j+1))) + v k = v 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hi := ih (fun j hj => hv j (by omega))
      have hd := hv k (by omega)
      omega

lemma case_count_bound (n k : ℕ) (v : ℕ → ℕ) (C : ℕ → Prop) [DecidablePred C]
    (h0 : v 0 ≤ n) (hv : ∀j<k, v (j+1) ≤ v j)
    (hC : ∀j<k, C j → n < 16 * (v j - v (j+1))) :
    ((Finset.range k).filter C).card ≤ 15 := by
  have hd := sum_drops v k hv
  have hsum : ((Finset.range k).filter C).card * (n+1) ≤
      ∑j∈(Finset.range k).filter C, 16 * (v j-v (j+1)) := by
    rw [← Finset.sum_const_nat (s := (Finset.range k).filter C) (f := fun _ => n+1) (fun _ _ => rfl)]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hj,hc⟩ := Finset.mem_filter.mp hj
    exact Nat.succ_le_of_lt (hC j (Finset.mem_range.mp hj) hc)
  have hsub : (∑j∈(Finset.range k).filter C, 16 * (v j-v (j+1))) ≤
      ∑j∈Finset.range k, 16 * (v j-v (j+1)) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  simp only [← Finset.mul_sum] at hsum hsub
  have hh : ((Finset.range k).filter C).card * (n+1) ≤ 16*n := by omega
  by_contra hbad
  have hc : 16 ≤ ((Finset.range k).filter C).card := by omega
  have hm := Nat.mul_le_mul_right (n+1) hc
  omega

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
lemma run_case1_count {q : ℕ} {s : ℕ → Finset (Fin n) × Finset (Fin n)}
    (hs : IsRun G q s) (k : ℕ) (hk : ∀j<k, (s j).2.Nonempty) :
    ((Finset.range k).filter (fun j => Case1 G (s j))).card ≤ 15 := by
  apply case_count_bound n k (fun j => (s j).2.card)
  · rw [hs.1]
    simp
  · intro j hj
    exact Finset.card_le_card (step_subset G (hs.2 j (hk j hj)))
  · intro j hj hc
    exact case1_step_drop G (hs.2 j (hk j hj)) hc

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE CaseOneCount

-- BEGIN COMPLETE MODULE LogConstants
section

namespace LubyMIS.Derandomized.Proof

lemma log_ratio_pos : 0 < Real.log (18 / 17 : ℝ) := Real.log_pos (by norm_num)

lemma log_two_ratio : Real.log (18 / 17 : ℝ) ≤ Real.log 2 := by
  apply Real.log_le_log <;> norm_num

lemma log_ratio_twentyfive : 2 * Real.log 2 ≤ 25 * Real.log (18 / 17 : ℝ) := by
  have hnum : (2 : ℝ)^2 ≤ (18/17 : ℝ)^25 := by norm_num
  have hh := Real.log_le_log (by norm_num : 0 < (2:ℝ)^2) hnum
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

lemma logarithmic_round_comparison (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ)^2) / Real.log (18/17 : ℝ) ≤ 25 * Real.logb 2 (n : ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn'
  have htwo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  rw [Real.log_pow, Real.logb]
  apply (div_le_iff₀ log_ratio_pos).mpr
  rw [show 25 * (Real.log (n:ℝ) / Real.log 2) * Real.log (18/17 : ℝ) =
      (25 * Real.log (18/17 : ℝ) * Real.log (n:ℝ)) / Real.log 2 by ring]
  apply (le_div_iff₀ htwo).mpr
  convert mul_le_mul_of_nonneg_right log_ratio_twentyfive hln using 1
  ring

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE LogConstants

-- BEGIN COMPLETE MODULE EdgeBudget
section

namespace LubyMIS.Derandomized.Proof

noncomputable def edgeBudget (e : ℕ) : ℝ :=
  if e = 0 then 0 else Real.log e / Real.log (18/17 : ℝ) + 1

lemma edgeBudget_nonneg (e : ℕ) : 0 ≤ edgeBudget e := by
  unfold edgeBudget
  split_ifs with he
  · exact le_rfl
  · have he' : (1:ℝ) ≤ e := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    positivity

lemma edgeBudget_mono {a b : ℕ} (h : a ≤ b) : edgeBudget a ≤ edgeBudget b := by
  by_cases ha : a=0
  · simpa [ha, edgeBudget] using edgeBudget_nonneg b
  · have hb : b≠0 := by omega
    simp only [edgeBudget, if_neg ha, if_neg hb]
    have hl := Real.log_le_log (show (0:ℝ)<a by exact_mod_cast Nat.pos_of_ne_zero ha)
      (show (a:ℝ)≤b by exact_mod_cast h)
    exact add_le_add ((div_le_div_iff_of_pos_right log_ratio_pos).mpr hl) le_rfl

lemma edgeBudget_contract {a b : ℕ} (ha : 0<a) (h : 18*b ≤ 17*a) :
    1 + edgeBudget b ≤ edgeBudget a := by
  have ha0 := Nat.ne_of_gt ha
  have har : (0:ℝ)<a := by exact_mod_cast ha
  have ha1 : (1:ℝ)≤a := by exact_mod_cast ha
  by_cases hb : b=0
  · simp only [hb, edgeBudget, if_neg ha0, ↓reduceIte]
    have hh : 0 ≤ Real.log (a:ℝ) / Real.log (18/17:ℝ) :=
      div_nonneg (Real.log_nonneg ha1) (le_of_lt log_ratio_pos)
    linarith
  · have hbr : (0:ℝ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hreal : (b:ℝ)*(18/17) ≤ a := by
      have hh : 18*(b:ℝ) ≤17*a := by exact_mod_cast h
      linarith
    have hl := Real.log_le_log (mul_pos hbr (by norm_num : (0:ℝ)<18/17)) hreal
    rw [Real.log_mul (ne_of_gt hbr) (by norm_num)] at hl
    simp only [edgeBudget, if_neg hb, if_neg ha0]
    have hd := (div_le_div_iff_of_pos_right log_ratio_pos).mpr hl
    rw [add_div, div_self (ne_of_gt log_ratio_pos)] at hd
    linarith

lemma edgeBudget_initial (n e : ℕ) (hn : 1≤n) (he : 2*e ≤ n^2) :
    edgeBudget e ≤ Real.log ((n:ℝ)^2) / Real.log (18/17:ℝ) := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  by_cases hz : e=0
  · simp only [hz, edgeBudget, ↓reduceIte]
    apply div_nonneg _ (le_of_lt log_ratio_pos)
    apply Real.log_nonneg
    nlinarith
  · have her : (0:ℝ)<e := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hreal : (2:ℝ)*e ≤ (n:ℝ)^2 := by exact_mod_cast he
    have hl := Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) her) hreal
    rw [Real.log_mul (by norm_num) (ne_of_gt her)] at hl
    unfold edgeBudget
    rw [if_neg hz]
    apply (le_div_iff₀ log_ratio_pos).mpr
    have hr := log_two_ratio
    have heq : (Real.log (e:ℝ) / Real.log (18/17:ℝ) + 1) * Real.log (18/17:ℝ) =
        Real.log (e:ℝ) + Real.log (18/17:ℝ) := by field_simp
    rw [heq]
    linarith

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE EdgeBudget

-- BEGIN COMPLETE MODULE RunBudget
section

namespace LubyMIS.Derandomized.Proof
open Classical

lemma counted_budget (e : ℕ → ℕ) (C : ℕ → Prop) [DecidablePred C] (k : ℕ)
    (hm : ∀j<k, e (j+1) ≤ e j)
    (hs : ∀j<k, ¬C j → 18*e (j+1) ≤ 17*e j) :
    ((((Finset.range k).filter (fun j => ¬C j ∧ e j≠0)).card : ℕ) : ℝ) +
      edgeBudget (e k) ≤ edgeBudget (e 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hi := ih (fun j hj => hm j (by omega)) (fun j hj => hs j (by omega))
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hc : C k
      · simp only [hc, not_true_eq_false, false_and, if_false]
        have he := edgeBudget_mono (hm k (by omega))
        linarith
      · by_cases he : e k=0
        · simp only [he, ne_eq, not_true_eq_false, and_false, if_false]
          have hb := edgeBudget_mono (hm k (by omega))
          linarith
        · simp only [hc, not_false_eq_true, he, ne_eq, and_self, if_true]
          rw [Finset.card_insert_of_notMem (by simp), Nat.cast_add, Nat.cast_one]
          have hb := edgeBudget_contract (Nat.pos_of_ne_zero he) (hs k (by omega) hc)
          linarith

lemma round_partition (C : ℕ → Prop) [DecidablePred C] (e : ℕ → ℕ) (k : ℕ) :
    k = ((Finset.range k).filter C).card +
      ((Finset.range k).filter (fun j => ¬C j ∧ e j≠0)).card +
      ((Finset.range k).filter (fun j => ¬C j ∧ e j=0)).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range k) C
  have h' := Finset.card_filter_add_card_filter_not
    (s := (Finset.range k).filter (fun j => ¬C j)) (fun j => e j=0)
  simp only [Finset.filter_filter, Finset.card_range] at h h'
  have heq : ((Finset.range k).filter (fun j => ¬C j ∧ ¬e j=0)) =
      ((Finset.range k).filter (fun j => ¬C j ∧ e j≠0)) := by
    ext j
    simp only [Finset.mem_filter, ne_eq]
  rw [heq] at h'
  omega

lemma zero_round_count (C : ℕ → Prop) [DecidablePred C] (e : ℕ → ℕ) (k : ℕ)
    (hz : ∀j<k, e j=0 → j+1=k) :
    ((Finset.range k).filter (fun j => ¬C j ∧ e j=0)).card ≤ 1 := by
  apply (Finset.card_le_card (show (Finset.range k).filter (fun j => ¬C j ∧ e j=0) ⊆ {k-1} from ?_)).trans
    (by simp)
  intro j hj
  obtain ⟨hj,_,he⟩ := Finset.mem_filter.mp hj
  have hh := hz j (Finset.mem_range.mp hj) he
  simp only [Finset.mem_singleton]
  omega

lemma total_round_bound (C : ℕ → Prop) [DecidablePred C] (e : ℕ → ℕ) (k : ℕ)
    (hc : ((Finset.range k).filter C).card ≤ 15)
    (hz : ∀j<k, e j=0 → j+1=k)
    (hm : ∀j<k, e (j+1) ≤ e j)
    (hs : ∀j<k, ¬C j → 18*e (j+1) ≤ 17*e j) :
    (k:ℝ) ≤ edgeBudget (e 0) + 16 := by
  have h1 := counted_budget e C k hm hs
  have h2 := edgeBudget_nonneg (e k)
  have h3 := zero_round_count C e k hz
  have h4 := round_partition C e k
  have hc' : (((Finset.range k).filter C).card:ℝ) ≤15 := by exact_mod_cast hc
  have h3' : (((Finset.range k).filter (fun j => ¬C j ∧ e j=0)).card:ℝ) ≤1 := by exact_mod_cast h3
  have h4' : (k:ℝ) = ((Finset.range k).filter C).card +
      ((Finset.range k).filter (fun j => ¬C j ∧ e j≠0)).card +
      ((Finset.range k).filter (fun j => ¬C j ∧ e j=0)).card := by exact_mod_cast h4
  linarith

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE RunBudget

-- BEGIN COMPLETE MODULE RunRoundBound
section

namespace LubyMIS.Derandomized.Proof
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma twice_edges_le_square (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    2*H.edgeFinset.card ≤ n^2 := by
  rw [← H.sum_degrees_eq_twice_card_edges]
  calc
    (∑v, H.degree v) ≤ ∑_v : Fin n, n := by
      apply Finset.sum_le_sum
      intro v hv
      have hh := H.degree_lt_card_verts v
      simp only [Fintype.card_fin] at hh
      omega
    _ = n^2 := by simp [pow_two]

lemma run_round_bound {q : ℕ} (hq : q.Prime) (hnq : n≤q) (hq2 : q≤2*n)
    {s : ℕ → Finset (Fin n) × Finset (Fin n)} (hs : IsRun G q s) :
    ∃k, (s k).2 = ∅ ∧ (∀j<k, (s j).2.Nonempty) ∧
      (k:ℝ) ≤ Real.log ((n:ℝ)^2) / Real.log (18/17:ℝ) + 16 ∧
      Maximal G.IsIndepSet ((s k).1 : Set (Fin n)) := by
  have hn : 0<n := by have hq' := hq.two_le; omega
  have shrink (j : ℕ) (hj : (s j).2.Nonempty) :
      ¬Case1 G (s j) → 18*(restrict G (s (j+1)).2).edgeFinset.card ≤
        17*(restrict G (s j).2).edgeFinset.card :=
    step_case2_shrink G hq hnq hn (hs.2 j hj)
  obtain ⟨k, _, he, hk⟩ := first_empty_of_strict (fun j hj =>
    step_card_strict G (hs.2 j hj) hj (shrink j hj))
  refine ⟨k, he, hk, ?_, good_empty_maximal G ?_⟩
  · have hc := run_case1_count G hs k hk
    have hz : ∀j<k, (restrict G (s j).2).edgeFinset.card=0 → j+1=k := by
      intro j hj hz
      have hnext := step_zero_edges G (hs.2 j (hk j hj)) hz
      by_contra hh
      have hlt : j+1<k := by omega
      have hne := hk (j+1) hlt
      exact hne.ne_empty hnext
    have hb := total_round_bound (fun j => Case1 G (s j))
      (fun j => (restrict G (s j).2).edgeFinset.card) k hc hz
      (fun j hj => step_edge_mono G (hs.2 j (hk j hj)))
      (fun j hj => shrink j (hk j hj))
    have hi := edgeBudget_initial n (restrict G (s 0).2).edgeFinset.card hn
      (twice_edges_le_square (restrict G (s 0).2))
    linarith
  · simpa only [he] using run_good_before G hs k hk

end LubyMIS.Derandomized.Proof
end
-- END COMPLETE MODULE RunRoundBound

-- BEGIN COMPLETE MODULE LubyRoot
section

namespace LubyMIS.Derandomized

/-- Algorithm D (Luby 1986, §4.4, p. 1047, with §3.1, p. 1039): for every graph `G` on `n` vertices
and every prime `n ≤ q ≤ 2n`, every run of Algorithm D stops after `k` executions of the loop body
with `k ≤ log(n²)/log(18/17) + 16 ≤ 25·log₂ n + 16`, and the set `I` it outputs is a maximal
independent set of `G`. -/
theorem algorithmD_rounds (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (s : ℕ → Finset (Fin n) × Finset (Fin n))
    (hs : IsRun G q s) :
    ∃ k : ℕ, (s k).2 = ∅ ∧ (∀ j < k, (s j).2.Nonempty) ∧
      (k : ℝ) ≤ Real.log ((n : ℝ) ^ 2) / Real.log (18 / 17) + 16 ∧
      (k : ℝ) ≤ 25 * Real.logb 2 (n : ℝ) + 16 ∧
      Maximal G.IsIndepSet ((s k).1 : Set (Fin n)) := by
  obtain ⟨k, he, hk, hb, hm⟩ := Proof.run_round_bound G hq hnq hq2 hs
  have hn : 1 ≤ n := by have hq' := hq.two_le; omega
  refine ⟨k, he, hk, hb, ?_, hm⟩
  have hl := Proof.logarithmic_round_comparison n hn
  linarith

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (s : ℕ → Finset (Fin n) × Finset (Fin n))
    (hs : IsRun G q s) :
    ∃ k : ℕ, (s k).2 = ∅ ∧ (∀ j < k, (s j).2.Nonempty) ∧
      (k : ℝ) ≤ Real.log ((n : ℝ) ^ 2) / Real.log (18 / 17) + 16 ∧
      (k : ℝ) ≤ 25 * Real.logb 2 (n : ℝ) + 16 ∧
      Maximal G.IsIndepSet ((s k).1 : Set (Fin n)) := by
  exact LubyMIS.Derandomized.algorithmD_rounds n G q hq hnq hq2 s hs
end
-- END COMPLETE MODULE LubyRoot
