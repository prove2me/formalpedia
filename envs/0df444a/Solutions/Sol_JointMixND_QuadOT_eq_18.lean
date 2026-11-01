-- Prove2me | solution 1 for JointMixND.QuadOT.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:03:09.988429+00:00
-- url     : https://prove2.me/submissions/5d649e02-148f-4319-ad57-8d26429cbe74

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JMNDT5Aux

open MeasureTheory ProbabilityTheory JointMixND.QuadOT

/-! ### Second moments of a coupling -/

noncomputable def mom {n : ℕ} (Q : Measure (Fin n → ℝ)) (i j : Fin n) : ℝ :=
  ∫ x, x i * x j ∂Q

lemma coord_memLp {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F) {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (i : Fin n) : MemLp (fun x : Fin n → ℝ => x i) 2 Q := by
  have hm : AEMeasurable (fun x : Fin n → ℝ => x i) Q := (measurable_pi_apply i).aemeasurable
  have h := hQ.2 i
  rw [← h] at hF2
  exact (memLp_map_measure_iff aestronglyMeasurable_id hm).1 hF2

lemma coord_mean {n : ℕ} {F : Measure ℝ} (hmean : ∫ t, t ∂F = 0) {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (i : Fin n) : ∫ x, x i ∂Q = 0 := by
  have := integral_map (μ := Q) (measurable_pi_apply i).aemeasurable (f := fun t : ℝ => t)
    aestronglyMeasurable_id
  rw [hQ.2 i] at this
  rw [← this]; exact hmean

lemma integrable_mul_coord {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i * x j) Q :=
  (coord_memLp hF2 hQ i).integrable_mul (coord_memLp hF2 hQ j)

lemma mom_diag {n : ℕ} {F : Measure ℝ} (hmean : ∫ t, t ∂F = 0)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i : Fin n) :
    mom Q i i = variance id F := by
  rw [variance_of_integral_eq_zero aemeasurable_id (by simpa using hmean)]
  have := integral_map (μ := Q) (measurable_pi_apply i).aemeasurable (f := fun t : ℝ => t ^ 2)
    (by fun_prop)
  rw [hQ.2 i] at this
  simp only [id, this, mom]
  congr 1; ext x; ring

lemma sq_sum_expand {n : ℕ} (K : Finset (Fin n)) (x : Fin n → ℝ) :
    (∑ i ∈ K, x i) ^ 2 = ∑ i ∈ K, ∑ j ∈ K, x i * x j := by
  rw [sq, Finset.sum_mul_sum]

lemma integrable_sq_sum {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    Integrable (fun x : Fin n → ℝ => (∑ i ∈ K, x i) ^ 2) Q := by
  simp_rw [sq_sum_expand]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_mul_coord hF2 hQ i j))

lemma sq_sum_eq {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    ∫ x, (∑ i ∈ K, x i) ^ 2 ∂Q = ∑ i ∈ K, ∑ j ∈ K, mom Q i j := by
  simp_rw [sq_sum_expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_mul_coord hF2 hQ i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => integrable_mul_coord hF2 hQ i j)]
  rfl

lemma cov_eq_mom {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F) (hmean : ∫ t, t ∂F = 0)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i j : Fin n) :
    covariance (fun x => x i) (fun x => x j) Q = mom Q i j := by
  haveI := hQ.1
  rw [covariance_eq_sub (coord_memLp hF2 hQ i) (coord_memLp hF2 hQ j),
    coord_mean hmean hQ i, coord_mean hmean hQ j]
  simp [mom]

/-! ### Symmetrization -/

lemma measurable_perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Measurable (fun x : Fin n → ℝ => x ∘ π) := by
  fun_prop

lemma sym_coupling {n : ℕ} {F : Measure ℝ} {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) :
    IsCoupling F (symmetrize Q) := by
  haveI := hQ.1
  have hfac : ((Nat.factorial n : ENNReal))⁻¹ * (Nat.factorial n : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.factorial_pos n).ne') (ENNReal.natCast_ne_top _)
  refine ⟨⟨?_⟩, fun i => ?_⟩
  · simp only [symmetrize, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    have : ∀ π : Equiv.Perm (Fin n), (Q.map (fun x => x ∘ π)) Set.univ = 1 := by
      intro π
      haveI := Measure.isProbabilityMeasure_map (μ := Q) (measurable_perm π).aemeasurable
      exact measure_univ
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact hfac
  · ext s hs
    rw [Measure.map_apply (measurable_pi_apply i) hs]
    simp only [symmetrize, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    have : ∀ π : Equiv.Perm (Fin n),
        (Q.map (fun x => x ∘ π)) ((fun x : Fin n → ℝ => x i) ⁻¹' s) = F s := by
      intro π
      rw [Measure.map_apply (measurable_perm π) (measurable_pi_apply i hs)]
      rw [← hQ.2 (π i), Measure.map_apply (measurable_pi_apply (π i)) hs]
      rfl
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, hfac, one_mul]

lemma sym_integral {n : ℕ} (Q : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (hint : ∀ π : Equiv.Perm (Fin n), Integrable (fun x => g (x ∘ π)) Q) :
    ∫ x, g x ∂(symmetrize Q) =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), ∫ x, g (x ∘ π) ∂Q := by
  unfold symmetrize
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl (fun π _ => ?_)
    exact integral_map (measurable_perm π).aemeasurable hg.aestronglyMeasurable
  · intro π _
    exact (integrable_map_measure hg.aestronglyMeasurable (measurable_perm π).aemeasurable).2
      (hint π)

lemma sym_mom {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i j : Fin n) :
    mom (symmetrize Q) i j =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), mom Q (π i) (π j) := by
  unfold mom
  rw [sym_integral Q (fun x => x i * x j) (by fun_prop)
    (fun π => integrable_mul_coord hF2 hQ (π i) (π j))]
  rfl

lemma exists_perm_pair {n : ℕ} (i j i' j' : Fin n) (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ σ : Equiv.Perm (Fin n), σ i' = i ∧ σ j' = j := by
  set τ := Equiv.swap i' i
  have hτ : τ i' = i := Equiv.swap_apply_left _ _
  have hτj : τ j' ≠ i := by
    intro h; apply hij'; rw [← hτ] at h; exact (τ.injective h).symm
  refine ⟨Equiv.swap (τ j') j * τ, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hτ]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτj) hij
  · rw [Equiv.Perm.mul_apply]; exact Equiv.swap_apply_left _ _

lemma sym_mom_eq {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i j i' j' : Fin n) (hij : i ≠ j)
    (hij' : i' ≠ j') : mom (symmetrize Q) i j = mom (symmetrize Q) i' j' := by
  obtain ⟨σ, h1, h2⟩ := exists_perm_pair i j i' j' hij hij'
  rw [sym_mom hF2 hQ, sym_mom hF2 hQ, ← h1, ← h2]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ) (fun π : Equiv.Perm (Fin n) => mom Q (π i') (π j'))

lemma sym_sq_sum {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    ∫ x, (∑ i ∈ K, x i) ^ 2 ∂(symmetrize Q) =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        ∫ x, (∑ i ∈ K.map π.toEmbedding, x i) ^ 2 ∂Q := by
  rw [sq_sum_eq hF2 (sym_coupling hQ)]
  simp_rw [sq_sum_eq hF2 hQ, sym_mom hF2 hQ, Finset.sum_map, Equiv.coe_toEmbedding]
  simp_rw [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

/-! ### Algebra -/

lemma sum_const_offdiag {n : ℕ} (m : Fin n → Fin n → ℝ) (s c : ℝ) (hd : ∀ i, m i i = s)
    (ho : ∀ i j, i ≠ j → m i j = c) (K : Finset (Fin n)) :
    ∑ i ∈ K, ∑ j ∈ K, m i j = (K.card : ℝ) * s + (K.card : ℝ) * ((K.card : ℝ) - 1) * c := by
  have : ∀ i ∈ K, ∑ j ∈ K, m i j = s + ((K.card : ℝ) - 1) * c := by
    intro i hi
    rw [← Finset.add_sum_erase K _ hi, hd i]
    rw [Finset.sum_congr rfl (fun j hj => ho i j (Finset.ne_of_mem_erase hj).symm)]
    rw [Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul,
      Nat.cast_sub (Finset.card_pos.2 ⟨i, hi⟩), Nat.cast_one]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  ring

noncomputable def vk (F : Measure ℝ) (n k : ℕ) : ℝ :=
  variance id F * ((k : ℝ) * ((n : ℝ) - (k : ℝ))) / ((n : ℝ) - 1)

lemma lower_bound {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q)
    (K : Finset (Fin n)) :
    vk F n K.card ≤ ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        ∫ x, (∑ i ∈ K.map π.toEmbedding, x i) ^ 2 ∂Q := by
  rw [← sym_sq_sum hF2 hQ K]
  have hS := sym_coupling hQ
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set c := mom (symmetrize Q) i0 i1
  have ho : ∀ i j, i ≠ j → mom (symmetrize Q) i j = c :=
    fun i j hij => sym_mom_eq hF2 hQ i j i0 i1 hij h01
  have hd := mom_diag hmean hS
  have hnn : 0 ≤ ∫ x, (∑ i ∈ (Finset.univ : Finset (Fin n)), x i) ^ 2 ∂(symmetrize Q) :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [sq_sum_eq hF2 hS, sum_const_offdiag _ _ c hd ho, Finset.card_univ, Fintype.card_fin] at hnn
  rw [sq_sum_eq hF2 hS, sum_const_offdiag _ _ c hd ho]
  have hs : 0 ≤ variance id F := variance_nonneg _ _
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hc0 : 0 ≤ (n : ℝ) * (variance id F + ((n : ℝ) - 1) * c) := by linarith
  have hc : 0 ≤ variance id F + ((n : ℝ) - 1) * c := (mul_nonneg_iff_of_pos_left hnpos).1 hc0
  have hk : 0 ≤ (K.card : ℝ) * ((K.card : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos K.card with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ K.card := by exact_mod_cast h
      exact mul_nonneg (by positivity) (by linarith)
  unfold vk
  rw [div_le_iff₀ hn1]
  nlinarith [mul_nonneg hk hc]

lemma avg_le {n : ℕ} (a : Equiv.Perm (Fin n) → ℝ) (M : ℝ) (h : ∀ π, a π ≤ M) :
    ((Nat.factorial n : ℝ))⁻¹ * ∑ π, a π ≤ M := by
  have hpos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rw [inv_mul_le_iff₀ hpos]
  have := Finset.sum_le_card_nsmul Finset.univ a M (fun π _ => h π)
  simpa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] using this

lemma le_maxCost {n : ℕ} (P : Measure (Fin n → ℝ)) (L : Finset (Fin n)) :
    ∫ x, (∑ i ∈ L, x i) ^ 2 ∂P ≤ maxCost P := by
  unfold maxCost
  exact Finset.le_sup' (fun K : Finset (Fin n) => ∫ x, (∑ i ∈ K, x i) ^ 2 ∂P) (Finset.mem_univ L)

lemma le_maxCostCard {n : ℕ} (k : ℕ) (P : Measure (Fin n → ℝ)) (L : Finset (Fin n))
    (hL : L.card = k) : ∫ x, (∑ i ∈ L, x i) ^ 2 ∂P ≤ maxCostCard k P := by
  unfold maxCostCard
  have hb : BddAbove (Set.range
      (fun K : {K : Finset (Fin n) // K.card = k} => ∫ x, (∑ i ∈ K.1, x i) ^ 2 ∂P)) :=
    (Set.finite_range _).bddAbove
  exact le_ciSup hb ⟨L, hL⟩

lemma lb12 {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q)
    (K : Finset (Fin n)) : vk F n K.card ≤ maxCost Q :=
  (lower_bound hn hF2 hmean hQ K).trans (avg_le _ _ (fun π => le_maxCost Q _))

lemma exists_card {n k : ℕ} (hk : k ≤ n) : ∃ K : Finset (Fin n), K.card = k := by
  obtain ⟨K, -, hK⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := k) (by simpa using hk)
  exact ⟨K, hK⟩

lemma lb13 {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q)
    (k : ℕ) (hk : k ≤ n) : vk F n k ≤ maxCostCard k Q := by
  obtain ⟨K, hK⟩ := exists_card hk
  rw [← hK]
  exact (lower_bound hn hF2 hmean hQ K).trans (avg_le _ _ (fun π =>
    le_maxCostCard _ Q _ (by rw [Finset.card_map])))

lemma pin {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {P : Measure (Fin n → ℝ)} (hP : IsCoupling F P) (k : ℕ)
    (hup : ∀ L : Finset (Fin n), L.card = k → ∫ x, (∑ i ∈ L, x i) ^ 2 ∂P ≤ vk F n k)
    (L : Finset (Fin n)) (hL : L.card = k) : ∫ x, (∑ i ∈ L, x i) ^ 2 ∂P = vk F n k := by
  refine le_antisymm (hup L hL) ?_
  have hlb := lower_bound hn hF2 hmean hP L
  rw [hL] at hlb
  set a : Equiv.Perm (Fin n) → ℝ := fun π => ∫ x, (∑ i ∈ L.map π.toEmbedding, x i) ^ 2 ∂P
    with ha_def
  have ha : ∀ π, a π ≤ vk F n k := fun π => hup _ (by rw [Finset.card_map, hL])
  have h1 : a 1 = ∫ x, (∑ i ∈ L, x i) ^ 2 ∂P := by
    have hm : Finset.map (Equiv.toEmbedding (1 : Equiv.Perm (Fin n))) L = L := by
      ext x; simp [Equiv.Perm.one_def]
    simp only [ha_def, hm]
  have hpos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rw [le_inv_mul_iff₀ hpos] at hlb
  have hsplit := Finset.add_sum_erase Finset.univ a (Finset.mem_univ 1)
  have hrest := Finset.sum_le_card_nsmul (Finset.univ.erase 1) a (vk F n k) (fun π _ => ha π)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (Nat.factorial_pos n), Nat.cast_one] at hrest
  rw [← h1]
  linarith

/-! ### Combinatorics: constant `k`-subset sums force constant off-diagonal entries -/

lemma comb {n k : ℕ} (hk2 : 2 ≤ k) (hkn : k + 2 ≤ n ∨ k = 2) (m : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, m i j = m j i) (s v : ℝ) (hd : ∀ i, m i i = s)
    (hT : ∀ L : Finset (Fin n), L.card = k → ∑ i ∈ L, ∑ j ∈ L, m i j = v) :
    ∀ i j i' j', i ≠ j → i' ≠ j' → m i j = m i' j' := by
  rcases hkn with hkn | hk
  · have Tins : ∀ (A : Finset (Fin n)) i, i ∉ A →
        ∑ x ∈ insert i A, ∑ y ∈ insert i A, m x y =
          s + 2 * ∑ a ∈ A, m i a + ∑ x ∈ A, ∑ y ∈ A, m x y := by
      intro A i hi
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hd]
      simp_rw [Finset.sum_insert hi]
      rw [Finset.sum_add_distrib]
      have : ∑ x ∈ A, m x i = ∑ a ∈ A, m i a := Finset.sum_congr rfl (fun x _ => hsym x i)
      rw [this]; ring
    have step1 : ∀ (A : Finset (Fin n)) i j, A.card + 1 = k → i ∉ A → j ∉ A →
        ∑ a ∈ A, m i a = ∑ a ∈ A, m j a := by
      intro A i j hA hi hj
      have h1 := hT (insert i A) (by rw [Finset.card_insert_of_notMem hi, hA])
      have h2 := hT (insert j A) (by rw [Finset.card_insert_of_notMem hj, hA])
      rw [Tins A i hi] at h1; rw [Tins A j hj] at h2; linarith
    have step2 : ∀ i j a a', i ≠ j → a ≠ a' → a ≠ i → a ≠ j → a' ≠ i → a' ≠ j →
        m i a - m j a = m i a' - m j a' := by
      intro i j a a' hij haa' hai haj ha'i ha'j
      set S := (((Finset.univ.erase i).erase j).erase a).erase a' with hSdef
      have hS : S.card = n - 4 := by
        rw [hSdef, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
          Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
        · omega
        all_goals simp [Ne.symm hij, hai, haj, ha'i, ha'j, Ne.symm haa']
      obtain ⟨B, hBS, hB⟩ := Finset.exists_subset_card_eq (s := S) (n := k - 2)
        (by rw [hS]; omega)
      have hmem : ∀ b ∈ B, b ≠ i ∧ b ≠ j ∧ b ≠ a ∧ b ≠ a' := by
        intro b hb
        have := hBS hb
        simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true] at this
        exact ⟨this.2.2.2, this.2.2.1, this.2.1, this.1⟩
      have haB : a ∉ B := fun h => (hmem a h).2.2.1 rfl
      have ha'B : a' ∉ B := fun h => (hmem a' h).2.2.2 rfl
      have hiB : i ∉ B := fun h => (hmem i h).1 rfl
      have hjB : j ∉ B := fun h => (hmem j h).2.1 rfl
      have e1 := step1 (insert a B) i j (by rw [Finset.card_insert_of_notMem haB, hB]; omega)
        (by simp [Finset.mem_insert, Ne.symm hai, hiB]) (by simp [Finset.mem_insert, Ne.symm haj, hjB])
      have e2 := step1 (insert a' B) i j (by rw [Finset.card_insert_of_notMem ha'B, hB]; omega)
        (by simp [Finset.mem_insert, Ne.symm ha'i, hiB])
        (by simp [Finset.mem_insert, Ne.symm ha'j, hjB])
      rw [Finset.sum_insert haB, Finset.sum_insert haB] at e1
      rw [Finset.sum_insert ha'B, Finset.sum_insert ha'B] at e2
      linarith
    have col : ∀ i j a, i ≠ a → j ≠ a → m i a = m j a := by
      intro i j a hia hja
      by_cases hij : i = j
      · rw [hij]
      set S := ((Finset.univ.erase i).erase j).erase a with hSdef
      have hS : S.card = n - 3 := by
        rw [hSdef, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
          Finset.card_univ, Fintype.card_fin]
        · omega
        all_goals simp [Ne.symm hij, Ne.symm hia, Ne.symm hja]
      obtain ⟨B, hBS, hB⟩ := Finset.exists_subset_card_eq (s := S) (n := k - 2)
        (by rw [hS]; omega)
      have hmem : ∀ b ∈ B, b ≠ i ∧ b ≠ j ∧ b ≠ a := by
        intro b hb
        have := hBS hb
        simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true] at this
        exact ⟨this.2.2, this.2.1, this.1⟩
      have haB : a ∉ B := fun h => (hmem a h).2.2 rfl
      have hiB : i ∉ B := fun h => (hmem i h).1 rfl
      have hjB : j ∉ B := fun h => (hmem j h).2.1 rfl
      have e := step1 (insert a B) i j (by rw [Finset.card_insert_of_notMem haB, hB]; omega)
        (by simp [Finset.mem_insert, hia, hiB]) (by simp [Finset.mem_insert, hja, hjB])
      rw [Finset.sum_insert haB, Finset.sum_insert haB] at e
      have hB' : ∑ b ∈ B, m i b - ∑ b ∈ B, m j b = (B.card : ℝ) * (m i a - m j a) := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl (fun b hb => (step2 i j a b hij (hmem b hb).2.2.symm
          (Ne.symm hia) (Ne.symm hja) (hmem b hb).1 (hmem b hb).2.1).symm)]
        rw [Finset.sum_const, nsmul_eq_mul]
      have h0 : ((B.card : ℝ) + 1) * (m i a - m j a) = 0 := by linarith
      have hc : ((B.card : ℝ) + 1) ≠ 0 := by positivity
      have := (mul_eq_zero.1 h0).resolve_left hc
      linarith
    intro i j i' j' hij hij'
    by_cases h : i' = j
    · rw [h] at hij' ⊢
      by_cases h2 : j' = i
      · rw [h2]; exact hsym i j
      · rw [hsym i j, col j j' i (Ne.symm hij) h2, hsym j' i, col i j j' (Ne.symm h2) hij']
    · rw [col i i' j hij h, hsym i' j, col j j' i' (Ne.symm h) (Ne.symm hij')]
      exact hsym j' i'
  · subst hk
    have h2 : ∀ i j, i ≠ j → m i j = (v - 2 * s) / 2 := by
      intro i j hij
      have := hT {i, j} (Finset.card_pair hij)
      simp_rw [Finset.sum_pair hij] at this
      rw [hd, hd, hsym j i] at this
      linarith
    intro i j i' j' hij hij'
    rw [h2 i j hij, h2 i' j' hij']

/-! ### Uniqueness of the covariance structure -/

lemma uniq {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {P : Measure (Fin n → ℝ)} (hP : IsCoupling F P) (k : ℕ)
    (hk2 : 2 ≤ k) (hkn : k + 2 ≤ n ∨ k = 2) (hkn' : k ≤ n)
    (hup : ∀ L : Finset (Fin n), L.card = k → ∫ x, (∑ i ∈ L, x i) ^ 2 ∂P ≤ vk F n k) :
    HasCorrPstar F P ∧ IsJointMix P ∧ IsNCD P := by
  have hT : ∀ L : Finset (Fin n), L.card = k → ∑ i ∈ L, ∑ j ∈ L, mom P i j = vk F n k :=
    fun L hL => by rw [← sq_sum_eq hF2 hP]; exact pin hn hF2 hmean hP k hup L hL
  have hsym : ∀ i j, mom P i j = mom P j i := fun i j => by
    unfold mom; congr 1; ext x; ring
  have hd := mom_diag hmean hP
  have hall := comb hk2 hkn (mom P) hsym _ _ hd hT
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set c := mom P i0 i1
  have ho : ∀ i j, i ≠ j → mom P i j = c := fun i j hij => hall i j i0 i1 hij h01
  obtain ⟨K, hK⟩ := exists_card hkn'
  have hv := hT K hK
  rw [sum_const_offdiag _ _ c hd ho, hK] at hv
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hc : c = -(variance id F) / ((n : ℝ) - 1) := by
    unfold vk at hv
    have hv' : ((k : ℝ) * variance id F + (k : ℝ) * ((k : ℝ) - 1) * c) * ((n : ℝ) - 1) =
        variance id F * ((k : ℝ) * ((n : ℝ) - (k : ℝ))) := by
      rw [hv]; field_simp
    have h0 : ((k : ℝ) * ((k : ℝ) - 1)) * (c * ((n : ℝ) - 1) + variance id F) = 0 := by
      linear_combination hv'
    have hkk : ((k : ℝ) * ((k : ℝ) - 1)) ≠ 0 := by
      apply mul_ne_zero <;> linarith
    have := (mul_eq_zero.1 h0).resolve_left hkk
    rw [eq_div_iff hn1.ne']
    linarith
  have hs : 0 ≤ variance id F := variance_nonneg _ _
  refine ⟨fun i j hij => ?_, ?_, fun i j hij => ?_⟩
  · rw [cov_eq_mom hF2 hmean hP, ho i j hij, hc]
  · have hz : ∫ x, (∑ i ∈ (Finset.univ : Finset (Fin n)), x i) ^ 2 ∂P = 0 := by
      rw [sq_sum_eq hF2 hP, sum_const_offdiag _ _ c hd ho, hc, Finset.card_univ,
        Fintype.card_fin]
      field_simp
      ring
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (integrable_sq_sum hF2 hP Finset.univ)).1 hz
    refine ⟨0, hae.mono fun x hx => ?_⟩
    simpa using hx
  · rw [cov_eq_mom hF2 hmean hP, ho i j hij, hc, neg_div]
    exact neg_nonpos.2 (div_nonneg hs hn1.le)

/-! ### Values at a `P*_n` law -/

lemma val {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {P : Measure (Fin n → ℝ)} (hP : IsCoupling F P)
    (hC : HasCorrPstar F P) (K : Finset (Fin n)) :
    ∫ x, (∑ i ∈ K, x i) ^ 2 ∂P = vk F n K.card := by
  have ho : ∀ i j, i ≠ j → mom P i j = -(variance id F) / ((n : ℝ) - 1) := fun i j hij => by
    rw [← cov_eq_mom hF2 hmean hP]; exact hC i j hij
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [sq_sum_eq hF2 hP, sum_const_offdiag _ _ _ (mom_diag hmean hP) ho]
  unfold vk
  field_simp
  ring

lemma nat_ineq (n j : ℕ) (hj : j ≤ n) :
    (j : ℝ) * ((n : ℝ) - j) ≤ ((n / 2 : ℕ) : ℝ) * ((n : ℝ) - ((n / 2 : ℕ) : ℝ)) := by
  set h := n / 2 with hh
  have h1 : 2 * h ≤ n := by omega
  have h2 : n ≤ 2 * h + 1 := by omega
  have r1 : (2 : ℝ) * h ≤ n := by exact_mod_cast h1
  have r2 : (n : ℝ) ≤ 2 * h + 1 := by exact_mod_cast h2
  rcases le_or_gt j h with hjh | hjh
  · have : (j : ℝ) ≤ h := by exact_mod_cast hjh
    nlinarith [mul_nonneg (sub_nonneg.2 this) (by linarith : (0 : ℝ) ≤ n - h - j)]
  · have : (h : ℝ) + 1 ≤ j := by exact_mod_cast hjh
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - h) (by linarith : (0 : ℝ) ≤ j - (n - h))]

lemma maxCost_val {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {P : Measure (Fin n → ℝ)} (hP : IsCoupling F P)
    (hC : HasCorrPstar F P) : maxCost P = vk F n (n / 2) := by
  have hs : 0 ≤ variance id F := variance_nonneg _ _
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  apply le_antisymm
  · unfold maxCost
    apply Finset.sup'_le
    intro K _
    rw [val hn hF2 hmean hP hC K]
    unfold vk
    have hK : K.card ≤ n := by simpa using Finset.card_le_univ K
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (nat_ineq n K.card hK) hs) hn1.le
  · obtain ⟨K, hK⟩ := exists_card (n := n) (k := n / 2) (Nat.div_le_self n 2)
    rw [← hK, ← val hn hF2 hmean hP hC K]
    exact le_maxCost P K

lemma maxCostCard_val {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) {P : Measure (Fin n → ℝ)} (hP : IsCoupling F P)
    (hC : HasCorrPstar F P) (k : ℕ) (hk : k ≤ n) : maxCostCard k P = vk F n k := by
  obtain ⟨K, hK⟩ := exists_card hk
  apply le_antisymm
  · unfold maxCostCard
    haveI : Nonempty {K : Finset (Fin n) // K.card = k} := ⟨⟨K, hK⟩⟩
    apply ciSup_le
    intro L
    rw [val hn hF2 hmean hP hC L.1, L.2]
  · rw [← hK, ← val hn hF2 hmean hP hC K, hK]
    exact le_maxCostCard k P K hK

/-! ### Existence of a law with correlation matrix `P*_n` -/

lemma exists_star {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    (hmean : ∫ t, t ∂F = 0) (hmix : CompletelyMixable n F) :
    ∃ Q : Measure (Fin n → ℝ), IsCoupling F Q ∧ HasCorrPstar F Q := by
  obtain ⟨P0, hP0, c0, hc0⟩ := hmix
  haveI := hP0.1
  have hS := sym_coupling hP0
  refine ⟨symmetrize P0, hS, ?_⟩
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set c := mom (symmetrize P0) i0 i1
  have ho : ∀ i j, i ≠ j → mom (symmetrize P0) i j = c :=
    fun i j hij => sym_mom_eq hF2 hP0 i j i0 i1 hij h01
  have hd := mom_diag hmean hS
  have hmeanS : ∫ x, ∑ i, x i ∂P0 = 0 := by
    rw [integral_finsetSum _ (fun i _ => (coord_memLp hF2 hP0 i).integrable one_le_two)]
    simp [coord_mean hmean hP0]
  have hc00 : c0 = 0 := by
    have : ∫ x, ∑ i, x i ∂P0 = c0 := by rw [integral_congr_ae hc0]; simp
    linarith
  have hz0 : ∫ x, (∑ i ∈ (Finset.univ : Finset (Fin n)), x i) ^ 2 ∂P0 = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hc0.mono fun x hx => by simp [hx, hc00])]
    simp
  have hz : ∫ x, (∑ i ∈ (Finset.univ : Finset (Fin n)), x i) ^ 2 ∂(symmetrize P0) = 0 := by
    rw [sym_sq_sum hF2 hP0]
    simp only [Finset.univ_map_equiv_to_embedding, hz0]
    simp
  rw [sq_sum_eq hF2 hS, sum_const_offdiag _ _ c hd ho, Finset.card_univ, Fintype.card_fin] at hz
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have h0 : (n : ℝ) * (variance id F + ((n : ℝ) - 1) * c) = 0 := by linarith
  have h1 := (mul_eq_zero.1 h0).resolve_left hnpos.ne'
  intro i j hij
  rw [cov_eq_mom hF2 hmean hS, ho i j hij, eq_div_iff hn1.ne']
  linarith

end JMNDT5Aux

open MeasureTheory ProbabilityTheory JointMixND.QuadOT JMNDT5Aux

theorem solution {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : MemLp id 2 F) (hmean : ∫ t, t ∂F = 0)
    (P : Measure (Fin n → ℝ)) (hP : IsCoupling F P) (hC : HasCorrPstar F P) :
    (∀ K : Finset (Fin n), ∫ x, (∑ i ∈ K, x i) ^ 2 ∂P =
        variance id F * ((K.card : ℝ) * ((n : ℝ) - (K.card : ℝ))) / ((n : ℝ) - 1)) ∧
    maxCost P =
      variance id F * (((n / 2 : ℕ) : ℝ) * ((n : ℝ) - ((n / 2 : ℕ) : ℝ))) / ((n : ℝ) - 1) :=
  ⟨fun K => val hn hF2 hmean hP hC K, maxCost_val hn hF2 hmean hP hC⟩
