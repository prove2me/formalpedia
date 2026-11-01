-- Prove2me | solution 1 for JointMixND.QuadOT.proof_theorem_4_rho_range
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:12:16.072704+00:00
-- url     : https://prove2.me/submissions/befc9cd2-4dd0-4c6c-aa17-762992b4c88d

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JMNDGen

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


lemma avg_le {n : ℕ} (a : Equiv.Perm (Fin n) → ℝ) (M : ℝ) (h : ∀ π, a π ≤ M) :
    ((Nat.factorial n : ℝ))⁻¹ * ∑ π, a π ≤ M := by
  have hpos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rw [inv_mul_le_iff₀ hpos]
  have := Finset.sum_le_card_nsmul Finset.univ a M (fun π _ => h π)
  simpa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] using this


lemma exists_card {n k : ℕ} (hk : k ≤ n) : ∃ K : Finset (Fin n), K.card = k := by
  obtain ⟨K, -, hK⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := k) (by simpa using hk)
  exact ⟨K, hK⟩


/-! ### General-mean covariance calculus -/

lemma coord_mean' {n : ℕ} {F : Measure ℝ} {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (i : Fin n) : ∫ x, x i ∂Q = ∫ t, t ∂F := by
  have := integral_map (μ := Q) (measurable_pi_apply i).aemeasurable (f := fun t : ℝ => t)
    aestronglyMeasurable_id
  rw [hQ.2 i] at this
  rw [← this]

noncomputable def cm {n : ℕ} (Q : Measure (Fin n → ℝ)) (i j : Fin n) : ℝ :=
  covariance (fun x => x i) (fun x => x j) Q

lemma cm_eq {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F) {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (i j : Fin n) : cm Q i j = mom Q i j - (∫ t, t ∂F) ^ 2 := by
  haveI := hQ.1
  unfold cm
  rw [covariance_eq_sub (coord_memLp hF2 hQ i) (coord_memLp hF2 hQ j),
    coord_mean' hQ i, coord_mean' hQ j]
  simp [mom, sq]

lemma cm_diag {n : ℕ} {F : Measure ℝ} {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (i : Fin n) : cm Q i i = variance id F := by
  unfold cm
  rw [covariance_self (measurable_pi_apply i).aemeasurable,
    ← variance_id_map (measurable_pi_apply i).aemeasurable, hQ.2 i]

lemma var_sum {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F) {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    variance (fun x => ∑ i ∈ K, x i) Q = ∑ i ∈ K, ∑ j ∈ K, cm Q i j := by
  haveI := hQ.1
  exact variance_fun_sum' (X := fun i (x : Fin n → ℝ) => x i) (fun i _ => coord_memLp hF2 hQ i)

lemma sym_cm {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i j : Fin n) :
    cm (symmetrize Q) i j =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), cm Q (π i) (π j) := by
  rw [cm_eq hF2 (sym_coupling hQ), sym_mom hF2 hQ]
  simp_rw [cm_eq hF2 hQ]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos n).ne'), one_mul]

lemma sym_cm_eq {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (i j i' j' : Fin n) (hij : i ≠ j)
    (hij' : i' ≠ j') : cm (symmetrize Q) i j = cm (symmetrize Q) i' j' := by
  obtain ⟨σ, h1, h2⟩ := exists_perm_pair i j i' j' hij hij'
  rw [sym_cm hF2 hQ, sym_cm hF2 hQ, ← h1, ← h2]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ) (fun π : Equiv.Perm (Fin n) => cm Q (π i') (π j'))

lemma sym_var_sum {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    variance (fun x => ∑ i ∈ K, x i) (symmetrize Q) =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        variance (fun x => ∑ i ∈ K.map π.toEmbedding, x i) Q := by
  rw [var_sum hF2 (sym_coupling hQ)]
  simp_rw [var_sum hF2 hQ, sym_cm hF2 hQ, Finset.sum_map, Equiv.coe_toEmbedding]
  simp_rw [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

lemma sym_offdiag {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) :
    ∃ c : ℝ, (∀ i j, i ≠ j → cm (symmetrize Q) i j = c) ∧
      0 ≤ variance id F + ((n : ℝ) - 1) * c := by
  have hS := sym_coupling hQ
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨cm (symmetrize Q) i0 i1, fun i j hij => sym_cm_eq hF2 hQ i j i0 i1 hij h01, ?_⟩
  have hnn := variance_nonneg (fun x => ∑ i ∈ (Finset.univ : Finset (Fin n)), x i) (symmetrize Q)
  rw [var_sum hF2 hS, sum_const_offdiag _ _ _ (cm_diag hS)
    (fun i j hij => sym_cm_eq hF2 hQ i j i0 i1 hij h01), Finset.card_univ,
    Fintype.card_fin] at hnn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hc0 : 0 ≤ (n : ℝ) * (variance id F + ((n : ℝ) - 1) * cm (symmetrize Q) i0 i1) := by
    linarith
  exact (mul_nonneg_iff_of_pos_left hnpos).1 hc0

lemma lb_sym {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    vk F n K.card ≤ variance (fun x => ∑ i ∈ K, x i) (symmetrize Q) := by
  obtain ⟨c, ho, hc⟩ := sym_offdiag hn hF2 hQ
  rw [var_sum hF2 (sym_coupling hQ), sum_const_offdiag _ _ c (cm_diag (sym_coupling hQ)) ho]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hk : 0 ≤ (K.card : ℝ) * ((K.card : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos K.card with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ K.card := by exact_mod_cast h
      exact mul_nonneg (by positivity) (by linarith)
  unfold vk
  rw [div_le_iff₀ hn1]
  nlinarith [mul_nonneg hk hc]

lemma lb_avg {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {Q : Measure (Fin n → ℝ)} (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    vk F n K.card ≤ ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        variance (fun x => ∑ i ∈ K.map π.toEmbedding, x i) Q := by
  rw [← sym_var_sum hF2 hQ]; exact lb_sym hn hF2 hQ K

lemma val_gen {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {P : Measure (Fin n → ℝ)} (hP : IsCoupling F P) (hC : HasCorrPstar F P)
    (K : Finset (Fin n)) : variance (fun x => ∑ i ∈ K, x i) P = vk F n K.card := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [var_sum hF2 hP, sum_const_offdiag _ _ _ (cm_diag hP) (fun i j hij => hC i j hij)]
  unfold vk
  field_simp
  ring

lemma sym_jm_corr {n : ℕ} (hn : 2 ≤ n) {F : Measure ℝ} (hF2 : MemLp id 2 F)
    {P0 : Measure (Fin n → ℝ)} (hP0 : IsCoupling F P0) (hJ : IsJointMix P0) :
    HasCorrPstar F (symmetrize P0) := by
  haveI := hP0.1
  have hS := sym_coupling hP0
  obtain ⟨c, ho, -⟩ := sym_offdiag hn hF2 hP0
  have h0 : variance (fun x => ∑ i ∈ (Finset.univ : Finset (Fin n)), x i) P0 = 0 := by
    obtain ⟨c0, hc0⟩ := hJ
    rw [variance_congr (Y := fun _ => c0) hc0, variance_eq_integral aemeasurable_const]
    simp
  have hz : variance (fun x => ∑ i ∈ (Finset.univ : Finset (Fin n)), x i) (symmetrize P0) = 0 := by
    rw [sym_var_sum hF2 hP0]
    simp only [Finset.univ_map_equiv_to_embedding, h0]
    simp
  rw [var_sum hF2 hS, sum_const_offdiag _ _ c (cm_diag hS) ho, Finset.card_univ,
    Fintype.card_fin] at hz
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have h0' : (n : ℝ) * (variance id F + ((n : ℝ) - 1) * c) = 0 := by linarith
  have h1 := (mul_eq_zero.1 h0').resolve_left hnpos.ne'
  intro i j hij
  show cm (symmetrize P0) i j = _
  rw [ho i j hij, eq_div_iff hn1.ne']
  linarith

lemma sq_int {n : ℕ} {F : Measure ℝ} (hF2 : MemLp id 2 F) {Q : Measure (Fin n → ℝ)}
    (hQ : IsCoupling F Q) (K : Finset (Fin n)) :
    ∫ x, (∑ i ∈ K, x i) ^ 2 ∂Q =
      variance (fun x => ∑ i ∈ K, x i) Q + ((K.card : ℝ) * ∫ t, t ∂F) ^ 2 := by
  haveI := hQ.1
  have hm : MemLp (fun x : Fin n → ℝ => ∑ i ∈ K, x i) 2 Q :=
    memLp_finsetSum K (fun i _ => coord_memLp hF2 hQ i)
  have hmean : ∫ x, (∑ i ∈ K, x i) ∂Q = (K.card : ℝ) * ∫ t, t ∂F := by
    rw [integral_finsetSum _ (fun i _ => (coord_memLp hF2 hQ i).integrable one_le_two)]
    simp [coord_mean' hQ]
  rw [variance_eq_sub hm, hmean]
  simp

/-! ### Worst-case costs -/

lemma bdd_cost {n : ℕ} (M : Set (Finset (Fin n) → ℝ)) (hM : M ⊆ ProbOnSubsets n)
    (f : ℝ → ℝ) (P : Measure (Fin n → ℝ)) : BddAbove ((fun μ => costF f P μ) '' M) := by
  refine ⟨∑ K : Finset (Fin n), |∫ x, f (∑ i ∈ K, x i) ∂P|, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have h := hM hμ
  unfold costF
  apply Finset.sum_le_sum
  intro K _
  have h0 := h.1 K
  have h1 : μ K ≤ 1 := by
    rw [← h.2]; exact Finset.single_le_sum (fun K _ => h.1 K) (Finset.mem_univ K)
  calc (∫ x, f (∑ i ∈ K, x i) ∂P) * μ K ≤ |∫ x, f (∑ i ∈ K, x i) ∂P| * μ K :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |∫ x, f (∑ i ∈ K, x i) ∂P| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := mul_one _

lemma worst_mono {n : ℕ} (M : Set (Finset (Fin n) → ℝ)) (hM : M ⊆ ProbOnSubsets n)
    (f : ℝ → ℝ) (P Q : Measure (Fin n → ℝ))
    (h : ∀ K : Finset (Fin n), ∫ x, f (∑ i ∈ K, x i) ∂P ≤ ∫ x, f (∑ i ∈ K, x i) ∂Q) :
    worstCost f M P ≤ worstCost f M Q := by
  unfold worstCost
  rcases M.eq_empty_or_nonempty with hE | hNE
  · simp [hE]
  apply csSup_le (hNE.image _)
  rintro _ ⟨μ, hμ, rfl⟩
  refine le_trans ?_ (le_csSup (bdd_cost M hM f Q) ⟨μ, hμ, rfl⟩)
  unfold costF
  apply Finset.sum_le_sum
  intro K _
  exact mul_le_mul_of_nonneg_right (h K) ((hM hμ).1 K)

lemma sum_comp_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)) (x : Fin n → ℝ) :
    ∑ i ∈ K, (x ∘ π) i = ∑ i ∈ K.map π.toEmbedding, x i := by
  rw [Finset.sum_map]; rfl

lemma map_map_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)) :
    (K.map π.toEmbedding).map π.symm.toEmbedding = K := by
  ext a; simp

lemma sym_integrable {n : ℕ} (Q : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ)
    (hg : Measurable g) (h : ∀ π : Equiv.Perm (Fin n), Integrable (fun x => g (x ∘ π)) Q) :
    Integrable g (symmetrize Q) := by
  unfold symmetrize
  refine Integrable.smul_measure ?_ (by simp [Nat.factorial_ne_zero])
  refine (integrable_finsetSum_measure).2 (fun π _ => ?_)
  exact (integrable_map_measure hg.aestronglyMeasurable (measurable_perm π).aemeasurable).2 (h π)

lemma worst_sym {n : ℕ} (Q : Measure (Fin n → ℝ)) (f : ℝ → ℝ) (hf : Measurable f)
    (hint : ∀ K : Finset (Fin n), Integrable (fun x => f (∑ i ∈ K, x i)) Q)
    (M : Set (Finset (Fin n) → ℝ)) (hM : M ⊆ ProbOnSubsets n) (hsymm : IsSymmetric M) :
    worstCost f M (symmetrize Q) ≤ worstCost f M Q := by
  have hI : ∀ K : Finset (Fin n), ∫ x, f (∑ i ∈ K, x i) ∂(symmetrize Q) =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        ∫ x, f (∑ i ∈ K.map π.toEmbedding, x i) ∂Q := by
    intro K
    rw [sym_integral Q (fun x => f (∑ i ∈ K, x i)) (hf.comp (by fun_prop)) (fun π => ?_)]
    · simp_rw [sum_comp_perm]
    · simp_rw [sum_comp_perm]; exact hint _
  have hcost : ∀ μ, costF f (symmetrize Q) μ =
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), costF f Q (permProb π.symm μ) := by
    intro μ
    unfold costF permProb
    simp_rw [hI, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    conv_rhs => rw [← Equiv.sum_comp π.finsetCongr]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [Equiv.finsetCongr_apply, map_map_symm]
    ring
  unfold worstCost
  rcases M.eq_empty_or_nonempty with hE | hNE
  · simp [hE]
  apply csSup_le (hNE.image _)
  rintro _ ⟨μ, hμ, rfl⟩
  show costF f (symmetrize Q) μ ≤ _
  rw [hcost μ]
  apply avg_le
  intro π
  exact le_csSup (bdd_cost M hM f Q) ⟨permProb π.symm μ, hsymm μ hμ π.symm, rfl⟩

end JMNDGen

open MeasureTheory ProbabilityTheory JointMixND.QuadOT JMNDGen

theorem solution {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : MemLp id 2 F) (hvar : 0 < variance id F) :
    (∀ (P : Measure (Fin n → ℝ)) (ρ : ℝ), IsCoupling F P →
        (∀ i j : Fin n, i ≠ j →
          covariance (fun x => x i) (fun x => x j) P = ρ * variance id F) →
        -1 / ((n : ℝ) - 1) ≤ ρ ∧ ρ ≤ 1) ∧
    (CompletelyMixable n F → ∃ P : Measure (Fin n → ℝ), IsCoupling F P ∧ HasCorrPstar F P) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  refine ⟨fun P ρ hP hρ => ⟨?_, ?_⟩, fun hmix => ?_⟩
  · haveI := hP.1
    have hnn := variance_nonneg (fun x => ∑ i ∈ (Finset.univ : Finset (Fin n)), x i) P
    rw [var_sum hF2 hP, sum_const_offdiag _ _ (ρ * variance id F) (cm_diag hP)
      (fun i j hij => hρ i j hij), Finset.card_univ, Fintype.card_fin] at hnn
    have e : (n : ℝ) * variance id F + n * ((n : ℝ) - 1) * (ρ * variance id F) =
        ((n : ℝ) * variance id F) * (1 + ((n : ℝ) - 1) * ρ) := by ring
    rw [e] at hnn
    have h1 := (mul_nonneg_iff_of_pos_left (mul_pos hnpos hvar)).1 hnn
    rw [div_le_iff₀ hn1]
    linarith
  · haveI := hP.1
    set i0 : Fin n := ⟨0, by omega⟩
    set i1 : Fin n := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hv : ∀ i : Fin n, variance (fun x : Fin n → ℝ => x i) P = variance id F := fun i => by
      rw [← variance_id_map (measurable_pi_apply i).aemeasurable, hP.2 i]
    have hnn := variance_nonneg (fun x : Fin n → ℝ => x i0 - x i1) P
    rw [variance_fun_sub (coord_memLp hF2 hP i0) (coord_memLp hF2 hP i1), hv, hv,
      hρ i0 i1 h01] at hnn
    nlinarith
  · obtain ⟨P0, hP0, hJ⟩ := hmix
    exact ⟨symmetrize P0, sym_coupling hP0, sym_jm_corr hn hF2 hP0 hJ⟩
