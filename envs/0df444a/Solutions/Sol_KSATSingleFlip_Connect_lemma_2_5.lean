-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:52:05.257774+00:00
-- url     : https://prove2.me/submissions/41fa1825-84fb-4f40-ac78-89c33e1ce619

import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The elementary symmetric sum of order d over s. -/
def auditSymSum {α : Type} [DecidableEq α] (a : α → ℝ) (s : Finset α) (d : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard d, ∏ i ∈ t, a i

/-- Elementary symmetric-sum insertion recurrence, valid with zero entries. -/
theorem auditSymSum_insert_succ {α : Type} [DecidableEq α] (a : α → ℝ)
    (s : Finset α) (x : α) (hx : x ∉ s) (d : ℕ) :
    auditSymSum a (insert x s) (d + 1) =
      auditSymSum a s (d + 1) + a x * auditSymSum a s d := by
  unfold auditSymSum
  rw [Finset.powersetCard_succ_insert hx d]
  have hd : Disjoint (s.powersetCard (d + 1)) ((s.powersetCard d).image (insert x)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht'
    have hs : insert x u ⊆ s := (Finset.mem_powersetCard.mp ht).1
    exact hx (hs (by simp))
  rw [Finset.sum_union hd, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply congrArg _
    apply Finset.sum_congr rfl
    intro t ht
    have hxt : x ∉ t := fun h => hx ((Finset.mem_powersetCard.mp ht).1 h)
    rw [Finset.prod_insert hxt]
  · intro t ht u hu heq
    have hxt : x ∉ t := fun h => hx ((Finset.mem_powersetCard.mp ht).1 h)
    have hxu : x ∉ u := fun h => hx ((Finset.mem_powersetCard.mp hu).1 h)
    have he := congrArg (fun z : Finset α => z.erase x) heq
    simpa [hxt, hxu] using he

theorem auditSymSum_nonneg {α : Type} [DecidableEq α] (a : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : Finset α) (d : ℕ) : 0 ≤ auditSymSum a s d := by
  unfold auditSymSum
  exact Finset.sum_nonneg fun t ht => Finset.prod_nonneg fun i hi => ha i

/-- Larger excluded weights leave smaller elementary symmetric sums. -/
theorem auditSymSum_erase_antitone {α : Type} [DecidableEq α] (a : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : Finset α) (i j : α) (hi : i ∈ s) (hj : j ∈ s)
    (hij : a i ≤ a j) (d : ℕ) :
    auditSymSum a (s.erase j) d ≤ auditSymSum a (s.erase i) d := by
  by_cases heq : i = j
  · subst i; exact le_rfl
  cases d with
  | zero => simp [auditSymSum]
  | succ d =>
    let t := (s.erase i).erase j
    have hit : i ∉ t := by simp [t]
    have hjt : j ∉ t := by simp [t]
    have hsi : s.erase i = insert j t := by
      ext z
      simp [t, heq, eq_comm, hj]
    have hsj : s.erase j = insert i t := by
      have hm : i ∈ s.erase j := by simp [hi, heq]
      simpa [t, Finset.erase_right_comm] using (Finset.insert_erase hm).symm
    rw [hsi, hsj, auditSymSum_insert_succ a t j hjt d,
      auditSymSum_insert_succ a t i hit d]
    have hh := mul_le_mul_of_nonneg_right hij (auditSymSum_nonneg a ha t d)
    linarith

/-- Anti-Chebyshev applied to weights and deleted-coordinate symmetric sums. -/
theorem auditSymSum_antichebyshev {α : Type} [DecidableEq α] (a : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : Finset α) (d : ℕ) :
    (s.card : ℝ) * (∑ i ∈ s, a i * auditSymSum a (s.erase i) d) ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, auditSymSum a (s.erase i) d) := by
  have hav : AntivaryOn (fun i => auditSymSum a (s.erase i) d) a s := by
    intro i hi j hj hij
    exact auditSymSum_erase_antitone a ha s i j hi hj hij.le d
  have h := hav.card_mul_sum_le_sum_mul_sum
  simpa only [mul_comm] using h

/-- Each d-subset is missed by exactly |s|-d deleted coordinates. -/
theorem auditSymSum_erase_sum {α : Type} [DecidableEq α] (a : α → ℝ)
    (s : Finset α) (d : ℕ) (hd : d ≤ s.card) :
    (∑ i ∈ s, auditSymSum a (s.erase i) d) =
      (s.card - d : ℕ) * auditSymSum a s d := by
  have hfilter (i : α) : (s.erase i).powersetCard d =
      (s.powersetCard d).filter (fun t => i ∉ t) := by
    ext t
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_erase]
    tauto
  unfold auditSymSum
  simp_rw [hfilter, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hsub := (Finset.mem_powersetCard.mp ht).1
  have hcard := (Finset.mem_powersetCard.mp ht).2
  rw [← Finset.sum_filter]
  have hf : s.filter (fun i => i ∉ t) = s \ t := by ext i; simp
  rw [hf, Finset.sum_const, Finset.card_sdiff_of_subset hsub, hcard]
  simp

/-- Each (d+1)-subset is counted once for each distinguished element. -/
theorem auditSymSum_weighted_erase_sum {α : Type} [DecidableEq α] (a : α → ℝ)
    (s : Finset α) (d : ℕ) :
    (∑ i ∈ s, a i * auditSymSum a (s.erase i) d) =
      ((d + 1 : ℕ) : ℝ) * auditSymSum a s (d + 1) := by
  classical
  let L := s.sigma (fun i => (s.erase i).powersetCard d)
  let R := (s.powersetCard (d + 1)).sigma (fun t => t)
  have hbij : (∑ z ∈ L, a z.1 * ∏ j ∈ z.2, a j) =
      ∑ z ∈ R, ∏ j ∈ z.1, a j := by
    apply Finset.sum_bij' (fun z _ => ⟨insert z.1 z.2, z.1⟩)
      (fun z _ => ⟨z.2, z.1.erase z.2⟩)
    · intro ⟨i,t⟩ ht
      simp only [L, Finset.mem_sigma, Finset.mem_powersetCard] at ht
      have hit : i ∉ t := fun hi => (Finset.notMem_erase i s) (ht.2.1 hi)
      simp [hit]
    · intro ⟨t,i⟩ ht
      simp only [R, Finset.mem_sigma] at ht
      simp [Finset.insert_erase ht.2]
    · intro ⟨i,t⟩ ht
      simp only [L, Finset.mem_sigma, Finset.mem_powersetCard] at ht
      have hit : i ∉ t := fun hi => (Finset.notMem_erase i s) (ht.2.1 hi)
      simp [Finset.prod_insert hit]
    · intro ⟨i,t⟩ ht
      simp only [L, Finset.mem_sigma, Finset.mem_powersetCard] at ht
      rcases ht with ⟨his, hts, htd⟩
      have hit : i ∉ t := by
        intro hi
        exact (Finset.notMem_erase i s) (hts hi)
      simp only [R, Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_insert_self, and_true]
      constructor
      · exact Finset.insert_subset his (Finset.Subset.trans hts (Finset.erase_subset i s))
      · simp [Finset.card_insert_of_notMem hit, htd]
    · intro ⟨t,i⟩ ht
      simp only [R, Finset.mem_sigma, Finset.mem_powersetCard] at ht
      rcases ht with ⟨⟨hts, htd⟩, hit⟩
      simp only [L, Finset.mem_sigma, Finset.mem_powersetCard]
      refine ⟨hts hit, ?_, ?_⟩
      · exact Finset.subset_erase.mpr ⟨Finset.Subset.trans (Finset.erase_subset i t) hts, Finset.notMem_erase i t⟩
      · have h := Finset.card_erase_add_one hit
        omega

  unfold auditSymSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  change (∑ z ∈ L, a z.1 * ∏ j ∈ z.2, a j) = _
  rw [hbij]
  change (∑ z ∈ R, ∏ j ∈ z.1, a j) = _
  dsimp [R]
  rw [← Finset.sum_sigma' (s.powersetCard (d + 1)) (fun t => t) (fun t _ => ∏ j ∈ t, a j)]
  apply Finset.sum_congr rfl
  intro t ht
  simp [(Finset.mem_powersetCard.mp ht).2, nsmul_eq_mul]

/-- Adjacent elementary symmetric means satisfy the Maclaurin step. -/
theorem auditSymSum_mean_step {α : Type} [DecidableEq α] (a : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : Finset α) (d : ℕ) (hd : d + 1 ≤ s.card) :
    auditSymSum a s (d + 1) / (Nat.choose s.card (d + 1) : ℝ) ≤
      ((∑ i ∈ s, a i) / (s.card : ℝ)) *
        (auditSymSum a s d / (Nat.choose s.card d : ℝ)) := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast (show 0 < s.card by omega)
  have hc : (0 : ℝ) < Nat.choose s.card d := by
    exact_mod_cast Nat.choose_pos (show d ≤ s.card by omega)
  have hcs : (0 : ℝ) < Nat.choose s.card (d + 1) := by
    exact_mod_cast Nat.choose_pos hd
  have hanti := auditSymSum_antichebyshev a ha s d
  rw [auditSymSum_weighted_erase_sum a s d,
      auditSymSum_erase_sum a s d (by omega)] at hanti
  have hchoose : ((Nat.choose s.card (d+1) : ℝ) * (d+1 : ℕ)) =
      (Nat.choose s.card d : ℝ) * (s.card - d : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq s.card d
  rw [← mul_div_mul_comm]
  apply (div_le_div_iff₀ hcs (mul_pos hn hc)).2
  have hnon : 0 ≤ auditSymSum a s d := auditSymSum_nonneg a ha s d
  have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i hi => ha i
  apply (mul_le_mul_iff_of_pos_right (show (0 : ℝ) < (d + 1 : ℕ) by positivity)).mp
  have hmul := mul_le_mul_of_nonneg_right hanti hc.le
  have heq := congrArg (fun x : ℝ => x * (∑ i ∈ s, a i) * auditSymSum a s d) hchoose
  nlinarith [hmul, heq]

/-- Elementary symmetric means are bounded by powers of the arithmetic mean. -/
theorem auditSymSum_mean_bound {α : Type} [DecidableEq α] (a : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : Finset α) (d : ℕ) (hd : d ≤ s.card) :
    auditSymSum a s d / (Nat.choose s.card d : ℝ) ≤
      ((∑ i ∈ s, a i) / (s.card : ℝ)) ^ d := by
  induction d with
  | zero => simp [auditSymSum]
  | succ d ih =>
    have hbase : 0 ≤ (∑ i ∈ s, a i) / (s.card : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun i hi => ha i) (Nat.cast_nonneg _)
    calc
      _ ≤ ((∑ i ∈ s, a i) / (s.card : ℝ)) *
          (auditSymSum a s d / (Nat.choose s.card d : ℝ)) :=
        auditSymSum_mean_step a ha s d hd
      _ ≤ ((∑ i ∈ s, a i) / (s.card : ℝ)) *
          (((∑ i ∈ s, a i) / (s.card : ℝ)) ^ d) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) hbase
      _ = _ := by rw [pow_succ, mul_comm]

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- Wang et al., Lemma 2.5: sampling without replacement. -/
theorem solution (N d : ℕ) (hd : d ≤ N) (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) :
    uexp (fun I : {I : Finset (Fin N) // I.card = d} => ∏ i ∈ I.1, a i) ≤ (uexp a) ^ d := by
  have hsum : (∑ I : {I : Finset (Fin N) // I.card = d}, ∏ i ∈ I.1, a i) =
      auditSymSum a Finset.univ d := by
    unfold auditSymSum
    symm
    exact Finset.sum_subtype (Finset.univ.powersetCard d) (by simp) _
  have hcard : Fintype.card {I : Finset (Fin N) // I.card = d} = Nat.choose N d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun I : Finset (Fin N) => I.card = d) = Finset.univ.powersetCard d := by
      ext I
      simp
    rw [heq, Finset.card_powersetCard]
    simp
  unfold uexp
  rw [hsum, hcard]
  simpa using auditSymSum_mean_bound a ha Finset.univ d (by simpa using hd)


#print axioms solution
