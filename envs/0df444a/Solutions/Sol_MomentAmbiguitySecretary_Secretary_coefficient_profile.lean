-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.coefficient_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:56.483216+00:00
-- url     : https://prove2.me/submissions/3110142f-c74c-4453-b573-8d0a96161136

import Theorems.Thm_MomentAmbiguitySecretary_Secretary_entire_product_coefficients

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.CoefProfile

/-- S(j) = ∑_{i<j} i / n. -/
def S (n j : ℕ) : ℕ := ∑ i ∈ Finset.range j, i / n

lemma S_block (n : ℕ) (hn : 1 ≤ n) (L b : ℕ) (hb : b ≤ n) :
    S n (n * L + b) = S n (n * L) + b * L := by
  unfold S
  rw [Finset.sum_range_add]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => L)]
  · simp [mul_comm]
  · intro r hr
    have hr' := Finset.mem_range.1 hr
    rw [Nat.div_eq_of_lt_le] <;> nlinarith

lemma S_full (n : ℕ) (hn : 1 ≤ n) (L : ℕ) : 2 * S n (n * L) = n * L * (L - 1) := by
  induction L with
  | zero => simp [S]
  | succ L ih =>
    have h := S_block n hn L n le_rfl
    have : n * (L + 1) = n * L + n := by ring
    rw [this, h, mul_add, ih]
    rcases L with _ | L
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring_nf

lemma exponent_eq (N j : ℕ) (hN : 2 ≤ N) : exponent N j = S (N - 1) j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  simp only [Nat.add_sub_cancel]
  have hj : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hb : j % n < n := Nat.mod_lt _ hn
  have h1 := S_block n hn (j / n) (j % n) hb.le
  have h2 := S_full n hn (j / n)
  unfold exponent
  simp only [Nat.add_sub_cancel]
  rw [← hj] at h1
  rw [h1]
  generalize S n (n * (j / n)) = s at *
  generalize j / n = L at *
  generalize j % n = b at *
  have : n * L * (L - 1) / 2 = s := by omega
  rw [this]; ring

lemma arith (N j : ℕ) (hN : 2 ≤ N) :
    (j : ℤ) - (exponent N j : ℤ) ≤ (N : ℤ) - 1 ∧
    ((j : ℤ) - (exponent N j : ℤ) = (N : ℤ) - 1 ↔ N - 1 ≤ j ∧ j ≤ 2 * N - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hj : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hb : j % n < n := Nat.mod_lt _ hn
  unfold exponent
  simp only [Nat.add_sub_cancel]
  generalize hL : j / n = L at *
  generalize hb' : j % n = b at *
  have hev : 2 ∣ n * L * (L - 1) := by
    have := Nat.even_mul_pred_self L
    rw [mul_assoc]
    exact Dvd.dvd.mul_left (even_iff_two_dvd.1 this) n
  obtain ⟨X, hX⟩ := hev
  have hX' : n * L * (L - 1) / 2 = X := by omega
  rw [hX']
  subst hj
  have key : ∀ L' : ℕ, L = L' + 1 → 2 * X = n * L * L' := by
    intro L' h; subst h; simpa using hX.symm
  rcases L with _ | _ | _ | L
  · simp at hX
    subst hX
    omega
  · have : X = 0 := by simpa using hX
    subst this
    omega
  · have : X = n := by simp at hX; nlinarith
    subst this
    omega
  · have hX2 : 2 * X = n * (L + 3) * (L + 2) := by simpa using hX.symm
    have h3 : n * (L + 3) ≥ 3 * n := by nlinarith
    constructor
    · zify at hX2 ⊢
      nlinarith
    · constructor
      · intro h
        exfalso
        zify at hX2 h
        nlinarith
      · rintro ⟨_, h⟩
        exfalso
        have e2 : 2 * (n + 1) - 2 = 2 * n := by omega
        rw [e2] at h
        nlinarith

lemma msum (c : ℕ →₀ ℕ) : (Finsupp.toMultiset c).sum = c.sum (fun m u => m * u) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Multiset.sum_add, hf, hg,
      Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single a b => simp [Finsupp.toMultiset_single, Finsupp.sum_single_index, Multiset.sum_nsmul, mul_comm]

lemma sum_getD (l : List ℕ) : ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    rw [ih]; ring

lemma count_le_filter (s : Multiset ℕ) (n k : ℕ) (hs : ∀ m, s.count m ≤ n) :
    Multiset.card (s.filter (· < k)) ≤ k * n := by
  have h : ∀ a ∈ s.filter (· < k), a ∈ Finset.range k := by
    intro a ha
    simpa using (Multiset.mem_filter.1 ha).2
  rw [← Multiset.sum_count_eq_card h]
  calc ∑ a ∈ Finset.range k, (s.filter (· < k)).count a
      ≤ ∑ a ∈ Finset.range k, n := by
        apply Finset.sum_le_sum
        intro a _
        exact (Multiset.count_le_of_le a (Multiset.filter_le _ _)).trans (hs a)
    _ = k * n := by simp

lemma key (s : Multiset ℕ) (n : ℕ) (hs : ∀ m, s.count m ≤ n) (i : ℕ)
    (hi : i < Multiset.card s) :
    i / n ≤ (s.sort (· ≤ ·)).getD i 0 := by
  set l := s.sort (· ≤ ·) with hl
  have hlen : l.length = Multiset.card s := Multiset.length_sort _
  have hi' : i < l.length := by omega
  by_contra h
  rw [not_le] at h
  set k := i / n with hk
  have hlik : l[i] < k := by rwa [List.getD_eq_getElem _ _ hi'] at h
  have hpw : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hall : ∀ a ∈ l.take (i + 1), a < k := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
    rw [List.getElem_take]
    have hj1 : j < i + 1 := by simp at hj; omega
    have hjl : j < l.length := by omega
    rcases Nat.lt_or_ge j i with hji | hji
    · exact lt_of_le_of_lt (List.pairwise_iff_getElem.1 hpw j i hjl hi' hji) hlik
    · have : j = i := by omega
      subst this; exact hlik
  have h1 : (l.take (i + 1)).countP (fun a => decide (a < k)) = i + 1 := by
    rw [List.countP_eq_length.2 (by simpa using hall)]
    simpa using hi'
  have h2 : (l.take (i + 1)).countP (fun a => decide (a < k)) ≤ l.countP (fun a => decide (a < k)) :=
    (List.take_sublist _ _).countP_le
  have h3 : l.countP (fun a => decide (a < k)) = Multiset.card (s.filter (· < k)) := by
    rw [← Multiset.coe_countP, hl, Multiset.sort_eq, Multiset.countP_eq_card_filter]
  have h4 := count_le_filter s n k hs
  have h5 : k * n ≤ i := by
    rw [hk, mul_comm]; exact Nat.mul_div_le i n
  omega

lemma lower_occ (N j : ℕ) (hN : 2 ≤ N) :
    ∃ c : Occupancy N j, occupancyExponent c = S (N - 1) j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  simp only [Nat.add_sub_cancel]
  let M0 : Multiset ℕ := (Multiset.range j).map (· / n)
  have hcount : ∀ m, M0.count m ≤ n := by
    intro m
    have : M0.count m = Multiset.card ((Multiset.range j).filter (fun a => m = a / n)) := by
      simp only [M0]; rw [Multiset.count_map]
    rw [this]
    have h2 : ((Multiset.range j).filter (fun a => m = a / n)) =
        ((Finset.range j).filter (fun a => m = a / n)).val := rfl
    rw [h2, Finset.card_val]
    calc ((Finset.range j).filter (fun a => m = a / n)).card
        ≤ (Finset.Ico (m * n) (m * n + n)).card := by
          apply Finset.card_le_card
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at ha ⊢
          obtain ⟨_, rfl⟩ := ha
          constructor
          · exact Nat.div_mul_le_self a n
          · have := Nat.lt_div_mul_add (a := a) hn
            exact this
      _ = n := by simp
  refine ⟨⟨Multiset.toFinsupp M0, ?_, ?_⟩, ?_⟩
  · intro m
    rw [Multiset.toFinsupp_apply]
    have := hcount m
    omega
  · have h := Finsupp.card_toMultiset (Multiset.toFinsupp M0)
    rw [Multiset.toFinsupp_toMultiset] at h
    have h2 : Multiset.card M0 = j := by simp [M0]
    exact h.symm.trans h2
  · unfold occupancyExponent
    show (Multiset.toFinsupp M0).sum (fun m u => m * u) = _
    rw [← msum, Multiset.toFinsupp_toMultiset]
    rfl

/-- sorted list of an occupancy -/
noncomputable def lst {N j : ℕ} (c : Occupancy N j) : List ℕ :=
  (Finsupp.toMultiset c.val).sort (· ≤ ·)

noncomputable def phi (N j : ℕ) (c : Occupancy N j) : Fin j → ℕ :=
  fun i => (lst c).getD i 0 - (i : ℕ) / (N - 1)

lemma lst_len {N j : ℕ} (c : Occupancy N j) : (lst c).length = j := by
  unfold lst
  rw [Multiset.length_sort, Finsupp.card_toMultiset]
  exact c.2.2

lemma lst_key {N j : ℕ} (hN : 2 ≤ N) (c : Occupancy N j) (i : ℕ) (hi : i < j) :
    i / (N - 1) ≤ (lst c).getD i 0 := by
  apply key
  · intro m
    rw [Finsupp.count_toMultiset]
    have := c.2.1 m
    omega
  · rw [Finsupp.card_toMultiset]
    have : c.val.sum (fun _ => id) = j := c.2.2
    omega

lemma exp_eq_phi {N j : ℕ} (hN : 2 ≤ N) (c : Occupancy N j) :
    occupancyExponent c = S (N - 1) j + ∑ i, phi N j c i := by
  have h1 : occupancyExponent c = (lst c).sum := by
    unfold occupancyExponent lst
    rw [← msum, ← Multiset.sum_coe, Multiset.sort_eq]
  have h2 : (lst c).sum = ∑ i ∈ Finset.range j, (lst c).getD i 0 := by
    rw [← sum_getD, lst_len]
  rw [h1, h2]
  unfold S phi
  rw [Fin.sum_univ_eq_sum_range (fun i => (lst c).getD i 0 - i / (N - 1)) j,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have := lst_key hN c i (Finset.mem_range.1 hi)
  omega

lemma phi_inj {N j : ℕ} (hN : 2 ≤ N) : Function.Injective (phi N j) := by
  intro c c' h
  have hl : lst c = lst c' := by
    apply List.ext_getElem (by rw [lst_len, lst_len])
    intro i h1 h2
    have hij : i < j := by rwa [lst_len] at h1
    have := congrFun h ⟨i, hij⟩
    simp only [phi] at this
    have k1 := lst_key hN c i hij
    have k2 := lst_key hN c' i hij
    rw [List.getD_eq_getElem _ _ h1] at this k1
    rw [List.getD_eq_getElem _ _ h2] at this k2
    omega
  apply Subtype.ext
  ext m
  rw [← Finsupp.count_toMultiset c.val m, ← Finsupp.count_toMultiset c'.val m]
  have e1 : ((lst c : List ℕ) : Multiset ℕ) = Finsupp.toMultiset c.val := Multiset.sort_eq _ _
  have e2 : ((lst c' : List ℕ) : Multiset ℕ) = Finsupp.toMultiset c'.val := Multiset.sort_eq _ _
  rw [← e1, ← e2, hl]

lemma geom_finset (B : ℕ) (hB : 2 ≤ B) (T : Finset ℕ) :
    ∑ h ∈ T, ((B : ℝ)⁻¹) ^ h ≤ 2 := by
  have hq0 : 0 ≤ (B : ℝ)⁻¹ := by positivity
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hq1 : (B : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hB'
  have hs := summable_geometric_of_lt_one hq0 (by linarith)
  calc ∑ h ∈ T, ((B : ℝ)⁻¹) ^ h ≤ ∑' h, ((B : ℝ)⁻¹) ^ h :=
        hs.sum_le_tsum T (fun _ _ => by positivity)
    _ = (1 - (B : ℝ)⁻¹)⁻¹ := tsum_geometric_of_lt_one hq0 (by linarith)
    _ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith

lemma upper_finite (N j B : ℕ) (hN : 2 ≤ N) (hB : 2 ≤ B) (t : Finset (Occupancy N j)) :
    ∑ c ∈ t, ((B : ℝ)⁻¹) ^ occupancyExponent c ≤ ((B : ℝ)⁻¹) ^ S (N - 1) j * 2 ^ j := by
  classical
  set q : ℝ := (B : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have step1 : ∑ c ∈ t, q ^ occupancyExponent c =
      q ^ S (N - 1) j * ∑ c ∈ t, ∏ i, q ^ (phi N j c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [exp_eq_phi hN c, pow_add, Finset.prod_pow_eq_pow_sum]
  have step2 : ∑ c ∈ t, ∏ i, q ^ (phi N j c i) =
      ∑ δ ∈ t.image (phi N j), ∏ i, q ^ (δ i) := by
    rw [Finset.sum_image (fun a _ b _ h => phi_inj hN h)]
  have step3 : ∑ δ ∈ t.image (phi N j), ∏ i, q ^ (δ i) ≤
      ∑ δ ∈ Fintype.piFinset (fun i : Fin j => (t.image (phi N j)).image (fun δ => δ i)),
        ∏ i, q ^ (δ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun δ hδ => Fintype.mem_piFinset.2 (fun i => Finset.mem_image_of_mem _ hδ))
      (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
  have step4 : ∑ δ ∈ Fintype.piFinset (fun i : Fin j => (t.image (phi N j)).image (fun δ => δ i)),
        ∏ i, q ^ (δ i) =
      ∏ i : Fin j, ∑ h ∈ (t.image (phi N j)).image (fun δ => δ i), q ^ h :=
    (Finset.prod_univ_sum _ _).symm
  have step5 : ∏ i : Fin j, ∑ h ∈ (t.image (phi N j)).image (fun δ => δ i), q ^ h ≤
      ∏ _i : Fin j, (2 : ℝ) :=
    Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
      (fun i _ => geom_finset B hB _)
  rw [step1]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at step5
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [step2]
  exact step3.trans (step4.le.trans step5)

end MomentAmbiguitySecretary.Secretary.Dev.CoefProfile

namespace MomentAmbiguitySecretary.Secretary

theorem chk_coefficient_profile (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    coefficientProfile B N := by
  intro j
  have hs : HasSum (fun c : Occupancy N j => ((B : ℝ)⁻¹) ^ occupancyExponent c)
      (coefficient B N j) :=
    ((entire_product_coefficients B N hB hN).2.2.2.2.2 j).2.2.1
  have hz : (B : ℝ) ^ (-(exponent N j : ℤ)) = ((B : ℝ)⁻¹) ^ Dev.CoefProfile.S (N - 1) j := by
    rw [Dev.CoefProfile.exponent_eq N j hN, zpow_neg, zpow_natCast, inv_pow]
  have ha := Dev.CoefProfile.arith N j hN
  refine ⟨?_, ?_, ha.1, ha.2⟩
  · rw [hz]
    obtain ⟨c, hc⟩ := Dev.CoefProfile.lower_occ N j hN
    have := le_hasSum hs c (fun c' _ => by positivity)
    rwa [hc] at this
  · rw [hz, mul_comm]
    exact hasSum_le_of_sum_le hs (fun t => Dev.CoefProfile.upper_finite N j B hN hB t)

end MomentAmbiguitySecretary.Secretary
end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_coefficient_profile := @MomentAmbiguitySecretary.Secretary.chk_coefficient_profile
