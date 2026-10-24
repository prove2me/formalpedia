-- Prove2me | solution 1 for InterdepSOS.RSVCG.expost_ir
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:35:45.105284+00:00
-- url     : https://prove2.me/submissions/1e8152d3-9f93-480b-a3ec-0f2a86786265

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism

namespace InterdepSOS.RSVCG.RSAux
open InterdepSOS.RSVCG

theorem keepOn_le {n : ℕ} (S : Finset (Fin n)) (z : Signal n) : keepOn S z ≤ z := by
  intro j; unfold keepOn; split_ifs <;> simp

theorem keepOn_mono {n : ℕ} {S S' : Finset (Fin n)} (hS : S ⊆ S') (z : Signal n) :
    keepOn S z ≤ keepOn S' z := by
  intro j; unfold keepOn
  by_cases h1 : j ∈ S
  · simp [h1, hS h1]
  · simp [h1]

theorem sos_tele {n : ℕ} (w : Signal n → ℝ) (hw : IsSOS w) (z : Signal n) (S : Finset (Fin n)) :
    ∀ U : Finset (Fin n), Disjoint S U →
      w (keepOn (S ∪ U) z) - w (keepOn S z) ≤ w (keepOn U z) - w (keepOn ∅ z) := by
  classical
  intro U
  induction U using Finset.induction_on with
  | empty => intro _; simp
  | insert j U hj ih =>
    intro hd
    have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hd h (Finset.mem_insert_self _ _)
    have hd' : Disjoint S U := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hd
    have key := hw j 0 (z j) (keepOn (S ∪ U) z) (keepOn U z) (by
      intro l _; exact keepOn_mono Finset.subset_union_right z l)
    have e1 : Function.update (keepOn (S ∪ U) z) j (0 + z j) = keepOn (S ∪ insert j U) z := by
      funext l; by_cases hl : l = j
      · subst hl; simp [keepOn]
      · simp [Function.update_of_ne hl, keepOn, hl]
    have e2 : Function.update (keepOn (S ∪ U) z) j 0 = keepOn (S ∪ U) z := by
      funext l; by_cases hl : l = j
      · subst hl; simp [keepOn, hjS, hj]
      · simp [Function.update_of_ne hl]
    have e3 : Function.update (keepOn U z) j (0 + z j) = keepOn (insert j U) z := by
      funext l; by_cases hl : l = j
      · subst hl; simp [keepOn]
      · simp [Function.update_of_ne hl, keepOn, hl]
    have e4 : Function.update (keepOn U z) j 0 = keepOn U z := by
      funext l; by_cases hl : l = j
      · subst hl; simp [keepOn, hj]
      · simp [Function.update_of_ne hl]
    rw [e1, e2, e3, e4, one_mul] at key
    linarith [ih hd']

/-- The pairing inequality behind Lemma 3.1 (`d = 1`). -/
theorem sos_pair {n : ℕ} (w : Signal n → ℝ) (hw : IsSOS w) (z : Signal n) (S : Finset (Fin n)) :
    w z + w (keepOn ∅ z) ≤ w (keepOn S z) + w (keepOn Sᶜ z) := by
  have := sos_tele w hw z S Sᶜ disjoint_compl_right
  have hz : keepOn (S ∪ Sᶜ) z = z := by
    funext l; simp [keepOn]
  rw [hz] at this
  linarith

theorem g_congr {n m : ℕ} {v g : Valuation n m} {h : Fin n → Bundle m → NNReal → ℝ}
    (hsep : IsSeparableSOS v g h) (i : Fin n) (T : Bundle m) (hT : T.Nonempty)
    (z z' : Signal n) (hzz : ∀ l, l ≠ i → z l = z' l) : g i T z = g i T z' := by
  have : z' = Function.update z i (z' i) := by
    funext l; by_cases hl : l = i
    · subst hl; simp
    · simp [Function.update_of_ne hl, hzz l hl]
  rw [this, (hsep i T hT).2.1]

/-- Sum over all partitions of the agent-`i` proxy weight. -/
theorem sum_weight_ge {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (s : Profile n m) (i : Fin n) (T : Bundle m) (hT : T.Nonempty) :
    (2 ^ n : ℝ) * v i T (sigT s T) ≤ 2 * ∑ B : Finset (Fin n), vcgWeight v B s i T := by
  classical
  obtain ⟨hvg, hg_ign, hg_mono, hh_mono, hg_sos⟩ := hsep i T hT
  set z := sigT s T with hz
  let φ : Finset (Fin n) → ℝ := fun B => v i T (keepOn (insert i Bᶜ) z)
  have hsw : ∀ B, vcgWeight v B s i T = φ B := fun B => rfl
  simp only [hsw]
  have hcomp : ∑ B : Finset (Fin n), φ Bᶜ = ∑ B : Finset (Fin n), φ B :=
    Equiv.sum_comp (Function.Involutive.toPerm _ compl_involutive) φ
  have hpt : ∀ B : Finset (Fin n), v i T z ≤ φ B + φ Bᶜ := by
    intro B
    have e1 : φ B = g i T (keepOn (insert i Bᶜ) z) + h i T (z i) := by
      simp only [φ, hvg]; simp [keepOn]
    have e2 : φ Bᶜ = g i T (keepOn (insert i B) z) + h i T (z i) := by
      simp only [φ, hvg, compl_compl]; simp [keepOn]
    have hp := sos_pair (g i T) hg_sos z (insert i Bᶜ)
    have hm : g i T (keepOn (insert i Bᶜ)ᶜ z) ≤ g i T (keepOn (insert i B) z) := by
      apply hg_mono; apply keepOn_mono
      intro l hl; simp at hl; simp [hl.2]
    -- g(0) + h(z i) ≥ 0
    have h0 : 0 ≤ g i T (keepOn ∅ z) + h i T (z i) := by
      have := hv.1 i T (Function.update (keepOn ∅ z) i (z i))
      rw [hvg, hg_ign] at this; simpa using this
    have := hvg z
    linarith
  have hsum : ∑ B : Finset (Fin n), v i T z ≤ ∑ B : Finset (Fin n), (φ B + φ Bᶜ) :=
    Finset.sum_le_sum fun B _ => hpt B
  rw [Finset.sum_add_distrib, hcomp] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hsum
  linarith


theorem display5 {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (s : Profile n m) (i : Fin n) (T : Bundle m) :
    v i T (sigT s T) / 2 * (1 / 2) ≤
      avgB (fun B => if i ∈ B then vcgWeight v B s i T else 0) := by
  classical
  by_cases hT : T.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    subst hT
    simp [avgB, vcgWeight, hv.2.1]
  have hS := sum_weight_ge v g h hv hsep s i T hT
  -- toggle involution
  let t : Finset (Fin n) → Finset (Fin n) := fun B => if i ∈ B then B.erase i else insert i B
  have ht : Function.Involutive t := by
    intro B; by_cases hB : i ∈ B
    · simp [t, hB, Finset.insert_erase hB]
    · simp [t, hB, Finset.erase_insert hB]
  have hwt : ∀ B, vcgWeight v (t B) s i T = vcgWeight v B s i T := by
    intro B; unfold vcgWeight; congr 2
    ext l; by_cases hl : l = i
    · subst hl; simp
    · by_cases hB : i ∈ B <;> simp [t, hB, hl]
  have hmem : ∀ B, (i ∈ t B ↔ i ∉ B) := by
    intro B; by_cases hB : i ∈ B <;> simp [t, hB]
  have htog : ∑ B : Finset (Fin n), (if i ∈ B then vcgWeight v B s i T else 0) =
      ∑ B : Finset (Fin n), (if i ∉ B then vcgWeight v B s i T else 0) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ ht)]
    apply Finset.sum_congr rfl; intro B _
    simp only [Function.Involutive.coe_toPerm, hwt, hmem]
  have hsplit : ∑ B : Finset (Fin n), (if i ∈ B then vcgWeight v B s i T else 0) +
      ∑ B : Finset (Fin n), (if i ∉ B then vcgWeight v B s i T else 0) =
      ∑ B : Finset (Fin n), vcgWeight v B s i T := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro B _
    by_cases hB : i ∈ B <;> simp [hB]
  unfold avgB
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [le_inv_mul_iff₀ hpos]
  linarith

theorem weight_le_val {n m : ℕ} (v : Valuation n m) (hv : IsCombValuation v)
    (B : Finset (Fin n)) (s : Profile n m) (j : Fin n) (T : Bundle m) :
    vcgWeight v B s j T ≤ v j T (sigT s T) := by
  by_cases hT : T.Nonempty
  · exact hv.2.2.1 j T hT (keepOn_le _ _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    subst hT; simp [vcgWeight, hv.2.1]

theorem approx {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (s : Profile n m) (Tstar : Alloc n m) (hT : IsAllocOn Finset.univ Tstar) :
    welfare v s Tstar ≤ 4 * avgB (fun B => welfare v s (alloc B s)) := by
  classical
  have hmono : ∀ f f' : Finset (Fin n) → ℝ, (∀ B, f B ≤ f' B) → avgB f ≤ avgB f' := by
    intro f f' hff; unfold avgB
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => hff B) (by positivity)
  have step1 : welfare v s Tstar ≤
      ∑ i, 4 * avgB (fun B => if i ∈ B then vcgWeight v B s i (Tstar i) else 0) := by
    unfold welfare
    apply Finset.sum_le_sum; intro i _
    have := display5 v g h hv hsep s i (Tstar i); linarith
  have step2 : ∑ i, 4 * avgB (fun B => if i ∈ B then vcgWeight v B s i (Tstar i) else 0) =
      4 * avgB (fun B => ∑ i ∈ B, vcgWeight v B s i (Tstar i)) := by
    rw [← Finset.mul_sum]; congr 1
    unfold avgB; rw [← Finset.mul_sum]; congr 1
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro B _
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have step3 : ∀ B, ∑ i ∈ B, vcgWeight v B s i (Tstar i) ≤ welfare v s (alloc B s) := by
    intro B
    let TB : Alloc n m := fun i => if i ∈ B then Tstar i else ∅
    have hTB : IsAllocOn B TB := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        simp only [TB]
        split_ifs
        · exact hT.1 hab
        all_goals simp
      · intro a ha; simp [TB, ha]
    have h1 : ∑ i ∈ B, vcgWeight v B s i (Tstar i) = ∑ i ∈ B, vcgWeight v B s i (TB i) := by
      apply Finset.sum_congr rfl; intro i hi; simp [TB, hi]
    rw [h1]
    refine le_trans ((halloc B s).2 TB hTB) ?_
    unfold welfare
    refine le_trans (Finset.sum_le_sum fun i _ => weight_le_val v hv B s i _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hv.1 _ _ _)
  rw [step2] at step1
  have := hmono _ _ step3
  linarith


theorem allocOn_erase {n m : ℕ} {B : Finset (Fin n)} {T : Alloc n m} (i : Fin n)
    (hT : IsAllocOn B T) (hi : T i = ∅) : IsAllocOn (B.erase i) T := by
  refine ⟨hT.1, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst hji; exact hi
  · exact hT.2 j (fun hB => hj (Finset.mem_erase.mpr ⟨hji, hB⟩))

theorem allocOn_of_erase {n m : ℕ} {B : Finset (Fin n)} {T : Alloc n m} (i : Fin n)
    (hT : IsAllocOn (B.erase i) T) : IsAllocOn B T :=
  ⟨hT.1, fun j hj => hT.2 j (fun h => hj (Finset.mem_of_mem_erase h))⟩

/-- `w_{−i}` is at most the optimal proxy welfare of `B`. -/
theorem wMinus_le {n m : ℕ} (v : Valuation n m) (hv : IsCombValuation v)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) (s : Profile n m) (i : Fin n) (hi : i ∈ B) :
    wMinus v B s i ≤ ∑ j ∈ B, vcgWeight v B s j (alloc B s j) := by
  classical
  unfold wMinus
  apply Finset.sup'_le
  intro T hT
  simp only [allocsOn, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  have hTi : T i = ∅ := hT.2 i (by simp)
  have h1 := (halloc B s).2 T (allocOn_of_erase i hT)
  rw [← Finset.add_sum_erase B _ hi, hTi] at h1
  simp only [vcgWeight, hv.2.1, zero_add] at h1
  exact h1

/-- the sum over `B ∖ {i}` of any feasible allocation to `B ∖ {i}` is at most `w_{−i}`. -/
theorem le_wMinus {n m : ℕ} (v : Valuation n m)
    (B : Finset (Fin n)) (s : Profile n m) (i : Fin n) (T : Alloc n m)
    (hT : IsAllocOn (B.erase i) T) :
    ∑ j ∈ B.erase i, vcgWeight v B s j (T j) ≤ wMinus v B s i := by
  classical
  unfold wMinus
  have hm : T ∈ allocsOn (m := m) (B.erase i) := by
    simp only [allocsOn, Finset.mem_filter, Finset.mem_univ, true_and]; exact hT
  exact Finset.le_sup' (f := fun T : Alloc n m => ∑ j ∈ B.erase i, vcgWeight v B s j (T j)) hm

theorem payNonneg {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) (s : Profile n m) (i : Fin n) :
    0 ≤ vcgPay v g alloc B s i := by
  classical
  unfold vcgPay
  split_ifs with hc
  swap; · exact le_refl _
  obtain ⟨hiB, hne⟩ := hc
  set T := alloc B s with hTdef
  have hg : g i (T i) (keepOn (insert i Bᶜ) (sigT s (T i))) ≤ g i (T i) (sigT s (T i)) :=
    (hsep i (T i) hne).2.2.1 (keepOn_le _ _)
  let T' : Alloc n m := fun j => if j = i then ∅ else T j
  have hT' : IsAllocOn (B.erase i) T' := by
    refine ⟨?_, ?_⟩
    · intro a b hab; simp only [T']
      split_ifs
      · simp
      · simp
      · simp
      · exact (halloc B s).1.1 hab
    · intro j hj
      simp only [T']
      split_ifs with hji
      · rfl
      · exact (halloc B s).1.2 j (fun hB => hj (Finset.mem_erase.mpr ⟨hji, hB⟩))
  have h1 := le_wMinus v B s i T' hT'
  have h2 : ∑ j ∈ B.erase i, vcgWeight v B s j (T' j) = ∑ j ∈ B.erase i, vcgWeight v B s j (T j) := by
    apply Finset.sum_congr rfl; intro j hj
    simp [T', Finset.ne_of_mem_erase hj]
  rw [h2] at h1
  linarith

theorem obs22 {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hsep : IsSeparableSOS v g h) (i : Fin n) (T : Bundle m) (hT : T.Nonempty) :
    IsSOS (v i T) := by
  obtain ⟨hvg, hg_ign, _, _, hg_sos⟩ := hsep i T hT
  intro j x δ z z' hzz
  simp only [hvg]
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self, hg_ign, one_mul]
    linarith
  · have := hg_sos j x δ z z' hzz
    simp only [Function.update_of_ne (Ne.symm hj)]
    linarith


theorem util_char {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m)
    (B : Finset (Fin n)) (i : Fin n) (hi : i ∈ B) (s : Profile n m) (y : Bundle m → NNReal) :
    utility v (alloc B) (vcgPay v g alloc B) i s y =
      if (alloc B (Function.update s i y) i).Nonempty then
        (∑ j ∈ B, vcgWeight v B s j (alloc B (Function.update s i y) j)) - wMinus v B s i
      else 0 := by
  classical
  set s' := Function.update s i y with hs'
  set T := alloc B s' with hT
  have hW : ∀ j, j ≠ i → ∀ U, vcgWeight v B s' j U = vcgWeight v B s j U := by
    intro j hj U; unfold vcgWeight; congr 1; funext l
    by_cases hl : l = i
    · subst hl
      have : l ∉ insert j Bᶜ := by simp [Ne.symm hj, hi]
      simp [keepOn, this]
    · simp [keepOn, sigT, hs', Function.update_of_ne hl]
  have hM : wMinus v B s' i = wMinus v B s i := by
    unfold wMinus; congr 1; funext U
    apply Finset.sum_congr rfl; intro j hj; exact hW j (Finset.ne_of_mem_erase hj) _
  unfold utility
  split_ifs with hne
  · have hpay : vcgPay v g alloc B s' i = g i (T i) (sigT s' (T i)) -
        g i (T i) (keepOn (insert i Bᶜ) (sigT s' (T i))) -
        ∑ j ∈ B.erase i, vcgWeight v B s' j (T j) + wMinus v B s' i := by
      unfold vcgPay; rw [if_pos ⟨hi, hne⟩]
    rw [hpay, hM]
    have hsum : ∑ j ∈ B.erase i, vcgWeight v B s' j (T j) =
        ∑ j ∈ B.erase i, vcgWeight v B s j (T j) :=
      Finset.sum_congr rfl (fun j hj => hW j (Finset.ne_of_mem_erase hj) _)
    rw [hsum, ← Finset.add_sum_erase B _ hi]
    obtain ⟨hvg, -, -, -, -⟩ := hsep i (T i) hne
    have g1 : g i (T i) (sigT s' (T i)) = g i (T i) (sigT s (T i)) :=
      g_congr hsep i (T i) hne _ _ (fun l hl => by simp [sigT, hs', Function.update_of_ne hl])
    have g2 : g i (T i) (keepOn (insert i Bᶜ) (sigT s' (T i))) =
        g i (T i) (keepOn (insert i Bᶜ) (sigT s (T i))) :=
      g_congr hsep i (T i) hne _ _ (fun l hl => by
        simp [keepOn, sigT, hs', Function.update_of_ne hl])
    have e1 : vcgWeight v B s i (T i) =
        g i (T i) (keepOn (insert i Bᶜ) (sigT s (T i))) + h i (T i) (s i (T i)) := by
      unfold vcgWeight; rw [hvg]; simp [keepOn, sigT]
    have e2 : v i (T i) (sigT s (T i)) = g i (T i) (sigT s (T i)) + h i (T i) (s i (T i)) := by
      rw [hvg]; rfl
    rw [g1, g2, e1, e2]; ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hne' : alloc B (Function.update s i y) i = ∅ := hne
    have hpay : vcgPay v g alloc B (Function.update s i y) i = 0 := by
      unfold vcgPay; rw [if_neg]; rintro ⟨-, h2⟩; rw [hne'] at h2; simp at h2
    rw [hpay, hne', hv.2.1]; simp

theorem util_truth {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) (i : Fin n) (hi : i ∈ B) (s : Profile n m) :
    utility v (alloc B) (vcgPay v g alloc B) i s (s i) =
      (∑ j ∈ B, vcgWeight v B s j (alloc B s j)) - wMinus v B s i := by
  classical
  have := util_char v g h hv hsep alloc B i hi s (s i)
  rw [Function.update_eq_self] at this
  rw [this]
  split_ifs with hne
  · rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 := wMinus_le v hv alloc halloc B s i hi
    have h2 := le_wMinus v B s i (alloc B s) (allocOn_erase i (halloc B s).1 hne)
    have h3 : ∑ j ∈ B, vcgWeight v B s j (alloc B s j) =
        ∑ j ∈ B.erase i, vcgWeight v B s j (alloc B s j) := by
      rw [← Finset.add_sum_erase B _ hi, hne]; simp [vcgWeight, hv.2.1]
    linarith

theorem util_out {n m : ℕ} (v g : Valuation n m) (hv : IsCombValuation v)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) (i : Fin n) (hi : i ∉ B) (s : Profile n m) (y : Bundle m → NNReal) :
    utility v (alloc B) (vcgPay v g alloc B) i s y = 0 := by
  unfold utility vcgPay
  rw [if_neg (fun hh => hi hh.1), (halloc B _).1.2 i hi, hv.2.1]; simp

theorem expostIC {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) :
    IsExPostIC v (alloc B) (vcgPay v g alloc B) := by
  intro i s y
  by_cases hi : i ∈ B
  · rw [util_truth v g h hv hsep alloc halloc B i hi s, util_char v g h hv hsep alloc B i hi s y]
    split_ifs
    · exact sub_le_sub_right ((halloc B s).2 _ (halloc B _).1) _
    · exact sub_nonneg.mpr (wMinus_le v hv alloc halloc B s i hi)
  · rw [util_out v g hv alloc halloc B i hi, util_out v g hv alloc halloc B i hi]

theorem expostIR {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) :
    IsExPostIR v (alloc B) (vcgPay v g alloc B) := by
  intro i s
  by_cases hi : i ∈ B
  · rw [util_truth v g h hv hsep alloc halloc B i hi s]
    exact sub_nonneg.mpr (wMinus_le v hv alloc halloc B s i hi)
  · rw [util_out v g hv alloc halloc B i hi]

end InterdepSOS.RSVCG.RSAux

open InterdepSOS.RSVCG

theorem solution {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) :
    IsExPostIR v (alloc B) (vcgPay v g alloc B) := RSAux.expostIR v g h hv hsep alloc halloc B
