-- Prove2me | solution 1 for MulticlassDS.Compress.lemma40_menu_compression
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T19:19:56.433985+00:00
-- url     : https://prove2.me/submissions/09756de5-23a3-4560-8430-aabb2606f5fe

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression

set_option autoImplicit false

namespace L40

-- ===== from scratch/probe/07aacce1_orient.lean =====
section

variable {α Y : Type*} [DecidableEq α] [DecidableEq Y]

/-- `u` and `v` agree on `Q` except possibly at `x`. -/
def AgreeOff (Q : Finset α) (x : α) (u v : α → Y) : Prop := ∀ y ∈ Q, y ≠ x → u y = v y

instance (Q : Finset α) (x : α) (u v : α → Y) : Decidable (AgreeOff Q x u v) := by
  unfold AgreeOff; infer_instance

/-- degree of `v` in the one-inclusion hypergraph of `C` on coordinates `Q`. -/
def deg (C : Finset (α → Y)) (Q : Finset α) (v : α → Y) : ℕ :=
  (Q.filter (fun x => ∃ u ∈ C, u x ≠ v x ∧ AgreeOff Q x u v)).card

lemma deg_step (C : Finset (α → Y)) (Q : Finset α) (x : α) (hx : x ∉ Q) (v : α → Y) :
    deg C (insert x Q) v ≤ deg (C.filter (fun u => u x = v x)) Q v + 1 := by
  unfold deg
  set Cx := C.filter (fun u => u x = v x) with hCx
  have hsub : (insert x Q).filter (fun z => ∃ u ∈ C, u z ≠ v z ∧ AgreeOff (insert x Q) z u v) ⊆
      insert x (Q.filter (fun z => ∃ u ∈ Cx, u z ≠ v z ∧ AgreeOff Q z u v)) := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_insert] at hz
    obtain ⟨hzQ, u, huC, hne, hag⟩ := hz
    rcases hzQ with rfl | hzQ
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter]
      have hzx : x ≠ z := fun h => hx (h ▸ hzQ)
      refine ⟨hzQ, u, ?_, hne, ?_⟩
      · rw [hCx, Finset.mem_filter]
        exact ⟨huC, hag x (Finset.mem_insert_self _ _) hzx⟩
      · intro y hy hyz
        exact hag y (Finset.mem_insert_of_mem hy) hyz
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _

lemma deg_step_const (C : Finset (α → Y)) (Q : Finset α) (x : α) (hx : x ∉ Q) (v : α → Y)
    (hall : ∀ u ∈ C, u x = v x) :
    deg C (insert x Q) v ≤ deg C Q v := by
  unfold deg
  apply Finset.card_le_card
  intro z hz
  rw [Finset.mem_filter, Finset.mem_insert] at hz
  obtain ⟨hzQ, u, huC, hne, hag⟩ := hz
  rcases hzQ with rfl | hzQ
  · exact absurd (hall u huC) hne
  · rw [Finset.mem_filter]
    refine ⟨hzQ, u, huC, hne, ?_⟩
    intro y hy hyz
    exact hag y (Finset.mem_insert_of_mem hy) hyz

/-- Every nonempty class has a vertex of degree at most `log₂ |C|`. -/
theorem mindeg (Q : Finset α) : ∀ C : Finset (α → Y), C.Nonempty →
    ∃ v ∈ C, 2 ^ (deg C Q v) ≤ C.card := by
  induction Q using Finset.induction_on with
  | empty =>
    intro C hC
    obtain ⟨v, hv⟩ := hC
    refine ⟨v, hv, ?_⟩
    simp [deg]
    exact ⟨v, hv⟩
  | @insert x Q hx ih =>
    intro C hC
    by_cases h : ∃ v₁ ∈ C, ∃ v₂ ∈ C, v₁ x ≠ v₂ x
    · obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ := h
      set A := C.filter (fun u => u x = v₁ x) with hA
      set B := C.filter (fun u => u x = v₂ x) with hB
      have hAB : A.card + B.card ≤ C.card := by
        have hBsub : B ⊆ C.filter (fun u => ¬ u x = v₁ x) := by
          intro u hu
          rw [hB, Finset.mem_filter] at hu
          rw [Finset.mem_filter]
          exact ⟨hu.1, fun h => hne (h.symm.trans hu.2)⟩
        have h1 : A.card + (C.filter (fun u => ¬ u x = v₁ x)).card = C.card :=
          Finset.card_filter_add_card_filter_not _
        have h2 := Finset.card_le_card hBsub
        omega
      have key : ∀ (w : α → Y), w ∈ C → 2 * (C.filter (fun u => u x = w x)).card ≤ C.card →
          ∃ v ∈ C, 2 ^ (deg C (insert x Q) v) ≤ C.card := by
        intro w hw hsmall
        obtain ⟨v, hvA, hv⟩ := ih (C.filter (fun u => u x = w x)) ⟨w, by simp [hw]⟩
        have hvC : v ∈ C := (Finset.mem_filter.mp hvA).1
        have hvx : v x = w x := (Finset.mem_filter.mp hvA).2
        have hfe : C.filter (fun u => u x = v x) = C.filter (fun u => u x = w x) := by
          rw [hvx]
        refine ⟨v, hvC, ?_⟩
        have hd := deg_step C Q x hx v
        rw [hfe] at hd
        calc 2 ^ deg C (insert x Q) v ≤ 2 ^ (deg (C.filter (fun u => u x = w x)) Q v + 1) :=
              Nat.pow_le_pow_right (by norm_num) hd
          _ = 2 * 2 ^ (deg (C.filter (fun u => u x = w x)) Q v) := by ring
          _ ≤ 2 * (C.filter (fun u => u x = w x)).card := by omega
          _ ≤ C.card := hsmall
      by_cases hAs : 2 * A.card ≤ C.card
      · exact key v₁ hv₁ hAs
      · have hBe : C.filter (fun u => u x = v₂ x) = B := rfl
        exact key v₂ hv₂ (by rw [hBe]; omega)
    · push Not at h
      obtain ⟨v₀, hv₀⟩ := hC
      obtain ⟨v, hvC, hv⟩ := ih C ⟨v₀, hv₀⟩
      refine ⟨v, hvC, ?_⟩
      have hd := deg_step_const C Q x hx v (fun u hu => h u hu v hvC)
      calc 2 ^ deg C (insert x Q) v ≤ 2 ^ deg C Q v := Nat.pow_le_pow_right (by norm_num) hd
        _ ≤ C.card := hv

/-- An orientation (a predictor `o x w` that only reads `w` on `Q \ {x}`) with
`2 ^ (number of mistakes of v) ≤ |C|` for every `v ∈ C`. -/
theorem orient [Nonempty Y] [DecidableEq (α → Y)] (Q : Finset α) (C : Finset (α → Y))
    (hinj : ∀ u ∈ C, ∀ v ∈ C, (∀ y ∈ Q, u y = v y) → u = v) :
    ∃ o : α → (α → Y) → Y,
      (∀ x w w', AgreeOff Q x w w' → o x w = o x w') ∧
      ∀ v ∈ C, 2 ^ ((Q.filter (fun x => o x v ≠ v x)).card) ≤ C.card := by
  induction C using Finset.strongInduction with
  | H C ih =>
    rcases C.eq_empty_or_nonempty with hC | hC
    · refine ⟨fun _ _ => Classical.arbitrary Y, fun _ _ _ _ => rfl, ?_⟩
      intro v hv
      rw [hC] at hv
      simp at hv
    · obtain ⟨v₀, hv₀C, hv₀⟩ := mindeg Q C hC
      have hsub : C.erase v₀ ⊂ C := Finset.erase_ssubset hv₀C
      obtain ⟨o', ho'r, ho'⟩ := ih (C.erase v₀) hsub (fun u hu v hv h =>
        hinj u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv) h)
      refine ⟨fun x w => if AgreeOff Q x w v₀ ∧ ¬ (∃ u ∈ C.erase v₀, AgreeOff Q x u v₀)
        then v₀ x else o' x w, ?_, ?_⟩
      · intro x w w' hww'
        have hiff : AgreeOff Q x w v₀ ↔ AgreeOff Q x w' v₀ := by
          constructor
          · intro h y hy hyx
            rw [← hww' y hy hyx]
            exact h y hy hyx
          · intro h y hy hyx
            rw [hww' y hy hyx]
            exact h y hy hyx
        simp only [hiff, ho'r x w w' hww']
      · intro v hv
        by_cases hvv : v = v₀
        · subst hvv
          have hle : (Q.filter (fun x => (if AgreeOff Q x v v ∧
              ¬ (∃ u ∈ C.erase v, AgreeOff Q x u v) then v x else o' x v) ≠ v x)).card ≤
              deg C Q v := by
            unfold deg
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx ⊢
            obtain ⟨hxQ, hx⟩ := hx
            refine ⟨hxQ, ?_⟩
            have hself : AgreeOff Q x v v := fun _ _ _ => rfl
            by_cases hex : ∃ u ∈ C.erase v, AgreeOff Q x u v
            · obtain ⟨u, huC, hu⟩ := hex
              refine ⟨u, Finset.mem_of_mem_erase huC, ?_, hu⟩
              intro hux
              have : u = v := hinj u (Finset.mem_of_mem_erase huC) v hv₀C (by
                intro y hy
                by_cases hyx : y = x
                · subst hyx; exact hux
                · exact hu y hy hyx)
              exact (Finset.ne_of_mem_erase huC) this
            · exfalso
              apply hx
              rw [if_pos ⟨hself, hex⟩]
          calc _ ≤ 2 ^ deg C Q v := Nat.pow_le_pow_right (by norm_num) hle
            _ ≤ C.card := hv₀
        · have hvE : v ∈ C.erase v₀ := Finset.mem_erase.mpr ⟨hvv, hv⟩
          have heq : Q.filter (fun x => (if AgreeOff Q x v v₀ ∧
              ¬ (∃ u ∈ C.erase v₀, AgreeOff Q x u v₀) then v₀ x else o' x v) ≠ v x) =
              Q.filter (fun x => o' x v ≠ v x) := by
            apply Finset.filter_congr
            intro x _
            by_cases hag : AgreeOff Q x v v₀
            · rw [if_neg (fun h => h.2 ⟨v, hvE, hag⟩)]
            · rw [if_neg (fun h => hag h.1)]
          rw [heq]
          exact (ho' v hvE).trans (Finset.card_le_card hsub.subset)

end


-- ===== from scratch/probe/07aacce1_boost.lean =====
section

/-- number of rounds `t` in which hypothesis `σs t` errs at `i`. -/
def cnt {n T : ℕ} {Θ : Type*} (bad : Θ → Fin n → Prop) [∀ θ i, Decidable (bad θ i)]
    (σs : Fin T → Θ) (i : Fin n) : ℕ :=
  ∑ t, if bad (σs t) i then 1 else 0

lemma boost_aux {n : ℕ} {Θ : Type*} (bad : Θ → Fin n → Prop) [∀ θ i, Decidable (bad θ i)]
    (hweak : ∀ w : Fin n → ℕ, ∃ θ, 4 * ∑ i, (if bad θ i then w i else 0) ≤ ∑ i, w i) :
    ∀ T : ℕ, ∃ σs : Fin T → Θ, 4 ^ T * ∑ i, 2 ^ (cnt bad σs i) ≤ 5 ^ T * n := by
  intro T
  induction T with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simp [cnt]
  | succ T ih =>
    obtain ⟨σs, hσs⟩ := ih
    obtain ⟨θ, hθ⟩ := hweak (fun i => 2 ^ (cnt bad σs i))
    refine ⟨Fin.snoc σs θ, ?_⟩
    have hc : ∀ i, cnt bad (Fin.snoc σs θ : Fin (T + 1) → Θ) i =
        cnt bad σs i + (if bad θ i then 1 else 0) := by
      intro i
      unfold cnt
      rw [Fin.sum_univ_castSucc]
      simp
    have hsum : ∑ i, 2 ^ (cnt bad (Fin.snoc σs θ : Fin (T + 1) → Θ) i) =
        ∑ i, 2 ^ (cnt bad σs i) + ∑ i, (if bad θ i then 2 ^ (cnt bad σs i) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i]
      split_ifs <;> ring
    rw [hsum]
    set W := ∑ i, 2 ^ (cnt bad σs i)
    set B := ∑ i, (if bad θ i then 2 ^ (cnt bad σs i) else 0)
    have h1 : 4 * (W + B) ≤ 5 * W := by omega
    calc 4 ^ (T + 1) * (W + B) = 4 ^ T * (4 * (W + B)) := by ring
      _ ≤ 4 ^ T * (5 * W) := Nat.mul_le_mul_left _ h1
      _ = 5 * (4 ^ T * W) := by ring
      _ ≤ 5 * (5 ^ T * n) := Nat.mul_le_mul_left _ hσs
      _ = 5 ^ (T + 1) * n := by ring

/-- Multiplicative-weights boosting: a weak learner with weighted error at most `1/4` for every
weighting yields `T` rounds after which every point is misclassified in fewer than `T/2` rounds. -/
theorem boost {n : ℕ} {Θ : Type*} (bad : Θ → Fin n → Prop) [∀ θ i, Decidable (bad θ i)]
    (hweak : ∀ w : Fin n → ℕ, ∃ θ, 4 * ∑ i, (if bad θ i then w i else 0) ≤ ∑ i, w i)
    (T : ℕ) (hT : 25 ^ T * n ^ 2 < 32 ^ T) :
    ∃ σs : Fin T → Θ, ∀ i, 2 * cnt bad σs i < T := by
  obtain ⟨σs, hσs⟩ := boost_aux bad hweak T
  refine ⟨σs, fun i => ?_⟩
  by_contra hcon
  push Not at hcon
  have hi : 2 ^ (cnt bad σs i) ≤ ∑ j, 2 ^ (cnt bad σs j) :=
    Finset.single_le_sum (f := fun j => 2 ^ (cnt bad σs j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : 4 ^ T * 2 ^ (cnt bad σs i) ≤ 5 ^ T * n :=
    (Nat.mul_le_mul_left _ hi).trans hσs
  have h3 : (4 ^ T * 2 ^ (cnt bad σs i)) ^ 2 ≤ (5 ^ T * n) ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 : 2 ^ T ≤ (2 ^ (cnt bad σs i)) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 32 ^ T ≤ 25 ^ T * n ^ 2 := by
    calc 32 ^ T = (4 ^ T) ^ 2 * 2 ^ T := by
          rw [← pow_mul, mul_comm T 2, pow_mul, ← mul_pow]; norm_num
      _ ≤ (4 ^ T) ^ 2 * (2 ^ (cnt bad σs i)) ^ 2 := Nat.mul_le_mul_left _ h4
      _ = (4 ^ T * 2 ^ (cnt bad σs i)) ^ 2 := by ring
      _ ≤ (5 ^ T * n) ^ 2 := h3
      _ = 25 ^ T * n ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm T 2, pow_mul]; norm_num
  omega

end


-- ===== from scratch/probe/07aacce1_loo.lean =====
section

lemma loo_slice {n m : ℕ} (Mis : (Fin m → Fin n) → Fin n → Prop) [∀ s i, Decidable (Mis s i)]
    (w : Fin n → ℕ) (j : Fin (m + 1)) :
    ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) * (if Mis (z ∘ j.succAbove) (z j) then 1 else 0) =
      ∑ s : Fin m → Fin n, (∏ t, w (s t)) * ∑ i, (if Mis s i then w i else 0) := by
  let e := Fin.insertNthEquiv (fun _ : Fin (m + 1) => Fin n) j
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h1 : (e (a, s)) j = a := by
    simp [e, Fin.insertNthEquiv]
  have h2 : (e (a, s)) ∘ j.succAbove = s := by
    funext t
    simp [e, Fin.insertNthEquiv]
  rw [Fin.prod_univ_succAbove _ j, h1]
  have h3 : ∀ t, (e (a, s)) (j.succAbove t) = s t := fun t => congrFun h2 t
  simp only [h3, h2]
  split_ifs <;> ring

/-- Leave-one-out averaging: if every `(m+1)`-sequence has at most `k` leave-one-out mistakes,
then for every weighting some `m`-sequence has weighted error at most `k/(m+1)`. -/
theorem loo {n m : ℕ} (Mis : (Fin m → Fin n) → Fin n → Prop) [∀ s i, Decidable (Mis s i)]
    (k : ℕ) (hn : 0 < n)
    (hk : ∀ z : Fin (m + 1) → Fin n,
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card ≤ k)
    (w : Fin n → ℕ) :
    ∃ s : Fin m → Fin n, (m + 1) * ∑ i, (if Mis s i then w i else 0) ≤ k * ∑ i, w i := by
  set P : (Fin m → Fin n) → ℕ := fun s => ∏ t, w (s t) with hP
  set E : (Fin m → Fin n) → ℕ := fun s => ∑ i, (if Mis s i then w i else 0) with hE
  have htot : ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) *
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card =
      (m + 1) * ∑ s, P s * E s := by
    simp only [Finset.card_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [loo_slice Mis w]
    simp [hP, hE, Finset.mul_sum]
  have hle : ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) *
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card ≤
      ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) * k :=
    Finset.sum_le_sum (fun z _ => Nat.mul_le_mul_left _ (hk z))
  have hpow : ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) * k = k * ((∑ i, w i) * ∑ s, P s) := by
    rw [← Finset.sum_mul, ← Fintype.sum_pow, hP, ← Fintype.sum_pow, pow_succ]
    ring
  rw [htot, hpow] at hle
  by_contra hcon
  push Not at hcon
  have hlt : ∀ s, k * ∑ i, w i < (m + 1) * E s := hcon
  rcases Nat.eq_zero_or_pos (∑ s, P s) with h0 | hpos
  · -- then the total weight is zero
    have hw : ∑ i, w i = 0 := by
      rw [hP, ← Fintype.sum_pow] at h0
      exact pow_eq_zero_iff'.mp h0 |>.1
    have hwi : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff.mp hw) i (Finset.mem_univ i)
    have := hlt (fun _ => ⟨0, hn⟩)
    simp [hE, hwi] at this
  · obtain ⟨s₀, -, hs₀⟩ := Finset.sum_pos_iff.mp hpos
    have hstrict : ∑ s, P s * (k * ∑ i, w i) < ∑ s, P s * ((m + 1) * E s) := by
      apply Finset.sum_lt_sum
      · intro s _
        exact Nat.mul_le_mul_left _ (hlt s).le
      · exact ⟨s₀, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_left (hlt s₀) hs₀⟩
    have e1 : ∑ s, P s * (k * ∑ i, w i) = k * ((∑ i, w i) * ∑ s, P s) := by
      rw [← Finset.sum_mul]; ring
    have e2 : ∑ s, P s * ((m + 1) * E s) = (m + 1) * ∑ s, P s * E s := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    rw [e1, e2] at hstrict
    exact absurd hle (not_le.mpr hstrict)

end


-- ===== from scratch/probe/07aacce1_count.lean =====
section

/-- `Σ_{i ≤ d} C(q,i) X^i`, the Natarajan/Sauer bound. -/
def F (X q d : ℕ) : ℕ := ∑ i ∈ Finset.range (d + 1), q.choose i * X ^ i

lemma F_zero (X q : ℕ) : F X q 0 = 1 := by simp [F]

lemma F_succ (X q d : ℕ) : F X (q + 1) (d + 1) = F X q (d + 1) + X * F X q d := by
  unfold F
  rw [Finset.sum_range_succ' _ (d + 1), Finset.sum_range_succ' (fun i => q.choose i * X ^ i) (d + 1)]
  simp only [Nat.choose_succ_succ, Nat.choose_zero_right, pow_zero, mul_one, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  have : ∀ i ∈ Finset.range (d + 1), q.choose i * X ^ (i + 1) = X * (q.choose i * X ^ i) := by
    intro i _; ring
  rw [Finset.sum_congr rfl this]
  ring

lemma bonf {β γ : Type*} [DecidableEq β] [DecidableEq γ] (I : β → Finset γ) (L : Finset β) :
    ∑ a ∈ L, (I a).card ≤ (L.biUnion I).card + ∑ a ∈ L, ∑ b ∈ L.erase a, (I a ∩ I b).card := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert b A hb ih =>
    rw [Finset.sum_insert hb, Finset.biUnion_insert, Finset.sum_insert hb, Finset.erase_insert hb]
    have hu := Finset.card_union_add_card_inter (I b) (A.biUnion I)
    have hint : (I b ∩ A.biUnion I).card ≤ ∑ c ∈ A, (I b ∩ I c).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hmono : ∑ a ∈ A, ∑ c ∈ A.erase a, (I a ∩ I c).card ≤
        ∑ a ∈ A, ∑ c ∈ (insert b A).erase a, (I a ∩ I c).card := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum_of_subset
      intro c hc
      rw [Finset.mem_erase] at hc ⊢
      exact ⟨hc.1, Finset.mem_insert_of_mem hc.2⟩
    omega

variable {α Y : Type*} [DecidableEq α] [DecidableEq Y] [DecidableEq (α → Y)]

/-- `C` N-shatters the coordinate set `R`. -/
def NSh (C : Finset (α → Y)) (R : Finset α) : Prop :=
  ∃ f g : α → Y, (∀ x ∈ R, f x ≠ g x) ∧
    ∀ c : α → Bool, ∃ v ∈ C, ∀ x ∈ R, v x = if c x then f x else g x

lemma nsh_lift (C : Finset (α → Y)) (x : α) (y₀ : Y) (R : Finset α) (hxR : x ∉ R) (a b : Y)
    (hab : a ≠ b)
    (h : NSh (((C.filter (fun v => v x = a)).image (fun v => Function.update v x y₀)) ∩
      ((C.filter (fun v => v x = b)).image (fun v => Function.update v x y₀))) R) :
    NSh C (insert x R) := by
  obtain ⟨f, g, hfg, hc⟩ := h
  refine ⟨Function.update f x a, Function.update g x b, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa using hab
    · have hzx : z ≠ x := fun h => hxR (h ▸ hz)
      simpa [Function.update_of_ne hzx] using hfg z hz
  · intro c
    obtain ⟨v', hv', hpat⟩ := hc c
    rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hv'
    obtain ⟨⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, hv₂e⟩⟩ := hv'
    rw [Finset.mem_filter] at hv₁ hv₂
    have hR : ∀ (w : α → Y), Function.update w x y₀ = Function.update v₁ x y₀ →
        ∀ z ∈ R, w z = if c z then Function.update f x a z else Function.update g x b z := by
      intro w hw z hz
      have hzx : z ≠ x := fun h => hxR (h ▸ hz)
      have := congrFun hw z
      rw [Function.update_of_ne hzx, Function.update_of_ne hzx] at this
      rw [Function.update_of_ne hzx, Function.update_of_ne hzx, this]
      have := hpat z hz
      rwa [Function.update_of_ne hzx] at this
    by_cases hcx : c x = true
    · refine ⟨v₁, hv₁.1, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp [hcx, hv₁.2]
      · exact hR v₁ rfl z hz
    · refine ⟨v₂, hv₂.1, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp [hcx, hv₂.2]
      · exact hR v₂ hv₂e z hz

/-- Natarajan's lemma (Sauer–Shelah form): a class supported on `Q`, with labels in sets of size
at most `p`, that N-shatters no set of size above `d`, has at most `Σ_{i≤d} C(|Q|,i) (p²)^i`
members. -/
theorem count (M : α → Finset Y) (p : ℕ) (hM : ∀ x, (M x).card ≤ p) (y₀ : Y) (Q : Finset α) :
    ∀ (C : Finset (α → Y)) (d : ℕ), (∀ v ∈ C, ∀ x, x ∉ Q → v x = y₀) →
      (∀ v ∈ C, ∀ x ∈ Q, v x ∈ M x) → (∀ R ⊆ Q, NSh C R → R.card ≤ d) →
      C.card ≤ F (p * p) Q.card d := by
  induction Q using Finset.induction_on with
  | empty =>
    intro C d hsupp _ _
    have : ∀ v ∈ C, v = fun _ => y₀ := fun v hv => funext fun x => hsupp v hv x (by simp)
    calc C.card ≤ ({fun _ => y₀} : Finset (α → Y)).card := by
          apply Finset.card_le_card
          intro v hv
          simp [this v hv]
      _ = 1 := by simp
      _ ≤ F (p * p) 0 d := by unfold F; rw [Finset.sum_range_succ']; simp
  | @insert x Q hx ih =>
    intro C d hsupp hmenu hdim
    set up : (α → Y) → (α → Y) := fun v => Function.update v x y₀ with hup
    set I : Y → Finset (α → Y) := fun a => (C.filter (fun v => v x = a)).image up with hI
    set Cm := C.image up with hCm
    have hsuppm : ∀ v ∈ Cm, ∀ z, z ∉ Q → v z = y₀ := by
      intro v hv z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      by_cases hzx : z = x
      · subst hzx; simp [hup]
      · simp only [hup, Function.update_of_ne hzx]
        exact hsupp w hw z (by simp [hzx, hz])
    have hmenum : ∀ v ∈ Cm, ∀ z ∈ Q, v z ∈ M z := by
      intro v hv z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hzx : z ≠ x := fun h => hx (h ▸ hz)
      simp only [hup, Function.update_of_ne hzx]
      exact hmenu w hw z (Finset.mem_insert_of_mem hz)
    have hres : ∀ (D : Finset (α → Y)), D ⊆ Cm → ∀ R ⊆ Q, NSh D R → NSh C R := by
      intro D hD R hR ⟨f, g, hfg, hc⟩
      refine ⟨f, g, hfg, fun c => ?_⟩
      obtain ⟨v', hv', hp⟩ := hc c
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hD hv')
      refine ⟨w, hw, fun z hz => ?_⟩
      have hzx : z ≠ x := fun h => hx (h ▸ hR hz)
      have := hp z hz
      simp only [hup, Function.update_of_ne hzx] at this
      exact this
    have hCmb : Cm.card ≤ F (p * p) Q.card d :=
      ih Cm d hsuppm hmenum (fun R hR hsh => hdim R (hR.trans (Finset.subset_insert _ _))
        (hres Cm le_rfl R hR hsh))
    have hfib : C.card = ∑ a ∈ M x, (C.filter (fun v => v x = a)).card :=
      Finset.card_eq_sum_card_fiberwise (fun v hv => hmenu v hv x (Finset.mem_insert_self _ _))
    have hIcard : ∀ a, (I a).card = (C.filter (fun v => v x = a)).card := by
      intro a
      apply Finset.card_image_of_injOn
      intro v hv w hw hvw
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv hw
      funext z
      by_cases hzx : z = x
      · subst hzx; rw [hv.2, hw.2]
      · have := congrFun hvw z
        simpa [hup, Function.update_of_ne hzx] using this
    have hIsub : ∀ a, I a ⊆ Cm := by
      intro a v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hw).1
    have hB := bonf I (M x)
    have hU : ((M x).biUnion I).card ≤ Cm.card :=
      Finset.card_le_card (Finset.biUnion_subset.mpr (fun a _ => hIsub a))
    rw [Finset.card_insert_of_notMem hx]
    have hsumI : ∑ a ∈ M x, (I a).card = C.card := by
      rw [hfib]; exact Finset.sum_congr rfl (fun a _ => hIcard a)
    cases d with
    | zero =>
      have hempty : ∀ a ∈ M x, ∀ b ∈ (M x).erase a, (I a ∩ I b).card = 0 := by
        intro a _ b hb
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv
        have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
        have hsh : NSh (I a ∩ I b) ∅ := ⟨v, v, by simp, fun _ => ⟨v, hv, by simp⟩⟩
        have := hdim (insert x ∅) (by simp) (nsh_lift C x y₀ ∅ (by simp) a b hab hsh)
        simp at this
      have h0 : ∑ a ∈ M x, ∑ b ∈ (M x).erase a, (I a ∩ I b).card = 0 :=
        Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun b hb => hempty a ha b hb))
      rw [F_zero] at hCmb ⊢
      omega
    | succ d =>
      have hpair : ∀ a ∈ M x, ∀ b ∈ (M x).erase a, (I a ∩ I b).card ≤ F (p * p) Q.card d := by
        intro a _ b hb
        have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
        have hsub : I a ∩ I b ⊆ Cm := Finset.inter_subset_left.trans (hIsub a)
        apply ih (I a ∩ I b) d (fun v hv => hsuppm v (hsub hv)) (fun v hv => hmenum v (hsub hv))
        intro R hR hsh
        have h1 := hdim (insert x R) (Finset.insert_subset_insert x hR)
          (nsh_lift C x y₀ R (fun h => hx (hR h)) a b hab hsh)
        rw [Finset.card_insert_of_notMem (fun h => hx (hR h))] at h1
        omega
      have hS : ∑ a ∈ M x, ∑ b ∈ (M x).erase a, (I a ∩ I b).card ≤
          p * p * F (p * p) Q.card d := by
        calc _ ≤ ∑ a ∈ M x, ∑ b ∈ (M x).erase a, F (p * p) Q.card d :=
              Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hpair a ha b hb))
          _ = ∑ a ∈ M x, ((M x).erase a).card * F (p * p) Q.card d := by simp
          _ ≤ ∑ a ∈ M x, p * F (p * p) Q.card d := by
              apply Finset.sum_le_sum
              intro a _
              exact Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans (hM x))
          _ = (M x).card * (p * F (p * p) Q.card d) := by simp
          _ ≤ p * (p * F (p * p) Q.card d) := Nat.mul_le_mul_right _ (hM x)
          _ = p * p * F (p * p) Q.card d := by ring
      rw [F_succ]
      omega

end


-- ===== from scratch/probe/07aacce1_fbound.lean =====
section

lemma sum_choose_le (q d : ℕ) (hd : d ≤ q) :
    32 ^ (q - d) * ∑ i ∈ Finset.range (d + 1), q.choose i ≤ 33 ^ q := by
  have h33 : (33 : ℕ) ^ q = ∑ i ∈ Finset.range (q + 1), 1 ^ i * 32 ^ (q - i) * q.choose i := by
    rw [show (33 : ℕ) = 1 + 32 by norm_num, add_pow]
    simp only [Nat.cast_id]
  rw [h33, Finset.mul_sum]
  calc ∑ i ∈ Finset.range (d + 1), 32 ^ (q - d) * q.choose i
      ≤ ∑ i ∈ Finset.range (d + 1), 1 ^ i * 32 ^ (q - i) * q.choose i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [one_pow, one_mul]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ ≤ ∑ i ∈ Finset.range (q + 1), 1 ^ i * 32 ^ (q - i) * q.choose i := by
        apply Finset.sum_le_sum_of_subset
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega

lemma F_le (X q d : ℕ) (hX : 1 ≤ X) :
    F X q d ≤ X ^ d * ∑ i ∈ Finset.range (d + 1), q.choose i := by
  unfold F
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_comm (X ^ d)]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hi')

/-- With `q = 35 d ℓ` sample points and `p ≤ 2^ℓ` labels, `F(p², q, d)^4 ≤ 2^q`. -/
theorem Fbound (d ℓ p : ℕ) (_hd : 1 ≤ d) (hℓ : 1 ≤ ℓ) (hp1 : 1 ≤ p) (hp : p ≤ 2 ^ ℓ) :
    F (p * p) (35 * d * ℓ) d ^ 4 ≤ 2 ^ (35 * d * ℓ) := by
  set q := 35 * d * ℓ with hq
  set D := d * ℓ with hD
  have hdD : d ≤ D := Nat.le_mul_of_pos_right d hℓ
  have hqD : q = 35 * D := by rw [hq, hD]; ring
  set S := ∑ i ∈ Finset.range (d + 1), q.choose i with hS
  have h1 : F (p * p) q d ≤ 2 ^ (2 * D) * S := by
    have hpp : p * p ≤ 4 ^ ℓ := by
      calc p * p ≤ 2 ^ ℓ * 2 ^ ℓ := Nat.mul_le_mul hp hp
        _ = 4 ^ ℓ := by rw [← mul_pow]; norm_num
    calc F (p * p) q d ≤ (p * p) ^ d * S := F_le _ _ _ (Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega)))
      _ ≤ (4 ^ ℓ) ^ d * S := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpp d)
      _ = 2 ^ (2 * D) * S := by
        rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, hD]; ring_nf
  have h2 : 32 ^ (q - d) * S ≤ 33 ^ q := sum_choose_le q d (by omega)
  have h33 : (33 : ℕ) ^ 20 ≤ 2 ^ 101 := by norm_num
  have h3 : (33 : ℕ) ^ (4 * q) ≤ 2 ^ (707 * D) := by
    calc (33 : ℕ) ^ (4 * q) = (33 ^ 20) ^ (7 * D) := by rw [← pow_mul, hqD]; ring_nf
      _ ≤ (2 ^ 101) ^ (7 * D) := Nat.pow_le_pow_left h33 _
      _ = 2 ^ (707 * D) := by rw [← pow_mul]; ring_nf
  have h32 : (32 : ℕ) ^ (q - d) = 2 ^ (5 * (q - d)) := by
    rw [pow_mul, show (2 : ℕ) ^ 5 = 32 by norm_num]
  have h4 : F (p * p) q d ^ 4 * 2 ^ (20 * (q - d)) ≤ 2 ^ (715 * D) := by
    calc F (p * p) q d ^ 4 * 2 ^ (20 * (q - d))
        ≤ (2 ^ (2 * D) * S) ^ 4 * 2 ^ (20 * (q - d)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 4)
      _ = 2 ^ (8 * D) * (32 ^ (q - d) * S) ^ 4 := by
          rw [h32, mul_pow, mul_pow, ← pow_mul, ← pow_mul, show 2 * D * 4 = 8 * D by ring,
            show 5 * (q - d) * 4 = 20 * (q - d) by ring]; ring
      _ ≤ 2 ^ (8 * D) * (33 ^ q) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 4)
      _ = 2 ^ (8 * D) * 33 ^ (4 * q) := by rw [← pow_mul, mul_comm q 4]
      _ ≤ 2 ^ (8 * D) * 2 ^ (707 * D) := Nat.mul_le_mul_left _ h3
      _ = 2 ^ (715 * D) := by rw [← pow_add]; ring_nf
  have h5 : 2 ^ (715 * D) ≤ 2 ^ q * 2 ^ (20 * (q - d)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.le_of_mul_le_mul_right (h4.trans h5) (by positivity)

end


-- ===== from scratch/probe/07aacce1_pred.lean =====
section

open Classical

variable {X Y : Type*}

/-- labelings on the finite point set `Q`, realizable by `H` inside the menus, equal to `y₀`
off `Q`. -/
def CQ (H : Set (X → Y)) (μ : X → Set Y) (y₀ : Y) (Q : Finset X) : Set (X → Y) :=
  {v | (∀ x, x ∉ Q → v x = y₀) ∧ ∃ h ∈ H, ∀ x ∈ Q, v x = h x ∧ h x ∈ μ x}

lemma CQ_finite (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    (Q : Finset X) : (CQ H μ y₀ Q).Finite := by
  have hinj : Set.InjOn (fun v : X → Y => fun x : Q => v x) (CQ H μ y₀ Q) := by
    intro v hv w hw hvw
    funext x
    by_cases hx : x ∈ Q
    · exact congrFun hvw ⟨x, hx⟩
    · rw [hv.1 x hx, hw.1 x hx]
  apply Set.Finite.of_finite_image _ hinj
  apply Set.Finite.subset (Set.Finite.pi (t := fun x : Q => μ x) (fun x => hμ x))
  rintro _ ⟨v, ⟨_, h, _, hh⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro x
  rw [(hh x x.2).1]
  exact (hh x x.2).2

noncomputable def CF (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    (Q : Finset X) : Finset (X → Y) :=
  (CQ_finite H μ hμ y₀ Q).toFinset

lemma ori_spec (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    (Q : Finset X) :
    ∃ o : X → (X → Y) → Y,
      (∀ x w w', AgreeOff Q x w w' → o x w = o x w') ∧
      ∀ v ∈ CF H μ hμ y₀ Q, 2 ^ ((Q.filter (fun x => o x v ≠ v x)).card) ≤
        (CF H μ hμ y₀ Q).card := by
  have : Nonempty Y := ⟨y₀⟩
  apply orient
  intro u hu v hv h
  rw [CF, Set.Finite.mem_toFinset] at hu hv
  funext x
  by_cases hx : x ∈ Q
  · exact h x hx
  · rw [hu.1 x hx, hv.1 x hx]

noncomputable def ori (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    (Q : Finset X) : X → (X → Y) → Y :=
  Classical.choose (ori_spec H μ hμ y₀ Q)

/-- the labeling read off a subsample. -/
noncomputable def lab {m : ℕ} (y₀ : Y) (s : Fin m → X × Y) (x : X) : Y :=
  if h : ∃ t, (s t).1 = x then (s h.choose).2 else y₀

noncomputable def pts {m : ℕ} (s : Fin m → X × Y) : Finset X := Finset.univ.image (fun t => (s t).1)

/-- the local one-inclusion predictor built from a block `s`. -/
noncomputable def pred (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    {m : ℕ} (s : Fin m → X × Y) (x : X) : Y :=
  if ∃ t, (s t).1 = x then lab y₀ s x else ori H μ hμ y₀ (insert x (pts s)) x (lab y₀ s)

theorem pred_loo (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    {n m : ℕ} (S : Fin n → X × Y) (hs : X → Y) (hsH : hs ∈ H)
    (hreal : ∀ i, hs (S i).1 = (S i).2) (hmen : ∀ i, (S i).2 ∈ μ (S i).1)
    (z : Fin (m + 1) → Fin n) :
    2 ^ (Finset.univ.filter (fun j : Fin (m + 1) =>
      pred H μ hμ y₀ (fun t => S (z (j.succAbove t))) (S (z j)).1 ≠ (S (z j)).2)).card ≤
      (CF H μ hμ y₀ (pts (fun i => S (z i)))).card := by
  set Qz := pts (fun i => S (z i)) with hQz
  have hmemQ : ∀ i, (S (z i)).1 ∈ Qz := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hQ : ∀ j : Fin (m + 1), insert (S (z j)).1 (pts (fun t => S (z (j.succAbove t)))) = Qz := by
    intro j
    ext y
    simp only [hQz, pts, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨t, rfl⟩)
      · exact ⟨j, rfl⟩
      · exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      by_cases hij : i = j
      · left; rw [hij]
      · right
        obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
        exact ⟨t, by rw [ht]⟩
  set vs : X → Y := fun x => if x ∈ Qz then hs x else y₀ with hvs_def
  have hvs : vs ∈ CF H μ hμ y₀ Qz := by
    rw [CF, Set.Finite.mem_toFinset]
    refine ⟨fun x hx => by simp [vs, hx], hs, hsH, fun x hx => ⟨by simp [vs, hx], ?_⟩⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [hreal]
    exact hmen _
  have hor : ∀ x w w', AgreeOff Qz x w w' → ori H μ hμ y₀ Qz x w = ori H μ hμ y₀ Qz x w' :=
    (Classical.choose_spec (ori_spec H μ hμ y₀ Qz)).1
  have hbd : ∀ v ∈ CF H μ hμ y₀ Qz, 2 ^ ((Qz.filter (fun x => ori H μ hμ y₀ Qz x v ≠ v x)).card) ≤
      (CF H μ hμ y₀ Qz).card :=
    (Classical.choose_spec (ori_spec H μ hμ y₀ Qz)).2
  have hvsx : ∀ i, vs (S (z i)).1 = (S (z i)).2 := by
    intro i
    simp only [vs, if_pos (hmemQ i)]
    exact hreal _
  have key : ∀ j, pred H μ hμ y₀ (fun t => S (z (j.succAbove t))) (S (z j)).1 ≠ (S (z j)).2 →
      (¬ ∃ t, (S (z (j.succAbove t))).1 = (S (z j)).1) ∧
      ori H μ hμ y₀ Qz (S (z j)).1 vs ≠ vs (S (z j)).1 := by
    intro j hj
    have hno : ¬ ∃ t, (S (z (j.succAbove t))).1 = (S (z j)).1 := by
      intro hex
      apply hj
      unfold pred
      rw [if_pos hex]
      unfold lab
      rw [dif_pos hex]
      have ht := hex.choose_spec
      rw [← hreal, ← hreal, ht]
    refine ⟨hno, ?_⟩
    have hpe : pred H μ hμ y₀ (fun t => S (z (j.succAbove t))) (S (z j)).1 =
        ori H μ hμ y₀ Qz (S (z j)).1 (lab y₀ (fun t => S (z (j.succAbove t)))) := by
      unfold pred
      rw [if_neg hno, hQ j]
    have hag : AgreeOff Qz (S (z j)).1 (lab y₀ (fun t => S (z (j.succAbove t)))) vs := by
      intro y hy hyx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      have hij : i ≠ j := fun h => hyx (by rw [h])
      obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hij
      have hex : ∃ t', (S (z (j.succAbove t'))).1 = (S (z (j.succAbove t))).1 := ⟨t, rfl⟩
      unfold lab
      rw [dif_pos hex, hvsx]
      have := hex.choose_spec
      rw [← hreal, ← hreal, this]
    rw [hpe, hor _ _ _ hag] at hj
    rwa [hvsx]
  calc 2 ^ (Finset.univ.filter (fun j : Fin (m + 1) =>
        pred H μ hμ y₀ (fun t => S (z (j.succAbove t))) (S (z j)).1 ≠ (S (z j)).2)).card
      ≤ 2 ^ (Qz.filter (fun x => ori H μ hμ y₀ Qz x vs ≠ vs x)).card := by
        apply Nat.pow_le_pow_right (by norm_num)
        apply Finset.card_le_card_of_injOn (fun j => (S (z j)).1)
        · intro j hj
          have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hmemQ j, (key j hj'.2).2⟩)
        · intro j₁ hj₁ j₂ hj₂ heq
          by_contra hne
          have hj₁' := Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)
          obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
          exact (key j₁ hj₁'.2).1 ⟨t, by rw [ht]; exact heq.symm⟩
    _ ≤ _ := hbd vs hvs

end


-- ===== from scratch/probe/07aacce1_main.lean =====
section

open Classical

variable {X Y : Type*}

lemma F_mono (X' q q' d : ℕ) (h : q ≤ q') : F X' q d ≤ F X' q' d := by
  unfold F
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_right _ (Nat.choose_le_choose i h)

lemma CF_dim (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y)
    (Q : Finset X) (d : ℕ) (hN : MulticlassDS.Compress.natarajanDim H = d) :
    ∀ R ⊆ Q, NSh (CF H μ hμ y₀ Q) R → R.card ≤ d := by
  intro R hRQ ⟨f, g, hfg, hc⟩
  let e := R.equivFin
  let Sq : Fin R.card → X := fun i => (e.symm i).1
  have hsh : MulticlassDS.Compress.NShatters H Sq := by
    refine ⟨fun i => f (Sq i), fun i => g (Sq i), fun i => hfg _ (e.symm i).2, ?_⟩
    intro c
    obtain ⟨v, hv, hpat⟩ := hc (fun x => if hx : x ∈ R then c (e ⟨x, hx⟩) else false)
    rw [CF, Set.Finite.mem_toFinset] at hv
    obtain ⟨-, h, hH, hh⟩ := hv
    show _ ∈ (fun h => h ∘ Sq) '' H
    refine ⟨h, hH, ?_⟩
    funext i
    have hiR : Sq i ∈ R := (e.symm i).2
    have h1 := hpat (Sq i) hiR
    rw [dif_pos hiR] at h1
    have h2 : e ⟨Sq i, hiR⟩ = i := by
      show e (e.symm i) = i
      exact e.apply_symm_apply i
    rw [h2] at h1
    show h (Sq i) = _
    rw [← (hh (Sq i) (hRQ hiR)).1, h1]
  have hle : ((R.card : ℕ) : ℕ∞) ≤ MulticlassDS.Compress.natarajanDim H :=
    le_iSup_of_le R.card (le_iSup_of_le Sq (le_iSup_of_le hsh le_rfl))
  rw [hN] at hle
  exact_mod_cast hle

lemma CF_card (H : Set (X → Y)) (μ : X → Set Y) (hμ : ∀ x, (μ x).Finite) (y₀ : Y) (p : ℕ)
    (hp : ∀ x, (μ x).encard ≤ p) (Q : Finset X) (d : ℕ)
    (hN : MulticlassDS.Compress.natarajanDim H = d) :
    (CF H μ hμ y₀ Q).card ≤ F (p * p) Q.card d := by
  apply count (fun x => (hμ x).toFinset) p _ y₀ Q (CF H μ hμ y₀ Q) d
  · intro v hv x hx
    rw [CF, Set.Finite.mem_toFinset] at hv
    exact hv.1 x hx
  · intro v hv x hx
    rw [CF, Set.Finite.mem_toFinset] at hv
    obtain ⟨-, h, -, hh⟩ := hv
    rw [Set.Finite.mem_toFinset, (hh x hx).1]
    exact (hh x hx).2
  · exact CF_dim H μ hμ y₀ Q d hN
  · intro x
    have := hp x
    rw [(hμ x).encard_eq_coe_toFinset_card] at this
    exact_mod_cast this

end

end L40

open MulticlassDS.Compress in
theorem solution {X Y : Type*} [Nonempty Y] (H : Set (X → Y)) (dN : ℕ)
    (hN : natarajanDim H = dN) (μ : X → Set Y) (p : ℕ) (hμ : IsMenu μ p) (n : ℕ) (hn : 0 < n) :
    ∃ r₂ : ℕ, (r₂ : ℝ) ≤ 10 ^ 3 * dN * Real.logb 2 p * Real.logb 2 (2 * (n : ℝ)) ∧
      ∃ ρ : (Fin r₂ → X × Y) → X → Y, IsMenuCompressionScheme H μ n r₂ ρ := by
  classical
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hμf : ∀ x, (μ x).Finite := fun x => Set.finite_of_encard_le_coe (hμ x)
  by_cases hp : p ≤ 1
  · refine ⟨0, ?_, fun _ x => if h : (μ x).Nonempty then h.some else y₀, ?_⟩
    · have : Real.logb 2 (p : ℝ) = 0 := by
        interval_cases p <;> simp
      rw [this]; simp
    · intro S _ hmen
      refine ⟨fun j => j.elim0, fun j => j.elim0, fun i => ?_⟩
      have hne : (μ (S i).1).Nonempty := ⟨_, hmen i⟩
      show (if h : (μ (S i).1).Nonempty then h.some else y₀) = (S i).2
      rw [dif_pos hne]
      have h1 : (μ (S i).1).encard ≤ 1 := (hμ (S i).1).trans (by exact_mod_cast hp)
      exact Set.encard_le_one_iff.mp h1 _ _ hne.some_mem (hmen i)
  by_cases hd : dN = 0
  · subst hd
    have hsing : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ = h₂ := by
      intro h₁ h₁H h₂ h₂H
      by_contra hne
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
      let Sq : Fin 1 → X := fun _ => x
      have hsh : NShatters H Sq := by
        refine ⟨fun _ => h₁ x, fun _ => h₂ x, fun _ => hx, fun c => ?_⟩
        show _ ∈ (fun h => h ∘ Sq) '' H
        by_cases hc : c 0 = true
        · refine ⟨h₁, h₁H, funext fun i => ?_⟩
          rw [Fin.fin_one_eq_zero i]
          simp [Sq, hc]
        · refine ⟨h₂, h₂H, funext fun i => ?_⟩
          rw [Fin.fin_one_eq_zero i]
          simp [Sq, hc]
      have hle : ((1 : ℕ) : ℕ∞) ≤ natarajanDim H :=
        le_iSup_of_le 1 (le_iSup_of_le Sq (le_iSup_of_le hsh le_rfl))
      rw [hN] at hle
      exact absurd hle (by norm_num)
    refine ⟨0, by simp, fun _ x => if h : H.Nonempty then h.some x else y₀, ?_⟩
    intro S ⟨h, hH, hh⟩ _
    refine ⟨fun j => j.elim0, fun j => j.elim0, fun i => ?_⟩
    show (if h : H.Nonempty then h.some (S i).1 else y₀) = (S i).2
    rw [dif_pos ⟨h, hH⟩, hsing _ (Set.Nonempty.some_mem ⟨h, hH⟩) h hH]
    exact hh i
  -- main case: p ≥ 2, dN ≥ 1
  push Not at hp
  have hd1 : 1 ≤ dN := Nat.one_le_iff_ne_zero.mpr hd
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Nat.clog 2 p := ⟨_, rfl⟩
  have hℓ : 1 ≤ ℓ := hℓdef ▸ Nat.clog_pos (by norm_num) hp
  have hpℓ : p ≤ 2 ^ ℓ := hℓdef ▸ Nat.le_pow_clog (by norm_num) p
  have hpos : 1 ≤ 35 * dN * ℓ := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 35) hd1) hℓ
    omega
  obtain ⟨m, hm1⟩ : ∃ m, m + 1 = 35 * dN * ℓ := ⟨35 * dN * ℓ - 1, by omega⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.log 2 n := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = 6 * (L + 1) := ⟨_, rfl⟩
  let blk : (Fin (m * T) → X × Y) → Fin T → Fin m → X × Y :=
    fun S' t a => S' (finProdFinEquiv (a, t))
  let ρ : (Fin (m * T) → X × Y) → X → Y := fun S' x =>
    if h : ∃ y, T < 2 * (Finset.univ.filter
        (fun t => L40.pred H μ hμf y₀ (blk S' t) x = y)).card then h.choose else y₀
  refine ⟨m * T, ?_, ρ, ?_⟩
  · -- the size bound
    have hlogp : 1 ≤ Real.logb 2 (p : ℝ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
      have h2p : 2 ≤ p := hp
      exact_mod_cast h2p
    have hℓr : (ℓ : ℝ) ≤ 2 * Real.logb 2 (p : ℝ) := by
      have h1 : 2 ^ (ℓ - 1) < p := by
        have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hp
        rw [hℓdef]
        simpa [Nat.pred_eq_sub_one] using this
      have h2 : ((ℓ - 1 : ℕ) : ℝ) < Real.logb 2 (p : ℝ) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]
        exact_mod_cast h1
      have h3 : (ℓ : ℝ) = ((ℓ - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub hℓ]; ring
      linarith
    have hLr : ((L : ℝ) + 1) ≤ Real.logb 2 (2 * (n : ℝ)) := by
      have h1 : 2 ^ L ≤ n := hLdef ▸ Nat.pow_log_le_self 2 (by omega)
      have h2 : (2 : ℝ) ^ (L + 1) ≤ 2 * (n : ℝ) := by
        rw [pow_succ]
        have : ((2 ^ L : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        push_cast at this
        linarith
      have h3 : ((L + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2 * (n : ℝ)) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
        exact h2
      push_cast at h3
      exact h3
    have hmr : (m : ℝ) ≤ 35 * dN * ℓ := by
      have : ((m + 1 : ℕ) : ℝ) = ((35 * dN * ℓ : ℕ) : ℝ) := by rw [hm1]
      push_cast at this
      linarith
    have hdN : (1 : ℝ) ≤ dN := by exact_mod_cast hd1
    have hLnn : (0 : ℝ) ≤ L := by positivity
    push_cast
    calc (m : ℝ) * (T : ℝ) = (m : ℝ) * (6 * ((L : ℝ) + 1)) := by rw [hTdef]; push_cast; ring
      _ ≤ (35 * dN * ℓ) * (6 * ((L : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right hmr; positivity
      _ ≤ (35 * dN * (2 * Real.logb 2 (p : ℝ))) * (6 * Real.logb 2 (2 * (n : ℝ))) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hℓr; positivity
          · linarith
          · positivity
          · have : (0 : ℝ) ≤ Real.logb 2 (p : ℝ) := by linarith
            positivity
      _ = 420 * dN * Real.logb 2 (p : ℝ) * Real.logb 2 (2 * (n : ℝ)) := by ring
      _ ≤ 10 ^ 3 * dN * Real.logb 2 (p : ℝ) * Real.logb 2 (2 * (n : ℝ)) := by
          have h0 : (0 : ℝ) ≤ dN * Real.logb 2 (p : ℝ) * Real.logb 2 (2 * (n : ℝ)) := by
            have : (0 : ℝ) ≤ Real.logb 2 (2 * (n : ℝ)) := by linarith
            have : (0 : ℝ) ≤ Real.logb 2 (p : ℝ) := by linarith
            positivity
          nlinarith
  · -- the scheme
    intro S ⟨hs, hsH, hreal⟩ hmen
    have hk : ∀ z : Fin (m + 1) → Fin n,
        (Finset.univ.filter (fun j : Fin (m + 1) =>
          L40.pred H μ hμf y₀ (fun t => S ((z ∘ j.succAbove) t)) (S (z j)).1 ≠ (S (z j)).2)).card
          ≤ (m + 1) / 4 := by
      intro z
      have h1 := L40.pred_loo H μ hμf y₀ S hs hsH hreal hmen z
      have h2 : (L40.CF H μ hμf y₀ (L40.pts (fun i => S (z i)))).card ≤
          L40.F (p * p) (m + 1) dN :=
        (L40.CF_card H μ hμf y₀ p hμ _ dN hN).trans
          (L40.F_mono _ _ _ _ (Finset.card_image_le.trans (by simp)))
      have h3 := L40.Fbound dN ℓ p hd1 hℓ (by omega) hpℓ
      rw [← hm1] at h3
      set c := (Finset.univ.filter (fun j : Fin (m + 1) =>
          L40.pred H μ hμf y₀ (fun t => S ((z ∘ j.succAbove) t)) (S (z j)).1 ≠ (S (z j)).2)).card
      have h4 : 2 ^ c ≤ L40.F (p * p) (m + 1) dN := h1.trans h2
      have h5 : 2 ^ (4 * c) ≤ 2 ^ (m + 1) := by
        calc 2 ^ (4 * c) = (2 ^ c) ^ 4 := by rw [← pow_mul, mul_comm]
          _ ≤ L40.F (p * p) (m + 1) dN ^ 4 := Nat.pow_le_pow_left h4 4
          _ ≤ 2 ^ (m + 1) := h3
      have h6 : 4 * c ≤ m + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    have hweak : ∀ w : Fin n → ℕ, ∃ θ : Fin m → Fin n, 4 * ∑ i,
        (if L40.pred H μ hμf y₀ (fun t => S (θ t)) (S i).1 ≠ (S i).2 then w i else 0) ≤
          ∑ i, w i := by
      intro w
      obtain ⟨θ, hθ⟩ := L40.loo (fun θ i => L40.pred H μ hμf y₀ (fun t => S (θ t)) (S i).1 ≠ (S i).2)
        ((m + 1) / 4) hn hk w
      refine ⟨θ, ?_⟩
      set E := ∑ i, (if L40.pred H μ hμf y₀ (fun t => S (θ t)) (S i).1 ≠ (S i).2 then w i else 0)
      have hd4 : 4 * ((m + 1) / 4) ≤ m + 1 := Nat.mul_div_le (m + 1) 4
      have : (m + 1) * (4 * E) ≤ (m + 1) * ∑ i, w i := by
        calc (m + 1) * (4 * E) = 4 * ((m + 1) * E) := by ring
          _ ≤ 4 * ((m + 1) / 4 * ∑ i, w i) := Nat.mul_le_mul_left _ hθ
          _ = (4 * ((m + 1) / 4)) * ∑ i, w i := by ring
          _ ≤ (m + 1) * ∑ i, w i := Nat.mul_le_mul_right _ hd4
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have hT : 25 ^ T * n ^ 2 < 32 ^ T := by
      have hn2 : n < 2 ^ (L + 1) := hLdef ▸ Nat.lt_pow_succ_log_self (by norm_num) n
      have hn4 : n ^ 2 < 4 ^ (L + 1) := by
        calc n ^ 2 < (2 ^ (L + 1)) ^ 2 := Nat.pow_lt_pow_left hn2 (by norm_num)
          _ = 4 ^ (L + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      calc 25 ^ T * n ^ 2 < 25 ^ T * 4 ^ (L + 1) := Nat.mul_lt_mul_of_pos_left hn4 (by positivity)
        _ = (25 ^ 6 * 4) ^ (L + 1) := by rw [hTdef, pow_mul, mul_pow]
        _ ≤ (32 ^ 6) ^ (L + 1) := Nat.pow_le_pow_left (by norm_num) _
        _ = 32 ^ T := by rw [hTdef, pow_mul]
    have hboost := L40.boost
      (fun (θ : Fin m → Fin n) (i : Fin n) => L40.pred H μ hμf y₀ (fun t => S (θ t)) (S i).1 ≠ (S i).2) hweak
    obtain ⟨σs, hσs⟩ := hboost T hT
    let S' : Fin (m * T) → X × Y := fun k =>
      S (σs (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1)
    have hblk : ∀ t, blk S' t = fun a => S (σs t a) := by
      intro t
      funext a
      show S (σs (finProdFinEquiv.symm (finProdFinEquiv (a, t))).2
        (finProdFinEquiv.symm (finProdFinEquiv (a, t))).1) = _
      rw [Equiv.symm_apply_apply]
    refine ⟨S', fun k => ⟨_, rfl⟩, fun i => ?_⟩
    have hgood : T < 2 * (Finset.univ.filter
        (fun t => L40.pred H μ hμf y₀ (blk S' t) (S i).1 = (S i).2)).card := by
      simp only [hblk]
      have hb := hσs i
      have hc : L40.cnt (fun θ i => L40.pred H μ hμf y₀ (fun t => S (θ t)) (S i).1 ≠ (S i).2)
          σs i = (Finset.univ.filter (fun t =>
            ¬ L40.pred H μ hμf y₀ (fun a => S (σs t a)) (S i).1 = (S i).2)).card := by
        rw [L40.cnt, Finset.card_filter]
      have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun t : Fin T => L40.pred H μ hμf y₀ (fun a => S (σs t a)) (S i).1 = (S i).2)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      omega
    show ρ S' (S i).1 = (S i).2
    have hex : ∃ y, T < 2 * (Finset.univ.filter
        (fun t => L40.pred H μ hμf y₀ (blk S' t) (S i).1 = y)).card := ⟨_, hgood⟩
    simp only [ρ]
    rw [dif_pos hex]
    have hy := hex.choose_spec
    by_contra hne
    have hsub : Finset.univ.filter (fun t => L40.pred H μ hμf y₀ (blk S' t) (S i).1 = hex.choose) ⊆
        Finset.univ.filter (fun t => ¬ L40.pred H μ hμf y₀ (blk S' t) (S i).1 = (S i).2) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, fun h => hne (ht.2.symm.trans h)⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun t : Fin T => L40.pred H μ hμf y₀ (blk S' t) (S i).1 = (S i).2)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have := Finset.card_le_card hsub
    omega
