-- Prove2me | solution 1 for KarpPapadimitriou.Facial.lt_on_system_iff_basic_dual
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:27:12.728126+00:00
-- url     : https://prove2.me/submissions/08eaa311-58a6-44b8-ba94-cb56a1806d54

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription



namespace KarpPapadimitriou.Facial

open Matrix

lemma kp_between {ι : Type} [Fintype ι] (α l u : ι → ℚ)
    (h : ∀ p q, 0 < α p → α q < 0 → l q ≤ u p) :
    ∃ t : ℚ, (∀ q, α q < 0 → l q ≤ t) ∧ ∀ p, 0 < α p → t ≤ u p := by
  classical
  by_cases hN : (Finset.univ.filter (fun q => α q < 0)).Nonempty
  · obtain ⟨q0, hq0, hmax⟩ := Finset.exists_max_image _ l hN
    refine ⟨l q0, fun q hq => hmax q (by simpa using hq), fun p hp => h p q0 hp (by simpa using hq0)⟩
  · by_cases hP : (Finset.univ.filter (fun p => 0 < α p)).Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image _ u hP
      refine ⟨u p0, fun q hq => ?_, fun p hp => hmin p (by simpa using hp)⟩
      exact absurd ⟨q, by simpa using hq⟩ hN
    · refine ⟨0, fun q hq => ?_, fun p hp => ?_⟩
      · exact absurd ⟨q, by simpa using hq⟩ hN
      · exact absurd ⟨p, by simpa using hp⟩ hP

theorem kp_fm : ∀ (n : ℕ) {ι : Type} [Fintype ι] (a : ι → Fin n → ℚ) (b : ι → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, a i ⬝ᵥ x ≤ b i) →
    ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • a i = 0) ∧ ∑ i, μ i * b i < 0 := by
  intro n
  induction n with
  | zero =>
    intro ι _ a b h
    classical
    have : ∃ i, b i < 0 := by
      by_contra hc
      push_neg at hc
      exact h ⟨0, fun i => by simpa using hc i⟩
    obtain ⟨i0, hi0⟩ := this
    refine ⟨fun i => if i = i0 then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
    · funext j; exact j.elim0
    · simpa using hi0
  | succ n ih =>
    intro ι _ a b h
    classical
    set α : ι → ℚ := fun i => a i 0 with hα
    set a' : ι → Fin n → ℚ := fun i j => a i j.succ with ha'
    have hdot : ∀ i (t : ℚ) (x' : Fin n → ℚ),
        a i ⬝ᵥ (vecCons t x') = α i * t + a' i ⬝ᵥ x' := by
      intro i t x'
      simp only [dotProduct, Fin.sum_univ_succ, hα, ha']
      simp
    let W : ι × ι → ι → ℚ := fun pq l =>
      (if α pq.1 = 0 ∧ pq.1 = pq.2 ∧ l = pq.1 then 1 else 0) +
      (if 0 < α pq.1 ∧ α pq.2 < 0 then
        ((if l = pq.1 then -α pq.2 else 0) + (if l = pq.2 then α pq.1 else 0)) else 0)
    have hW0 : ∀ pq l, 0 ≤ W pq l := by
      intro pq l
      simp only [W]
      split_ifs <;> first | linarith | (try norm_num) <;> nlinarith
    have hW1 : ∀ i, α i = 0 → ∀ v : ι → ℚ, ∑ l, W (i, i) l * v l = v i := by
      intro i hi v
      have : ∀ l, W (i, i) l = if l = i then 1 else 0 := by
        intro l; simp [W, hi]
      simp [this]
    have hW2 : ∀ p q, 0 < α p → α q < 0 → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = -α q * v p + α p * v q := by
      intro p q hp hq v
      have hpq : p ≠ q := fun e => by subst e; linarith
      have : ∀ l, W (p, q) l = (if l = p then -α q else 0) + (if l = q then α p else 0) := by
        intro l; simp [W, hp, hq, hp.ne', hpq]
      simp [this, add_mul, Finset.sum_add_distrib]
    have hW3 : ∀ p q, ¬ (α p = 0 ∧ p = q) → ¬ (0 < α p ∧ α q < 0) → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = 0 := by
      intro p q h1 h2 v
      have : ∀ l, W (p, q) l = 0 := by
        intro l
        have h1' : ¬ (α p = 0 ∧ p = q ∧ l = p) := fun h => h1 ⟨h.1, h.2.1⟩
        simp only [W]; rw [if_neg h1', if_neg h2]; simp
      simp [this]
    have hWα : ∀ pq, ∑ l, W pq l * α l = 0 := by
      intro pq
      obtain ⟨p, q⟩ := pq
      by_cases h1 : α p = 0 ∧ p = q
      · obtain ⟨h1a, rfl⟩ := h1
        rw [hW1 p h1a]; exact h1a
      · by_cases h2 : 0 < α p ∧ α q < 0
        · rw [hW2 p q h2.1 h2.2]; ring
        · exact hW3 p q h1 h2 _
    let a'' : ι × ι → Fin n → ℚ := fun pq => ∑ l, W pq l • a' l
    let b'' : ι × ι → ℚ := fun pq => ∑ l, W pq l * b l
    have hinf : ¬ ∃ x' : Fin n → ℚ, ∀ pq, a'' pq ⬝ᵥ x' ≤ b'' pq := by
      rintro ⟨x', hx'⟩
      have hex := kp_between α (fun q => (b q - a' q ⬝ᵥ x') / α q)
        (fun p => (b p - a' p ⬝ᵥ x') / α p) (by
          intro p q hp hq
          have := hx' (p, q)
          have e1 : a'' (p, q) ⬝ᵥ x' = ∑ l, W (p, q) l * (a' l ⬝ᵥ x') := by
            simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          rw [e1] at this
          have hsum : ∑ l, W (p, q) l * (a' l ⬝ᵥ x') = -α q * (a' p ⬝ᵥ x') + α p * (a' q ⬝ᵥ x') :=
            hW2 p q hp hq _
          have hb : b'' (p, q) = -α q * b p + α p * b q := hW2 p q hp hq _
          rw [hsum, hb] at this
          rw [div_le_iff_of_neg hq, div_mul_eq_mul_div, div_le_iff₀ hp]
          nlinarith)
      obtain ⟨t, htl, htu⟩ := hex
      apply h
      refine ⟨vecCons t x', fun i => ?_⟩
      rw [hdot]
      rcases lt_trichotomy (α i) 0 with hi | hi | hi
      · have := htl i hi
        rw [div_le_iff_of_neg hi] at this
        linarith
      · have := hx' (i, i)
        have e1 : a'' (i, i) ⬝ᵥ x' = a' i ⬝ᵥ x' := by
          simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          exact hW1 i hi (fun l => a' l ⬝ᵥ x')
        have e2 : b'' (i, i) = b i := hW1 i hi b
        rw [e1, e2] at this
        rw [hi]; linarith
      · have := htu i hi
        rw [le_div_iff₀ hi] at this
        linarith
    obtain ⟨μ'', hμ0, hμa, hμb⟩ := ih a'' b'' hinf
    refine ⟨fun l => ∑ pq, μ'' pq * W pq l, fun l => Finset.sum_nonneg (fun pq _ => mul_nonneg (hμ0 pq) (hW0 pq l)), ?_, ?_⟩
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have : ∀ l, a l 0 = α l := fun l => rfl
        simp only [this]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * α l
            = ∑ pq, μ'' pq * ∑ l, W pq l * α l := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by simp [hWα]
      · have := congrFun hμa j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, a''] at this ⊢
        have e : ∀ l, a l j.succ = a' l j := fun l => rfl
        simp only [e]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * a' l j
            = ∑ pq, μ'' pq * ∑ l, W pq l * a' l j := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by rw [← this]
    · calc ∑ l, (∑ pq, μ'' pq * W pq l) * b l
          = ∑ pq, μ'' pq * b'' pq := by
            simp only [b'', Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ < 0 := hμb


lemma kp_dual {n : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin n → ℚ) (g : ι → ℚ) (c : Fin n → ℚ)
    (k : ℚ) (x0 : Fin n → ℚ) (hx0 : ∀ i, a i ⬝ᵥ x0 ≤ g i)
    (hlt : ∀ x : Fin n → ℚ, (∀ i, a i ⬝ᵥ x ≤ g i) → c ⬝ᵥ x < k) :
    ∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i • a i = c ∧ ∑ i, y i * g i < k := by
  classical
  let a2 : Option ι → Fin n → ℚ := fun o => match o with
    | none => -c
    | some i => a i
  let b2 : Option ι → ℚ := fun o => match o with
    | none => -k
    | some i => g i
  have hinf : ¬ ∃ x : Fin n → ℚ, ∀ o, a2 o ⬝ᵥ x ≤ b2 o := by
    rintro ⟨x, hx⟩
    have h1 : ∀ i, a i ⬝ᵥ x ≤ g i := fun i => hx (some i)
    have h2 : -c ⬝ᵥ x ≤ -k := hx none
    have := hlt x h1
    rw [neg_dotProduct] at h2
    linarith
  obtain ⟨μ, hμ0, hμa, hμb⟩ := kp_fm n a2 b2 hinf
  rw [Fintype.sum_option] at hμa hμb
  simp only [a2, b2] at hμa hμb
  have hlam := hμ0 none
  have hsum : ∑ i, μ (some i) * (a i ⬝ᵥ x0) ≤ ∑ i, μ (some i) * g i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx0 i) (hμ0 _)
  have hdot : ∑ i, μ (some i) * (a i ⬝ᵥ x0) = (∑ i, μ (some i) • a i) ⬝ᵥ x0 := by
    rw [sum_dotProduct]; simp [smul_dotProduct]
  rcases hlam.lt_or_eq with hpos | hzero
  · refine ⟨fun i => μ (some i) / μ none, fun i => div_nonneg (hμ0 _) hpos.le, ?_, ?_⟩
    · have : ∑ i, μ (some i) • a i = μ none • c := by
        have : ∑ i, μ (some i) • a i + μ none • -c = 0 := by rw [add_comm]; exact hμa
        rw [smul_neg] at this
        exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact this)
      calc ∑ i, (μ (some i) / μ none) • a i = (μ none)⁻¹ • ∑ i, μ (some i) • a i := by
            rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul, div_eq_inv_mul]
        _ = c := by rw [this, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    · have : ∑ i, μ (some i) * g i + μ none * -k < 0 := by rw [add_comm]; exact hμb
      have h3 : ∑ i, μ (some i) * g i < μ none * k := by linarith
      calc ∑ i, μ (some i) / μ none * g i = (∑ i, μ (some i) * g i) / μ none := by
            rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
        _ < k := by rw [div_lt_iff₀ hpos]; linarith
  · exfalso
    rw [← hzero] at hμa hμb
    simp at hμa hμb
    rw [hμa, zero_dotProduct] at hdot
    linarith

/-- Linear independence relative to the support of `y`. -/
def IndOn {n : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin n → ℚ) (y : ι → ℚ) : Prop :=
  ∀ d : ι → ℚ, (∀ i, y i = 0 → d i = 0) → ∑ i, d i • a i = 0 → d = 0

lemma kp_reduce {n : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin n → ℚ) (g : ι → ℚ) (c : Fin n → ℚ)
    (k : ℚ) (x0 : Fin n → ℚ) (hx0 : ∀ i, a i ⬝ᵥ x0 ≤ g i) :
    ∀ m : ℕ, ∀ y : ι → ℚ, (Finset.univ.filter (fun i => y i ≠ 0)).card = m → (∀ i, 0 ≤ y i) →
      ∑ i, y i • a i = c → ∑ i, y i * g i < k →
      ∃ y' : ι → ℚ, (∀ i, 0 ≤ y' i) ∧ ∑ i, y' i • a i = c ∧ ∑ i, y' i * g i < k ∧ IndOn a y' := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro y hm hy0 hya hyg
  by_cases hind : IndOn a y
  · exact ⟨y, hy0, hya, hyg, hind⟩
  · unfold IndOn at hind
    push_neg at hind
    obtain ⟨d, hd0, hda, hdne⟩ := hind
    have hdot : ∑ i, d i * (a i ⬝ᵥ x0) = 0 := by
      have : (∑ i, d i • a i) ⬝ᵥ x0 = 0 := by rw [hda, zero_dotProduct]
      rw [sum_dotProduct] at this
      simpa [smul_dotProduct] using this
    have hD : ∑ i, d i * g i = ∑ i, d i * (g i - a i ⬝ᵥ x0) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hdot, sub_zero]
    have hs : ∀ i, 0 ≤ g i - a i ⬝ᵥ x0 := fun i => sub_nonneg.2 (hx0 i)
    have hDnn : (∀ i, 0 ≤ d i) → 0 ≤ ∑ i, d i * g i := fun h => by
      rw [hD]; exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (hs i)
    have hDnp : (∀ i, d i ≤ 0) → ∑ i, d i * g i ≤ 0 := fun h => by
      rw [hD]; exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (h i) (hs i)
    have hne : ∃ i, d i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hdne (funext hc)
    -- choose e
    have hex : ∃ e : ι → ℚ, (∀ i, y i = 0 → e i = 0) ∧ ∑ i, e i • a i = 0 ∧
        0 ≤ ∑ i, e i * g i ∧ ∃ i, 0 < e i := by
      by_cases hA : (∃ i, 0 < d i) ∧ 0 ≤ ∑ i, d i * g i
      · exact ⟨d, hd0, hda, hA.2, hA.1⟩
      · by_cases hB : (∃ i, d i < 0) ∧ ∑ i, d i * g i ≤ 0
        · refine ⟨-d, fun i hi => by simp [hd0 i hi], ?_, ?_, ?_⟩
          · simp [hda]
          · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]; linarith [hB.2]
          · obtain ⟨i, hi⟩ := hB.1; exact ⟨i, by simpa using hi⟩
        · exfalso
          obtain ⟨i0, hi0⟩ := hne
          by_cases hpos : ∃ i, 0 < d i
          · have hDneg : ∑ i, d i * g i < 0 := by
              by_contra hc; push_neg at hc; exact hA ⟨hpos, hc⟩
            by_cases hall : ∀ i, 0 ≤ d i
            · linarith [hDnn hall]
            · push_neg at hall
              exact hB ⟨hall, hDneg.le⟩
          · push_neg at hpos
            have hneg : ∃ i, d i < 0 := ⟨i0, lt_of_le_of_ne (hpos i0) hi0⟩
            have := hDnp hpos
            exact hB ⟨hneg, this⟩
    obtain ⟨e, he0, hea, heg, i1, hi1⟩ := hex
    set P := Finset.univ.filter (fun i => 0 < e i) with hP
    have hPne : P.Nonempty := ⟨i1, by simp [hP, hi1]⟩
    obtain ⟨i0, hi0P, hmin⟩ := Finset.exists_min_image P (fun i => y i / e i) hPne
    have hei0 : 0 < e i0 := by simpa [hP] using hi0P
    set t := y i0 / e i0 with ht
    have ht0 : 0 ≤ t := div_nonneg (hy0 _) hei0.le
    have hy'0 : ∀ i, 0 ≤ y i - t * e i := by
      intro i
      by_cases hi : 0 < e i
      · have := hmin i (by simp [hP, hi])
        have : t ≤ y i / e i := this
        rw [le_div_iff₀ hi] at this
        linarith
      · push_neg at hi
        nlinarith [hy0 i, mul_nonneg ht0 (neg_nonneg.2 hi)]
    have hy'a : ∑ i, (y i - t * e i) • a i = c := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hea, smul_zero, sub_zero]
      exact hya
    have hy'g : ∑ i, (y i - t * e i) * g i < k := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      nlinarith [mul_nonneg ht0 heg]
    have hyi0 : y i0 ≠ 0 := fun h0 => by have := he0 i0 h0; linarith
    have hy'i0 : y i0 - t * e i0 = 0 := by
      rw [ht]; field_simp; ring
    have hsub : (Finset.univ.filter (fun i => y i - t * e i ≠ 0)) ⊂ (Finset.univ.filter (fun i => y i ≠ 0)) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i0, by simp [hyi0], by simp [hy'i0]⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro h0; apply hi; rw [h0, he0 i h0]; ring
    exact ih _ (hm ▸ Finset.card_lt_card hsub) (fun i => y i - t * e i) rfl hy'0 hy'a hy'g

lemma kp_span {n : ℕ} {ι : Type} (a : ι → Fin n → ℚ)
    (hspan : ∀ d : Fin n → ℚ, (∀ i, a i ⬝ᵥ d = 0) → d = 0) :
    Submodule.span ℚ (Set.range a) = ⊤ := by
  by_contra hne
  have hlt : Submodule.span ℚ (Set.range a) < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set d : Fin n → ℚ := fun j => f (fun l => if j = l then 1 else 0) with hd
  have hfx : ∀ x, f x = x ⬝ᵥ d := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [dotProduct, hd]
  have : d = 0 := by
    apply hspan
    intro i
    have h1 : a i ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨i, rfl⟩)
    rw [LinearMap.mem_ker, hfx] at h1
    exact h1
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx, this]; simp

lemma kp_basic {n : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin n → ℚ) (g : ι → ℚ) (c : Fin n → ℚ)
    (k : ℚ) (y : ι → ℚ) (hy0 : ∀ i, 0 ≤ y i) (hya : ∑ i, y i • a i = c)
    (hyg : ∑ i, y i * g i < k) (hind : IndOn a y)
    (hspan : ∀ d : Fin n → ℚ, (∀ i, a i ⬝ᵥ d = 0) → d = 0) :
    ∃ (B : Fin n → ι) (y' : Fin n → ℚ), LinearIndependent ℚ (fun j => a (B j)) ∧
      (∀ j, 0 ≤ y' j) ∧ (∑ j, y' j • a (B j) = c) ∧ ∑ j, y' j * g (B j) < k := by
  classical
  set S : Set ι := {i | y i ≠ 0} with hS
  have hSli : LinearIndepOn ℚ a S := by
    rw [LinearIndepOn, Fintype.linearIndependent_iff]
    intro f hf i
    let d : ι → ℚ := fun j => if h : j ∈ S then f ⟨j, h⟩ else 0
    have hd0 : ∀ j, y j = 0 → d j = 0 := by
      intro j hj
      have : j ∉ S := by simpa [hS] using hj
      simp [d, this]
    have hdsum : ∑ j, d j • a j = 0 := by
      rw [← hf]
      have : ∑ j : ι, d j • a j = ∑ j ∈ Finset.univ.filter (fun j => j ∈ S), d j • a j := by
        rw [Finset.sum_filter_of_ne]
        intro j _ hne
        by_contra hjS
        apply hne
        simp [d, hjS]
      rw [this, Finset.sum_subtype (Finset.univ.filter (fun j => j ∈ S)) (p := fun j => j ∈ S) (by simp)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [d, j.2]
    have := hind d hd0 hdsum
    have h2 := congrFun this i.1
    simpa [d, i.2] using h2
  obtain ⟨b, -, hSb, hspanb, hlib⟩ := exists_linearIndepOn_extension (K := ℚ) (v := a) hSli
    (Set.subset_univ S)
  have : Fintype b := Fintype.ofFinite b
  have hli : LinearIndependent ℚ (fun i : b => a i) := hlib
  have hspan_top : Submodule.span ℚ (Set.range (fun i : b => a i)) = ⊤ := by
    rw [eq_top_iff, ← kp_span a hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := hspanb ⟨i, Set.mem_univ i, rfl⟩
    have e : Set.range (fun i : b => a i) = a '' b := by ext; simp
    rw [e]; exact this
  have hcard : Fintype.card b = n := by
    have h1 := finrank_span_eq_card hli
    rw [hspan_top, finrank_top] at h1
    simpa using h1.symm
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hsupp : ∀ i, i ∉ b → y i = 0 := by
    intro i hi
    by_contra h
    exact hi (hSb h)
  have hsum : ∀ {M : Type} [AddCommMonoid M] (F : ι → M), (∀ i, i ∉ b → F i = 0) →
      ∑ j : Fin n, F (e j) = ∑ i, F i := by
    intro M _ F hF
    rw [show (∑ j : Fin n, F (e j)) = ∑ i : b, F i from Equiv.sum_comp e (fun i : b => F i)]
    have h1 : ∑ i, F i = ∑ i ∈ Finset.univ.filter (fun j => j ∈ b), F i := by
      rw [Finset.sum_filter_of_ne]
      intro j _ hne
      by_contra hjb
      exact hne (hF j hjb)
    rw [h1, Finset.sum_subtype (Finset.univ.filter (fun j => j ∈ b)) (p := fun j => j ∈ b) (by simp)]
  refine ⟨fun j => (e j).1, fun j => y (e j).1, ?_, fun j => hy0 _, ?_, ?_⟩
  · have := hli.comp e e.injective
    exact this
  · rw [hsum (fun i => y i • a i) (fun i hi => by simp [hsupp i hi])]
    exact hya
  · rw [hsum (fun i => y i * g i) (fun i hi => by simp [hsupp i hi])]
    exact hyg

lemma kp_hull_nonneg (C : COP) (z : List Bool) (hz : z ∈ C.L) :
    ∀ x ∈ hull C z, ∀ j, 0 ≤ x j := by
  have hconv : Convex ℚ {x : Fin (C.n z) → ℚ | ∀ j, 0 ≤ x j} := by
    intro x hx y hy a b ha hb hab j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
  have hsub : (fun x : Fin (C.n z) → ℤ => fun j => (x j : ℚ)) '' C.S z ⊆
      {x : Fin (C.n z) → ℚ | ∀ j, 0 ≤ x j} := by
    rintro _ ⟨x, hx, rfl⟩ j
    show (0 : ℚ) ≤ (x j : ℚ)
    exact_mod_cast C.S_nonneg z hz x hx j
  intro x hx
  exact convexHull_min hsub hconv hx

lemma kp_rows_finite (C : COP) (F : Triples C) (hs : IsSmall C F) (z : List Bool) :
    {fg : (Fin (C.n z) → ℤ) × ℤ |
        (⟨z, fg⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F}.Finite := by
  obtain ⟨k, hk⟩ := hs
  set B : ℤ := (2 : ℤ) ^ ((z.length + C.n z) ^ k + k) with hB
  have hfin : (Set.Icc (fun _ : Fin (C.n z) => -B) (fun _ => B) ×ˢ Set.Icc (-B) B :
      Set ((Fin (C.n z) → ℤ) × ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine hfin.subset ?_
  intro fg hfg
  have h := hk _ hfg
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_, ?_⟩
  · have := (abs_le.1 (h.1 i)).1; simpa using this
  · have := (abs_le.1 (h.1 i)).2; simpa using this
  · exact (abs_le.1 h.2).1
  · exact (abs_le.1 h.2).2

theorem lt_on_system_core (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (z : List Bool) (hz : z ∈ C.L) (hS : (C.S z).Nonempty)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∀ x : Fin (C.n z) → ℚ,
        (∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
            (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
              (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)) →
          (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)) ↔
      ∃ (fm : Matrix (Fin (C.n z)) (Fin (C.n z)) ℤ) (g : Fin (C.n z) → ℤ),
        (∀ i, (⟨z, (fm i, g i)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F) ∧
          fm.det ≠ 0 ∧
          ∃ y : Fin (C.n z) → ℚ,
            Matrix.vecMul y (fm.map (fun a : ℤ => (a : ℚ))) = (fun j => (c j : ℚ)) ∧
              0 ≤ y ∧ y ⬝ᵥ (fun i => (g i : ℚ)) < (k : ℚ) := by
  classical
  constructor
  · intro hlt
    set R : Set ((Fin (C.n z) → ℤ) × ℤ) := {fg | (⟨z, fg⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F} with hR
    have hfin : R.Finite := kp_rows_finite C F hs z
    have : Fintype R := hfin.fintype
    let a : R → Fin (C.n z) → ℚ := fun i j => (i.1.1 j : ℚ)
    let g : R → ℚ := fun i => (i.1.2 : ℚ)
    let cq : Fin (C.n z) → ℚ := fun j => (c j : ℚ)
    obtain ⟨x, hxS⟩ := hS
    let x0 : Fin (C.n z) → ℚ := fun j => (x j : ℚ)
    have hx0mem : x0 ∈ hull C z := subset_convexHull ℚ _ ⟨x, hxS, rfl⟩
    have hx0 : ∀ i, a i ⬝ᵥ x0 ≤ g i := by
      intro i
      exact (hF.2 z hz x0).1 hx0mem i.1.1 i.1.2 i.2
    have hlt' : ∀ x : Fin (C.n z) → ℚ, (∀ i, a i ⬝ᵥ x ≤ g i) → cq ⬝ᵥ x < k := by
      intro x hx
      exact hlt x (fun f g hm => hx ⟨(f, g), hm⟩)
    have hspan : ∀ d : Fin (C.n z) → ℚ, (∀ i, a i ⬝ᵥ d = 0) → d = 0 := by
      intro d hd
      funext j
      by_contra hdj
      set t : ℚ := -(x0 j + 1) / d j with ht
      have hmem : (x0 + t • d) ∈ hull C z := by
        rw [hF.2 z hz]
        intro f g hm
        have h1 := (hF.2 z hz x0).1 hx0mem f g hm
        have h2 := hd ⟨(f, g), hm⟩
        simp only [a] at h2
        rw [dotProduct_add, dotProduct_smul, h2]
        simpa using h1
      have := kp_hull_nonneg C z hz _ hmem j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht] at this
      rw [div_mul_cancel₀ _ hdj] at this
      linarith
    obtain ⟨y, hy0, hya, hyg⟩ := kp_dual a g cq k x0 hx0 hlt'
    obtain ⟨y1, hy10, hy1a, hy1g, hy1i⟩ := kp_reduce a g cq k x0 hx0 _ y rfl hy0 hya hyg
    obtain ⟨B, y2, hli, hy20, hy2a, hy2g⟩ := kp_basic a g cq k y1 hy10 hy1a hy1g hy1i hspan
    let fm : Matrix (Fin (C.n z)) (Fin (C.n z)) ℤ := Matrix.of fun i j => (B i).1.1 j
    refine ⟨fm, fun i => (B i).1.2, fun i => (B i).2, ?_, y2, ?_, hy20, ?_⟩
    · intro hdet
      have h1 : (fm.map (fun a : ℤ => (a : ℚ))).det = 0 := by
        have := RingHom.map_det (Int.castRingHom ℚ) fm
        rw [hdet] at this
        simpa using this.symm
      have h2 : LinearIndependent ℚ (fm.map (fun a : ℤ => (a : ℚ))).row := hli
      rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at h2
      rw [h1] at h2
      exact not_isUnit_zero h2
    · funext j
      have := congrFun hy2a j
      simpa [Matrix.vecMul, dotProduct, a, fm, cq] using this
    · simpa [dotProduct, g] using hy2g
  · rintro ⟨fm, g, hmem, -, y, hy, hy0, hyg⟩ x hx
    have hc : (fun j => (c j : ℚ)) ⬝ᵥ x = y ⬝ᵥ ((fm.map (fun a : ℤ => (a : ℚ))) *ᵥ x) := by
      rw [← hy, Matrix.dotProduct_mulVec]
    rw [hc]
    refine lt_of_le_of_lt ?_ hyg
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hy0 i)
    have := hx (fm i) (g i) (hmem i)
    simpa [Matrix.mulVec, dotProduct] using this

end KarpPapadimitriou.Facial

open KarpPapadimitriou.Facial


theorem solution (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (z : List Bool) (hz : z ∈ C.L) (hS : (C.S z).Nonempty)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∀ x : Fin (C.n z) → ℚ,
        (∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
            (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
              (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)) →
          (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)) ↔
      ∃ (fm : Matrix (Fin (C.n z)) (Fin (C.n z)) ℤ) (g : Fin (C.n z) → ℤ),
        (∀ i, (⟨z, (fm i, g i)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F) ∧
          fm.det ≠ 0 ∧
          ∃ y : Fin (C.n z) → ℚ,
            Matrix.vecMul y (fm.map (fun a : ℤ => (a : ℚ))) = (fun j => (c j : ℚ)) ∧
              0 ≤ y ∧ y ⬝ᵥ (fun i => (g i : ℚ)) < (k : ℚ) := by
  exact lt_on_system_core C F hF hs z hz hS c k
