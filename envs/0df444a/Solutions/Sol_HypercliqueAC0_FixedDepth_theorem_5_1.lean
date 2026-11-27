-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:31:55.104268+00:00
-- url     : https://prove2.me/submissions/733f9644-733b-4079-b949-ebbc4100daaf

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_5
import Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_6

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
open Filter Topology

/-! ### The planted restriction and the output gate -/

lemma T51_rho_le {m r : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m))
    (z : FreeEdge G (complete r A) → Bool) (e : Edge m r)
    (he : rho G (complete r A) z e = true) : plant G A e = true := by
  unfold rho at he
  unfold plant
  split_ifs at he with h1
  · have : e.val ⊆ A := by
      have := h1.1
      simp [complete] at this
      exact this
    simp [this]
  · simp [he]

lemma T51_hc_iff {m r ℓ : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m)) (hA : A.card = ℓ)
    (hgood : plantedGood ℓ A G) (z : FreeEdge G (complete r A) → Bool) :
    hyperclique m r ℓ (rho G (complete r A) z) = true ↔ ∀ e, z e = true := by
  constructor
  · intro hc e
    unfold hyperclique at hc
    obtain ⟨Q, hQ, hQe⟩ := of_decide_eq_true hc
    have hQA : Q = A := hgood.1 Q hQ (fun e he => T51_rho_le G A z e (hQe e he))
    have he1 : e.val.val ⊆ A := by
      have := e.2.1
      simp [complete] at this
      exact this
    have := hQe e.val (hQA ▸ he1)
    unfold rho at this
    rw [dif_pos e.2] at this
    exact this
  · intro hz
    unfold hyperclique
    apply decide_eq_true
    refine ⟨A, hA, fun e he => ?_⟩
    unfold rho
    split_ifs with h1
    · exact hz _
    · have hmem : e ∈ (complete r A).edges := by simp [complete, he]
      have : ¬ G e = false := fun h => h1 ⟨hmem, h⟩
      simpa using this

lemma T51_coeff {X : Type} [Fintype X] (f : (X → Bool) → ℝ)
    (hf : ∀ z, f z = if (∀ e, z e = true) then 1 else 0) :
    multilinearCoeff f Finset.univ = 1 := by
  unfold multilinearCoeff
  rw [Finset.sum_eq_single (Finset.univ : Finset X)]
  · rw [hf]
    simp [indicator]
  · intro T _ hT
    rw [hf]
    have : ¬ ∀ e, indicator T e = true := by
      intro h
      apply hT
      ext e
      have := h e
      simp [indicator] at this
      simp [this]
    rw [if_neg this, mul_zero]
  · intro h
    exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

lemma T51_rho_congr {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r) (v : Edge m r)
    (z z' : FreeEdge G H → Bool) (h : ∀ e : FreeEdge G H, e.val = v → z e = z' e) :
    rho G H z v = rho G H z' v := by
  unfold rho
  split_ifs with h1
  · exact h _ rfl
  · rfl

/-- Two distinct missing edges of `K_A`. -/
lemma T51_two_free {m r ℓ : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m)) (hA : A.card = ℓ)
    (hgood : plantedGood ℓ A G) (hrl : r < ℓ) :
    ∃ e1 e2 : FreeEdge G (complete r A), e1 ≠ e2 := by
  have hpos : 0 < A.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  obtain ⟨e1, he1A, -, he1G⟩ := hgood.2 u hu
  have : ¬ A ⊆ e1.val := by
    intro hsub
    have := Finset.card_le_card hsub
    rw [e1.2] at this
    omega
  obtain ⟨w, hwA, hwe⟩ := Finset.not_subset.mp this
  obtain ⟨e2, he2A, hwe2, he2G⟩ := hgood.2 w hwA
  refine ⟨⟨e1, by simp [complete, he1A], he1G⟩, ⟨e2, by simp [complete, he2A], he2G⟩, ?_⟩
  intro heq
  have : e1 = e2 := congrArg Subtype.val heq
  subst this
  exact hwe hwe2

lemma T51_output_gate {m r ℓ : ℕ} (C : MantriCVQ.ACCircuit (Edge m r))
    (hC : ∀ x, C.eval x = hyperclique m r ℓ x)
    (G : Edge m r → Bool) (A : Finset (Fin m)) (hA : A.card = ℓ)
    (hgood : plantedGood ℓ A G) (hrl : r < ℓ) :
    ∃ i, C.output = .gate i := by
  obtain ⟨e1, e2, hne⟩ := T51_two_free G A hA hgood hrl
  have hall : hyperclique m r ℓ (rho G (complete r A) (fun _ => true)) = true :=
    (T51_hc_iff G A hA hgood _).2 (fun _ => rfl)
  have h1 : hyperclique m r ℓ (rho G (complete r A) (fun e => decide (e ≠ e1))) = false := by
    by_contra hc
    have := (T51_hc_iff G A hA hgood _).1 (by simpa using hc) e1
    simp at this
  have h2 : hyperclique m r ℓ (rho G (complete r A) (fun e => decide (e ≠ e2))) = false := by
    by_contra hc
    have := (T51_hc_iff G A hA hgood _).1 (by simpa using hc) e2
    simp at this
  cases hout : C.output with
  | gate i => exact ⟨i, rfl⟩
  | const b =>
    exfalso
    have ha := hC (rho G (complete r A) (fun _ => true))
    have hb := hC (rho G (complete r A) (fun e => decide (e ≠ e1)))
    simp only [MantriCVQ.ACCircuit.eval, hout, MantriCVQ.Src.eval] at ha hb
    rw [hall] at ha
    rw [h1] at hb
    rw [ha] at hb
    exact Bool.noConfusion hb
  | lit v b =>
    exfalso
    have ha := hC (rho G (complete r A) (fun _ => true))
    have hb := hC (rho G (complete r A) (fun e => decide (e ≠ e1)))
    have hc := hC (rho G (complete r A) (fun e => decide (e ≠ e2)))
    simp only [MantriCVQ.ACCircuit.eval, hout, MantriCVQ.Src.eval] at ha hb hc
    rw [hall] at ha
    rw [h1] at hb
    rw [h2] at hc
    by_cases hv : e1.val = v
    · have : rho G (complete r A) (fun e => decide (e ≠ e2)) v =
          rho G (complete r A) (fun _ => true) v := by
        apply T51_rho_congr
        intro e he
        have : e ≠ e2 := by
          intro h; apply hne; apply Subtype.ext; rw [hv, ← he, h]
        simp [this]
      rw [this, ha] at hc
      exact Bool.noConfusion hc
    · have : rho G (complete r A) (fun e => decide (e ≠ e1)) v =
          rho G (complete r A) (fun _ => true) v := by
        apply T51_rho_congr
        intro e he
        have : e ≠ e1 := by
          intro h; apply hv; rw [← he, h]
        simp [this]
      rw [this, ha] at hb
      exact Bool.noConfusion hb

lemma T51_gate_eval {X : Type} (C : MantriCVQ.ACCircuit X) (i : ℕ) (hout : C.output = .gate i) :
    (∀ x, gateValue C ⟨i, C.wf_output i hout⟩ x = C.eval x) ∧
      gateDepth C ⟨i, C.wf_output i hout⟩ = C.depth := by
  constructor
  · intro x
    simp only [gateValue, gateValues, MantriCVQ.ACCircuit.eval, hout, MantriCVQ.Src.eval]
  · simp only [gateDepth, gateDepths, MantriCVQ.ACCircuit.depth, hout, MantriCVQ.Src.depth]

/-- On the good planted event, the output gate has a monomial touching all of `A`. -/
lemma T51_event {m r ℓ h s : ℕ} (C : MantriCVQ.ACCircuit (Edge m r)) (hd : C.depth ≤ h)
    (hC : ∀ x, C.eval x = hyperclique m r ℓ x)
    (G : Edge m r → Bool) (A : Finset (Fin m)) (hA : A.card = ℓ)
    (hgood : plantedGood ℓ A G) (hrl : r < ℓ) (hsl : s < ℓ) :
    ∃ k : Fin C.gates.length, gateDepth C k ≤ h ∧
      hasLargeMonomial G (complete r A) (boolReal (gateValue C k)) s := by
  obtain ⟨i, hout⟩ := T51_output_gate C hC G A hA hgood hrl
  obtain ⟨hv, hdep⟩ := T51_gate_eval C i hout
  refine ⟨⟨i, C.wf_output i hout⟩, hdep ▸ hd, Finset.univ, ?_, ?_⟩
  · unfold isMonomial
    rw [T51_coeff]
    · exact one_ne_zero
    · intro z
      simp only [restricted, boolReal, hv, hC]
      by_cases hz : ∀ e, z e = true
      · rw [if_pos ((T51_hc_iff G A hA hgood z).2 hz), if_pos hz]
      · rw [if_neg (fun h => hz ((T51_hc_iff G A hA hgood z).1 h)), if_neg hz]
  · have hsub : A ⊆ verticesOf ((Finset.univ : Finset (FreeEdge G (complete r A))).image
        (fun e => e.val)) := by
      intro u hu
      obtain ⟨e, heA, hue, heG⟩ := hgood.2 u hu
      unfold verticesOf
      rw [Finset.mem_biUnion]
      exact ⟨e, Finset.mem_image.mpr ⟨⟨e, by simp [complete, heA], heG⟩, Finset.mem_univ _, rfl⟩,
        hue⟩
    have := Finset.card_le_card hsub
    omega


/-! ### Probability monotonicity -/

lemma T51_weight_nonneg {X : Type} [Fintype X] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : X → Bool) : 0 ≤ weight p x := by
  unfold weight OAI.Problem313.BiasedFourier.weight
  apply Finset.prod_nonneg
  intro i _
  unfold OAI.Problem313.BiasedFourier.scalarWeight
  split_ifs <;> linarith

lemma T51_prob_mono {X : Type} [Fintype X] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : (X → Bool) → Prop) (hEF : ∀ x, E x → F x) : probability p E ≤ probability p F := by
  unfold probability expectation
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (T51_weight_nonneg p hp0 hp1 x)
  show (if E x then (1:ℝ) else 0) ≤ (if F x then (1:ℝ) else 0)
  by_cases hE : E x
  · rw [if_pos hE, if_pos (hEF x hE)]
  · rw [if_neg hE]; split_ifs <;> norm_num

lemma T51_joint_ge {v m r : ℕ} (hvm : v ≤ m) (p : ℝ) (q : ℝ)
    (event : (Fin v ↪ Fin m) → (Edge m r → Bool) → Prop)
    (h : ∀ ι, q ≤ probability p (event ι)) : q ≤ jointProbability p event := by
  unfold jointProbability
  have hne : Nonempty (Fin v ↪ Fin m) := ⟨Fin.castLEEmb hvm⟩
  have hcard : (0 : ℝ) < Fintype.card (Fin v ↪ Fin m) := by
    exact_mod_cast Fintype.card_pos
  have hsum : (Fintype.card (Fin v ↪ Fin m) : ℝ) * q ≤ ∑ ι, probability p (event ι) := by
    have := Finset.sum_le_sum (fun ι (_ : ι ∈ (Finset.univ : Finset (Fin v ↪ Fin m))) => h ι)
    simpa [Finset.sum_const, Finset.card_univ] using this
  rw [inv_mul_eq_div, le_div_iff₀ hcard]
  linarith


/-! ### Binomial ratios and the choice of constants -/

lemma T51_choose_nat (s ℓ : ℕ) (hsl : s ≤ ℓ) :
    ∀ k : ℕ, s.choose k * ℓ ^ k ≤ ℓ.choose k * s ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (s - k) * ℓ ≤ (ℓ - k) * s := by
      rcases le_or_gt k s with hks | hks
      · obtain ⟨t, rfl⟩ : ∃ t, s = k + t := ⟨s - k, by omega⟩
        obtain ⟨u, rfl⟩ : ∃ u, ℓ = k + t + u := ⟨ℓ - (k + t), by omega⟩
        rw [show k + t - k = t by omega, show k + t + u - k = t + u by omega]
        nlinarith [Nat.zero_le (u * k)]
      · rw [show s - k = 0 by omega]; simp
    have h1 := Nat.choose_succ_right_eq s k
    have h2 := Nat.choose_succ_right_eq ℓ k
    have key : s.choose (k + 1) * ℓ ^ (k + 1) * (k + 1) ≤ ℓ.choose (k + 1) * s ^ (k + 1) * (k + 1) := by
      calc s.choose (k + 1) * ℓ ^ (k + 1) * (k + 1)
          = (s.choose (k + 1) * (k + 1)) * ℓ ^ k * ℓ := by rw [pow_succ]; ring
        _ = (s.choose k * ℓ ^ k) * ((s - k) * ℓ) := by rw [h1]; ring
        _ ≤ (ℓ.choose k * s ^ k) * ((ℓ - k) * s) := Nat.mul_le_mul ih hk
        _ = (ℓ.choose (k + 1) * (k + 1)) * s ^ k * s := by rw [h2]; ring
        _ = ℓ.choose (k + 1) * s ^ (k + 1) * (k + 1) := by rw [pow_succ]; ring
    exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos k)

lemma T51_choose_real (s ℓ k : ℕ) (hsl : s ≤ ℓ) (γ : ℝ)
    (hs : (s : ℝ) ≤ γ * ℓ) : (s.choose k : ℝ) ≤ (ℓ.choose k : ℝ) * γ ^ k := by
  rcases Nat.eq_zero_or_pos ℓ with hl | hl
  · subst hl
    have : s = 0 := by omega
    subst this
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · simp [Nat.choose_eq_zero_of_lt hk]
  · have h := T51_choose_nat s ℓ hsl k
    have hR : (s.choose k : ℝ) * (ℓ : ℝ) ^ k ≤ (ℓ.choose k : ℝ) * (s : ℝ) ^ k := by
      exact_mod_cast h
    have hlpos : (0 : ℝ) < (ℓ : ℝ) ^ k := by positivity
    have hsk : (s : ℝ) ^ k ≤ (γ * ℓ) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hs k
    have : (s.choose k : ℝ) * (ℓ : ℝ) ^ k ≤ ((ℓ.choose k : ℝ) * γ ^ k) * (ℓ : ℝ) ^ k := by
      calc _ ≤ (ℓ.choose k : ℝ) * (s : ℝ) ^ k := hR
        _ ≤ (ℓ.choose k : ℝ) * (γ * ℓ) ^ k :=
            mul_le_mul_of_nonneg_left hsk (Nat.cast_nonneg _)
        _ = _ := by rw [mul_pow]; ring
    exact le_of_mul_le_mul_right this hlpos

/-- `(x^(1/(r-1)))^(r-1) = x`. -/
lemma T51_rpow_pow (r : ℕ) (hr : 2 ≤ r) (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / ((r : ℝ) - 1))) ^ (r - 1) = x := by
  have : (1 / ((r : ℝ) - 1)) = (((r - 1 : ℕ) : ℝ))⁻¹ := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this]
  exact Real.rpow_inv_natCast_pow hx (by omega)

/-- The value of the optimization at `ξ = 0`. -/
lemma T51_c_identity (r : ℕ) (hr : 2 ≤ r) (a : ℝ) (ha : 0 < a) :
    a * (a / r) ^ (1 / ((r : ℝ) - 1)) - ((a / r) ^ (1 / ((r : ℝ) - 1))) ^ r =
      c r * a ^ ((r : ℝ) / ((r : ℝ) - 1)) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hr0 : (0 : ℝ) < r := by linarith
  set g := (a / r) ^ (1 / ((r : ℝ) - 1)) with hg
  have hgr : g ^ r = g * (a / r) := by
    have : g ^ r = g * g ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, hg, T51_rpow_pow r hr (a / r) (by positivity)]
  rw [hgr]
  unfold c
  have e1 : g = a ^ (1 / ((r : ℝ) - 1)) * ((r : ℝ) ^ (1 / ((r : ℝ) - 1)))⁻¹ := by
    rw [hg, Real.div_rpow ha.le hr0.le, div_eq_mul_inv]
  have e2 : (r : ℝ) ^ (-(1 : ℝ) / ((r : ℝ) - 1)) = ((r : ℝ) ^ (1 / ((r : ℝ) - 1)))⁻¹ := by
    rw [neg_div, Real.rpow_neg hr0.le]
  have e3 : a ^ ((r : ℝ) / ((r : ℝ) - 1)) = a * a ^ (1 / ((r : ℝ) - 1)) := by
    have : (r : ℝ) / ((r : ℝ) - 1) = 1 + 1 / ((r : ℝ) - 1) := by
      have hne : (r : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [this, Real.rpow_add ha, Real.rpow_one]
  rw [e2, e3, e1]
  field_simp

lemma T51_params (r : ℕ) (hr : 2 ≤ r) (a η : ℝ) (ha : 0 < a) (ha1 : a < 1) (hη : 0 < η) :
    ∃ ξ γ : ℝ, 0 < ξ ∧ ξ < a ∧ 0 < γ ∧ γ < 1 ∧ (1 + ξ) * r * γ ^ (r - 1) = a - ξ ∧
      c r * a ^ ((r : ℝ) / ((r : ℝ) - 1)) - η / 4 < (a - ξ) * γ - (1 + ξ) * γ ^ r := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hr0 : (0 : ℝ) < r := by linarith
  have he : (0 : ℝ) ≤ 1 / ((r : ℝ) - 1) := by
    apply div_nonneg zero_le_one; linarith
  set g : ℝ → ℝ := fun ξ => ((a - ξ) / (r * (1 + ξ))) ^ (1 / ((r : ℝ) - 1)) with hg
  set F : ℝ → ℝ := fun ξ => (a - ξ) * g ξ - (1 + ξ) * (g ξ) ^ r with hF
  have hgc : ContinuousAt g 0 := by
    apply ContinuousAt.rpow_const _ (Or.inr he)
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp; linarith
  have hFc : ContinuousAt F 0 := by
    simp only [hF]
    fun_prop
  have hF0 : F 0 = c r * a ^ ((r : ℝ) / ((r : ℝ) - 1)) := by
    rw [← T51_c_identity r hr a ha]
    simp [hF, hg]
  have hev : ∀ᶠ ξ in nhds (0 : ℝ), F 0 - η / 4 < F ξ := by
    apply hFc.eventually (Ioi_mem_nhds _)
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set ξ := min (δ / 2) (a / 2) with hξ
  have hξ0 : 0 < ξ := lt_min (by linarith) (by linarith)
  have hξa : ξ ≤ a / 2 := min_le_right _ _
  have hξd : ξ ≤ δ / 2 := min_le_left _ _
  have hbase0 : 0 < (a - ξ) / (r * (1 + ξ)) := by
    apply div_pos (by linarith); positivity
  have hbase1 : (a - ξ) / (r * (1 + ξ)) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  refine ⟨ξ, g ξ, hξ0, by linarith, Real.rpow_pos_of_pos hbase0 _, ?_, ?_, ?_⟩
  · apply Real.rpow_lt_one hbase0.le hbase1
    apply div_pos zero_lt_one; linarith
  · simp only [hg]
    rw [T51_rpow_pow r hr _ hbase0.le]
    field_simp
  · have := hball (y := ξ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hξ0]; linarith)
    rw [← hF0]
    exact this


/-! ### Asymptotics in m -/

lemma T51_asymp (h : ℕ) (ξ K η : ℝ) (hξ : 0 < ξ) (hη : 0 < η) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 2 ≤ (m : ℝ) ∧ (Real.logb 2 m) ^ (h + 1) ≤ (m : ℝ) ^ ξ ∧
      K * (m : ℝ) ^ (-ξ) + 2 * (m : ℝ) ^ (-1 : ℝ) < 1 ∧ 4 ≤ (m : ℝ) ^ (η / 4) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have e2 : ∀ᶠ x : ℝ in atTop, (Real.logb 2 x) ^ (h + 1) ≤ x ^ ξ := by
    have hb := (isLittleO_log_rpow_rpow_atTop (((h + 1 : ℕ) : ℝ)) hξ).bound
      (pow_pos hlog2 (h + 1))
    filter_upwards [hb, eventually_ge_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)] at hx
    rw [Real.logb, div_pow, div_le_iff₀ (by positivity)]
    linarith
  have e3 : ∀ᶠ x : ℝ in atTop, K * x ^ (-ξ) + 2 * x ^ (-1 : ℝ) < 1 := by
    have ht : Tendsto (fun x : ℝ => K * x ^ (-ξ) + 2 * x ^ (-1 : ℝ)) atTop (𝓝 (K * 0 + 2 * 0)) :=
      ((tendsto_rpow_neg_atTop hξ).const_mul K).add
        ((tendsto_rpow_neg_atTop zero_lt_one).const_mul 2)
    exact ht.eventually_lt_const (by norm_num)
  have e4 : ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ (η / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 4
  have := tendsto_natCast_atTop_atTop.eventually (e1.and (e2.and (e3.and e4)))
  obtain ⟨M, hM⟩ := eventually_atTop.mp this
  exact ⟨M, fun m hm => hM m hm⟩


/-! ### The numerical steps of the proof of Theorem 5.1 -/

/-- First hypothesis of Lemma 4.5: `κ^h (log₂ m)^(h+1) ≤ Λ m`. -/
lemma T51_hyp1 (h m ℓ : ℕ) (ε ξ : ℝ) (hm : (1 : ℝ) < m)
    (hle : (ℓ : ℝ) ≤ (m : ℝ) ^ (1 / (h : ℝ) - ε)) (hh0 : (0 : ℝ) < h)
    (hlogm : (Real.logb 2 m) ^ (h + 1) ≤ (m : ℝ) ^ ξ) :
    (ℓ : ℝ) ^ h * (Real.logb 2 (m : ℝ)) ^ (h + 1) ≤
      (m : ℝ) ^ (-((h : ℝ) * ε - ξ)) * (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hl1 : (ℓ : ℝ) ^ h ≤ (m : ℝ) ^ (1 - (h : ℝ) * ε) := by
    calc (ℓ : ℝ) ^ h ≤ ((m : ℝ) ^ (1 / (h : ℝ) - ε)) ^ h :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hle h
      _ = (m : ℝ) ^ ((1 / (h : ℝ) - ε) * h) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
      _ = (m : ℝ) ^ (1 - (h : ℝ) * ε) := by
          congr 1; field_simp
  have hlog0 : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg (by norm_num) hm.le
  calc (ℓ : ℝ) ^ h * (Real.logb 2 (m : ℝ)) ^ (h + 1)
      ≤ (m : ℝ) ^ (1 - (h : ℝ) * ε) * (m : ℝ) ^ ξ :=
        mul_le_mul hl1 hlogm (by positivity) (by positivity)
    _ = _ := by
        rw [← Real.rpow_add hm0, show 1 - (h : ℝ) * ε + ξ = -((h : ℝ) * ε - ξ) + 1 by ring,
          Real.rpow_add hm0, Real.rpow_one]

/-- `ℓ C(ℓ-1,r-1) = r C(ℓ,r)`. -/
lemma T51_choose_id (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) :
    (ℓ : ℝ) * (Nat.choose (ℓ - 1) (r - 1) : ℝ) = r * (Nat.choose ℓ r : ℝ) := by
  have := Nat.add_one_mul_choose_eq (ℓ - 1) (r - 1)
  rw [show ℓ - 1 + 1 = ℓ by omega, show r - 1 + 1 = r by omega] at this
  have h' : (ℓ : ℝ) * (Nat.choose (ℓ - 1) (r - 1) : ℝ) = (Nat.choose ℓ r : ℝ) * r := by
    exact_mod_cast this
  rw [h', mul_comm]

/-- Second hypothesis of Lemma 4.5: `C(s-1,r-1) ln(1/p) ≤ ln(1/Λ)`. -/
lemma T51_hyp2 (m ℓ r s : ℕ) (ξ γ b : ℝ) (hm : (1 : ℝ) < m) (hr : 2 ≤ r) (hrs : r ≤ s)
    (hsl : s < ℓ) (hγ1 : γ < 1) (hξ : 0 < ξ) (hs_le : (s : ℝ) ≤ γ * ℓ)
    (hγeq : (1 + ξ) * r * γ ^ (r - 1) = b) :
    (Nat.choose (s - 1) (r - 1) : ℝ) *
        Real.log (1 / (m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) ≤
      Real.log (1 / (m : ℝ) ^ (-b)) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hCl : (0 : ℝ) < Nat.choose ℓ r := by exact_mod_cast Nat.choose_pos (by omega)
  have hL : 0 < Real.log (m : ℝ) := Real.log_pos hm
  rw [one_div, Real.log_inv, Real.log_rpow hm0, one_div, Real.log_inv, Real.log_rpow hm0]
  have hbin : (Nat.choose (s - 1) (r - 1) : ℝ) ≤
      (Nat.choose (ℓ - 1) (r - 1) : ℝ) * γ ^ (r - 1) := by
    apply T51_choose_real (s - 1) (ℓ - 1) (r - 1) (by omega) γ
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    have : γ * ((ℓ : ℝ) - 1) = γ * ℓ - γ := by ring
    linarith
  have hid := T51_choose_id ℓ r (by omega) (by omega)
  have key : (Nat.choose (s - 1) (r - 1) : ℝ) * ((1 + ξ) * ℓ) ≤ b * (Nat.choose ℓ r : ℝ) := by
    calc (Nat.choose (s - 1) (r - 1) : ℝ) * ((1 + ξ) * ℓ)
        ≤ (Nat.choose (ℓ - 1) (r - 1) : ℝ) * γ ^ (r - 1) * ((1 + ξ) * ℓ) :=
          mul_le_mul_of_nonneg_right hbin (by positivity)
      _ = ((1 + ξ) * r * γ ^ (r - 1)) * (Nat.choose ℓ r : ℝ) := by
          linear_combination ((1 + ξ) * γ ^ (r - 1)) * hid
      _ = b * (Nat.choose ℓ r : ℝ) := by rw [hγeq]
  calc (Nat.choose (s - 1) (r - 1) : ℝ) *
        -(-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) * Real.log m)
      = ((Nat.choose (s - 1) (r - 1) : ℝ) * ((1 + ξ) * ℓ)) / (Nat.choose ℓ r : ℝ)
          * Real.log m := by ring
    _ ≤ b * Real.log m :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hCl).2 key) hL.le
    _ = -(-b * Real.log m) := by ring

/-- The gate-count hypothesis of Lemma 4.5: `G ≤ m^ℓ / 2`. -/
lemma T51_hG (m ℓ : ℕ) (Gc E η : ℝ) (hm2 : (2 : ℝ) ≤ m) (hℓ : (0 : ℝ) < ℓ)
    (hηℓ : 4 ≤ η * ℓ) (hEb : E < 1 + η / 4) (hlt : Gc ≤ (m : ℝ) ^ ((E - η) * ℓ)) :
    Gc ≤ (m : ℝ) ^ (ℓ : ℝ) / 2 := by
  have hm0 : (0 : ℝ) < m := by linarith
  have h1 : (E - η) * ℓ ≤ (ℓ : ℝ) - 1 := by
    have : (E - η) * ℓ ≤ (1 - 3 * η / 4) * ℓ :=
      mul_le_mul_of_nonneg_right (by linarith) hℓ.le
    linarith
  calc Gc ≤ (m : ℝ) ^ ((E - η) * ℓ) := hlt
    _ ≤ (m : ℝ) ^ ((ℓ : ℝ) - 1) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1
    _ = (m : ℝ) ^ (ℓ : ℝ) / m := by rw [Real.rpow_sub hm0, Real.rpow_one]
    _ ≤ (m : ℝ) ^ (ℓ : ℝ) / 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hm2

/-- The main term of Lemma 4.5 is at most `1/m`. -/
lemma T51_hup (m ℓ r s : ℕ) (Gc E η ξ γ b : ℝ) (hm : (1 : ℝ) < m) (hr : r ≤ ℓ) (hsl : s ≤ ℓ)
    (hℓ : (0 : ℝ) < ℓ) (hηℓ : 4 ≤ η * ℓ) (hξ : 0 < ξ) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hs_le : (s : ℝ) ≤ γ * ℓ) (hs_gt : γ * ℓ - 1 < s)
    (hmain : E - η / 4 < b * γ - (1 + ξ) * γ ^ r)
    (h4 : 4 ≤ (m : ℝ) ^ (η / 4)) (hlt : Gc ≤ (m : ℝ) ^ ((E - η) * ℓ)) :
    Gc * (4 : ℝ) ^ ℓ * ((m : ℝ) ^ (-b)) ^ s *
        ((m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) ^ (-(Nat.choose s r : ℝ)) ≤
      (m : ℝ) ^ (-1 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hCl : (0 : ℝ) < Nat.choose ℓ r := by exact_mod_cast Nat.choose_pos hr
  have h4l : (4 : ℝ) ^ ℓ ≤ (m : ℝ) ^ (η / 4 * ℓ) := by
    calc (4 : ℝ) ^ ℓ ≤ ((m : ℝ) ^ (η / 4)) ^ ℓ := pow_le_pow_left₀ (by norm_num) h4 ℓ
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
  have hΛs : ((m : ℝ) ^ (-b)) ^ s = (m : ℝ) ^ (-b * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
  have hps : ((m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) ^ (-(Nat.choose s r : ℝ)) =
      (m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) * (-(Nat.choose s r : ℝ))) := by
    rw [← Real.rpow_mul hm0.le]
  have hCs : (Nat.choose s r : ℝ) / (Nat.choose ℓ r : ℝ) ≤ γ ^ r := by
    rw [div_le_iff₀ hCl]
    have := T51_choose_real s ℓ r hsl γ hs_le
    linarith
  have hexp : (E - η) * ℓ + η / 4 * ℓ + -b * s +
      -((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) * (-(Nat.choose s r : ℝ)) ≤ -1 := by
    have e1 : -((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) * (-(Nat.choose s r : ℝ)) =
        ((1 + ξ) * ℓ) * ((Nat.choose s r : ℝ) / (Nat.choose ℓ r : ℝ)) := by ring
    have e2 : ((1 + ξ) * ℓ) * ((Nat.choose s r : ℝ) / (Nat.choose ℓ r : ℝ)) ≤
        ((1 + ξ) * ℓ) * γ ^ r := mul_le_mul_of_nonneg_left hCs (by positivity)
    have e3 : b * (γ * ℓ - 1) ≤ b * s := mul_le_mul_of_nonneg_left hs_gt.le hb0.le
    have e4 : (E - η / 4) * ℓ ≤ (b * γ - (1 + ξ) * γ ^ r) * ℓ :=
      mul_le_mul_of_nonneg_right hmain.le hℓ.le
    rw [e1]
    have e5 : b * (γ * ℓ - 1) = b * γ * ℓ - b := by ring
    have e6 : (b * γ - (1 + ξ) * γ ^ r) * ℓ = b * γ * ℓ - ((1 + ξ) * ℓ) * γ ^ r := by ring
    have e7 : (E - η / 4) * ℓ = (E - η) * ℓ + 3 * (η * ℓ) / 4 := by ring
    have e8 : η / 4 * ℓ = (η * ℓ) / 4 := by ring
    have e9 : -b * s = -(b * s) := by ring
    rw [e8, e9]
    linarith
  calc Gc * (4 : ℝ) ^ ℓ * ((m : ℝ) ^ (-b)) ^ s *
        ((m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) ^ (-(Nat.choose s r : ℝ))
      ≤ (m : ℝ) ^ ((E - η) * ℓ) * (m : ℝ) ^ (η / 4 * ℓ) * ((m : ℝ) ^ (-b)) ^ s *
          ((m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) ^ (-(Nat.choose s r : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hlt h4l (by positivity) (by positivity)
    _ = (m : ℝ) ^ ((E - η) * ℓ + η / 4 * ℓ + -b * s +
          -((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) * (-(Nat.choose s r : ℝ))) := by
        rw [hΛs, hps, Real.rpow_add hm0, Real.rpow_add hm0, Real.rpow_add hm0]
    _ ≤ (m : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm.le hexp

/-- Lower bound on the large-gate probability from Lemma 4.6 and the planted event. -/
lemma T51_hlow {m r ℓ h s : ℕ} (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hℓm : ℓ ≤ m)
    (hrl : r < ℓ) (hsl : s < ℓ)
    (C : MantriCVQ.ACCircuit (Edge m r)) (hd : C.depth ≤ h)
    (hC : ∀ x, C.eval x = hyperclique m r ℓ x)
    (h46 : ∀ A : Finset (Fin m), A.card = ℓ → probability p (plantedGood (r := r) ℓ A) ≥ q) :
    q ≤ largeGateProbability p ℓ h s C := by
  unfold largeGateProbability
  apply T51_joint_ge hℓm
  intro ι
  have hA : (Finset.univ.map ι).card = ℓ := by simp
  calc q ≤ probability p (plantedGood (r := r) ℓ (Finset.univ.map ι)) := h46 _ hA
    _ ≤ _ := T51_prob_mono p hp0.le hp1.le _ _
        (fun G hgood => T51_event C hd hC G _ hA hgood hrl hsl)

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (h r : ℕ) (hh : 2 ≤ h) (hr : 2 ≤ r)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ ℓ₀ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
      (ℓ : ℝ) ≤ (m : ℝ) ^ (1 / (h : ℝ) - ε) →
      ∀ C : MantriCVQ.ACCircuit (Edge m r), C.depth ≤ h →
        (∀ x, C.eval x = hyperclique m r ℓ x) →
        (m : ℝ) ^ ((c r * ((h : ℝ) * ε) ^ ((r : ℝ) / ((r : ℝ) - 1)) - η) * (ℓ : ℝ)) <
          (C.gates.length : ℝ) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hh2 : (2 : ℝ) ≤ h := by exact_mod_cast hh
  by_cases ha1 : 1 ≤ (h : ℝ) * ε
  · -- trivial case: no integer ℓ ≥ 2 satisfies ℓ ≤ m^(1/h - ε)
    refine ⟨2, 1, ?_⟩
    intro m hm ℓ hℓ hle C _ _
    exfalso
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hexp : 1 / (h : ℝ) - ε ≤ 0 := by
      have : 1 / (h : ℝ) ≤ ε := by rw [div_le_iff₀ hh0]; linarith
      linarith
    have h1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 hexp
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  push Not at ha1
  have ha : 0 < (h : ℝ) * ε := by positivity
  obtain ⟨ξ, γ, hξ0, hξa, hγ0, hγ1, hγeq, hmain⟩ := T51_params r hr _ η ha ha1 hη
  have hb0 : 0 < (h : ℝ) * ε - ξ := by linarith
  have hb1 : (h : ℝ) * ε - ξ < 1 := by linarith
  obtain ⟨K, hK, h46⟩ := lemma_4_6
  obtain ⟨m46, hm46⟩ := h46 r hr ξ hξ0 (by linarith)
  obtain ⟨m45, hm45⟩ := lemma_4_5 h r (by omega) hr
  obtain ⟨M, hM⟩ := T51_asymp h ξ K η hξ0 hη
  refine ⟨⌈((r : ℝ) + 1) / γ⌉₊ + ⌈4 / η⌉₊ + r + 2, max (max m46 m45) M, ?_⟩
  intro m hm ℓ hℓ hle C hdepth heval
  by_contra hlt
  push Not at hlt
  obtain ⟨hm2, hlogm, hfin, h4⟩ := hM m (le_trans (le_max_right _ _) hm)
  have hm46' : m46 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm45' : m45 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  -- facts about ℓ
  have hℓr : r + 2 ≤ ℓ := by omega
  have hℓR : (ℓ : ℝ) ≥ ⌈((r : ℝ) + 1) / γ⌉₊ + ⌈4 / η⌉₊ := by
    have := (Nat.cast_le (α := ℝ)).2 hℓ
    push_cast at this; linarith
  have hγℓ : (r : ℝ) + 1 ≤ γ * ℓ := by
    have h1 := Nat.le_ceil (((r : ℝ) + 1) / γ)
    have h2 : (0 : ℝ) ≤ ⌈4 / η⌉₊ := Nat.cast_nonneg _
    have : ((r : ℝ) + 1) / γ ≤ ℓ := by linarith
    rw [div_le_iff₀ hγ0] at this; linarith
  have hηℓ : 4 ≤ η * ℓ := by
    have h1 := Nat.le_ceil (4 / η)
    have h2 : (0 : ℝ) ≤ ⌈((r : ℝ) + 1) / γ⌉₊ := Nat.cast_nonneg _
    have : 4 / η ≤ ℓ := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hs_le : (⌊γ * ℓ⌋₊ : ℝ) ≤ γ * ℓ := Nat.floor_le (by positivity)
  have hs_gt : γ * ℓ - 1 < ⌊γ * ℓ⌋₊ := by have := Nat.lt_floor_add_one (γ * ℓ); linarith
  have hrs : r ≤ ⌊γ * ℓ⌋₊ := Nat.le_floor (by linarith)
  have hsl : ⌊γ * ℓ⌋₊ < ℓ := by
    have : γ * ℓ < ℓ := by nlinarith
    exact_mod_cast lt_of_le_of_lt hs_le this
  -- facts about m
  have hX : (1 : ℝ) < m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hℓm : ℓ < m := by
    have h1 : (m : ℝ) ^ (1 / (h : ℝ) - ε) < (m : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hX
      have : 1 / (h : ℝ) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num) hh2
      linarith
    rw [Real.rpow_one] at h1
    exact_mod_cast (lt_of_le_of_lt hle h1)
  -- the bias p and Λ
  have hCl : (0 : ℝ) < Nat.choose ℓ r := by exact_mod_cast Nat.choose_pos (by omega)
  have hp0 : 0 < (m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ)) :=
    Real.rpow_pos_of_pos hm0 _
  have hp1 : (m : ℝ) ^ (-((1 + ξ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg hX
    apply div_neg_of_neg_of_pos _ hCl
    have : 0 < (1 + ξ) * (ℓ : ℝ) := by positivity
    linarith
  have hΛ0 : 0 < (m : ℝ) ^ (-((h : ℝ) * ε - ξ)) := Real.rpow_pos_of_pos hm0 _
  have hΛ1 : (m : ℝ) ^ (-((h : ℝ) * ε - ξ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX.le (by linarith)
  have hEb : c r * ((h : ℝ) * ε) ^ ((r : ℝ) / ((r : ℝ) - 1)) < 1 + η / 4 := by
    have : 0 ≤ (1 + ξ) * γ ^ r := by positivity
    have : ((h : ℝ) * ε - ξ) * γ < 1 := by nlinarith
    linarith
  have hG := T51_hG m ℓ _ _ η hm2 hℓpos hηℓ hEb hlt
  -- Lemma 4.5
  have h45 := hm45 m hm45' ⌊γ * ℓ⌋₊ ℓ _ (ℓ : ℝ) _ hrs (by omega) hℓm hp0 hp1
    (max_le (by exact_mod_cast (by omega : r + 1 ≤ ℓ)) (by linarith)) hΛ0 hΛ1
    (T51_hyp1 h m ℓ ε ξ hX hle hh0 hlogm)
    (T51_hyp2 m ℓ r ⌊γ * ℓ⌋₊ ξ γ _ hX hr hrs hsl hγ1 hξ0 hs_le hγeq) C (by omega) hG
  -- Lemma 4.6 and the planted event
  have hlow := T51_hlow (h := h) (s := ⌊γ * ℓ⌋₊) _ _ hp0 hp1 hℓm.le (by omega) hsl C hdepth heval
    (fun A hA => hm46 m hm46' ℓ _ A (by omega) hℓm.le hp0 le_rfl hA)
  have hup := T51_hup m ℓ r ⌊γ * ℓ⌋₊ _ _ η ξ γ _ hX (by omega) hsl.le hℓpos hηℓ hξ0 hb0
    hb1.le hs_le hs_gt hmain h4 hlt
  have hmℓ : (m : ℝ) ^ (-(ℓ : ℝ)) ≤ (m : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX.le
      (by have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
          linarith)
  linarith
