-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_probabilistic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:26:04.169617+00:00
-- url     : https://prove2.me/submissions/c414cf77-1ef6-4ed3-a493-4a4e8f32c43b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KSATSingleFlip_Connect_lemma_7_12
import Theorems.Thm_KSATSingleFlip_Connect_repair_bounds_actual_law



open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The planted assignment satisfies the subformula retained by satIdx. -/
theorem audit_satIdx_satisfies {n : ℕ} (Φ : GFormula (Fin n)) (z : Fin n → Bool) :
    z ∈ sols (subF Φ (satIdx Φ z)) := by
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  change FSat z (subF Φ (satIdx Φ z))
  intro C hC
  unfold subF at hC
  obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hC
  split at hc
  next h =>
    have hsat : ClauseSat z (Φ.get c) := (Finset.mem_filter.mp h).2
    cases hc
    exact hsat
  next _ => simp at hc

/-- A Glauber update preserves satisfiability. -/
theorem audit_glauber_step_preserves {n : ℕ} (Φ : GFormula (Fin n)) (x : Fin n → Bool)
    (u : Fin n × Bool) (hx : FSat x Φ) : FSat (glauberStep Φ x u) Φ := by
  unfold glauberStep
  split
  next h => exact h
  next _ =>
    split
    next h => exact h
    next _ => exact hx

/-- The planted-subformula Glauber chain remains satisfying at every time. -/
theorem audit_glauber_planted_satisfies {n t : ℕ} (Φ : GFormula (Fin n))
    (z : Fin n → Bool) (s : Fin t → Fin n × Bool) :
    glauberState (subF Φ (satIdx Φ z)) z s ∈ sols (subF Φ (satIdx Φ z)) := by
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  change FSat (glauberRun (subF Φ (satIdx Φ z)) z (List.ofFn s)) (subF Φ (satIdx Φ z))
  have hg : ∀ (seq : List (Fin n × Bool)) x,
      FSat x (subF Φ (satIdx Φ z)) →
      FSat (glauberRun (subF Φ (satIdx Φ z)) x seq) (subF Φ (satIdx Φ z)) := by
    intro seq
    induction seq with
    | nil => intro x hx; exact hx
    | cons u seq ih =>
      intro x hx
      apply ih
      exact audit_glauber_step_preserves _ x u hx
  apply hg
  simpa [sols] using audit_satIdx_satisfies Φ z

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Uniform finite expectations are monotone, including on an empty type. -/
theorem audit_uexp_mono {β : Type} [Fintype β] (f g : β → ℝ)
    (h : ∀ x, f x ≤ g x) : uexp f ≤ uexp g := by
  unfold uexp
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

/-- An event probability is in [0,1], including on an empty sample space. -/
theorem audit_uprob_bounds {β : Type} [Fintype β] (P : β → Prop) :
    0 ≤ uprob P ∧ uprob P ≤ 1 := by
  classical
  have h0 : 0 ≤ uprob P := by
    unfold uprob uexp
    positivity
  have h1 : uprob P ≤ uexp (fun _ : β => (1 : ℝ)) :=
    audit_uexp_mono _ _ (fun x => by split <;> norm_num)
  have hconst : uexp (fun _ : β => (1 : ℝ)) ≤ 1 := by
    unfold uexp
    by_cases h : Fintype.card β = 0
    · simp [h]
    · have hp : (0 : ℝ) < Fintype.card β := by exact_mod_cast (Nat.pos_of_ne_zero h)
      simp [ne_of_gt hp]
  exact ⟨h0, h1.trans hconst⟩

/-- Poisson expectations of [0,1]-valued functions are monotone. -/
theorem audit_poisExp_mono {α : Type} [DecidableEq α] (S : Finset α) (m : ℝ)
    (hm : 0 ≤ m) (f g : List α → ℝ)
    (hf0 : ∀ l, 0 ≤ f l) (hg1 : ∀ l, g l ≤ 1)
    (hfg : ∀ l, f l ≤ g l) : poisExp S m f ≤ poisExp S m g := by
  let A : ℕ → ℝ := fun N => poisW m N * uexp (fun F : Fin N → S => f (List.ofFn fun i => (F i).1))
  let B : ℕ → ℝ := fun N => poisW m N * uexp (fun F : Fin N → S => g (List.ofFn fun i => (F i).1))
  have hw : ∀ N, 0 ≤ poisW m N := by intro N; unfold poisW; positivity
  have hA0 : ∀ N, 0 ≤ A N := by
    intro N
    apply mul_nonneg (hw N)
    unfold uexp
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun F _ => hf0 _)
  have hAB : ∀ N, A N ≤ B N := by
    intro N
    exact mul_le_mul_of_nonneg_left (audit_uexp_mono _ _ (fun F => hfg _)) (hw N)
  have hBup : ∀ N, B N ≤ poisW m N := by
    intro N
    have hmean : uexp (fun F : Fin N → S => g (List.ofFn fun i => (F i).1)) ≤ 1 := by
      have h := audit_uexp_mono (fun F : Fin N → S => g (List.ofFn fun i => (F i).1)) (fun _ => 1) (fun F => hg1 _)
      have hc : uexp (fun _ : Fin N → S => (1 : ℝ)) ≤ 1 := by
        unfold uexp
        by_cases he : Fintype.card (Fin N → S) = 0
        · simp [he]
        · have hp : (0 : ℝ) < Fintype.card (Fin N → S) := by exact_mod_cast (Nat.pos_of_ne_zero he)
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          exact (div_le_one₀ hp).mpr le_rfl
      exact h.trans hc
    calc
      B N ≤ poisW m N * 1 := mul_le_mul_of_nonneg_left hmean (hw N)
      _ = poisW m N := mul_one _
  have hs : Summable (fun N => poisW m N) := by
    have h := (Real.summable_pow_div_factorial m).mul_left (Real.exp (-m))
    simpa only [poisW, mul_div_assoc] using h
  have hsB : Summable B := Summable.of_nonneg_of_le (fun N => le_trans (hA0 N) (hAB N)) hBup hs
  have hsA : Summable A := Summable.of_nonneg_of_le hA0 hAB hsB
  exact Summable.tsum_le_tsum hAB hsA hsB

end KSATSingleFlip.Connect


open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- If the three repair bounds hold at a Glauber sample, Lemma 7.12 implies
that the sample satisfies the success event of Lemma 7.4. -/
theorem audit_repair_bounds_imply_glauber_success :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (Φp : List (ProperClause n k))
      (z : Fin n → Bool) (t D : ℕ) (s : Fin t → Fin n × Bool),
      let Φ := ofList Φp
      let I0 := satIdx Φ z
      let X := glauberState (subF Φ I0) z s
      RepairBounds k Φ I0 X → Reg k D Φ →
      ((omittedWeak Φ I0 X).card : ℝ) ≤ rho k ^ 4 * n →
      ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
        (∃ r i, RepairRun k Φ I0 X (RState.init Φ X W) r i) ∧
        ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
          RepairRun k Φ I0 X (RState.init Φ X W) r i →
            ∃ U y, r = some (U, y) ∧ IsGoodRepair k Φ X W U y := by
  obtain ⟨k0, h⟩ := lemma_7_12
  refine ⟨k0, ?_⟩
  intro k hk
  obtain ⟨n0, hn⟩ := h k hk
  refine ⟨n0, ?_⟩
  intro n hn0 Φp z t D s
  dsimp only
  intro hb hr hd W hw
  exact hn n hn0 D Φp _ _ (audit_glauber_planted_satisfies (ofList Φp) z s) hr hd hb W hw

/-- An estimate for RepairBounds under the actual planted/Glauber law directly
yields the probabilistic success guarantee. -/
theorem audit_glauber_bounds_probability_implies_success :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      ∀ (z : Fin n → Bool) (t D : ℕ),
      (1 - Real.exp (-(rho k ^ 8) * n) ≤
        poisExp (allClauses n k) m (fun l =>
          uprob fun s : Fin t → Fin n × Bool =>
            let Φ := ofList l
            let I0 := satIdx Φ z
            let X := glauberState (subF Φ I0) z s
            RepairBounds k Φ I0 X)) →
      1 - Real.exp (-(rho k ^ 8) * n) ≤
        poisExp (allClauses n k) m (fun l =>
          uprob fun s : Fin t → Fin n × Bool =>
            let Φ := ofList l
            let I0 := satIdx Φ z
            let X := glauberState (subF Φ I0) z s
            Reg k D Φ → ((omittedWeak Φ I0 X).card : ℝ) ≤ rho k ^ 4 * n →
              ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
                (∃ r i, RepairRun k Φ I0 X (RState.init Φ X W) r i) ∧
                ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
                  RepairRun k Φ I0 X (RState.init Φ X W) r i →
                    ∃ U y, r = some (U, y) ∧ IsGoodRepair k Φ X W U y) := by
  obtain ⟨k0, hk⟩ := audit_repair_bounds_imply_glauber_success
  refine ⟨k0, ?_⟩
  intro k hk0
  obtain ⟨n0, hn⟩ := hk k hk0
  refine ⟨n0, ?_⟩
  intro n hn0 m hm z t D hprob
  apply hprob.trans
  apply audit_poisExp_mono (allClauses n k) m hm
  · intro l
    exact (audit_uprob_bounds _).1
  · intro l
    exact (audit_uprob_bounds _).2
  · intro l
    unfold uprob
    apply audit_uexp_mono
    intro s
    by_cases hb : RepairBounds k (ofList l) (satIdx (ofList l) z)
        (glauberState (subF (ofList l) (satIdx (ofList l) z)) z s)
    · have hs := hn n hn0 l z t D s hb
      simp only [hb, if_pos]
      split
      · norm_num
      · rename_i hnot
        exact (hnot hs).elim
    · simp only [hb, if_false]
      split <;> norm_num

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect OAI.FixedClauseThreshold



theorem solution :
    (∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ (z : Fin n → Bool) (t D : ℕ),
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φp := ofList l
              let I0 := satIdx Φp z
              let X := glauberState (subF Φp I0) z s
              Reg k D Φp → ((omittedWeak Φp I0 X).card : ℝ) ≤ rho k ^ 4 * n →
                ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
                  (∃ r i, RepairRun k Φp I0 X (RState.init Φp X W) r i) ∧
                  ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
                    RepairRun k Φp I0 X (RState.init Φp X W) r i →
                      ∃ U y, r = some (U, y) ∧ IsGoodRepair k Φp X W U y)) := by
  obtain ⟨k1, hk1⟩ := audit_glauber_bounds_probability_implies_success
  obtain ⟨k2, hk2⟩ := repair_bounds_actual_law
  refine ⟨max k1 k2, ?_⟩
  intro k hk
  obtain ⟨n1, hn1⟩ := hk1 k (le_trans (le_max_left _ _) hk)
  obtain ⟨n2, hn2⟩ := hk2 k (le_trans (le_max_right _ _) hk)
  refine ⟨max n1 n2, ?_⟩
  intro n hn m hm hupper z t D
  exact hn1 n (le_trans (le_max_left _ _) hn) m hm z t D
    (hn2 n (le_trans (le_max_right _ _) hn) m hm hupper z t)



#print axioms solution
