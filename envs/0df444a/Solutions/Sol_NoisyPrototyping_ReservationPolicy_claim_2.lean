-- Prove2me | solution 1 for NoisyPrototyping.ReservationPolicy.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:21:44.274573+00:00
-- url     : https://prove2.me/submissions/dae8cd86-4813-4370-b014-ab1bc9bb2c0e

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model
import Theorems.Thm_NoisyPrototyping_ReservationPolicy_claim_1_posterior_mean
import Theorems.Thm_NoisyPrototyping_ReservationPolicy_footnote_4

open MeasureTheory ProbabilityTheory
open NoisyPrototyping.ReservationPolicy



namespace NPCore

variable {N : ℕ}

theorem runAux_prefix (ρ : Policy N) (ω : Fin N → ℝ × ℝ) :
    ∀ (k : ℕ) (h : History N), ∃ t, (runAux ρ ω k h).1 = h ++ t := by
  intro k
  induction k with
  | zero => intro h; exact ⟨[], by simp [runAux]⟩
  | succ k ih =>
    intro h
    simp only [runAux]
    cases ρ.next h with
    | evaluate j =>
      simp only
      split_ifs
      · exact ⟨[], by simp⟩
      · obtain ⟨t, ht⟩ := ih (h ++ [(j, (ω j).2)])
        exact ⟨[(j, (ω j).2)] ++ t, by simp [ht]⟩
    | launch j =>
      simp only
      split_ifs <;> exact ⟨[], by simp⟩
    | stopNone => exact ⟨[], by simp⟩

theorem runAux_nodup (ρ : Policy N) (ω : Fin N → ℝ × ℝ) :
    ∀ (k : ℕ) (h : History N), (h.map Prod.fst).Nodup →
      ((runAux ρ ω k h).1.map Prod.fst).Nodup := by
  intro k
  induction k with
  | zero => intro h hh; simpa [runAux] using hh
  | succ k ih =>
    intro h hh
    simp only [runAux]
    cases ρ.next h with
    | evaluate j =>
      simp only
      split_ifs with hj
      · exact hh
      · apply ih
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact List.nodup_append.2 ⟨hh, List.nodup_singleton _, by
          intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hj ha⟩
    | launch j =>
      simp only
      split_ifs <;> exact hh
    | stopNone => exact hh

theorem runAux_launch_mem (ρ : Policy N) (ω : Fin N → ℝ × ℝ) :
    ∀ (k : ℕ) (h : History N) (j : Fin N), (runAux ρ ω k h).2 = Decision.launch j →
      j ∈ (runAux ρ ω k h).1.map Prod.fst := by
  intro k
  induction k with
  | zero => intro h j hj; simp [runAux] at hj
  | succ k ih =>
    intro h j hj
    simp only [runAux] at hj ⊢
    cases hn : ρ.next h with
    | evaluate i =>
      rw [hn] at hj
      simp only at hj ⊢
      split_ifs with hi
      · rw [if_pos hi] at hj; simp at hj
      · rw [if_neg hi] at hj; exact ih _ _ hj
    | launch i =>
      rw [hn] at hj
      simp only at hj ⊢
      split_ifs with hi
      · rw [if_pos hi] at hj
        simp only [Decision.launch.injEq] at hj
        subst hj; exact hi
      · rw [if_neg hi] at hj; simp at hj
    | stopNone => rw [hn] at hj; simp at hj

theorem runAux_congr (ρ : Policy N) (ω ω' : Fin N → ℝ × ℝ) (hω : ∀ j, (ω j).2 = (ω' j).2) :
    ∀ (k : ℕ) (h : History N), runAux ρ ω k h = runAux ρ ω' k h := by
  intro k
  induction k with
  | zero => intro h; simp [runAux]
  | succ k ih =>
    intro h
    simp only [runAux]
    cases ρ.next h with
    | evaluate j => simp only [hω j]; split_ifs <;> simp [ih]
    | launch j => rfl
    | stopNone => rfl

theorem runAux_mem_congr (ρ : Policy N) (ω ω' : Fin N → ℝ × ℝ) (i : Fin N)
    (hω : ∀ j, j ≠ i → (ω j).2 = (ω' j).2) :
    ∀ (k : ℕ) (h : History N), i ∉ h.map Prod.fst →
      (i ∈ (runAux ρ ω k h).1.map Prod.fst ↔ i ∈ (runAux ρ ω' k h).1.map Prod.fst) := by
  intro k
  induction k with
  | zero => intro h _; simp [runAux]
  | succ k ih =>
    intro h hi
    simp only [runAux]
    cases ρ.next h with
    | evaluate j =>
      simp only
      split_ifs with hj
      · exact Iff.rfl
      · by_cases hji : j = i
        · subst hji
          obtain ⟨t, ht⟩ := runAux_prefix ρ ω k (h ++ [(j, (ω j).2)])
          obtain ⟨t', ht'⟩ := runAux_prefix ρ ω' k (h ++ [(j, (ω' j).2)])
          rw [ht, ht']; simp
        · rw [hω j hji]
          apply ih
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton, not_or]
          exact ⟨hi, fun h' => hji h'.symm⟩
    | launch j => simp only
    | stopNone => exact Iff.rfl

theorem run_nodup (ρ : Policy N) (ω : Fin N → ℝ × ℝ) :
    ((run ρ ω).1.map Prod.fst).Nodup := runAux_nodup ρ ω _ [] (by simp)

theorem run_launch_mem (ρ : Policy N) (ω : Fin N → ℝ × ℝ) (j : Fin N)
    (hj : (run ρ ω).2 = Decision.launch j) : j ∈ (run ρ ω).1.map Prod.fst :=
  runAux_launch_mem ρ ω _ [] j hj

theorem run_congr (ρ : Policy N) (ω ω' : Fin N → ℝ × ℝ) (hω : ∀ j, (ω j).2 = (ω' j).2) :
    run ρ ω = run ρ ω' := runAux_congr ρ ω ω' hω _ []

theorem run_mem_congr (ρ : Policy N) (ω ω' : Fin N → ℝ × ℝ) (i : Fin N)
    (hω : ∀ j, j ≠ i → (ω j).2 = (ω' j).2) :
    (i ∈ (run ρ ω).1.map Prod.fst ↔ i ∈ (run ρ ω').1.map Prod.fst) :=
  runAux_mem_congr ρ ω ω' i hω _ [] (by simp)

end NPCore



namespace NPCore

variable {N : ℕ}

def decCode : Decision N → Fin N ⊕ Fin N ⊕ Unit
  | Decision.evaluate j => Sum.inl j
  | Decision.launch j => Sum.inr (Sum.inl j)
  | Decision.stopNone => Sum.inr (Sum.inr ())

theorem decCode_injective : Function.Injective (decCode (N := N)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [decCode]

instance : Countable (Decision N) := decCode_injective.countable

/-- the event-measurability half of admissibility -/
def EventsMeas (ρ : Policy N) : Prop :=
  ∀ (l : List (Fin N)) (d : Decision N),
    MeasurableSet {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = (l, d)}

theorem measurableSet_key (ρ : Policy N) (hev : EventsMeas ρ)
    (T : Set (List (Fin N) × Decision N)) :
    MeasurableSet {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) ∈ T} := by
  have : {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) ∈ T} =
      ⋃ k ∈ T, {ω | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = k} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable T) (fun k _ => hev k.1 k.2)

theorem measurableSet_opened (ρ : Policy N) (hev : EventsMeas ρ) (i : Fin N) :
    MeasurableSet {ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst} :=
  measurableSet_key ρ hev {k | i ∈ k.1}

theorem measurableSet_launch (ρ : Policy N) (hev : EventsMeas ρ) (j : Fin N) :
    MeasurableSet {ω : Fin N → ℝ × ℝ | (run ρ ω).2 = Decision.launch j} :=
  measurableSet_key ρ hev {k | k.2 = Decision.launch j}

theorem measurable_launchedValue (d : Decision N) :
    Measurable (fun ω : Fin N → ℝ × ℝ => launchedValue ω d) := by
  cases d with
  | evaluate j => exact measurable_const
  | launch j => exact measurable_fst.comp (measurable_pi_apply j)
  | stopNone => exact measurable_const

theorem cost_sum_eq (c : Fin N → ℝ) (h : History N) (hh : (h.map Prod.fst).Nodup) :
    (h.map (fun e => c e.1)).sum = ∑ i, if i ∈ h.map Prod.fst then c i else 0 := by
  classical
  have h1 : (h.map (fun e => c e.1)) = ((h.map Prod.fst).map c) := by simp
  rw [h1, ← List.sum_toFinset c hh, ← Finset.sum_filter]
  congr 1; ext i; simp

theorem netPayoff_measurable (S : SearchProblem N) (ρ : Policy N) (hev : EventsMeas ρ) :
    Measurable (netPayoff S ρ) := by
  let _ : MeasurableSpace (List (Fin N) × Decision N) := ⊤
  have _ : MeasurableSingletonClass (List (Fin N) × Decision N) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hkey : Measurable (fun ω : Fin N → ℝ × ℝ => ((run ρ ω).1.map Prod.fst, (run ρ ω).2)) :=
    measurable_to_countable' (fun k => by
      have := hev k.1 k.2
      simpa [Set.preimage] using this)
  let Φ : (Fin N → ℝ × ℝ) × (List (Fin N) × Decision N) → ℝ :=
    fun p => launchedValue p.1 p.2.2 - (p.2.1.map S.cost).sum
  have hΦ : Measurable Φ := measurable_from_prod_countable_left (fun k => by
    show Measurable (fun x => launchedValue x k.2 - (k.1.map S.cost).sum)
    exact (measurable_launchedValue k.2).sub measurable_const)
  have : netPayoff S ρ = Φ ∘ (fun ω => (ω, ((run ρ ω).1.map Prod.fst, (run ρ ω).2))) := by
    funext ω; simp [Φ, netPayoff, List.map_map, Function.comp_def]
  rw [this]
  exact hΦ.comp (measurable_id.prodMk hkey)

theorem abs_netPayoff_le (S : SearchProblem N) (ρ : Policy N) (ω : Fin N → ℝ × ℝ) :
    |netPayoff S ρ ω| ≤ (∑ i, |(ω i).1|) + ∑ i, |S.cost i| := by
  classical
  unfold netPayoff
  have h1 : |launchedValue ω (run ρ ω).2| ≤ ∑ i, |(ω i).1| := by
    cases (run ρ ω).2 with
    | evaluate j => simp [launchedValue]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    | launch j =>
      simp only [launchedValue]
      exact Finset.single_le_sum (f := fun i => |(ω i).1|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    | stopNone => simp [launchedValue]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h2 : |((run ρ ω).1.map (fun e => S.cost e.1)).sum| ≤ ∑ i, |S.cost i| := by
    rw [cost_sum_eq _ _ (run_nodup ρ ω)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    split_ifs <;> simp
  calc _ ≤ |launchedValue ω (run ρ ω).2| + |((run ρ ω).1.map (fun e => S.cost e.1)).sum| :=
        abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

theorem integrable_coord_fst (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (hY : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i)) (i : Fin N) :
    Integrable (fun ω : Fin N → ℝ × ℝ => (ω i).1) S.outcomeLaw := by
  have hmp := measurePreserving_eval S.law i
  have : Integrable (fun z : ℝ × ℝ => z.1) (Measure.map (Function.eval i) (Measure.pi S.law)) := by
    rw [hmp.map_eq]; exact hY i
  exact this.comp_measurable (measurable_pi_apply i)

theorem netPayoff_integrable (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (hY : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i)) (ρ : Policy N) (hev : EventsMeas ρ) :
    Integrable (netPayoff S ρ) S.outcomeLaw := by
  have _ : IsProbabilityMeasure S.outcomeLaw := by
    unfold SearchProblem.outcomeLaw; infer_instance
  have hb : Integrable (fun ω : Fin N → ℝ × ℝ => (∑ i, |(ω i).1|) + ∑ i, |S.cost i|)
      S.outcomeLaw :=
    (integrable_finsetSum _ (fun i _ => (integrable_coord_fst S hY i).abs)).add
      (integrable_const _)
  refine hb.mono' (netPayoff_measurable S ρ hev).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_netPayoff_le S ρ ω

theorem admissible_iff (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (hY : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i)) (ρ : Policy N) :
    Admissible S ρ ↔ EventsMeas ρ :=
  ⟨fun h => h.1, fun h => ⟨h, netPayoff_integrable S hY ρ h⟩⟩

end NPCore



namespace NPCore

variable {N : ℕ}

theorem integral_opened_mul (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (ρ : Policy N) (hev : EventsMeas ρ) (i : Fin N) (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) :
    ∫ ω, ({ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst}.indicator 1 ω) * φ (ω i)
        ∂S.outcomeLaw =
      S.outcomeLaw.real {ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst} *
        ∫ z, φ z ∂(S.law i) := by
  classical
  set O := {ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst} with hO
  have hOm : MeasurableSet O := measurableSet_opened ρ hev i
  set μ := S.outcomeLaw with hμ
  have hind : iIndepFun (fun j (ω : Fin N → ℝ × ℝ) => ω j) μ := by
    have := iIndepFun_pi (μ := S.law) (X := fun _ (z : ℝ × ℝ) => z)
      (fun _ => aemeasurable_id)
    exact this
  have hST : Disjoint ({i}ᶜ : Finset (Fin N)) {i} := disjoint_compl_left
  have hI := hind.indepFun_finset ({i}ᶜ) {i} hST (fun j => measurable_pi_apply j)
  let z0 : ℝ × ℝ := (0, 0)
  let F : (({i}ᶜ : Finset (Fin N)) → ℝ × ℝ) → (Fin N → ℝ × ℝ) := fun r j =>
    if h : j = i then z0 else r ⟨j, by simpa using h⟩
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro j
    by_cases h : j = i
    · simp only [F, h, dite_true]; exact measurable_const
    · simp only [F, h, dite_false]; exact measurable_pi_apply _
  let G : (({i} : Finset (Fin N)) → ℝ × ℝ) → ℝ × ℝ := fun r => r ⟨i, Finset.mem_singleton_self i⟩
  have hG : Measurable G := measurable_pi_apply _
  have hone : Measurable (O.indicator (1 : (Fin N → ℝ × ℝ) → ℝ)) :=
    measurable_one.indicator hOm
  have hI2 := hI.comp (hone.comp hF) (hφ.comp hG)
  have hX : (O.indicator (1 : (Fin N → ℝ × ℝ) → ℝ) ∘ F) ∘ (fun ω (j : ({i}ᶜ : Finset (Fin N))) => ω j)
      = O.indicator 1 := by
    funext ω
    simp only [Function.comp_apply]
    have hmem : (F fun j => ω ↑j) ∈ O ↔ ω ∈ O := by
      simp only [hO, Set.mem_ofPred_eq]
      apply run_mem_congr
      intro j hj
      simp [F, hj]
    by_cases h : ω ∈ O
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.1 h'))]
  have hY : (φ ∘ G) ∘ (fun (ω : Fin N → ℝ × ℝ) (j : ({i} : Finset (Fin N))) => ω j) =
      fun ω => φ (ω i) := by
    funext ω; rfl
  rw [hX, hY] at hI2
  have := hI2.integral_mul_eq_mul_integral
    hone.aestronglyMeasurable
    ((hφ.comp (measurable_pi_apply i)).aestronglyMeasurable)
  simp only [Pi.mul_apply] at this
  rw [this, integral_indicator_one hOm]
  congr 1
  have hmp := measurePreserving_eval S.law i
  have hmap : Measure.map (fun f : Fin N → ℝ × ℝ => f i) μ = S.law i := hmp.map_eq
  have := integral_map (μ := μ) (measurable_pi_apply i).aemeasurable
    (f := φ) (by rw [hmap]; exact hφ.aestronglyMeasurable)
  rw [hmap] at this
  exact this.symm

end NPCore



namespace NPCore

variable {N : ℕ}

theorem integrable_comp_eval (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (i : Fin N) (g : ℝ × ℝ → ℝ) (hg : Integrable g (S.law i)) :
    Integrable (fun ω : Fin N → ℝ × ℝ => g (ω i)) S.outcomeLaw := by
  have hmp := measurePreserving_eval S.law i
  have hmap : Measure.map (fun f : Fin N → ℝ × ℝ => f i) S.outcomeLaw = S.law i := hmp.map_eq
  have : Integrable g (Measure.map (fun f : Fin N → ℝ × ℝ => f i) S.outcomeLaw) := by
    rw [hmap]; exact hg
  exact this.comp_measurable (measurable_pi_apply i)

theorem ae_coord (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (i : Fin N) {P : ℝ × ℝ → Prop} (h : ∀ᵐ z ∂(S.law i), P z) :
    ∀ᵐ ω ∂S.outcomeLaw, P (ω i) := by
  have hmp := measurePreserving_eval S.law i
  have hmap : Measure.map (fun f : Fin N → ℝ × ℝ => f i) S.outcomeLaw = S.law i := hmp.map_eq
  rw [← hmap] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

/-- The amortized bound `max 0 (max_i min(x_i, R_i))`. -/
noncomputable def Kv (q : Fin N → ℝ → ℝ) (R : Fin N → ℝ) (ω : Fin N → ℝ × ℝ) : ℝ :=
  max 0 (⨆ i, min (q i (ω i).2) (R i))

/-- The amortized payoff: launched value minus excesses of opened prototypes. -/
noncomputable def Am (q : Fin N → ℝ → ℝ) (R : Fin N → ℝ) (ρ : Policy N)
    (ω : Fin N → ℝ × ℝ) : ℝ :=
  launchedValue ω (run ρ ω).2 -
    ∑ i, if i ∈ (run ρ ω).1.map Prod.fst then max (q i (ω i).2 - R i) 0 else 0

theorem Kv_measurable (q : Fin N → ℝ → ℝ) (hq : ∀ i, Measurable (q i)) (R : Fin N → ℝ) :
    Measurable (Kv q R) := by
  unfold Kv
  refine measurable_const.max ?_
  exact Measurable.iSup (fun i => ((hq i).comp (measurable_snd.comp (measurable_pi_apply i))).min
    measurable_const)

theorem Kv_nonneg (q : Fin N → ℝ → ℝ) (R : Fin N → ℝ) (ω : Fin N → ℝ × ℝ) : 0 ≤ Kv q R ω :=
  le_max_left _ _

theorem le_Kv (q : Fin N → ℝ → ℝ) (R : Fin N → ℝ) (ω : Fin N → ℝ × ℝ) (i : Fin N) :
    min (q i (ω i).2) (R i) ≤ Kv q R ω :=
  (le_ciSup (f := fun i => min (q i (ω i).2) (R i)) (Set.finite_range _).bddAbove i).trans
    (le_max_right _ _)

theorem Kv_le (q : Fin N → ℝ → ℝ) (R : Fin N → ℝ) (ω : Fin N → ℝ × ℝ) (v : ℝ) (hv : 0 ≤ v)
    (h : ∀ i, min (q i (ω i).2) (R i) ≤ v) : Kv q R ω ≤ v :=
  max_le hv (Real.iSup_le h hv)

theorem Kv_integrable (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (q : Fin N → ℝ → ℝ) (hqm : ∀ i, Measurable (q i))
    (hqi : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i)) (R : Fin N → ℝ) :
    Integrable (Kv q R) S.outcomeLaw := by
  have _ : IsProbabilityMeasure S.outcomeLaw := by
    unfold SearchProblem.outcomeLaw; infer_instance
  have hb : Integrable (fun ω : Fin N → ℝ × ℝ => ∑ i, (|q i (ω i).2| + |R i|)) S.outcomeLaw :=
    integrable_finsetSum _ (fun i _ =>
      (integrable_comp_eval S i _ (hqi i)).abs.add (integrable_const _))
  refine hb.mono' (Kv_measurable q hqm R).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Kv_nonneg q R ω)]
  apply Kv_le _ _ _ _ (Finset.sum_nonneg (fun i _ => by positivity))
  intro i
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => |q i (ω i).2| + |R i|)
    (fun _ _ => by positivity) (Finset.mem_univ i))
  exact (min_le_left _ _).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))

section signal

variable (S : SearchProblem N) [hprob : ∀ i, IsProbabilityMeasure (S.law i)]
  (q : Fin N → ℝ → ℝ) (R : Fin N → ℝ)

theorem value_eq_integral_Am
    (hY : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i))
    (hqm : ∀ i, Measurable (q i))
    (hqi : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i))
    (hR : ∀ i, ∫ z, max (q i z.2 - R i) 0 ∂(S.law i) = S.cost i)
    (ρ : Policy N) (hev : EventsMeas ρ) :
    Integrable (Am q R ρ) S.outcomeLaw ∧ value S ρ = ∫ ω, Am q R ρ ω ∂S.outcomeLaw := by
  classical
  set φ : Fin N → ℝ × ℝ → ℝ := fun i z => max (q i z.2 - R i) 0 - S.cost i with hφ
  have hφm : ∀ i, Measurable (φ i) := fun i =>
    ((((hqm i).comp measurable_snd).sub_const _).max measurable_const).sub_const _
  have hφi : ∀ i, Integrable (φ i) (S.law i) := fun i =>
    ((hqi i).sub (integrable_const (R i))).pos_part.sub (integrable_const _)
  let O : Fin N → Set (Fin N → ℝ × ℝ) := fun i => {ω | i ∈ (run ρ ω).1.map Prod.fst}
  let D : (Fin N → ℝ × ℝ) → ℝ := fun ω => ∑ i, (O i).indicator 1 ω * φ i (ω i)
  have hDterm : ∀ i, Integrable (fun ω => (O i).indicator 1 ω * φ i (ω i)) S.outcomeLaw := by
    intro i
    have : (fun ω => (O i).indicator 1 ω * φ i (ω i)) =
        (O i).indicator (fun ω => φ i (ω i)) := by
      funext ω; by_cases h : ω ∈ O i <;> simp [h]
    rw [this]
    exact (integrable_comp_eval S i _ (hφi i)).indicator (measurableSet_opened ρ hev i)
  have hD0 : ∫ ω, D ω ∂S.outcomeLaw = 0 := by
    simp only [D]
    rw [integral_finsetSum _ (fun i _ => hDterm i)]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_opened_mul S ρ hev i (φ i) (hφm i)]
    have : ∫ z, φ i z ∂(S.law i) = 0 := by
      have hpos : Integrable (fun z : ℝ × ℝ => max (q i z.2 - R i) 0) (S.law i) :=
        ((hqi i).sub (integrable_const (R i))).pos_part
      simp only [hφ]
      rw [integral_sub hpos (integrable_const _), hR i]
      simp
    rw [this, mul_zero]
  have hpt : ∀ ω, netPayoff S ρ ω - D ω = Am q R ρ ω := by
    intro ω
    simp only [netPayoff, Am, D, O]
    rw [cost_sum_eq _ _ (run_nodup ρ ω)]
    have : ∀ i, ({ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst}.indicator 1 ω) * φ i (ω i)
        = (if i ∈ (run ρ ω).1.map Prod.fst then max (q i (ω i).2 - R i) 0 else 0) -
          (if i ∈ (run ρ ω).1.map Prod.fst then S.cost i else 0) := by
      intro i
      by_cases h : i ∈ (run ρ ω).1.map Prod.fst
      · rw [Set.indicator_of_mem (show ω ∈ {ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst}
          from h)]
        simp [h, hφ]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω : Fin N → ℝ × ℝ |
          i ∈ (run ρ ω).1.map Prod.fst} from h)]
        simp [h]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib]
    ring
  have hnI := netPayoff_integrable S hY ρ hev
  have hDI : Integrable D S.outcomeLaw := integrable_finsetSum _ (fun i _ => hDterm i)
  unfold value
  have : (fun ω => Am q R ρ ω) = fun ω => netPayoff S ρ ω - D ω := by
    funext ω; rw [hpt]
  refine ⟨?_, ?_⟩
  · have h2 : Am q R ρ = fun ω => netPayoff S ρ ω - D ω := this
    rw [h2]; exact hnI.sub hDI
  rw [this, integral_sub hnI hDI, hD0, sub_zero]

theorem Am_le_Kv (ρ : Policy N) (ω : Fin N → ℝ × ℝ)
    (hω : ∀ i, (ω i).1 = q i (ω i).2) : Am q R ρ ω ≤ Kv q R ω := by
  classical
  unfold Am
  have hnn : 0 ≤ ∑ i, (if i ∈ (run ρ ω).1.map Prod.fst then max (q i (ω i).2 - R i) 0 else 0) :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> simp)
  cases hd : (run ρ ω).2 with
  | evaluate j => simp only [launchedValue]; linarith [Kv_nonneg q R ω]
  | stopNone => simp only [launchedValue]; linarith [Kv_nonneg q R ω]
  | launch j =>
    simp only [launchedValue]
    have hj := run_launch_mem ρ ω j hd
    have hle : max (q j (ω j).2 - R j) 0 ≤
        ∑ i, (if i ∈ (run ρ ω).1.map Prod.fst then max (q i (ω i).2 - R i) 0 else 0) := by
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun i => if i ∈ (run ρ ω).1.map Prod.fst then max (q i (ω i).2 - R i) 0 else 0)
        (fun i _ => by split_ifs <;> simp) (Finset.mem_univ j))
      simp [hj]
    have hk := le_Kv q R ω j
    rw [hω j]
    have : q j (ω j).2 - max (q j (ω j).2 - R j) 0 = min (q j (ω j).2) (R j) := by
      rcases le_total (q j (ω j).2) (R j) with h | h
      · rw [max_eq_right (by linarith), min_eq_left h]; ring
      · rw [max_eq_left (by linarith), min_eq_right h]; ring
    linarith

theorem value_le_integral_Kv
    (hY : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i))
    (hqm : ∀ i, Measurable (q i))
    (hq : ∀ i, (fun z : ℝ × ℝ => z.1) =ᵐ[S.law i] (fun z => q i z.2))
    (hR : ∀ i, ∫ z, max (q i z.2 - R i) 0 ∂(S.law i) = S.cost i)
    (ρ : Policy N) (hadm : Admissible S ρ) :
    value S ρ ≤ ∫ ω, Kv q R ω ∂S.outcomeLaw := by
  have hqi : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i) :=
    fun i => (hY i).congr (hq i)
  obtain ⟨hAmI, hv⟩ := value_eq_integral_Am S q R hY hqm hqi hR ρ hadm.1
  rw [hv]
  apply integral_mono_ae hAmI (Kv_integrable S q hqm hqi R)
  have hall : ∀ᵐ ω ∂S.outcomeLaw, ∀ i, (ω i).1 = q i (ω i).2 :=
    ae_all_iff.2 (fun i => ae_coord S i (hq i))
  filter_upwards [hall] with ω hω
  exact Am_le_Kv q R ρ ω hω

end signal

end NPCore



namespace NPCore

variable {N : ℕ}

theorem VB_append (q : Fin N → ℝ → ℝ) (h : History N) (e : Fin N × ℝ) :
    VB q (h ++ [e]) = if (VB q h).1 > q e.1 e.2 then VB q h else (q e.1 e.2, some e.1) := by
  simp [VB, List.foldl_append]

theorem foldl_B_mem (q : Fin N → ℝ → ℝ) (b : Fin N) :
    ∀ (h : History N) (init : ℝ × Option (Fin N)),
      (h.foldl (fun vb e => if vb.1 > q e.1 e.2 then vb else (q e.1 e.2, some e.1)) init).2
        = some b → init.2 = some b ∨ b ∈ h.map Prod.fst := by
  intro h
  induction h with
  | nil => intro init hb; left; simpa using hb
  | cons e t ih =>
    intro init hb
    simp only [List.foldl_cons] at hb
    rcases ih _ hb with h1 | h1
    · split_ifs at h1 with hc
      · left; exact h1
      · right; simp only [Option.some.injEq] at h1; subst h1; simp
    · right; simp only [List.map_cons, List.mem_cons]; right; exact h1

theorem B_mem (q : Fin N → ℝ → ℝ) (h : History N) (b : Fin N) (hb : B q h = some b) :
    b ∈ h.map Prod.fst := by
  rcases foldl_B_mem q b h (0, none) hb with h1 | h1
  · simp at h1
  · exact h1

/-- the history of the index policy after `t` evaluations -/
def hist (σ : Fin N ≃ Fin N) (ω : Fin N → ℝ × ℝ) (t : ℕ) : History N :=
  ((List.finRange N).take t).map (fun s => (σ s, (ω (σ s)).2))

theorem hist_length (σ : Fin N ≃ Fin N) (ω : Fin N → ℝ × ℝ) (t : ℕ) :
    (hist σ ω t).length = min t N := by
  simp [hist]

theorem hist_zero (σ : Fin N ≃ Fin N) (ω : Fin N → ℝ × ℝ) : hist σ ω 0 = [] := by
  simp [hist]

theorem hist_succ (σ : Fin N ≃ Fin N) (ω : Fin N → ℝ × ℝ) (t : ℕ) :
    hist σ ω (t + 1) = if ht : t < N then
      hist σ ω t ++ [(σ ⟨t, ht⟩, (ω (σ ⟨t, ht⟩)).2)] else hist σ ω t := by
  unfold hist
  rw [List.take_add_one]
  split_ifs with ht
  · have : (List.finRange N)[t]? = some ⟨t, ht⟩ := by
      rw [List.getElem?_eq_getElem (by simpa using ht)]
      simp
    rw [this]; simp
  · have : (List.finRange N)[t]? = none := by
      rw [List.getElem?_eq_none]; simp; omega
    rw [this]; simp

theorem mem_hist (σ : Fin N ≃ Fin N) (ω : Fin N → ℝ × ℝ) (j : Fin N) :
    ∀ t, (j ∈ (hist σ ω t).map Prod.fst ↔ (σ.symm j).val < t) := by
  intro t
  induction t with
  | zero => simp [hist_zero]
  | succ t ih =>
    rw [hist_succ]
    split_ifs with ht
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton, ih]
      constructor
      · rintro (h | h)
        · omega
        · subst h; simp
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
        · left; exact h'
        · right
          have : σ.symm j = ⟨t, ht⟩ := Fin.ext h'
          rw [← this]; simp
    · rw [ih]
      have := (σ.symm j).isLt
      omega

section index

variable (q : Fin N → ℝ → ℝ) (σ : Fin N ≃ Fin N) (R : Fin N → ℝ)

theorem next_hist_lt (ω : Fin N → ℝ × ℝ) (t : ℕ) (ht : t < N) :
    (fidelityPolicy q σ R).next (hist σ ω t) =
      if V q (hist σ ω t) < R (σ ⟨t, ht⟩) then Decision.evaluate (σ ⟨t, ht⟩)
      else stopDecision (B q (hist σ ω t)) := by
  have hl : (hist σ ω t).length = t := by rw [hist_length]; omega
  have h1 : (hist σ ω t).length < N := by rw [hl]; exact ht
  have hf : (⟨(hist σ ω t).length, h1⟩ : Fin N) = ⟨t, ht⟩ := Fin.ext hl
  simp only [fidelityPolicy]
  rw [dif_pos h1, hf]

theorem next_hist_ge (ω : Fin N → ℝ × ℝ) (t : ℕ) (ht : N ≤ t) :
    (fidelityPolicy q σ R).next (hist σ ω t) = stopDecision (B q (hist σ ω t)) := by
  have h1 : ¬ (hist σ ω t).length < N := by rw [hist_length]; omega
  simp only [fidelityPolicy]
  rw [dif_neg h1]

/-- stopping predicate -/
def StopAt (ω : Fin N → ℝ × ℝ) (t : ℕ) : Prop :=
  ∀ ht : t < N, R (σ ⟨t, ht⟩) ≤ V q (hist σ ω t)

theorem exists_stop (ω : Fin N → ℝ × ℝ) : ∃ t, StopAt q σ R ω t :=
  ⟨N, fun ht => absurd ht (lt_irrefl N)⟩

open Classical in
noncomputable def stopN (ω : Fin N → ℝ × ℝ) : ℕ := Nat.find (exists_stop q σ R ω)

theorem stopN_le (ω : Fin N → ℝ × ℝ) : stopN q σ R ω ≤ N := by
  classical
  unfold stopN
  exact Nat.find_min' _ (fun ht => absurd ht (lt_irrefl N))

theorem runAux_stopDecision (ω : Fin N → ℝ × ℝ) (k : ℕ) (h : History N) :
    runAux (fidelityPolicy q σ R) ω (k + 1) h =
      match (fidelityPolicy q σ R).next h with
      | Decision.evaluate j =>
          if j ∈ h.map Prod.fst then (h, Decision.stopNone)
          else runAux (fidelityPolicy q σ R) ω k (h ++ [(j, (ω j).2)])
      | Decision.launch j =>
          if j ∈ h.map Prod.fst then (h, Decision.launch j) else (h, Decision.stopNone)
      | Decision.stopNone => (h, Decision.stopNone) := rfl

theorem runAux_stop_eq (ω : Fin N → ℝ × ℝ) (k : ℕ) (h : History N)
    (hn : (fidelityPolicy q σ R).next h = stopDecision (B q h)) :
    runAux (fidelityPolicy q σ R) ω (k + 1) h = (h, stopDecision (B q h)) := by
  rw [runAux_stopDecision, hn]
  cases hb : B q h with
  | none => simp [stopDecision]
  | some b =>
    simp only [stopDecision]
    rw [if_pos (B_mem q h b hb)]

theorem run_index (ω : Fin N → ℝ × ℝ) :
    run (fidelityPolicy q σ R) ω =
      (hist σ ω (stopN q σ R ω), stopDecision (B q (hist σ ω (stopN q σ R ω)))) := by
  classical
  set n := stopN q σ R ω with hn
  have hnN : n ≤ N := stopN_le q σ R ω
  have key : ∀ d, ∀ t, t + d = n →
      runAux (fidelityPolicy q σ R) ω (N + 1 - t) (hist σ ω t) =
        (hist σ ω n, stopDecision (B q (hist σ ω n))) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      simp only [add_zero] at ht
      subst ht
      have hfuel : N + 1 - n = (N - n) + 1 := by omega
      rw [hfuel]
      apply runAux_stop_eq
      by_cases hlt : n < N
      · rw [next_hist_lt q σ R ω n hlt]
        have hs : StopAt q σ R ω n := by
          rw [hn]; unfold stopN; exact Nat.find_spec (exists_stop q σ R ω)
        rw [if_neg (not_lt.2 (hs hlt))]
      · exact next_hist_ge q σ R ω n (not_lt.1 hlt)
    | succ d ih =>
      intro t ht
      have htn : t < n := by omega
      have hns : ¬ StopAt q σ R ω t := by
        have h2 : t < stopN q σ R ω := hn ▸ htn
        unfold stopN at h2
        exact Nat.find_min (exists_stop q σ R ω) h2
      have htN : t < N := by omega
      have hV : V q (hist σ ω t) < R (σ ⟨t, htN⟩) := by
        by_contra hc
        apply hns
        intro ht'
        exact not_lt.1 hc
      have hfuel : N + 1 - t = (N - t) + 1 := by omega
      rw [hfuel, runAux_stopDecision, next_hist_lt q σ R ω t htN, if_pos hV]
      simp only
      have hnot : σ ⟨t, htN⟩ ∉ (hist σ ω t).map Prod.fst := by
        rw [mem_hist]; simp
      rw [if_neg hnot]
      have : hist σ ω t ++ [(σ ⟨t, htN⟩, (ω (σ ⟨t, htN⟩)).2)] = hist σ ω (t + 1) := by
        rw [hist_succ, dif_pos htN]
      rw [this]
      have := ih (t + 1) (by omega)
      have hfuel2 : N - t = N + 1 - (t + 1) := by omega
      rw [hfuel2]; exact this
  unfold run
  have h0 := key n 0 (by omega)
  rw [hist_zero] at h0
  simpa using h0

end index

end NPCore



namespace NPCore

variable {N : ℕ}

section index

variable (q : Fin N → ℝ → ℝ) (σ : Fin N ≃ Fin N) (R : Fin N → ℝ)

theorem VB_hist_succ (ω : Fin N → ℝ × ℝ) (t : ℕ) (ht : t < N) :
    VB q (hist σ ω (t + 1)) =
      if (VB q (hist σ ω t)).1 > q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 then VB q (hist σ ω t)
      else (q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2, some (σ ⟨t, ht⟩)) := by
  rw [hist_succ, dif_pos ht, VB_append]

theorem hist_inv (ω : Fin N → ℝ × ℝ) : ∀ t : ℕ,
    0 ≤ V q (hist σ ω t) ∧
    (∀ s : Fin N, s.val < t → q (σ s) (ω (σ s)).2 ≤ V q (hist σ ω t)) ∧
    (B q (hist σ ω t) = none → V q (hist σ ω t) = 0 ∧
      ∀ s : Fin N, s.val < t → q (σ s) (ω (σ s)).2 < 0) ∧
    (∀ b, B q (hist σ ω t) = some b →
      (σ.symm b).val < t ∧ V q (hist σ ω t) = q b (ω b).2) := by
  intro t
  induction t with
  | zero =>
    simp only [hist_zero, V, B, VB, List.foldl_nil, le_refl, Nat.not_lt_zero, false_imp_iff,
      implies_true, true_and, and_self, reduceCtorEq, and_true]
  | succ t ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    by_cases ht : t < N
    · have hrec := VB_hist_succ q σ ω t ht
      set xt := q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 with hxt
      by_cases hc : V q (hist σ ω t) > xt
      · have hV : V q (hist σ ω (t+1)) = V q (hist σ ω t) := by
          simp only [V]; rw [hrec, if_pos (show (VB q (hist σ ω t)).1 > xt from hc)]
        have hB : B q (hist σ ω (t+1)) = B q (hist σ ω t) := by
          simp only [B]; rw [hrec, if_pos (show (VB q (hist σ ω t)).1 > xt from hc)]
        rw [hV, hB]
        refine ⟨i1, ?_, ?_, ?_⟩
        · intro s hs
          rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
          · exact i2 s h
          · have : s = ⟨t, ht⟩ := Fin.ext h
            subst this; exact le_of_lt hc
        · intro hn
          obtain ⟨j1, j2⟩ := i3 hn
          refine ⟨j1, fun s hs => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
          · exact j2 s h
          · have : s = ⟨t, ht⟩ := Fin.ext h
            subst this; rw [j1] at hc; exact hc
        · intro b hb
          obtain ⟨j1, j2⟩ := i4 b hb
          exact ⟨by omega, j2⟩
      · have hV : V q (hist σ ω (t+1)) = xt := by
          simp only [V]; rw [hrec, if_neg (show ¬ (VB q (hist σ ω t)).1 > xt from hc)]
        have hB : B q (hist σ ω (t+1)) = some (σ ⟨t, ht⟩) := by
          simp only [B]; rw [hrec, if_neg (show ¬ (VB q (hist σ ω t)).1 > xt from hc)]
        rw [hV, hB]
        push_neg at hc
        refine ⟨i1.trans hc, ?_, ?_, ?_⟩
        · intro s hs
          rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
          · exact (i2 s h).trans hc
          · have : s = ⟨t, ht⟩ := Fin.ext h
            subst this; exact le_refl _
        · intro hn; simp at hn
        · intro b hb
          simp only [Option.some.injEq] at hb
          subst hb
          simp [hxt]
    · have hh : hist σ ω (t+1) = hist σ ω t := by rw [hist_succ, dif_neg ht]
      rw [hh]
      refine ⟨i1, fun s hs => i2 s (by have := s.isLt; omega), fun hn => ?_, fun b hb => ?_⟩
      · obtain ⟨j1, j2⟩ := i3 hn
        exact ⟨j1, fun s hs => j2 s (by have := s.isLt; omega)⟩
      · obtain ⟨j1, j2⟩ := i4 b hb
        exact ⟨by omega, j2⟩

theorem lt_of_lt_stopN (ω : Fin N → ℝ × ℝ) (s : Fin N) (hs : s.val < stopN q σ R ω) :
    V q (hist σ ω s.val) < R (σ s) := by
  classical
  have h2 := hs
  unfold stopN at h2
  have hns := Nat.find_min (exists_stop q σ R ω) h2
  by_contra hc
  apply hns
  intro ht
  have : (⟨s.val, ht⟩ : Fin N) = s := Fin.ext rfl
  rw [this]; exact not_lt.1 hc

theorem stop_at_stopN (ω : Fin N → ℝ × ℝ) (ht : stopN q σ R ω < N) :
    R (σ ⟨stopN q σ R ω, ht⟩) ≤ V q (hist σ ω (stopN q σ R ω)) := by
  classical
  have := Nat.find_spec (exists_stop q σ R ω)
  exact this ht

theorem Am_index_eq (hσ : ∀ a b, a ≤ b → R (σ b) ≤ R (σ a)) (ω : Fin N → ℝ × ℝ)
    (hω : ∀ i, (ω i).1 = q i (ω i).2) :
    Am q R (fidelityPolicy q σ R) ω = Kv q R ω := by
  classical
  set n := stopN q σ R ω with hn
  have hnN : n ≤ N := stopN_le q σ R ω
  have hmem : ∀ i, i ∈ (hist σ ω n).map Prod.fst ↔ (σ.symm i).val < n := fun i =>
    mem_hist σ ω i n
  unfold Am
  rw [run_index q σ R ω]
  simp only [← hn]
  -- notation
  have hx : ∀ s : Fin N, q (σ s) (ω (σ s)).2 = q (σ s) (ω (σ s)).2 := fun _ => rfl
  obtain ⟨_, _, _, _⟩ := hist_inv q σ ω n
  -- positive-excess uniqueness
  have hexc : ∀ s : Fin N, s.val < n → R (σ s) < q (σ s) (ω (σ s)).2 →
      s.val + 1 = n ∧ B q (hist σ ω n) = some (σ s) := by
    intro s hs hgt
    have hVs := lt_of_lt_stopN q σ R ω s hs
    have hlast : s.val + 1 = n := by
      by_contra hne
      have hs1 : s.val + 1 < n := by omega
      have hs1N : s.val + 1 < N := by omega
      have h1 := lt_of_lt_stopN q σ R ω ⟨s.val + 1, hs1N⟩ hs1
      have h2 := (hist_inv q σ ω (s.val + 1)).2.1 s (by simp)
      have h3 := hσ s ⟨s.val + 1, hs1N⟩ (by simp [Fin.le_def])
      simp only at h1
      linarith
    refine ⟨hlast, ?_⟩
    have hrec := VB_hist_succ q σ ω s.val (by omega)
    have hse : (⟨s.val, by omega⟩ : Fin N) = s := Fin.ext rfl
    rw [hse] at hrec
    rw [← hlast]
    simp only [B]
    rw [hrec, if_neg (by simp only [gt_iff_lt, not_lt]; exact (le_of_lt (hVs.trans hgt)))]
  by_cases hA : ∃ s : Fin N, s.val < n ∧ R (σ s) < q (σ s) (ω (σ s)).2
  · obtain ⟨s, hs, hgt⟩ := hA
    obtain ⟨hlast, hB⟩ := hexc s hs hgt
    rw [hB]
    simp only [stopDecision, launchedValue]
    have hsum : (∑ i, if i ∈ (hist σ ω n).map Prod.fst then max (q i (ω i).2 - R i) 0 else 0)
        = q (σ s) (ω (σ s)).2 - R (σ s) := by
      rw [Finset.sum_eq_single (σ s)]
      · rw [if_pos ((hmem _).2 (by simpa using hs))]
        exact max_eq_left (by linarith)
      · intro i _ hi
        split_ifs with hi2
        · obtain ⟨s', rfl⟩ := σ.surjective i
          have hs' : s'.val < n := by simpa using (hmem _).1 hi2
          by_contra hne
          have : R (σ s') < q (σ s') (ω (σ s')).2 := by
            by_contra hle; push_neg at hle
            exact hne (max_eq_right (by linarith))
          obtain ⟨hl2, _⟩ := hexc s' hs' this
          apply hi
          congr 1; exact Fin.ext (by omega)
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, hω]
    have hVs := lt_of_lt_stopN q σ R ω s hs
    have hV0 := (hist_inv q σ ω s.val).1
    apply le_antisymm
    · have := le_Kv q R ω (σ s)
      rw [min_eq_right (le_of_lt hgt)] at this
      linarith
    · apply Kv_le q R ω _ (by linarith)
      intro i
      obtain ⟨s', rfl⟩ := σ.surjective i
      rcases lt_trichotomy s'.val s.val with h | h | h
      · have := (hist_inv q σ ω s.val).2.1 s' h
        have := min_le_left (q (σ s') (ω (σ s')).2) (R (σ s'))
        linarith
      · have : s' = s := Fin.ext h
        subst this
        have := min_le_right (q (σ s') (ω (σ s')).2) (R (σ s'))
        linarith
      · have := hσ s s' (le_of_lt h)
        have := min_le_right (q (σ s') (ω (σ s')).2) (R (σ s'))
        linarith
  · push_neg at hA
    have hsum : (∑ i, if i ∈ (hist σ ω n).map Prod.fst then max (q i (ω i).2 - R i) 0 else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · obtain ⟨s', rfl⟩ := σ.surjective i
        have hs' : s'.val < n := by simpa using (hmem _).1 hi
        have := hA s' hs'
        exact max_eq_right (by linarith)
      · rfl
    rw [hsum, sub_zero]
    obtain ⟨hV0, hVge, hBnone, hBsome⟩ := hist_inv q σ ω n
    -- bound for unopened prototypes
    have hun : ∀ s' : Fin N, n ≤ s'.val → R (σ s') ≤ V q (hist σ ω n) := by
      intro s' hs'
      have hnlt : n < N := lt_of_le_of_lt hs' s'.isLt
      have h1 := stop_at_stopN q σ R ω hnlt
      have h2 := hσ ⟨n, hnlt⟩ s' (by simp [Fin.le_def]; exact hs')
      simp only [← hn] at h1
      linarith
    cases hb : B q (hist σ ω n) with
    | none =>
      simp only [stopDecision, launchedValue]
      obtain ⟨hz, hneg⟩ := hBnone hb
      apply le_antisymm (Kv_nonneg q R ω)
      apply Kv_le q R ω 0 le_rfl
      intro i
      obtain ⟨s', rfl⟩ := σ.surjective i
      by_cases h : s'.val < n
      · have := hneg s' h
        have := min_le_left (q (σ s') (ω (σ s')).2) (R (σ s'))
        linarith
      · have := hun s' (not_lt.1 h)
        have := min_le_right (q (σ s') (ω (σ s')).2) (R (σ s'))
        linarith
    | some b =>
      simp only [stopDecision, launchedValue]
      obtain ⟨hbn, hVb⟩ := hBsome b hb
      rw [hω b, ← hVb]
      apply le_antisymm
      · have h1 := le_Kv q R ω b
        have h2 := hA (σ.symm b) hbn
        simp only [Equiv.apply_symm_apply] at h2
        rw [min_eq_left h2, ← hVb] at h1
        exact h1
      · apply Kv_le q R ω _ hV0
        intro i
        obtain ⟨s', rfl⟩ := σ.surjective i
        by_cases h : s'.val < n
        · have := hVge s' h
          have := min_le_left (q (σ s') (ω (σ s')).2) (R (σ s'))
          linarith
        · have := hun s' (not_lt.1 h)
          have := min_le_right (q (σ s') (ω (σ s')).2) (R (σ s'))
          linarith

end index

end NPCore



namespace NPCore

variable {N : ℕ}

section index

variable (q : Fin N → ℝ → ℝ) (σ : Fin N ≃ Fin N) (R : Fin N → ℝ)

theorem hist_meas (hqm : ∀ i, Measurable (q i)) : ∀ t : ℕ,
    Measurable (fun ω : Fin N → ℝ × ℝ => V q (hist σ ω t)) ∧
    ∀ o : Option (Fin N), MeasurableSet {ω : Fin N → ℝ × ℝ | B q (hist σ ω t) = o} := by
  intro t
  induction t with
  | zero =>
    simp only [hist_zero]
    exact ⟨measurable_const, fun o => MeasurableSet.const _⟩
  | succ t ih =>
    obtain ⟨hV, hB⟩ := ih
    by_cases ht : t < N
    · have hx : Measurable (fun ω : Fin N → ℝ × ℝ => q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2) :=
        (hqm _).comp (measurable_snd.comp (measurable_pi_apply _))
      have hc : MeasurableSet {ω : Fin N → ℝ × ℝ |
          q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 < V q (hist σ ω t)} :=
        measurableSet_lt hx hV
      have eV : (fun ω : Fin N → ℝ × ℝ => V q (hist σ ω (t + 1))) = fun ω =>
          max (V q (hist σ ω t)) (q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2) := by
        funext ω
        show (VB q (hist σ ω (t + 1))).1 = _
        rw [VB_hist_succ q σ ω t ht]
        by_cases h : (VB q (hist σ ω t)).1 > q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2
        · rw [if_pos h]; exact (max_eq_left h.le).symm
        · rw [if_neg h]; exact (max_eq_right (not_lt.1 h)).symm
      refine ⟨?_, fun o => ?_⟩
      · rw [eV]; exact hV.max hx
      · have eB : {ω : Fin N → ℝ × ℝ | B q (hist σ ω (t + 1)) = o} =
            ({ω | q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 < V q (hist σ ω t)} ∩
              {ω | B q (hist σ ω t) = o}) ∪
            ({ω | q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 < V q (hist σ ω t)}ᶜ ∩
              {_ω | some (σ ⟨t, ht⟩) = o}) := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
          show (VB q (hist σ ω (t + 1))).2 = o ↔ _
          rw [VB_hist_succ q σ ω t ht]
          by_cases h : (VB q (hist σ ω t)).1 > q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2
          · rw [if_pos h]
            have h' : q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 < V q (hist σ ω t) := h
            simp only [h', true_and, not_true_eq_false, false_and, or_false]
            rfl
          · rw [if_neg h]
            have h' : ¬ q (σ ⟨t, ht⟩) (ω (σ ⟨t, ht⟩)).2 < V q (hist σ ω t) := h
            simp only [h', false_and, not_false_eq_true, true_and, false_or]
        rw [eB]
        exact (hc.inter (hB o)).union (hc.compl.inter (MeasurableSet.const _))
    · have hh : ∀ ω, hist σ ω (t+1) = hist σ ω t := fun ω => by rw [hist_succ, dif_neg ht]
      simp only [hh]
      exact ⟨hV, hB⟩

theorem stopAt_meas (hqm : ∀ i, Measurable (q i)) (t : ℕ) :
    MeasurableSet {ω : Fin N → ℝ × ℝ | StopAt q σ R ω t} := by
  by_cases ht : t < N
  · have : {ω : Fin N → ℝ × ℝ | StopAt q σ R ω t} =
        {ω | R (σ ⟨t, ht⟩) ≤ V q (hist σ ω t)} := by
      ext ω; simp only [StopAt, Set.mem_ofPred_eq]
      exact ⟨fun h => h ht, fun h _ => h⟩
    rw [this]
    exact measurableSet_le measurable_const (hist_meas q σ hqm t).1
  · have : {ω : Fin N → ℝ × ℝ | StopAt q σ R ω t} = Set.univ := by
      ext ω; simp only [StopAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro h; exact absurd h ht
    rw [this]; exact MeasurableSet.univ

theorem stopN_meas (hqm : ∀ i, Measurable (q i)) (t : ℕ) :
    MeasurableSet {ω : Fin N → ℝ × ℝ | stopN q σ R ω = t} := by
  classical
  have : {ω : Fin N → ℝ × ℝ | stopN q σ R ω = t} =
      {ω | StopAt q σ R ω t} ∩ ⋂ s ∈ Finset.range t, {ω | StopAt q σ R ω s}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
      Set.mem_compl_iff]
    unfold stopN
    rw [Nat.find_eq_iff]
  rw [this]
  exact (stopAt_meas q σ R hqm t).inter (MeasurableSet.biInter (Set.to_countable _)
    (fun s _ => (stopAt_meas q σ R hqm s).compl))

theorem index_eventsMeas (hqm : ∀ i, Measurable (q i)) :
    EventsMeas (fidelityPolicy q σ R) := by
  classical
  intro l d
  have : {ω : Fin N → ℝ × ℝ | ((run (fidelityPolicy q σ R) ω).1.map Prod.fst,
      (run (fidelityPolicy q σ R) ω).2) = (l, d)} =
      ⋃ t ∈ Finset.range (N + 1), ⋃ o ∈ (Set.univ : Set (Option (Fin N))),
        {ω | stopN q σ R ω = t} ∩ {ω | B q (hist σ ω t) = o} ∩
          {_ω | (((List.finRange N).take t).map σ, stopDecision o) = (l, d)} := by
    ext ω
    simp only [run_index, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Finset.mem_range, Set.mem_univ, exists_true_left]
    constructor
    · intro h
      refine ⟨stopN q σ R ω, by have := stopN_le q σ R ω; omega,
        B q (hist σ ω (stopN q σ R ω)), ⟨rfl, rfl⟩, ?_⟩
      rw [← h]; simp [hist, List.map_map, Function.comp_def]
    · rintro ⟨t, _, o, ⟨h1, h2⟩, h3⟩
      rw [← h3, h1, h2]; simp [hist, List.map_map, Function.comp_def]
  rw [this]
  refine MeasurableSet.biUnion (Set.to_countable _) (fun t _ =>
    MeasurableSet.biUnion (Set.to_countable _) (fun o _ => ?_))
  exact ((stopN_meas q σ R hqm t).inter ((hist_meas q σ hqm t).2 o)).inter
    (MeasurableSet.const _)

end index

/-- Weitzman's theorem for a search problem whose payoff is a function of the observed signal. -/
theorem signal_index_optimal {N : ℕ} (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (hY : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i))
    (q : Fin N → ℝ → ℝ) (hqm : ∀ i, Measurable (q i))
    (hq : ∀ i, (fun z : ℝ × ℝ => z.1) =ᵐ[S.law i] (fun z => q i z.2))
    (R : Fin N → ℝ) (hR : ∀ i, ∫ z, max (q i z.2 - R i) 0 ∂(S.law i) = S.cost i)
    (σ : Fin N ≃ Fin N) (hσ : ∀ a b, a ≤ b → R (σ b) ≤ R (σ a)) :
    Admissible S (fidelityPolicy q σ R) ∧
    (∀ ρ : Policy N, Admissible S ρ → value S ρ ≤ value S (fidelityPolicy q σ R)) ∧
    value S (fidelityPolicy q σ R) = ∫ ω, Kv q R ω ∂S.outcomeLaw := by
  have hqi : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i) :=
    fun i => (hY i).congr (hq i)
  have hev := index_eventsMeas q σ R hqm
  have hadm : Admissible S (fidelityPolicy q σ R) := (admissible_iff S hY _).2 hev
  have hval : value S (fidelityPolicy q σ R) = ∫ ω, Kv q R ω ∂S.outcomeLaw := by
    rw [(value_eq_integral_Am S q R hY hqm hqi hR _ hev).2]
    apply integral_congr_ae
    have hall : ∀ᵐ ω ∂S.outcomeLaw, ∀ i, (ω i).1 = q i (ω i).2 :=
      ae_all_iff.2 (fun i => ae_coord S i (hq i))
    filter_upwards [hall] with ω hω
    exact Am_index_eq q σ R hσ ω hω
  refine ⟨hadm, fun ρ hρ => ?_, hval⟩
  rw [hval]
  exact value_le_integral_Kv S q R hY hqm hq hR ρ hρ

end NPCore



namespace NPCore

variable {N : ℕ}

/-- replace each measurement by its posterior value -/
noncomputable def mapH (q : Fin N → ℝ → ℝ) (h : History N) : History N :=
  h.map (fun e => (e.1, q e.1 e.2))

theorem mapH_fst (q : Fin N → ℝ → ℝ) (h : History N) :
    (mapH q h).map Prod.fst = h.map Prod.fst := by
  simp [mapH, List.map_map, Function.comp_def]

noncomputable def PhiMap (q : Fin N → ℝ → ℝ) (ω : Fin N → ℝ × ℝ) : Fin N → ℝ × ℝ :=
  fun i => (q i (ω i).2, q i (ω i).2)

theorem sim_runAux (q : Fin N → ℝ → ℝ) (ρ ρ' : Policy N)
    (hsim : ∀ h, ρ.next h = ρ'.next (mapH q h)) (ω : Fin N → ℝ × ℝ) :
    ∀ k h, runAux ρ' (PhiMap q ω) k (mapH q h) =
      (mapH q (runAux ρ ω k h).1, (runAux ρ ω k h).2) := by
  intro k
  induction k with
  | zero => intro h; simp [runAux]
  | succ k ih =>
    intro h
    simp only [runAux]
    rw [← hsim h]
    cases ρ.next h with
    | evaluate j =>
      simp only [mapH_fst]
      split_ifs with hj
      · rfl
      · have : mapH q h ++ [(j, (PhiMap q ω j).2)] = mapH q (h ++ [(j, (ω j).2)]) := by
          simp [mapH, PhiMap]
        rw [this, ih]
    | launch j => simp only [mapH_fst]; split_ifs <;> rfl
    | stopNone => rfl

theorem sim_run (q : Fin N → ℝ → ℝ) (ρ ρ' : Policy N)
    (hsim : ∀ h, ρ.next h = ρ'.next (mapH q h)) (ω : Fin N → ℝ × ℝ) :
    run ρ' (PhiMap q ω) = (mapH q (run ρ ω).1, (run ρ ω).2) := by
  have := sim_runAux q ρ ρ' hsim ω (N + 1) []
  have h0 : mapH q ([] : History N) = [] := rfl
  rw [h0] at this
  exact this

theorem PhiMap_measurable (q : Fin N → ℝ → ℝ) (hqm : ∀ i, Measurable (q i)) :
    Measurable (PhiMap q) := by
  apply measurable_pi_lambda
  intro i
  have : Measurable (fun ω : Fin N → ℝ × ℝ => q i (ω i).2) :=
    (hqm i).comp (measurable_snd.comp (measurable_pi_apply i))
  exact this.prodMk this

theorem sim_events (q : Fin N → ℝ → ℝ) (hqm : ∀ i, Measurable (q i)) (ρ ρ' : Policy N)
    (hsim : ∀ h, ρ.next h = ρ'.next (mapH q h)) (hev : EventsMeas ρ') : EventsMeas ρ := by
  intro l d
  have : {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = (l, d)} =
      PhiMap q ⁻¹' {ω | ((run ρ' ω).1.map Prod.fst, (run ρ' ω).2) = (l, d)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, sim_run q ρ ρ' hsim ω, mapH_fst]
  rw [this]
  exact PhiMap_measurable q hqm (hev l d)

theorem VB_mapH (q : Fin N → ℝ → ℝ) (h : History N) :
    VB (fun _ => id) (mapH q h) = VB q h := by
  simp [VB, mapH, List.foldl_map]

theorem sim_index (q : Fin N → ℝ → ℝ) (σ : Fin N ≃ Fin N) (R : Fin N → ℝ) (h : History N) :
    (fidelityPolicy q σ R).next h = (fidelityPolicy (fun _ => id) σ R).next (mapH q h) := by
  have hV : V (fun _ => id) (mapH q h) = V q h := by simp only [V, VB_mapH]
  have hB : B (fun _ => id) (mapH q h) = B q h := by simp only [B, VB_mapH]
  have hl : (mapH q h).length = h.length := by simp [mapH]
  simp only [fidelityPolicy, hV, hB]
  by_cases hn : h.length < N
  · rw [dif_pos hn, dif_pos (by rw [hl]; exact hn)]
    have : (⟨(mapH q h).length, by rw [hl]; exact hn⟩ : Fin N) = ⟨h.length, hn⟩ := Fin.ext hl
    rw [this]
  · rw [dif_neg hn, dif_neg (by rw [hl]; exact hn)]

end NPCore

open NPCore in
theorem solution {N : ℕ} (M : Model N) (f : Fin N → ℝ × ℝ → ℝ)
    (hf_nonneg : ∀ i z, 0 ≤ f i z) (hf_meas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, M.law i =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f i z))) :
    (∀ i, IsProbabilityMeasure (g M.toSearchProblem (fun j => Q (f j)) i) ∧
      Integrable (fun x : ℝ => x) (g M.toSearchProblem (fun j => Q (f j)) i)) ∧
    (∀ (σ : Fin N ≃ Fin N) (R : Fin N → ℝ),
      (Admissible (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost)
          (fidelityPolicy (fun _ => id) σ R) →
        Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j)))
          (fidelityPolicy (fun j => Q (f j)) σ R)) ∧
      value (M.toSearchProblem.posteriorProblem (fun j => Q (f j)))
          (fidelityPolicy (fun j => Q (f j)) σ R) =
        value (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost)
          (fidelityPolicy (fun _ => id) σ R)) ∧
    (∀ ρ : Policy N, Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ →
      ∃ ρ' : Policy N, Admissible (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ' ∧
        value (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ ≤
          value (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ') ∧
    ∀ ρ' : Policy N, Admissible (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ' →
      ∃ ρ : Policy N, Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ ∧
        value (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ =
          value (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ' := by
  classical
  set S := M.toSearchProblem with hS
  set q : Fin N → ℝ → ℝ := fun j => Q (f j) with hqdef
  set P2 := S.posteriorProblem q with hP2
  set PH := pandoraProblem (g S q) M.cost with hPH
  have hSprob : ∀ i, IsProbabilityMeasure (S.law i) := M.law_prob
  -- measurability of Q
  have hqm : ∀ i, Measurable (q i) := by
    intro i
    have hhm : Measurable (fun m : ℝ => ∫ P : ℝ, f i (P, m)) :=
      (StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
        (hf_meas i).stronglyMeasurable).measurable
    have hkm : Measurable (fun m : ℝ => ∫ P : ℝ, P * f i (P, m)) :=
      (StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
        ((measurable_fst.mul (hf_meas i)).stronglyMeasurable)).measurable
    exact hkm.div hhm
  -- integrability of Q ∘ snd (from the posterior-mean lemma)
  have hqi : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i) := by
    intro i
    have := claim_1_posterior_mean (f i) (hf_nonneg i) (hf_meas i) (S.law i) (hlaw i)
      (M.value_integrable i)
    exact (integrable_condExp).congr this.symm
  have hmq : ∀ i, Measurable (fun z : ℝ × ℝ => q i z.2) := fun i => (hqm i).comp measurable_snd
  have hgprob : ∀ i, IsProbabilityMeasure (g S q i) := fun i =>
    Measure.isProbabilityMeasure_map (hmq i).aemeasurable
  have hgint : ∀ i, Integrable (fun x : ℝ => x) (g S q i) := by
    intro i
    show Integrable (fun x : ℝ => x) ((S.law i).map (fun z => q i z.2))
    rw [integrable_map_measure (measurable_id' (α := ℝ)).aestronglyMeasurable
      (hmq i).aemeasurable]
    exact hqi i
  have hmd : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  have hm2 : ∀ i, Measurable (fun z : ℝ × ℝ => (q i z.2, z.2)) := fun i =>
    (hmq i).prodMk measurable_snd
  have hP2prob : ∀ i, IsProbabilityMeasure (P2.law i) := fun i =>
    Measure.isProbabilityMeasure_map (hm2 i).aemeasurable
  have hPHprob : ∀ i, IsProbabilityMeasure (PH.law i) := fun i =>
    Measure.isProbabilityMeasure_map hmd.aemeasurable
  have hY2 : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (P2.law i) := by
    intro i
    show Integrable (fun z : ℝ × ℝ => z.1) ((S.law i).map (fun z => (q i z.2, z.2)))
    rw [integrable_map_measure measurable_fst.aestronglyMeasurable (hm2 i).aemeasurable]
    exact hqi i
  have hYH : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (PH.law i) := by
    intro i
    show Integrable (fun z : ℝ × ℝ => z.1) ((g S q i).map (fun x => (x, x)))
    rw [integrable_map_measure measurable_fst.aestronglyMeasurable hmd.aemeasurable]
    exact hgint i
  have hq2 : ∀ i, (fun z : ℝ × ℝ => z.1) =ᵐ[P2.law i] (fun z => q i z.2) := by
    intro i
    show ∀ᵐ z ∂((S.law i).map (fun z => (q i z.2, z.2))), z.1 = q i z.2
    have hms : MeasurableSet {z : ℝ × ℝ | z.1 = q i z.2} :=
      measurableSet_eq_fun measurable_fst (hmq i)
    rw [ae_map_iff (hm2 i).aemeasurable hms]
    exact Filter.Eventually.of_forall (fun x => rfl)
  -- the outcome law of PH is the image of that of P2 under PhiMap
  have hlawmap : PH.outcomeLaw = Measure.map (PhiMap q) P2.outcomeLaw := by
    have hφ : ∀ i, Measurable (fun z : ℝ × ℝ => (q i z.2, q i z.2)) := fun i =>
      (hmq i).prodMk (hmq i)
    have _ : ∀ i, SigmaFinite (Measure.map (fun z : ℝ × ℝ => (q i z.2, q i z.2)) (P2.law i)) :=
      fun i => by
        have := Measure.isProbabilityMeasure_map (μ := P2.law i) (hφ i).aemeasurable
        infer_instance
    have := Measure.pi_map_pi (μ := P2.law) (f := fun i (z : ℝ × ℝ) => (q i z.2, q i z.2))
      (fun i => (hφ i).aemeasurable)
    unfold SearchProblem.outcomeLaw
    rw [show (PhiMap q) = (fun (x : Fin N → ℝ × ℝ) i => (q i (x i).2, q i (x i).2)) from rfl,
      this]
    congr 1
    funext i
    show (g S q i).map (fun x => (x, x)) =
      ((S.law i).map (fun z => (q i z.2, z.2))).map (fun z => (q i z.2, q i z.2))
    simp only [g]
    rw [Measure.map_map hmd (hmq i), Measure.map_map (hφ i) (hm2 i)]
    rfl
  -- generic simulation of values
  have sim_value : ∀ ρ ρ' : Policy N, (∀ h, ρ.next h = ρ'.next (mapH q h)) →
      EventsMeas ρ' → value P2 ρ = value PH ρ' := by
    intro ρ ρ' hsim hev'
    unfold value
    rw [hlawmap, integral_map (PhiMap_measurable q hqm).aemeasurable
      (netPayoff_measurable PH ρ' hev').aestronglyMeasurable]
    apply integral_congr_ae
    have hall : ∀ᵐ ω ∂P2.outcomeLaw, ∀ i, (ω i).1 = q i (ω i).2 :=
      ae_all_iff.2 (fun i => ae_coord P2 i (hq2 i))
    filter_upwards [hall] with ω hω
    simp only [netPayoff, sim_run q ρ ρ' hsim ω]
    have hc : ((mapH q (run ρ ω).1).map (fun e => PH.cost e.1)) =
        ((run ρ ω).1.map (fun e => P2.cost e.1)) := by
      simp [mapH, List.map_map, Function.comp_def, hPH, hP2, pandoraProblem,
        SearchProblem.posteriorProblem, hS]
    rw [hc]
    congr 1
    cases (run ρ ω).2 with
    | evaluate j => rfl
    | launch j => simp only [launchedValue, PhiMap]; exact hω j
    | stopNone => rfl
  refine ⟨fun i => ⟨hgprob i, hgint i⟩, ?_, ?_, ?_⟩
  · intro σ R
    refine ⟨fun hadm => ?_, ?_⟩
    · exact (admissible_iff P2 hY2 _).2
        (sim_events q hqm _ _ (sim_index q σ R) hadm.1)
    · exact sim_value _ _ (sim_index q σ R) (index_eventsMeas _ σ R (fun _ => measurable_id))
  · intro ρ hρ
    -- choose reservation prices and an ordering
    have hroot : ∀ i, ∃ r : ℝ, IsLeast {r : ℝ | ∫ x, max (x - r) 0 ∂(g S q i) = M.cost i} r :=
      fun i => (footnote_4 (g S q i) (hgint i) (M.cost i) (M.cost_pos i)).2.2.2
    choose R hR using hroot
    let σ : Fin N ≃ Fin N := Tuple.sort (fun i => -R i)
    have hσ : ∀ a b, a ≤ b → R (σ b) ≤ R (σ a) := by
      intro a b hab
      have := Tuple.monotone_sort (fun i => -R i) hab
      simp only [Function.comp_apply, neg_le_neg_iff] at this
      exact this
    have hR2 : ∀ i, ∫ z, max (q i z.2 - R i) 0 ∂(P2.law i) = P2.cost i := by
      intro i
      show ∫ z, max (q i z.2 - R i) 0 ∂((S.law i).map (fun z => (q i z.2, z.2))) = M.cost i
      have hmax : Measurable (fun z : ℝ × ℝ => max (q i z.2 - R i) 0) :=
        ((hmq i).sub_const _).max measurable_const
      rw [integral_map (hm2 i).aemeasurable hmax.aestronglyMeasurable]
      have := (hR i).1
      simp only [Set.mem_ofPred_eq] at this
      rw [← this]
      show _ = ∫ x, max (x - R i) 0 ∂((S.law i).map (fun z => q i z.2))
      have hmax2 : Measurable (fun x : ℝ => max (x - R i) 0) :=
        ((measurable_id' (α := ℝ)).sub_const _).max measurable_const
      rw [integral_map (hmq i).aemeasurable hmax2.aestronglyMeasurable]
    obtain ⟨_, hopt, _⟩ := signal_index_optimal P2 hY2 q hqm hq2 R hR2 σ hσ
    refine ⟨fidelityPolicy (fun _ => id) σ R,
      (admissible_iff PH hYH _).2 (index_eventsMeas _ σ R (fun _ => measurable_id)), ?_⟩
    rw [← sim_value _ _ (sim_index q σ R) (index_eventsMeas _ σ R (fun _ => measurable_id))]
    exact hopt ρ hρ
  · intro ρ' hρ'
    let ρ : Policy N := ⟨fun h => ρ'.next (mapH q h)⟩
    have hsim : ∀ h, ρ.next h = ρ'.next (mapH q h) := fun h => rfl
    exact ⟨ρ, (admissible_iff P2 hY2 _).2 (sim_events q hqm ρ ρ' hsim hρ'.1),
      sim_value ρ ρ' hsim hρ'.1⟩


