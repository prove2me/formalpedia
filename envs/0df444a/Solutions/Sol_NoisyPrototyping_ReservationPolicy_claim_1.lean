-- Prove2me | solution 1 for NoisyPrototyping.ReservationPolicy.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:24:01.253901+00:00
-- url     : https://prove2.me/submissions/49907500-ce6b-4f09-a987-d2bc86059cf8

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model
import Theorems.Thm_NoisyPrototyping_ReservationPolicy_claim_1_posterior_mean

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

theorem integral_indicator_meas_dep (S : SearchProblem N) [∀ i, IsProbabilityMeasure (S.law i)]
    (j : Fin N) (A : Set (Fin N → ℝ × ℝ)) (hA : MeasurableSet A)
    (hdep : ∀ ω ω' : Fin N → ℝ × ℝ, (∀ i, (ω i).2 = (ω' i).2) → (ω ∈ A ↔ ω' ∈ A))
    (φ : ℝ × ℝ → ℝ) (hφm : Measurable φ) (hφi : Integrable φ (S.law j))
    (hφ0 : ∀ B : Set ℝ, MeasurableSet B → ∫ z in Prod.snd ⁻¹' B, φ z ∂(S.law j) = 0) :
    ∫ ω, A.indicator (fun ω => φ (ω j)) ω ∂S.outcomeLaw = 0 := by
  classical
  set μ := S.outcomeLaw with hμ
  have _ : IsProbabilityMeasure μ := by
    rw [hμ]; unfold SearchProblem.outcomeLaw; infer_instance
  have hind : iIndepFun (fun k (ω : Fin N → ℝ × ℝ) => ω k) μ :=
    iIndepFun_pi (μ := S.law) (X := fun _ (z : ℝ × ℝ) => z) (fun _ => aemeasurable_id)
  have hST : Disjoint ({j}ᶜ : Finset (Fin N)) {j} := disjoint_compl_left
  have hI := hind.indepFun_finset ({j}ᶜ) {j} hST (fun k => measurable_pi_apply k)
  let G : (({j} : Finset (Fin N)) → ℝ × ℝ) → ℝ × ℝ := fun r => r ⟨j, Finset.mem_singleton_self j⟩
  have hG : Measurable G := measurable_pi_apply _
  have hUV := hI.comp measurable_id hG
  let U : (Fin N → ℝ × ℝ) → (({j}ᶜ : Finset (Fin N)) → ℝ × ℝ) := fun ω k => ω k
  have hU : Measurable U := measurable_pi_lambda _ (fun k => measurable_pi_apply _)
  have hV : Measurable (fun ω : Fin N → ℝ × ℝ => ω j) := measurable_pi_apply j
  have hUV' : IndepFun U (fun ω : Fin N → ℝ × ℝ => ω j) μ := hUV
  have hmap := hUV'.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable
  have hmapV : Measure.map (fun ω : Fin N → ℝ × ℝ => ω j) μ = S.law j :=
    (measurePreserving_eval S.law j).map_eq
  rw [hmapV] at hmap
  let F : (({j}ᶜ : Finset (Fin N)) → ℝ × ℝ) × (ℝ × ℝ) → (Fin N → ℝ × ℝ) := fun p i =>
    if h : i = j then p.2 else p.1 ⟨i, by simpa using h⟩
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    by_cases h : i = j
    · simp only [F, h, dite_true]; exact measurable_snd
    · simp only [F, h, dite_false]; exact (measurable_pi_apply _).comp measurable_fst
  have hFUV : ∀ ω, F (U ω, ω j) = ω := by
    intro ω; funext i
    by_cases h : i = j
    · subst h; simp [F]
    · simp [F, h, U]
  set ψ : (Fin N → ℝ × ℝ) → ℝ := A.indicator (fun ω => φ (ω j)) with hψ
  have hψm : Measurable ψ := (hφm.comp hV).indicator hA
  have hψi : Integrable ψ μ := by
    have hmp := measurePreserving_eval S.law j
    have hmap' : Measure.map (fun f : Fin N → ℝ × ℝ => f j) μ = S.law j := hmp.map_eq
    have : Integrable φ (Measure.map (fun f : Fin N → ℝ × ℝ => f j) μ) := by
      rw [hmap']; exact hφi
    exact (this.comp_measurable hV).indicator hA
  let Ψ := ψ ∘ F
  have hΨm : Measurable Ψ := hψm.comp hF
  have hpair : Measurable (fun ω : Fin N → ℝ × ℝ => (U ω, ω j)) := hU.prodMk hV
  have e1 : ∫ ω, ψ ω ∂μ = ∫ p, Ψ p ∂(Measure.map (fun ω => (U ω, ω j)) μ) := by
    rw [integral_map hpair.aemeasurable hΨm.aestronglyMeasurable]
    congr 1; funext ω; simp only [Ψ, Function.comp_apply, hFUV]
  have hΨi : Integrable Ψ (Measure.map (fun ω => (U ω, ω j)) μ) := by
    rw [integrable_map_measure hΨm.aestronglyMeasurable hpair.aemeasurable]
    have : Ψ ∘ (fun ω => (U ω, ω j)) = ψ := by
      funext ω; simp only [Ψ, Function.comp_apply, hFUV]
    rw [this]; exact hψi
  rw [hmap] at e1 hΨi
  show ∫ ω, ψ ω ∂μ = 0
  rw [e1, integral_prod _ hΨi]
  have hin : ∀ u, ∫ z, Ψ (u, z) ∂(S.law j) = 0 := by
    intro u
    let B : Set ℝ := (fun m : ℝ => F (u, ((0 : ℝ), m))) ⁻¹' A
    have hBm : MeasurableSet B := by
      have : Measurable (fun m : ℝ => F (u, ((0 : ℝ), m))) :=
        hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      exact this hA
    have : (fun z => Ψ (u, z)) = (Prod.snd ⁻¹' B).indicator φ := by
      funext z
      have hmem : F (u, z) ∈ A ↔ z ∈ Prod.snd ⁻¹' B := by
        simp only [Set.mem_preimage, B]
        apply hdep
        intro i
        by_cases h : i = j
        · subst h; simp [F]
        · simp [F, h]
      have hFj : F (u, z) j = z := by simp [F]
      by_cases hz : z ∈ Prod.snd ⁻¹' B
      · rw [Set.indicator_of_mem hz]
        simp only [Ψ, Function.comp_apply, hψ]
        rw [Set.indicator_of_mem (hmem.2 hz), hFj]
      · rw [Set.indicator_of_notMem hz]
        simp only [Ψ, Function.comp_apply, hψ]
        rw [Set.indicator_of_notMem (fun h => hz (hmem.1 h))]
    rw [this, integral_indicator (measurable_snd hBm)]
    exact hφ0 B hBm
  simp only [hin, integral_zero]

end NPCore

open NPCore in
theorem solution {N : ℕ} (M : Model N) (f : Fin N → ℝ × ℝ → ℝ)
    (hf_nonneg : ∀ i z, 0 ≤ f i z) (hf_meas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, M.law i =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f i z)))
    (ρ : Policy N) :
    (Admissible M.toSearchProblem ρ ↔
      Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ) ∧
    (Admissible M.toSearchProblem ρ →
      value M.toSearchProblem ρ =
        value (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ) := by
  classical
  set S := M.toSearchProblem with hS
  set q : Fin N → ℝ → ℝ := fun j => Q (f j) with hqdef
  set P2 := S.posteriorProblem q with hP2
  have hSprob : ∀ i, IsProbabilityMeasure (S.law i) := M.law_prob
  have hqm : ∀ i, Measurable (q i) := by
    intro i
    have hhm : Measurable (fun m : ℝ => ∫ P : ℝ, f i (P, m)) :=
      (StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
        (hf_meas i).stronglyMeasurable).measurable
    have hkm : Measurable (fun m : ℝ => ∫ P : ℝ, P * f i (P, m)) :=
      (StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
        ((measurable_fst.mul (hf_meas i)).stronglyMeasurable)).measurable
    exact hkm.div hhm
  have hpm : ∀ i, (fun z : ℝ × ℝ => q i z.2) =ᵐ[S.law i]
      (S.law i)[fun z : ℝ × ℝ => z.1 | MeasurableSpace.comap Prod.snd inferInstance] :=
    fun i => claim_1_posterior_mean (f i) (hf_nonneg i) (hf_meas i) (S.law i) (hlaw i)
      (M.value_integrable i)
  have hqi : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i) := fun i =>
    (integrable_condExp).congr (hpm i).symm
  have hmq : ∀ i, Measurable (fun z : ℝ × ℝ => q i z.2) := fun i => (hqm i).comp measurable_snd
  have hm2 : ∀ i, Measurable (fun z : ℝ × ℝ => (q i z.2, z.2)) := fun i =>
    (hmq i).prodMk measurable_snd
  have hP2prob : ∀ i, IsProbabilityMeasure (P2.law i) := fun i =>
    Measure.isProbabilityMeasure_map (hm2 i).aemeasurable
  have hY2 : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (P2.law i) := by
    intro i
    show Integrable (fun z : ℝ × ℝ => z.1) ((S.law i).map (fun z => (q i z.2, z.2)))
    rw [integrable_map_measure measurable_fst.aestronglyMeasurable (hm2 i).aemeasurable]
    exact hqi i
  have hYS : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i) := M.value_integrable
  have hiff : Admissible S ρ ↔ Admissible P2 ρ :=
    (admissible_iff S hYS ρ).trans (admissible_iff P2 hY2 ρ).symm
  refine ⟨hiff, fun hadm => ?_⟩
  have hev := hadm.1
  -- the outcome law of P2 is the image of that of S
  let T : (Fin N → ℝ × ℝ) → (Fin N → ℝ × ℝ) := fun ω i => (q i (ω i).2, (ω i).2)
  have hT : Measurable T := by
    apply measurable_pi_lambda; intro i
    exact (hm2 i).comp (measurable_pi_apply i)
  have hlawmap : P2.outcomeLaw = Measure.map T S.outcomeLaw := by
    have _ : ∀ i, SigmaFinite (Measure.map (fun z : ℝ × ℝ => (q i z.2, z.2)) (S.law i)) :=
      fun i => by
        have := Measure.isProbabilityMeasure_map (μ := S.law i) (hm2 i).aemeasurable
        infer_instance
    have := Measure.pi_map_pi (μ := S.law) (f := fun i (z : ℝ × ℝ) => (q i z.2, z.2))
      (fun i => (hm2 i).aemeasurable)
    unfold SearchProblem.outcomeLaw
    rw [show T = (fun (x : Fin N → ℝ × ℝ) i => (q i (x i).2, (x i).2)) from rfl, this]
    rfl
  have hn2m := netPayoff_measurable P2 ρ hev
  have hv2 : value P2 ρ = ∫ ω, netPayoff P2 ρ (T ω) ∂S.outcomeLaw := by
    unfold value
    rw [hlawmap, integral_map hT.aemeasurable hn2m.aestronglyMeasurable]
  have hn2i : Integrable (fun ω => netPayoff P2 ρ (T ω)) S.outcomeLaw := by
    have := netPayoff_integrable P2 hY2 ρ hev
    rw [hlawmap, integrable_map_measure hn2m.aestronglyMeasurable hT.aemeasurable] at this
    exact this
  have hn1i := netPayoff_integrable S hYS ρ hev
  -- pointwise difference
  let A : Fin N → Set (Fin N → ℝ × ℝ) := fun j => {ω | (run ρ ω).2 = Decision.launch j}
  let φ : Fin N → ℝ × ℝ → ℝ := fun j z => z.1 - q j z.2
  have hdiff : ∀ ω, netPayoff S ρ ω - netPayoff P2 ρ (T ω) =
      ∑ j, (A j).indicator (fun ω => φ j (ω j)) ω := by
    intro ω
    have hrun : run ρ (T ω) = run ρ ω := run_congr ρ (T ω) ω (fun i => rfl)
    simp only [netPayoff, hrun]
    have hc : ((run ρ ω).1.map (fun e => P2.cost e.1)) = ((run ρ ω).1.map (fun e => S.cost e.1)) :=
      rfl
    rw [hc]
    cases hd : (run ρ ω).2 with
    | evaluate k =>
      simp only [launchedValue, sub_self]
      symm; apply Finset.sum_eq_zero; intro j _
      apply Set.indicator_of_notMem
      simp [A, hd]
    | stopNone =>
      simp only [launchedValue, sub_self]
      symm; apply Finset.sum_eq_zero; intro j _
      apply Set.indicator_of_notMem
      simp [A, hd]
    | launch k =>
      simp only [launchedValue, sub_sub_sub_cancel_right]
      rw [Finset.sum_eq_single k]
      · rw [Set.indicator_of_mem (show ω ∈ A k by simp [A, hd])]
      · intro j _ hjk
        apply Set.indicator_of_notMem
        simp only [A, Set.mem_ofPred_eq, hd, Decision.launch.injEq]
        exact fun h => hjk h.symm
      · intro h; exact absurd (Finset.mem_univ k) h
  have hzero : ∀ j, ∫ ω, (A j).indicator (fun ω => φ j (ω j)) ω ∂S.outcomeLaw = 0 := by
    intro j
    apply integral_indicator_meas_dep S j (A j) (measurableSet_launch ρ hev j)
    · intro ω ω' h
      simp only [A, Set.mem_ofPred_eq, run_congr ρ ω ω' h]
    · exact measurable_fst.sub (hmq j)
    · exact (hYS j).sub (hqi j)
    · intro B hB
      have hs : MeasurableSet[MeasurableSpace.comap Prod.snd inferInstance]
          (Prod.snd ⁻¹' B : Set (ℝ × ℝ)) := ⟨B, hB, rfl⟩
      simp only [φ]
      rw [integral_sub (hYS j).integrableOn (hqi j).integrableOn]
      have e : ∫ z in Prod.snd ⁻¹' B, q j z.2 ∂(S.law j) = ∫ z in Prod.snd ⁻¹' B,
          ((S.law j)[fun z : ℝ × ℝ => z.1 | MeasurableSpace.comap Prod.snd inferInstance]) z
            ∂(S.law j) :=
        setIntegral_congr_ae (measurable_snd hB) (by
          filter_upwards [hpm j] with z hz _ using hz)
      rw [e]
      rw [setIntegral_condExp (measurable_snd.comap_le) (hYS j) hs, sub_self]
  have : value S ρ - value P2 ρ = 0 := by
    rw [hv2]
    unfold value
    rw [← integral_sub hn1i hn2i]
    simp only [hdiff]
    rw [integral_finsetSum _ (fun j _ => ?_)]
    · exact Finset.sum_eq_zero (fun j _ => hzero j)
    · exact ((hYS j).sub (hqi j)) |> fun h => by
        have hmp := measurePreserving_eval S.law j
        have hmap' : Measure.map (fun f : Fin N → ℝ × ℝ => f j) S.outcomeLaw = S.law j :=
          hmp.map_eq
        have : Integrable (φ j) (Measure.map (fun f : Fin N → ℝ × ℝ => f j) S.outcomeLaw) := by
          rw [hmap']; exact h
        exact (this.comp_measurable (measurable_pi_apply j)).indicator
          (measurableSet_launch ρ hev j)
  linarith


