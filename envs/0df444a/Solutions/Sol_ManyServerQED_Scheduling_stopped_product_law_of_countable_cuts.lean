-- Prove2me | solution 1 for ManyServerQED.Scheduling.stopped_product_law_of_countable_cuts
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:59:42.18402+00:00
-- url     : https://prove2.me/submissions/b157321d-c816-4677-84ef-331c018e2b9e

import Mathlib

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal

private theorem countable_cut_product {Ω I β : Type*} [m : MeasurableSpace Ω] [Countable I] [MeasurableSpace β]
    (P : Measure Ω) (Q : Measure β) (K : Ω → I) (F : I → Ω → β)
    (G : I → MeasurableSpace Ω) (hG : ∀ j, G j ≤ m)
    (hF : ∀ j, Measurable (F j))
    (hL : ∀ j, Measure.map (F j) P = Q)
    (hInd : ∀ j, Indep (G j) (MeasurableSpace.comap (F j) inferInstance) P)
    (A : Set Ω) (B : Set β) (hB : MeasurableSet B)
    (hA : ∀ j, MeasurableSet[G j] (A ∩ {ω | K ω = j})) :
    P (A ∩ {ω | F (K ω) ω ∈ B}) = P A * Q B := by
  let U j := A ∩ {ω | K ω = j}
  let V j := U j ∩ (F j ⁻¹' B)
  have hU (j : I) : MeasurableSet (U j) := hG j _ (hA j)
  have hV (j : I) : MeasurableSet (V j) := (hU j).inter ((hF j) hB)
  have hu : Pairwise (Disjoint on U) := by
    intro a b h
    change Disjoint (U a) (U b)
    rw [Set.disjoint_left]
    intro ω hω hω'
    exact h (hω.2.symm.trans hω'.2)
  have hv : Pairwise (Disjoint on V) := by
    intro a b h
    exact (hu h).mono inter_subset_left inter_subset_left
  have hAeq : A = ⋃ j, U j := by
    ext ω
    constructor
    · intro h
      exact mem_iUnion_of_mem (K ω) ⟨h, rfl⟩
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact hj.1
  have hReq : (A ∩ {ω | F (K ω) ω ∈ B}) = ⋃ j, V j := by
    ext ω
    constructor
    · rintro ⟨hA, hB⟩
      exact mem_iUnion_of_mem (K ω) ⟨⟨hA, rfl⟩, hB⟩
    · intro h
      obtain ⟨j, ⟨⟨ha, hk⟩, hf⟩⟩ := mem_iUnion.mp h
      refine ⟨ha, ?_⟩
      change F (K ω) ω ∈ B
      rw [hk]
      exact hf
  have hstep (j : I) : P (V j) = P (U j) * Q B := by
    have hf : MeasurableSet[MeasurableSpace.comap (F j) inferInstance] (F j ⁻¹' B) :=
      ⟨B, hB, rfl⟩
    have hl' : P (F j ⁻¹' B) = Q B := by rw [← Measure.map_apply (hF j) hB, hL j]
    change P (U j ∩ (F j ⁻¹' B)) = _
    rw [((hInd j).indepSet_of_measurableSet (hA j) hf).measure_inter_eq_mul, hl']
  rw [hReq, measure_iUnion hv hV, hAeq, measure_iUnion hu hU]
  simp only [hstep, ENNReal.tsum_mul_right]

private theorem stable_map {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (P : Measure Ω) [IsFiniteMeasure P]
    (Q : Measure (∀ i, E i)) (f : ℕ → Ω → (∀ i, E i)) (g : Ω → (∀ i, E i))
    (hf : ∀ j, Measurable (f j)) (hg : Measurable g)
    (hLaw : ∀ j, Measure.map (f j) P = Q)
    (hStable : ∀ ω i, ∀ᶠ j in atTop, f j ω i = g ω i) :
    Measure.map g P = Q := by
  classical
  have hU : Measure.map g P univ = Q univ := by
    rw [← hLaw 0, Measure.map_apply hg MeasurableSet.univ,
      Measure.map_apply (hf 0) MeasurableSet.univ]
    simp only [preimage_univ]
  refine ext_of_generate_finite (measurableCylinders E) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun C hC => ?_) hU
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders C).mp hC
  let C := cylinder s S
  have hC : MeasurableSet C := hS.cylinder
  let W j := f j ⁻¹' C
  let V := g ⁻¹' C
  have hW (j : ℕ) : MeasurableSet (W j) := hf j hC
  have hMass (j : ℕ) : P (W j) = Q C := by
    rw [← hLaw j, Measure.map_apply (hf j) hC]
  have hSt (ω : Ω) : ∀ᶠ j in atTop, (ω ∈ W j ↔ ω ∈ V) := by
    have h : ∀ᶠ j in atTop, ∀ i ∈ s, f j ω i = g ω i :=
      (Filter.eventually_all_finset s).2 (fun i _ => hStable ω i)
    filter_upwards [h] with j hj
    change s.restrict (f j ω) ∈ S ↔ s.restrict (g ω) ∈ S
    rw [show s.restrict (f j ω) = s.restrict (g ω) from funext fun i => hj i.1 i.2]
  let U (m : ℕ) := ⋂ j, ⋂ (_ : m ≤ j), W j
  let L (m : ℕ) := ⋃ j, ⋃ (_ : m ≤ j), W j
  have hUeq : V = ⋃ m, U m := by
    ext ω
    simp only [U, mem_iUnion, mem_iInter]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := eventually_atTop.1 (hSt ω)
      exact ⟨m, fun j hj => (hm j hj).2 h⟩
    · rintro ⟨m, hm⟩
      obtain ⟨b, hb⟩ := eventually_atTop.1 (hSt ω)
      exact (hb (max m b) (le_max_right _ _)).1 (hm (max m b) (le_max_left _ _))
  have hLeq : V = ⋂ m, L m := by
    ext ω
    simp only [L, mem_iUnion, mem_iInter]
    constructor
    · intro h m
      obtain ⟨b, hb⟩ := eventually_atTop.1 (hSt ω)
      exact ⟨max m b, le_max_left _ _, (hb _ (le_max_right _ _)).2 h⟩
    · intro h
      obtain ⟨b, hb⟩ := eventually_atTop.1 (hSt ω)
      obtain ⟨j, hj, hw⟩ := h b
      exact (hb j hj).1 hw
  have hUM : Monotone U := by
    intro a b hab ω hw
    simp only [U, mem_iInter] at *
    exact fun j hj => hw j (hab.trans hj)
  have hLM : Antitone L := by
    intro a b hab ω hw
    simp only [L, mem_iUnion] at *
    obtain ⟨j, hj, hw⟩ := hw
    exact ⟨j, hab.trans hj, hw⟩
  have hLm (m : ℕ) : MeasurableSet (L m) :=
    MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ : m ≤ j => hW j))
  rw [Measure.map_apply hg hC]
  change P V = Q C
  apply le_antisymm
  · rw [hUeq, hUM.measure_iUnion]
    refine iSup_le (fun m => ?_)
    rw [← hMass m]
    exact measure_mono (iInter₂_subset m le_rfl)
  · rw [hLeq, hLM.measure_iInter (fun m => (hLm m).nullMeasurableSet)
      ⟨0, measure_ne_top P (L 0)⟩]
    refine le_iInf (fun m => ?_)
    rw [← hMass m]
    exact measure_mono (fun ω h => mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨le_rfl, h⟩⟩)

private theorem grid_from_cells {Ω I J : Type*} [m : MeasurableSpace Ω] [Countable J] [MeasurableSpace J]
    [DiscreteMeasurableSpace J] {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (P : Measure Ω) [IsFiniteMeasure P] (Q : Measure (∀ i, E i))
    (G : ℕ → J → MeasurableSpace Ω) (F : ℕ → J → Ω → (∀ i, E i))
    (K : ℕ → Ω → J) (g : Ω → (∀ i, E i)) (A : Set Ω)
    (hK : ∀ n, Measurable (K n)) (hg : Measurable g)
    (hG : ∀ n j, G n j ≤ m) (hF : ∀ n j, Measurable (F n j))
    (hLaw : ∀ n j, Measure.map (F n j) P = Q)
    (hInd : ∀ n j, Indep (G n j) (MeasurableSpace.comap (F n j) inferInstance) P)
    (hCell : ∀ n j, MeasurableSet[G n j] (A ∩ {ω | K n ω = j}))
    (hStable : ∀ ω i, ∀ᶠ n in atTop, F n (K n ω) ω i = g ω i) :
    Measure.map g (P.restrict A) = P A • Q := by
  classical
  let f (n : ℕ) (ω : Ω) := F n (K n ω) ω
  have hf (n : ℕ) : Measurable (f n) :=
    (measurable_from_prod_countable_left (f := fun v : Ω × J => F n v.2 v.1) (fun j => hF n j)).comp (measurable_id.prodMk (hK n))
  apply stable_map (P.restrict A) (P A • Q) f g hf hg _ hStable
  intro n
  ext B hB
  rw [Measure.map_apply (hf n) hB, Measure.restrict_apply ((hf n) hB), inter_comm,
    Measure.smul_apply, smul_eq_mul]
  exact countable_cut_product P Q (K n) (F n) (G n) (hG n) (hF n)
    (hLaw n) (hInd n) A B hB (hCell n)

theorem solution {Ω I J : Type*} [m : MeasurableSpace Ω] [Countable J]
    [PartialOrder J] [MeasurableSpace J] [DiscreteMeasurableSpace J]
    (P : Measure Ω) [IsFiniteMeasure P] (Q : Measure (I → ℝ))
    (G : ℕ → J → MeasurableSpace Ω) (F : ℕ → J → Ω → I → ℝ)
    (K : ℕ → Ω → J) (g : Ω → I → ℝ) (A : Set Ω)
    (hG : ∀ n j, G n j ≤ m) (hMono : ∀ n, Monotone (G n))
    (hF : ∀ n j, Measurable (F n j))
    (hLaw : ∀ n j, Measure.map (F n j) P = Q)
    (hInd : ∀ n j, Indep (G n j) (MeasurableSpace.comap (F n j) inferInstance) P)
    (hLower : ∀ n j, MeasurableSet[G n j] (A ∩ {ω | K n ω ≤ j}))
    (hIndex : ∀ n j, MeasurableSet {ω | K n ω ≤ j})
    (hStable : ∀ ω i, ∀ᶠ n in atTop, F n (K n ω) ω i = g ω i) :
    Measurable g ∧ Measure.map g (P.restrict A) = P A • Q := by
  have cell (B : Set Ω) (n : ℕ) (j : J) : B ∩ {ω | K n ω = j} =
      (B ∩ {ω | K n ω ≤ j}) \ ⋃ l, ⋃ (_ : l < j), (B ∩ {ω | K n ω ≤ l}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_iUnion]
    constructor
    · rintro ⟨hB, rfl⟩
      exact ⟨⟨hB, le_rfl⟩, fun ⟨_, hl, _, hk⟩ => (not_lt_of_ge hk) hl⟩
    · rintro ⟨⟨hB, hj⟩, hn⟩
      refine ⟨hB, le_antisymm hj ?_⟩
      by_contra! h
      exact hn ⟨K n ω, lt_of_le_not_ge hj h, hB, le_rfl⟩
  have hK (n : ℕ) : Measurable (K n) := by
    apply measurable_to_countable'
    intro j
    change MeasurableSet {ω | K n ω = j}
    rw [← univ_inter {ω | K n ω = j}, cell, univ_inter]
    have hS : MeasurableSet (⋃ l, ⋃ (_ : l < j), (univ ∩ {ω | K n ω ≤ l})) :=
      MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ => MeasurableSet.univ.inter (hIndex n l)
    exact (hIndex n j).diff hS
  have hf (n : ℕ) : Measurable (fun ω => F n (K n ω) ω) :=
    (measurable_from_prod_countable_left (f := fun v : Ω × J => F n v.2 v.1)
      (fun j => hF n j)).comp (measurable_id.prodMk (hK n))
  have hg : Measurable g := measurable_pi_lambda _ fun i =>
    measurable_of_tendsto_metrizable (fun n => (measurable_pi_apply i).comp (hf n))
      (tendsto_pi_nhds.2 fun ω => by
        apply Tendsto.congr' _ (tendsto_const_nhds (x := g ω i))
        filter_upwards [hStable ω i] with n hn
        exact hn.symm)
  refine ⟨hg, grid_from_cells P Q G F K g A hK hg hG hF hLaw hInd ?_ hStable⟩
  intro n j
  rw [cell]
  exact (hLower n j).diff (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun h =>
    hMono n h.le _ (hLower n l))
