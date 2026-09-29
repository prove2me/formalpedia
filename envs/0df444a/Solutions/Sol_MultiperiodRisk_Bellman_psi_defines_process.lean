-- Prove2me | solution 1 for MultiperiodRisk.Bellman.psi_defines_process
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:53:28.961981+00:00
-- url     : https://prove2.me/submissions/6ab9ca5a-ad7f-40d3-8bba-8eb78bffa2bf

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

theorem aux_pdp_unique {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)} {g₁ g₂ : Ω → ℝ}
    (h₁ : IsEssInf μ m' S g₁) (h₂ : IsEssInf μ m' S g₂) : g₁ =ᵐ[μ] g₂ :=
  (h₂.2.2 g₁ h₁.1 h₁.2.1).antisymm (h₁.2.2 g₂ h₂.1 h₂.2.1)

theorem aux_pdp_essInfFamily_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)} {g : Ω → ℝ}
    (h : IsEssInf μ m' S g) : essInfFamily μ m' S =ᵐ[μ] g := by
  have hex : ∃ g, IsEssInf μ m' S g := ⟨g, h⟩
  unfold essInfFamily
  rw [dif_pos hex]
  exact aux_pdp_unique hex.choose_spec h

theorem aux_pdp_essInfFamily_spec {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)}
    (h : ∃ g, IsEssInf μ m' S g) : IsEssInf μ m' S (essInfFamily μ m' S) := by
  unfold essInfFamily
  rw [dif_pos h]
  exact h.choose_spec

theorem aux_pdp_exists {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    {S : Set (Ω → ℝ)} (hne : S.Nonempty) (hmeas : ∀ h ∈ S, StronglyMeasurable[m'] h)
    (c : ℝ) (hc : ∀ h ∈ S, ∀ᵐ ω ∂μ, c ≤ h ω) : ∃ g, IsEssInf μ m' S g := by
  classical
  obtain ⟨h₀, hh₀⟩ := hne
  let G : (ℕ → S) → Ω → ℝ := fun s ω => ⨅ n, max c ((s n : Ω → ℝ) ω)
  have hGmeas : ∀ s, Measurable[m'] (G s) := fun s =>
    Measurable.iInf (fun n => measurable_const.max (hmeas _ (s n).2).measurable)
  have hGbdd : ∀ (s : ℕ → S) ω, BddBelow (Set.range fun n => max c ((s n : Ω → ℝ) ω)) :=
    fun s ω => ⟨c, by rintro _ ⟨n, rfl⟩; exact le_max_left _ _⟩
  have hGle : ∀ s n ω, G s ω ≤ max c ((s n : Ω → ℝ) ω) := fun s n ω => ciInf_le (hGbdd s ω) n
  have hint : ∀ s, Integrable (fun ω => Real.arctan (G s ω)) μ := by
    intro s
    refine Integrable.of_bound ?_ (Real.pi / 2) (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Real.continuous_arctan.measurable.comp ((hGmeas s).mono hm le_rfl)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  let φ : (ℕ → S) → ℝ := fun s => ∫ ω, Real.arctan (G s ω) ∂μ
  have hφmono : ∀ s s', (∀ ω, G s ω ≤ G s' ω) → φ s ≤ φ s' := fun s s' h =>
    integral_mono (hint s) (hint s') (fun ω => Real.arctan_strictMono.monotone (h ω))
  have hVne : (Set.range φ).Nonempty := ⟨_, ⟨fun _ => ⟨h₀, hh₀⟩, rfl⟩⟩
  have hVbdd : BddBelow (Set.range φ) := by
    refine ⟨∫ _ω, (-(Real.pi / 2)) ∂μ, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact integral_mono (integrable_const _) (hint s)
      (fun ω => (Real.neg_pi_div_two_lt_arctan _).le)
  obtain ⟨u, -, hu_tend, hu_mem⟩ := exists_seq_tendsto_sInf hVne hVbdd
  choose s hs using hu_mem
  let s' : ℕ → S := fun n => s n.unpair.1 n.unpair.2
  have hs'le : ∀ k ω, G s' ω ≤ G (s k) ω := by
    intro k ω
    refine le_ciInf fun j => ?_
    have := hGle s' (Nat.pair k j) ω
    simpa [s', Nat.unpair_pair] using this
  have hφs' : φ s' = sInf (Set.range φ) := by
    refine le_antisymm ?_ (csInf_le hVbdd ⟨s', rfl⟩)
    refine ge_of_tendsto' hu_tend fun k => ?_
    rw [← hs k]
    exact hφmono _ _ (hs'le k)
  refine ⟨G s', (hGmeas s').stronglyMeasurable, ?_, ?_⟩
  · intro h hh
    let s'' : ℕ → S := fun n => if n = 0 then ⟨h, hh⟩ else s' (n - 1)
    have h1 : ∀ ω, G s'' ω ≤ G s' ω := by
      intro ω
      refine le_ciInf fun j => ?_
      have := hGle s'' (j + 1) ω
      simpa [s''] using this
    have h2 : ∀ ω, G s'' ω ≤ max c (h ω) := by
      intro ω
      have := hGle s'' 0 ω
      simpa [s''] using this
    have h3 : φ s' ≤ φ s'' := by
      rw [hφs']
      exact csInf_le hVbdd ⟨s'', rfl⟩
    have h4 : ∫ ω, (Real.arctan (G s' ω) - Real.arctan (G s'' ω)) ∂μ = 0 := by
      rw [integral_sub (hint s') (hint s'')]
      have := hφmono _ _ h1
      simp only [φ] at this h3
      linarith
    have h5 := (integral_eq_zero_iff_of_nonneg (fun ω => sub_nonneg.2
      (Real.arctan_strictMono.monotone (h1 ω))) ((hint s').sub (hint s''))).1 h4
    filter_upwards [h5, hc h hh] with ω hω hcω
    have : G s' ω = G s'' ω := by
      have := sub_eq_zero.1 hω
      exact Real.arctan_injective this
    rw [this]
    exact (h2 ω).trans (max_le hcω le_rfl)
  · intro g' _ hg'
    have : ∀ᵐ ω ∂μ, ∀ n, g' ω ≤ (s' n : Ω → ℝ) ω :=
      ae_all_iff.2 fun n => hg' _ (s' n).2
    filter_upwards [this] with ω hω
    exact le_ciInf fun n => (hω n).trans (le_max_right _ _)

section aux
variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

theorem aux_pdp_Qfin (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set) :
    IsFiniteMeasure (Q P₀ f) :=
  isFiniteMeasure_withDensity_ofReal (D.integrable f hf).2

theorem aux_pdp_Qac (f : Ω → ℝ) : Q P₀ f ≪ P₀ := withDensity_absolutelyContinuous _ _

theorem aux_pdp_acQ (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D) : P₀ ≪ Q P₀ f := by
  refine withDensity_absolutelyContinuous'
    (D.integrable f hf.1).aestronglyMeasurable.aemeasurable.ennreal_ofReal ?_
  filter_upwards [hf.2] with ω hω
  simpa using hω

theorem aux_pdp_exists_k {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) (ω : Ω) :
    ∃ k ≤ N, τ ω = (k : WithTop ℕ) := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτ ω)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
  refine ⟨k, ?_, hk.symm⟩
  have := hτ ω
  rw [← hk] at this
  exact WithTop.coe_le_coe.1 this

theorem aux_pdp_sv_of_eq (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} {ω : Ω} {k : ℕ}
    (h : τ ω = (k : WithTop ℕ)) : stoppedValue X τ ω = X k ω := by
  simp only [stoppedValue, h]
  rfl

theorem aux_pdp_sv_sum (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) :
    stoppedValue X τ = fun ω => ∑ n ∈ Finset.range (N + 1),
      {ω | τ ω = (n : WithTop ℕ)}.indicator (X n) ω := by
  funext ω
  obtain ⟨k, hk, h⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq X h]
  rw [Finset.sum_eq_single k]
  · simp [h]
  · intro b _ hb
    simp [h, Ne.symm hb]
  · intro hk'
    exact absurd (Finset.mem_range.2 (by omega)) hk'

theorem aux_pdp_sv_int (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    {f : Ω → ℝ} (hf : f ∈ D.set) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) :
    Integrable (stoppedValue X τ) (Q P₀ f) := by
  have := aux_pdp_Qfin D hf
  obtain ⟨C, hC⟩ := hX.2
  rw [aux_pdp_sv_sum X hτ.2]
  refine integrable_finsetSum _ fun n hn => ?_
  have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  refine Integrable.indicator ?_ (ℱ.le n _ (hτ.1.measurableSet_eq n))
  refine Integrable.of_bound ((hX.1 n hn').mono (ℱ.le n)).aestronglyMeasurable C ?_
  exact (aux_pdp_Qac f).ae_le (hC n hn')

theorem aux_pdp_lb (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    {C : ℝ} (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    {f : Ω → ℝ} (hf : f ∈ Pe D) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ)
    {m' : MeasurableSpace Ω} (hm' : m' ≤ m) :
    ∀ᵐ ω ∂P₀, -C ≤ (Q P₀ f)[stoppedValue X τ | m'] ω := by
  have := aux_pdp_Qfin D hf.1
  have hall : ∀ᵐ ω ∂P₀, ∀ n, n ≤ N → |X n ω| ≤ C :=
    ae_all_iff.2 fun n => by
      by_cases hn : n ≤ N
      · filter_upwards [hC n hn] with ω hω using fun _ => hω
      · exact Filter.Eventually.of_forall fun ω h => absurd h hn
  have hY : ∀ᵐ ω ∂(Q P₀ f), (fun _ => -C) ω ≤ stoppedValue X τ ω := by
    refine (aux_pdp_Qac f).ae_le ?_
    filter_upwards [hall] with ω hω
    obtain ⟨k, hk, h⟩ := aux_pdp_exists_k hτ.2 ω
    rw [aux_pdp_sv_of_eq X h]
    exact (abs_le.1 (hω k hk)).1
  have := condExp_mono (m := m') (integrable_const (-C)) (aux_pdp_sv_int D X hX hf.1 hτ) hY
  rw [condExp_const hm'] at this
  exact (aux_pdp_acQ D hf).ae_le this

theorem aux_pdp_loc (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (t : ℕ) {f : Ω → ℝ} (hf : f ∈ Pe D)
    {τ₁ τ₂ : Ω → WithTop ℕ} (h₁ : IsBddStoppingTime ℱ N τ₁) (h₂ : IsBddStoppingTime ℱ N τ₂)
    (heq : ∀ ω, σ ω = (t : WithTop ℕ) → τ₁ ω = τ₂ ω) :
    ∀ᵐ ω ∂P₀, σ ω = (t : WithTop ℕ) →
      (Q P₀ f)[stoppedValue X τ₁ | hσ.measurableSpace] ω =
        (Q P₀ f)[stoppedValue X τ₂ | ℱ t] ω := by
  have := aux_pdp_Qfin D hf.1
  have hi₁ := aux_pdp_sv_int D X hX hf.1 h₁
  have hi₂ := aux_pdp_sv_int D X hX hf.1 h₂
  have hAt : MeasurableSet[ℱ t] {ω | σ ω = (t : WithTop ℕ)} := hσ.measurableSet_eq t
  have hA : MeasurableSet {ω | σ ω = (t : WithTop ℕ)} := ℱ.le t _ hAt
  have step1 := condExp_stopping_time_ae_eq_restrict_eq_of_countable (μ := Q P₀ f)
    (f := stoppedValue X τ₁) hσ t
  have step1' : ∀ᵐ ω ∂(Q P₀ f), σ ω = (t : WithTop ℕ) →
      (Q P₀ f)[stoppedValue X τ₁ | hσ.measurableSpace] ω =
        (Q P₀ f)[stoppedValue X τ₁ | ℱ t] ω := (ae_restrict_iff' hA).1 step1
  have hind : {ω | σ ω = (t : WithTop ℕ)}.indicator (stoppedValue X τ₁) =
      {ω | σ ω = (t : WithTop ℕ)}.indicator (stoppedValue X τ₂) := by
    funext ω
    by_cases hω : σ ω = (t : WithTop ℕ)
    · simp [Set.indicator_of_mem, hω, stoppedValue, heq ω hω]
    · simp [hω]
  have e1 := condExp_indicator hi₁ hAt
  have e2 := condExp_indicator hi₂ hAt
  rw [hind] at e1
  have e3 := e1.symm.trans e2
  have : ∀ᵐ ω ∂(Q P₀ f), σ ω = (t : WithTop ℕ) →
      (Q P₀ f)[stoppedValue X τ₁ | hσ.measurableSpace] ω =
        (Q P₀ f)[stoppedValue X τ₂ | ℱ t] ω := by
    filter_upwards [step1', e3] with ω hω1 hω3 hωt
    rw [hω1 hωt]
    have hmem : ω ∈ {ω | σ ω = (t : WithTop ℕ)} := hωt
    simpa [Set.indicator_of_mem hmem] using hω3
  exact (aux_pdp_acQ D hf).ae_le this

end aux

section aux
variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

theorem aux_pdp_piece {σ τ₁ τ₂ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hτ₁ : IsStoppingTime ℱ τ₁) (hτ₂ : IsStoppingTime ℱ τ₂) (t : ℕ)
    (h₁ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₁ ω)
    (h₂ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₂ ω) :
    IsStoppingTime ℱ (fun ω => if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) := by
  classical
  intro i
  show MeasurableSet[ℱ i]
    {ω | (if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) ≤ (i : WithTop ℕ)}
  by_cases hi : t ≤ i
  · have hset : {ω | (if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) ≤ (i : WithTop ℕ)} =
        ({ω | σ ω = (t : WithTop ℕ)} ∩ {ω | τ₁ ω ≤ (i : WithTop ℕ)}) ∪
          ({ω | σ ω = (t : WithTop ℕ)}ᶜ ∩ {ω | τ₂ ω ≤ (i : WithTop ℕ)}) := by
      ext ω
      by_cases hω : σ ω = (t : WithTop ℕ) <;> simp [hω]
    have hA : MeasurableSet[ℱ i] {ω | σ ω = (t : WithTop ℕ)} :=
      ℱ.mono hi _ (hσ.measurableSet_eq t)
    rw [hset]
    exact (hA.inter (hτ₁ i)).union (hA.compl.inter (hτ₂ i))
  · have hit : (i : WithTop ℕ) < (t : WithTop ℕ) := by exact_mod_cast (not_le.1 hi)
    have hset : {ω | (if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) ≤ (i : WithTop ℕ)} =
        {ω | τ₂ ω ≤ (i : WithTop ℕ)} := by
      ext ω
      by_cases hω : σ ω = (t : WithTop ℕ)
      · simp only [hω, if_true, Set.mem_ofPred_eq]
        constructor
        · intro h; exact absurd (lt_of_le_of_lt ((h₁ ω hω).trans h) hit) (lt_irrefl _)
        · intro h; exact absurd (lt_of_le_of_lt ((h₂ ω hω).trans h) hit) (lt_irrefl _)
      · simp [hω]
    rw [hset]
    exact hτ₂ i

theorem aux_pdp_piece_bdd {σ τ₁ τ₂ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hτ₁ : IsBddStoppingTime ℱ N τ₁) (hτ₂ : IsBddStoppingTime ℱ N τ₂) (t : ℕ)
    (h₁ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₁ ω)
    (h₂ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₂ ω) :
    IsBddStoppingTime ℱ N (fun ω => if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) := by
  refine ⟨aux_pdp_piece hσ hτ₁.1 hτ₂.1 t h₁ h₂, fun ω => ?_⟩
  dsimp only
  split_ifs
  · exact hτ₁.2 ω
  · exact hτ₂.2 ω

theorem aux_pdp_ind_meas {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (t : ℕ) {h : Ω → ℝ}
    (hh : StronglyMeasurable[ℱ t] h) :
    StronglyMeasurable[hσ.measurableSpace] ({ω | σ ω = (t : WithTop ℕ)}.indicator h) := by
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  rw [Set.indicator_preimage, Set.ite]
  refine MeasurableSet.union ?_ ?_
  · exact (hσ.measurableSet_inter_eq_iff _ t).2 ((hh.measurable hB).inter (hσ.measurableSet_eq t))
  · exact (measurable_const hB).diff (hσ.measurableSet_eq' t)

theorem aux_pdp_ind_meas' {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (t : ℕ) {h : Ω → ℝ}
    (hh : StronglyMeasurable[hσ.measurableSpace] h) :
    StronglyMeasurable[ℱ t] ({ω | σ ω = (t : WithTop ℕ)}.indicator h) := by
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  rw [Set.indicator_preimage, Set.ite]
  refine MeasurableSet.union ?_ ?_
  · exact (hσ.measurableSet_inter_eq_iff _ t).1 ((hh.measurable hB).inter (hσ.measurableSet_eq' t))
  · exact (measurable_const hB).diff (hσ.measurableSet_eq t)

end aux


end MultiperiodRisk.Bellman

open MultiperiodRisk.Bellman
open MeasureTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    Psi D X σ hσ.1 =ᵐ[P₀] fun ω =>
      ∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0 := by
  classical
  obtain ⟨C, hC⟩ := hX.2
  obtain ⟨f₀, hf₀⟩ := hPe
  let fam : ℕ → Set (Ω → ℝ) := fun t => {h | ∃ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ ∧
    (∀ ω, (t : WithTop ℕ) ≤ τ ω) ∧ ∃ f ∈ Pe D, h = (Q P₀ f)[stoppedValue X τ | ℱ t]}
  have hPsiN : ∀ t ≤ N, IsEssInf P₀ (ℱ t) (fam t) (PsiN D X t) := by
    intro t ht
    have hconst : IsBddStoppingTime ℱ N (fun _ => (t : WithTop ℕ)) :=
      ⟨isStoppingTime_const ℱ t, fun _ => by
        show (t : WithTop ℕ) ≤ (N : WithTop ℕ)
        exact_mod_cast ht⟩
    have key : IsEssInf P₀ (isStoppingTime_const ℱ t).measurableSpace
        (psiFamily D X (fun _ => (t : WithTop ℕ)) (isStoppingTime_const ℱ t)) (PsiN D X t) := by
      apply aux_pdp_essInfFamily_spec
      refine aux_pdp_exists (isStoppingTime_const ℱ t).measurableSpace_le
        ⟨_, (fun _ => (t : WithTop ℕ)), hconst, fun _ => le_rfl, f₀, hf₀, rfl⟩ ?_ (-C) ?_
      · rintro h ⟨τ, hτ, -, f, hf, rfl⟩
        exact stronglyMeasurable_condExp
      · rintro h ⟨τ, hτ, -, f, hf, rfl⟩
        exact aux_pdp_lb D X hX hC hf hτ (isStoppingTime_const ℱ t).measurableSpace_le
    have e1 : (isStoppingTime_const ℱ t).measurableSpace = ℱ t :=
      IsStoppingTime.measurableSpace_const ℱ t
    have e2 : psiFamily D X (fun _ => (t : WithTop ℕ)) (isStoppingTime_const ℱ t) = fam t := by
      ext h
      simp only [psiFamily, fam, e1]
    rw [e1, e2] at key
    exact key
  have hval : ∀ ω (k : ℕ), σ ω = (k : WithTop ℕ) →
      (∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0) =
        PsiN D X k ω := by
    intro ω k hk
    have hkN : k ≤ N := by
      have := hσ.2 ω
      rw [hk] at this
      exact_mod_cast this
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b _ hb
      simp [hk, Ne.symm hb]
    · intro hk'
      exact absurd (Finset.mem_range.2 (by omega)) hk'
  have key : IsEssInf P₀ hσ.1.measurableSpace (psiFamily D X σ hσ.1) (fun ω =>
      ∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0) := by
    refine ⟨?_, ?_, ?_⟩
    · have hfun : (fun ω => ∑ t ∈ Finset.range (N + 1),
          if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0) = fun ω =>
          ∑ t ∈ Finset.range (N + 1), {ω | σ ω = (t : WithTop ℕ)}.indicator (PsiN D X t) ω := by
        funext ω
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases h : σ ω = (t : WithTop ℕ) <;> simp [h]
      rw [hfun]
      refine Finset.stronglyMeasurable_fun_sum _ fun t ht => ?_
      exact aux_pdp_ind_meas hσ.1 t (hPsiN t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht))).1
    · rintro h ⟨τ, hτ, hστ, f, hf, rfl⟩
      have hloc : ∀ t, ∀ᵐ ω ∂P₀, t ≤ N → σ ω = (t : WithTop ℕ) →
          PsiN D X t ω ≤ (Q P₀ f)[stoppedValue X τ | hσ.1.measurableSpace] ω := by
        intro t
        by_cases ht : t ≤ N
        · let τ' : Ω → WithTop ℕ := fun ω =>
            if σ ω = (t : WithTop ℕ) then τ ω else (N : WithTop ℕ)
          have hτ' : IsBddStoppingTime ℱ N τ' :=
            aux_pdp_piece_bdd (τ₂ := fun _ => (N : WithTop ℕ)) hσ.1 hτ
              ⟨isStoppingTime_const ℱ N, fun _ => le_rfl⟩ t
              (fun ω hω => by rw [← hω]; exact hστ ω) (fun ω _ => by exact_mod_cast ht)
          have hmem : (Q P₀ f)[stoppedValue X τ' | ℱ t] ∈ fam t := by
            refine ⟨τ', hτ', fun ω => ?_, f, hf, rfl⟩
            show (t : WithTop ℕ) ≤ (if σ ω = (t : WithTop ℕ) then τ ω else (N : WithTop ℕ))
            split_ifs with hω
            · rw [← hω]; exact hστ ω
            · exact_mod_cast ht
          have h1 := (hPsiN t ht).2.1 _ hmem
          have h2 := aux_pdp_loc D X hX hσ.1 t hf hτ hτ' (fun ω hω => by simp [τ', hω])
          filter_upwards [h1, h2] with ω hω1 hω2 _ hωt
          rw [hω2 hωt]
          exact hω1
        · exact Filter.Eventually.of_forall fun ω h => absurd h ht
      filter_upwards [ae_all_iff.2 hloc] with ω hω
      obtain ⟨k, hk, hσk⟩ := aux_pdp_exists_k hσ.2 ω
      rw [hval ω k hσk]
      exact hω k hk hσk
    · intro g' hg'meas hg'le
      have hloc : ∀ t, ∀ᵐ ω ∂P₀, t ≤ N → σ ω = (t : WithTop ℕ) → g' ω ≤ PsiN D X t ω := by
        intro t
        by_cases ht : t ≤ N
        · let g't : Ω → ℝ := fun ω => if σ ω = (t : WithTop ℕ) then g' ω else PsiN D X t ω
          have hg't_eq : g't = {ω | σ ω = (t : WithTop ℕ)}.indicator g' +
              {ω | σ ω = (t : WithTop ℕ)}ᶜ.indicator (PsiN D X t) := by
            funext ω
            by_cases h : σ ω = (t : WithTop ℕ) <;> simp [g't, h]
          have hg't_meas : StronglyMeasurable[ℱ t] g't := by
            rw [hg't_eq]
            exact (aux_pdp_ind_meas' hσ.1 t hg'meas).add
              ((hPsiN t ht).1.indicator (hσ.1.measurableSet_eq t).compl)
          have hg't_le : ∀ h ∈ fam t, g't ≤ᵐ[P₀] h := by
            rintro h ⟨τ, hτ, htτ, f, hf, rfl⟩
            let τ'' : Ω → WithTop ℕ := fun ω => if σ ω = (t : WithTop ℕ) then τ ω else σ ω
            have hτ'' : IsBddStoppingTime ℱ N τ'' :=
              aux_pdp_piece_bdd hσ.1 hτ hσ t (fun ω _ => htτ ω) (fun ω hω => le_of_eq hω.symm)
            have hmem : (Q P₀ f)[stoppedValue X τ'' | hσ.1.measurableSpace] ∈
                psiFamily D X σ hσ.1 := by
              refine ⟨τ'', hτ'', fun ω => ?_, f, hf, rfl⟩
              show σ ω ≤ (if σ ω = (t : WithTop ℕ) then τ ω else σ ω)
              split_ifs with hω
              · rw [hω]; exact htτ ω
              · exact le_rfl
            have h1 := hg'le _ hmem
            have h2 := aux_pdp_loc D X hX hσ.1 t hf hτ'' hτ (fun ω hω => by simp [τ'', hω])
            have h3 := (hPsiN t ht).2.1 _ ⟨τ, hτ, htτ, f, hf, rfl⟩
            filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
            by_cases hωt : σ ω = (t : WithTop ℕ)
            · simp only [g't, hωt, if_true]
              rw [← hω2 hωt]
              exact hω1
            · simp only [g't, hωt, if_false]
              exact hω3
          have := (hPsiN t ht).2.2 g't hg't_meas hg't_le
          filter_upwards [this] with ω hω _ hωt
          simpa [g't, hωt] using hω
        · exact Filter.Eventually.of_forall fun ω h => absurd h ht
      filter_upwards [ae_all_iff.2 hloc] with ω hω
      obtain ⟨k, hk, hσk⟩ := aux_pdp_exists_k hσ.2 ω
      rw [hval ω k hσk]
      exact hω k hk hσk
  exact aux_pdp_essInfFamily_eq key
