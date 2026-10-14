-- Prove2me | solution 1 for MDPFinance.Semicontinuous.measurable_maximizer_existence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-11T16:45:15.644+00:00
-- url     : https://prove2.me/submissions/b58717ad-2305-4948-99cb-9dc7ec741e76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Theorems.Thm_KunuguiNovikov_measurableSet_image_fst_of_isCompact_sections

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous.MeasMaxSketch

open Set

namespace MDPSel

/-- one lexicographic step -/
def stepK {E A : Type*} (φ : A → ℝ) (K : E → Set A) (x : E) : Set A :=
  {a | a ∈ K x ∧ ∀ b ∈ K x, φ a ≤ φ b}

lemma stepK_props {E A : Type*} [MeasurableSpace E] [TopologicalSpace A] [T2Space A]
    (φ : A → ℝ) (hφ : Continuous φ) (K : E → Set A)
    (hK : ∀ x, IsCompact (K x)) (hne : ∀ x, (K x).Nonempty)
    (hm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty}) :
    (∀ x, IsCompact (stepK φ K x)) ∧ (∀ x, (stepK φ K x).Nonempty) ∧
    (∀ F, IsClosed F → MeasurableSet {x | (stepK φ K x ∩ F).Nonempty}) := by
  have hcl : ∀ x, IsClosed (stepK φ K x) := by
    intro x
    have : stepK φ K x = K x ∩ ⋂ b ∈ K x, {a | φ a ≤ φ b} := by
      ext a; simp [stepK]
    rw [this]
    exact (hK x).isClosed.inter (isClosed_biInter fun b _ => isClosed_le hφ continuous_const)
  refine ⟨fun x => (hK x).of_isClosed_subset (hcl x) (fun a ha => ha.1), fun x => ?_, ?_⟩
  · obtain ⟨a, ha, hmin⟩ := (hK x).exists_isMinOn (hne x) hφ.continuousOn
    exact ⟨a, ha, fun b hb => hmin hb⟩
  · intro F hF
    -- characterization
    have key : {x | (stepK φ K x ∩ F).Nonempty} =
        ⋂ j : ℕ, ⋂ q : ℚ, ({x | (K x ∩ {a | φ a ≤ q}).Nonempty}ᶜ ∪
          {x | (K x ∩ (F ∩ {a | φ a ≤ (q : ℝ) + 1 / ((j : ℝ) + 1)})).Nonempty}) := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
      constructor
      · rintro ⟨a, ⟨haK, hamin⟩, haF⟩ j q
        by_cases h : (K x ∩ {a | φ a ≤ q}).Nonempty
        · right
          obtain ⟨b, hbK, hbq⟩ := h
          refine ⟨a, haK, haF, ?_⟩
          have := hamin b hbK
          simp only [mem_ofPred_eq] at hbq ⊢
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          linarith
        · left; exact h
      · intro H
        obtain ⟨a0, ha0, hmin0⟩ := (hK x).exists_isMinOn (hne x) hφ.continuousOn
        obtain ⟨q0, hq0⟩ := exists_rat_gt (φ a0)
        have hKF : (K x ∩ F).Nonempty := by
          rcases H 0 q0 with h | h
          · exact absurd ⟨a0, ha0, hq0.le⟩ h
          · obtain ⟨a, haK, haF, _⟩ := h
            exact ⟨a, haK, haF⟩
        obtain ⟨b, ⟨hbK, hbF⟩, hbmin⟩ :=
          ((hK x).inter_right hF).exists_isMinOn hKF hφ.continuousOn
        refine ⟨b, ⟨hbK, fun c hc => ?_⟩, hbF⟩
        have hc0 : φ a0 ≤ φ c := hmin0 hc
        suffices φ b ≤ φ a0 by linarith
        by_contra hlt
        push_neg at hlt
        obtain ⟨j, hj⟩ := exists_nat_gt (2 / (φ b - φ a0))
        have hpos : 0 < φ b - φ a0 := by linarith
        have hj' : 2 / ((j:ℝ) + 1) < φ b - φ a0 := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hj
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show φ a0 < φ a0 + 1 / ((j:ℝ) + 1) by
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          linarith)
        rcases H j q with h | h
        · exact h ⟨a0, ha0, hq1.le⟩
        · obtain ⟨c, hcK, hcF, hcq⟩ := h
          have := hbmin ⟨hcK, hcF⟩
          simp only [mem_ofPred_eq] at hcq this
          have e : 2 / ((j:ℝ) + 1) = 1 / ((j:ℝ) + 1) + 1 / ((j:ℝ) + 1) := by ring
          linarith
    rw [key]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun q => ?_
    exact (hm _ (isClosed_le hφ continuous_const)).compl.union
      (hm _ (hF.inter (isClosed_le hφ continuous_const)))

def iterK {E A : Type*} (φ : ℕ → A → ℝ) (K : E → Set A) : ℕ → E → Set A
  | 0 => K
  | i + 1 => stepK (φ i) (iterK φ K i)

theorem select {E A : Type*} [MeasurableSpace E] [TopologicalSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (K : E → Set A) (hK : ∀ x, IsCompact (K x)) (hne : ∀ x, (K x).Nonempty)
    (hm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty}) :
    ∃ f : E → A, Measurable f ∧ ∀ x, f x ∈ K x := by
  by_cases hE : Nonempty E
  swap
  · refine ⟨fun x => (hE ⟨x⟩).elim, ?_, fun x => (hE ⟨x⟩).elim⟩
    exact fun s _ => by
      have : (fun x : E => (hE ⟨x⟩).elim : E → A) ⁻¹' s = ∅ := by
        ext x; exact (hE ⟨x⟩).elim
      rw [this]; exact MeasurableSet.empty
  obtain ⟨x0⟩ := hE
  haveI : Nonempty A := ⟨(hne x0).some⟩
  letI := TopologicalSpace.metrizableSpaceMetric A
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  let φ : ℕ → A → ℝ := fun i a => dist a (d i)
  have hφc : ∀ i, Continuous (φ i) := fun i => continuous_id.dist continuous_const
  have hsep : ∀ a b : A, (∀ i, φ i a = φ i b) → a = b := by
    intro a b h
    have : ∀ ε > 0, dist a b < ε := by
      intro ε hε
      obtain ⟨i, hi⟩ := hd.exists_dist_lt a (half_pos hε)
      have h1 := h i
      simp only [φ] at h1
      calc dist a b ≤ dist a (d i) + dist (d i) b := dist_triangle _ _ _
        _ = dist a (d i) + dist a (d i) := by rw [dist_comm (d i) b, ← h1]
        _ < ε := by have := dist_comm a (d i); linarith
    exact dist_le_zero.1 (le_of_forall_gt_imp_ge_of_dense fun ε hε => (this ε hε).le) |> fun h => h
  have P : ∀ i, (∀ x, IsCompact (iterK φ K i x)) ∧ (∀ x, (iterK φ K i x).Nonempty) ∧
      (∀ F, IsClosed F → MeasurableSet {x | (iterK φ K i x ∩ F).Nonempty}) := by
    intro i
    induction i with
    | zero => exact ⟨hK, hne, hm⟩
    | succ i ih => exact stepK_props (φ i) (hφc i) _ ih.1 ih.2.1 ih.2.2
  have hsub : ∀ x i, iterK φ K (i + 1) x ⊆ iterK φ K i x := fun x i a ha => ha.1
  have hinter : ∀ x F, IsClosed F → (∀ i, (iterK φ K i x ∩ F).Nonempty) →
      (⋂ i, (iterK φ K i x ∩ F)).Nonempty := by
    intro x F hF h
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro i; exact inter_subset_inter_left _ (hsub x i)
    · exact h
    · exact ((P 0).1 x).inter_right hF
    · intro i; exact ((P i).1 x).isClosed.inter hF
  have huniq : ∀ x a b, (∀ i, a ∈ iterK φ K i x) → (∀ i, b ∈ iterK φ K i x) → a = b := by
    intro x a b ha hb
    apply hsep
    intro i
    exact le_antisymm ((ha (i+1)).2 b (hb i)) ((hb (i+1)).2 a (ha i))
  have hex : ∀ x, ∃ a, ∀ i, a ∈ iterK φ K i x := by
    intro x
    obtain ⟨a, ha⟩ := hinter x univ isClosed_univ (fun i => by simpa using (P i).2.1 x)
    exact ⟨a, fun i => (mem_iInter.1 ha i).1⟩
  choose f hf using hex
  refine ⟨f, ?_, fun x => hf x 0⟩
  apply measurable_of_isClosed
  intro F hF
  have : f ⁻¹' F = ⋂ i, {x | (iterK φ K i x ∩ F).Nonempty} := by
    ext x
    simp only [mem_preimage, mem_iInter, mem_ofPred_eq]
    constructor
    · intro h i; exact ⟨f x, hf x i, h⟩
    · intro h
      obtain ⟨a, ha⟩ := hinter x F hF h
      have ha' : ∀ i, a ∈ iterK φ K i x ∩ F := fun i => mem_iInter.1 ha i
      have : a = f x := huniq x a (f x) (fun i => (ha' i).1) (hf x)
      rw [← this]; exact (ha' 0).2
  rw [this]
  exact MeasurableSet.iInter fun i => (P i).2.2 F hF

end MDPSel

/-- `L_n v` is jointly measurable on `E × A`. -/
lemma L_measurable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (hn : n < N) (v : E → EReal) (hv : Measurable v) :
    Measurable (L M n v) := by
  have h1 : Measurable fun xa : E × A => (M.r n xa : EReal) :=
    measurable_coe_real_ereal.comp (M.hr_meas n hn)
  have h2 : Measurable fun xa : E × A =>
      ((∫⁻ x, (v x ⊔ 0).toENNReal ∂(M.Q n xa) : ENNReal) : EReal) :=
    measurable_coe_ennreal_ereal.comp
      (Measurable.lintegral_kernel (hv.sup measurable_const).ereal_toENNReal)
  have h3 : Measurable fun xa : E × A =>
      ((∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂(M.Q n xa) : ENNReal) : EReal) :=
    measurable_coe_ennreal_ereal.comp
      (Measurable.lintegral_kernel (hv.neg.sup measurable_const).ereal_toENNReal)
  exact h1.add (h2.add h3.neg)

/-- On a compact nonempty fiber the supremum defining `T_n v` is attained. -/
lemma T_attained {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace A]
    {N : ℕ} (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (x : E)
    (hc : IsCompact (M.Dx n x)) (hne : (M.Dx n x).Nonempty)
    (hu : UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x)) :
    ∃ a ∈ M.Dx n x, L M n v (x, a) = T M n v x := by
  obtain ⟨a, ha, hmax⟩ := hu.exists_isMaxOn hne hc
  exact ⟨a, ha, le_antisymm (le_biSup (fun b => L M n v (x, b)) ha)
    (iSup₂_le fun b hb => hmax hb)⟩

end MDPFinance.Semicontinuous.MeasMaxSketch

open MDPFinance.Semicontinuous.MeasMaxSketch Set

theorem solution {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_compact : ∀ x, IsCompact (M.Dx n x))
    (hL_usc : ∀ x, UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x)) :
    Measurable (T M n v) ∧ ∃ f, IsMaximizer M n v f := by
  have hLm : Measurable (L M n v) := L_measurable M n hn v hv.1
  have hne : ∀ x, (M.Dx n x).Nonempty := by
    obtain ⟨f, _, hf⟩ := M.hD_sel n hn
    exact fun x => ⟨f x, hf x⟩
  have hDm : MeasurableSet (M.D n) := M.hD_meas n hn
  -- sections `{a ∈ D_n(x) | c ≤ L_n v(x,a)}` are compact
  have hsec : ∀ (c : E → EReal) (F : Set A), IsClosed F → ∀ x,
      IsCompact {a | (x, a) ∈ {p : E × A | p ∈ M.D n ∧ c p.1 ≤ L M n v p ∧ p.2 ∈ F}} := by
    intro c F hF x
    have : {a | (x, a) ∈ {p : E × A | p ∈ M.D n ∧ c p.1 ≤ L M n v p ∧ p.2 ∈ F}} =
        (M.Dx n x ∩ (fun a => L M n v (x, a)) ⁻¹' Ici (c x)) ∩ F := by
      ext a
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [this]
    exact ((hL_usc x).isCompact_inter_preimage_Ici (hD_compact x) (c x)).inter_right hF
  -- the projection identity
  have hproj : ∀ (c : E → EReal) (F : Set A), IsClosed F →
      Prod.fst '' {p : E × A | p ∈ M.D n ∧ c p.1 ≤ L M n v p ∧ p.2 ∈ F} =
        {x | (M.Dx n x ∩ (fun a => L M n v (x, a)) ⁻¹' Ici (c x) ∩ F).Nonempty} := by
    intro c F _
    ext x
    simp only [mem_image, mem_ofPred_eq, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, ⟨h1, h2⟩, h3⟩
    · rintro ⟨a, ⟨h1, h2⟩, h3⟩; exact ⟨a, h1, h2, h3⟩
  have hmeasProj : ∀ (c : E → EReal), Measurable c → ∀ F : Set A, IsClosed F →
      MeasurableSet {x | (M.Dx n x ∩ (fun a => L M n v (x, a)) ⁻¹' Ici (c x) ∩ F).Nonempty} := by
    intro c hc F hF
    rw [← hproj c F hF]
    apply KunuguiNovikov.measurableSet_image_fst_of_isCompact_sections
    · exact hDm.inter ((measurableSet_le (hc.comp measurable_fst) hLm).inter
        (hF.measurableSet.preimage measurable_snd))
    · exact hsec c F hF
  -- Step 1: measurability of `T_n v`
  have hTm : Measurable (T M n v) := by
    apply measurable_of_Ici
    intro α
    have : T M n v ⁻¹' Ici α =
        {x | (M.Dx n x ∩ (fun a => L M n v (x, a)) ⁻¹' Ici ((fun _ => α) x) ∩ univ).Nonempty} := by
      ext x
      simp only [mem_preimage, mem_Ici, mem_ofPred_eq, inter_univ]
      constructor
      · intro h
        obtain ⟨a, ha, heq⟩ := T_attained M n v x (hD_compact x) (hne x) (hL_usc x)
        exact ⟨a, ha, by simp [heq, h]⟩
      · rintro ⟨a, ha, h⟩
        exact le_trans h (le_biSup (fun b => L M n v (x, b)) ha)
    rw [this]
    exact hmeasProj (fun _ => α) measurable_const univ isClosed_univ
  refine ⟨hTm, ?_⟩
  -- Step 2: a measurable selector of the argmax correspondence
  let K : E → Set A := fun x => M.Dx n x ∩ (fun a => L M n v (x, a)) ⁻¹' Ici (T M n v x)
  have hKc : ∀ x, IsCompact (K x) := fun x =>
    (hL_usc x).isCompact_inter_preimage_Ici (hD_compact x) _
  have hKne : ∀ x, (K x).Nonempty := by
    intro x
    obtain ⟨a, ha, heq⟩ := T_attained M n v x (hD_compact x) (hne x) (hL_usc x)
    exact ⟨a, ha, by simp [heq]⟩
  have hKm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty} :=
    fun F hF => hmeasProj (T M n v) hTm F hF
  obtain ⟨f, hfm, hfK⟩ := MDPSel.select K hKc hKne hKm
  refine ⟨f, ⟨hfm, fun x => (hfK x).1⟩, funext fun x => ?_⟩
  exact le_antisymm (le_biSup (fun b => L M n v (x, b)) (hfK x).1) (hfK x).2
