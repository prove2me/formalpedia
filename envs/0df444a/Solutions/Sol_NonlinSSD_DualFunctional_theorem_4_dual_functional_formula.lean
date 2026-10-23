-- Prove2me | solution 1 for NonlinSSD.DualFunctional.theorem_4_dual_functional_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:02:15.346627+00:00
-- url     : https://prove2.me/submissions/e71e6c07-2e2b-46c6-95e8-b43becad51ff

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

set_option autoImplicit false

open MeasureTheory

namespace NSSD8a065062

open NonlinSSD.DualFunctional NonlinSSD.Optimality

lemma v_le_zero {a b : ℝ} {v : ℝ → ℝ} (hv : v ∈ U1 a b) (t : ℝ) : v t ≤ 0 := by
  calc v t ≤ v (max t b) := hv.2.1 (le_max_left _ _)
    _ = 0 := hv.2.2.1 _ (le_max_right _ _)

lemma v_lower {a b : ℝ} {v : ℝ → ℝ} (hv : v ∈ U1 a b) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ t ≤ a, v t = v a + c * (t - a)) (t : ℝ) : v a - c * |t - a| ≤ v t := by
  rcases le_total t a with h | h
  · rw [hc t h, abs_of_nonpos (by linarith)]; linarith
  · have := hv.2.1 h
    nlinarith [abs_nonneg (t - a), mul_nonneg hc0 (abs_nonneg (t - a))]

lemma int_vX {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a b : ℝ} {v : ℝ → ℝ} (hv : v ∈ U1 a b) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ t ≤ a, v t = v a + c * (t - a)) {X : Ω → ℝ} (hX : Integrable X P) :
    Integrable (fun ω => v (X ω)) P := by
  have hmeas : AEStronglyMeasurable (fun ω => v (X ω)) P :=
    (hv.2.1.measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
  have hg : Integrable (fun ω => |v a| + c * |X ω - a|) P :=
    (integrable_const _).add ((hX.sub (integrable_const a)).abs.const_mul c)
  refine Integrable.mono' hg hmeas ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  have h1 := v_le_zero hv (X ω)
  have h2 := v_lower hv hc0 hc (X ω)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · nlinarith [neg_abs_le (v a)]
  · nlinarith [abs_nonneg (v a), mul_nonneg hc0 (abs_nonneg (X ω - a))]

lemma int_integrand {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a b : ℝ} {v : ℝ → ℝ} (hv : v ∈ U1 a b) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ t ≤ a, v t = v a + c * (t - a)) {Y ζ X : Ω → ℝ} (hY : Integrable Y P)
    (hζ : MemLp ζ ⊤ P) (hX : Integrable X P) :
    Integrable (fun ω => v (X ω) - v (Y ω) - ζ ω * X ω) P := by
  have h3 : Integrable (fun ω => ζ ω * X ω) P := by
    have := hX.mul_of_top_right hζ
    exact this
  exact ((int_vX hv hc0 hc hX).sub (int_vX hv hc0 hc hY)).sub h3

/-- argmax set of `x ↦ v x - ξ x` on `[a,b]` -/
def S (v : ℝ → ℝ) (a b ξ : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc a b ∧ ∀ y ∈ Set.Icc a b, v y - ξ * y ≤ v x - ξ * x}

noncomputable def g (v : ℝ → ℝ) (a b ξ : ℝ) : ℝ := sSup (S v a b ξ)

lemma S_nonempty {a b : ℝ} {v : ℝ → ℝ} (hab : a ≤ b) (hcont : Continuous v) (ξ : ℝ) :
    (S v a b ξ).Nonempty := by
  have hc2 : Continuous fun x => v x - ξ * x := by fun_prop
  obtain ⟨x, hx, hmax⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn
    (Set.nonempty_Icc.2 hab) hc2.continuousOn
  exact ⟨x, hx, fun y hy => isMaxOn_iff.mp hmax y hy⟩

lemma S_closed {a b : ℝ} {v : ℝ → ℝ} (hcont : Continuous v) (ξ : ℝ) :
    IsClosed (S v a b ξ) := by
  have : S v a b ξ = Set.Icc a b ∩ ⋂ y ∈ Set.Icc a b, {x | v y - ξ * y ≤ v x - ξ * x} := by
    ext x; simp [S]
  rw [this]
  exact isClosed_Icc.inter (isClosed_biInter fun y _ => isClosed_le continuous_const (by fun_prop))

lemma g_mem {a b : ℝ} {v : ℝ → ℝ} (hab : a ≤ b) (hcont : Continuous v) (ξ : ℝ) :
    g v a b ξ ∈ S v a b ξ :=
  (S_closed hcont ξ).csSup_mem (S_nonempty hab hcont ξ) ⟨b, fun x hx => hx.1.2⟩

lemma g_anti {a b : ℝ} {v : ℝ → ℝ} (hab : a ≤ b) (hcont : Continuous v) :
    Antitone (g v a b) := by
  intro ξ1 ξ2 h
  rcases h.lt_or_eq with h | h
  · obtain ⟨hx1, hm1⟩ := g_mem hab hcont ξ1
    obtain ⟨hx2, hm2⟩ := g_mem hab hcont ξ2
    have e1 := hm1 _ hx2
    have e2 := hm2 _ hx1
    by_contra hcon
    push_neg at hcon
    nlinarith
  · subst h; exact le_rfl

lemma g_max {a b : ℝ} {v : ℝ → ℝ} (hv : v ∈ U1 a b) (hab : a ≤ b) (hcont : Continuous v)
    {c : ℝ} (hc : ∀ t ≤ a, v t = v a + c * (t - a)) {ξ : ℝ} (h0 : 0 ≤ ξ) (hξc : ξ ≤ c)
    (x : ℝ) : v x - ξ * x ≤ v (g v a b ξ) - ξ * g v a b ξ := by
  obtain ⟨_, hm⟩ := g_mem hab hcont ξ
  rcases lt_or_ge x a with hxa | hxa
  · have := hm a ⟨le_rfl, hab⟩
    rw [hc x hxa.le]; nlinarith
  · rcases le_or_gt x b with hxb | hxb
    · exact hm x ⟨hxa, hxb⟩
    · have := hm b ⟨hab, le_rfl⟩
      rw [hv.2.2.1 x hxb.le]; rw [hv.2.2.1 b le_rfl] at this; nlinarith

lemma conj_eq {a b : ℝ} {v : ℝ → ℝ} (hv : v ∈ U1 a b) (hab : a ≤ b) (hcont : Continuous v)
    {c : ℝ} (hc : ∀ t ≤ a, v t = v a + c * (t - a)) {ξ : ℝ} (h0 : 0 ≤ ξ) (hξc : ξ ≤ c) :
    concaveConj v ξ = ((ξ * g v a b ξ - v (g v a b ξ) : ℝ) : EReal) := by
  unfold concaveConj
  apply le_antisymm
  · exact iInf_le (fun t => ((ξ * t - v t : ℝ) : EReal)) _
  · refine le_iInf fun t => ?_
    have := g_max hv hab hcont hc h0 hξc t
    exact EReal.coe_le_coe_iff.2 (by linarith)

lemma leftDeriv_eq {a c : ℝ} {v : ℝ → ℝ} (hc : ∀ t ≤ a, v t = v a + c * (t - a)) :
    leftDeriv v a = c := by
  unfold leftDeriv
  have h1 : HasDerivAt (fun t => v a + c * (t - a)) c a := by
    have := (((hasDerivAt_id a).sub_const a).const_mul c).const_add (v a)
    simpa using this
  have h2 : HasDerivWithinAt v c (Set.Iic a) a :=
    h1.hasDerivWithinAt.congr (fun t ht => hc t ht) (hc a le_rfl)
  exact h2.derivWithin (uniqueDiffWithinAt_Iic a)

lemma pos_K {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : Set Ω}
    (hB : MeasurableSet B) (hPB : P B ≠ 0) {f : Ω → ℝ} (hfi : Integrable f P)
    (hfpos : ∀ ω ∈ B, 0 < f ω) : 0 < ∫ ω, B.indicator f ω ∂P := by
  rw [integral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (B.indicator f) = B := by
      ext ω
      by_cases h : ω ∈ B
      · simp [Function.mem_support, h, (hfpos ω h).ne']
      · simp [Function.mem_support, h]
    rw [this]; exact pos_iff_ne_zero.2 hPB
  · refine Filter.Eventually.of_forall fun ω => ?_
    by_cases h : ω ∈ B
    · simp [h, (hfpos ω h).le]
    · simp [h]
  · exact hfi.indicator hB

lemma lower_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {v : ℝ → ℝ} {Y ζ X : Ω → ℝ} (hvY : Integrable (fun ω => v (Y ω)) P) {B : Set Ω}
    (hB : MeasurableSet B) {f : Ω → ℝ} (hfi : Integrable f P) (m N : ℝ)
    (hint : Integrable (fun ω => v (X ω) - v (Y ω) - ζ ω * X ω) P)
    (hpt : ∀ᵐ ω ∂P, m - v (Y ω) + N * B.indicator f ω ≤ v (X ω) - v (Y ω) - ζ ω * X ω) :
    m - ∫ ω, v (Y ω) ∂P + N * ∫ ω, B.indicator f ω ∂P ≤
      ∫ ω, (v (X ω) - v (Y ω) - ζ ω * X ω) ∂P := by
  have hli : Integrable (fun ω => m - v (Y ω) + N * B.indicator f ω) P :=
    ((integrable_const m).sub hvY).add ((hfi.indicator hB).const_mul N)
  have heq : ∫ ω, (m - v (Y ω) + N * B.indicator f ω) ∂P =
      m - ∫ ω, v (Y ω) ∂P + N * ∫ ω, B.indicator f ω ∂P := by
    have i1 : Integrable (fun ω => m - v (Y ω)) P := (integrable_const m).sub hvY
    have i2 : Integrable (fun ω => N * B.indicator f ω) P := (hfi.indicator hB).const_mul N
    rw [integral_add i1 i2, integral_sub (integrable_const m) hvY, integral_const,
      integral_const_mul]
    simp
  rw [← heq]
  exact integral_mono_ae hli hint hpt

lemma top_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {v : ℝ → ℝ} {Y ζ : Ω → ℝ} {K m : ℝ} (hK : 0 < K)
    (hX : ∀ n : ℕ, ∃ X : Ω → ℝ, Integrable X P ∧
      m - ∫ ω, v (Y ω) ∂P + n * K ≤ ∫ ω, (v (X ω) - v (Y ω) - ζ ω * X ω) ∂P) :
    dualD P Y v ζ = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt ((y - m + ∫ ω, v (Y ω) ∂P) / K)
  obtain ⟨X, hXi, hXb⟩ := hX n
  unfold dualD
  refine lt_of_lt_of_le ?_ (le_iSup₂_of_le X hXi le_rfl)
  rw [EReal.coe_lt_coe_iff]
  rw [div_lt_iff₀ hK] at hn
  linarith

end NSSD8a065062

open NSSD8a065062

open MeasureTheory NonlinSSD.DualFunctional in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b) (ζ : Ω → ℝ) (hζ : MemLp ζ ⊤ P) :
    ((∀ᵐ ω ∂P, 0 ≤ ζ ω ∧ ζ ω ≤ leftDeriv v a) →
      (∀ᵐ ω ∂P, concaveConj v (ζ ω) ≠ ⊥) ∧
      Integrable (fun ω => (concaveConj v (ζ ω)).toReal) P ∧
      dualD P Y v ζ = ((-∫ ω, ((concaveConj v (ζ ω)).toReal + v (Y ω)) ∂P : ℝ) : EReal)) ∧
    (¬ (∀ᵐ ω ∂P, 0 ≤ ζ ω ∧ ζ ω ≤ leftDeriv v a) → dualD P Y v ζ = ⊤) := by
  obtain ⟨c, hc0, hc⟩ := hv.2.2.2
  have hcont : Continuous v := continuousOn_univ.mp (hv.1.continuousOn isOpen_univ)
  rw [leftDeriv_eq hc]
  have hvY := int_vX hv hc0 hc hY
  refine ⟨fun hae => ?_, fun hnot => ?_⟩
  · have hae2 : ∀ᵐ ω ∂P, (concaveConj v (ζ ω)).toReal =
        ζ ω * g v a b (ζ ω) - v (g v a b (ζ ω)) := by
      filter_upwards [hae] with ω hω
      rw [conj_eq hv hab hcont hc hω.1 hω.2, EReal.toReal_coe]
    have hgm : Measurable (g v a b) := (g_anti hab hcont).measurable
    have hGm : AEStronglyMeasurable (fun ω => g v a b (ζ ω)) P :=
      (hgm.comp_aemeasurable hζ.1.aemeasurable).aestronglyMeasurable
    have hGi : Integrable (fun ω => g v a b (ζ ω)) P := by
      refine Integrable.of_bound hGm (|a| + |b|) (Filter.Eventually.of_forall fun ω => ?_)
      obtain ⟨⟨h1, h2⟩, _⟩ := g_mem hab hcont (ζ ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le a, abs_nonneg b]
      · linarith [le_abs_self b, abs_nonneg a]
    have hRi : Integrable (fun ω => ζ ω * g v a b (ζ ω) - v (g v a b (ζ ω))) P := by
      have h1 : Integrable (fun ω => ζ ω * g v a b (ζ ω)) P := by
        have := hGi.mul_of_top_right hζ
        exact this
      exact h1.sub (int_vX hv hc0 hc hGi)
    refine ⟨?_, hRi.congr (hae2.mono fun ω h => h.symm), ?_⟩
    · filter_upwards [hae] with ω hω
      rw [conj_eq hv hab hcont hc hω.1 hω.2]
      exact EReal.coe_ne_bot _
    · have hRHS : (-∫ ω, ((concaveConj v (ζ ω)).toReal + v (Y ω)) ∂P) =
          ∫ ω, (v (g v a b (ζ ω)) - v (Y ω) - ζ ω * g v a b (ζ ω)) ∂P := by
        rw [← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [hae2] with ω h
        rw [h]; ring
      rw [hRHS]
      unfold dualD
      apply le_antisymm
      · refine iSup₂_le fun X hX => ?_
        refine EReal.coe_le_coe_iff.2 (integral_mono_ae (int_integrand hv hc0 hc hY hζ hX)
          (int_integrand hv hc0 hc hY hζ hGi) ?_)
        filter_upwards [hae] with ω hω
        have := g_max hv hab hcont hc hω.1 hω.2 (X ω)
        linarith
      · exact le_iSup₂_of_le (fun ω => g v a b (ζ ω)) hGi le_rfl
  · set ζ' := hζ.1.mk ζ with hζ'def
    have hζ'm : Measurable ζ' := hζ.1.stronglyMeasurable_mk.measurable
    have hζeq : ζ =ᵐ[P] ζ' := hζ.1.ae_eq_mk
    have hζ'i : MemLp ζ' ⊤ P := (memLp_congr_ae hζeq).1 hζ
    have hζ'int : Integrable ζ' P := hζ'i.integrable le_top
    have hnot' : ¬ ∀ᵐ ω ∂P, 0 ≤ ζ' ω ∧ ζ' ω ≤ c := by
      intro h; apply hnot
      filter_upwards [h, hζeq] with ω h1 h2
      rw [h2]; exact h1
    set m : ℝ := min (v 0) (v a - c * a) with hmdef
    have hm1 : m ≤ v 0 := min_le_left _ _
    have hm2 : m ≤ v a - c * a := min_le_right _ _
    have hv0 : v 0 ≤ 0 := v_le_zero hv 0
    have hsplit : P {ω | ζ' ω < 0} ≠ 0 ∨ P {ω | c < ζ' ω} ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hnot'
      have h1 : ∀ᵐ ω ∂P, ¬ ζ' ω < 0 := by rw [ae_iff]; simpa using hcon.1
      have h2 : ∀ᵐ ω ∂P, ¬ c < ζ' ω := by rw [ae_iff]; simpa using hcon.2
      filter_upwards [h1, h2] with ω h1 h2
      exact ⟨not_lt.1 h1, not_lt.1 h2⟩
    rcases hsplit with hA | hB
    · -- ζ' < 0 on a set of positive measure: push X up to +∞ there
      have hBm : MeasurableSet {ω | ζ' ω < 0} := measurableSet_lt hζ'm measurable_const
      have hfi : Integrable (fun ω => -ζ' ω) P := hζ'int.neg
      have hK := pos_K hBm hA hfi (fun ω hω => by
        have : ζ' ω < 0 := hω
        linarith)
      refine top_aux (m := m) hK fun n => ?_
      set N : ℝ := (n : ℝ) + |b| with hNdef
      have hNb : b ≤ N := by
        have := le_abs_self b; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
      have hNn : (n : ℝ) ≤ N := by have := abs_nonneg b; linarith
      have hXi : Integrable ({ω | ζ' ω < 0}.indicator fun _ => N) P :=
        (integrable_const N).indicator hBm
      refine ⟨_, hXi, ?_⟩
      have hlow := lower_aux hvY hBm hfi m N (int_integrand hv hc0 hc hY hζ hXi) (by
        filter_upwards [hζeq] with ω hω
        rw [hω]
        by_cases h : ω ∈ {ω | ζ' ω < 0}
        · simp only [Set.indicator_of_mem h]
          rw [hv.2.2.1 N hNb]
          have : ζ' ω < 0 := h
          nlinarith
        · simp only [Set.indicator_of_notMem h]
          nlinarith)
      have : (n : ℝ) * ∫ ω, {ω | ζ' ω < 0}.indicator (fun ω => -ζ' ω) ω ∂P ≤
          N * ∫ ω, {ω | ζ' ω < 0}.indicator (fun ω => -ζ' ω) ω ∂P :=
        mul_le_mul_of_nonneg_right hNn hK.le
      linarith
    · -- ζ' > c on a set of positive measure: push X down to -∞ there
      have hBm : MeasurableSet {ω | c < ζ' ω} := measurableSet_lt measurable_const hζ'm
      have hfi : Integrable (fun ω => ζ' ω - c) P := hζ'int.sub (integrable_const c)
      have hK := pos_K hBm hB hfi (fun ω hω => by
        have : c < ζ' ω := hω
        linarith)
      refine top_aux (m := m) hK fun n => ?_
      set N : ℝ := (n : ℝ) + |a| with hNdef
      have hNa : -N ≤ a := by
        have := neg_abs_le a; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
      have hNn : (n : ℝ) ≤ N := by have := abs_nonneg a; linarith
      have hXi : Integrable ({ω | c < ζ' ω}.indicator fun _ => -N) P :=
        (integrable_const (-N)).indicator hBm
      refine ⟨_, hXi, ?_⟩
      have hlow := lower_aux hvY hBm hfi m N (int_integrand hv hc0 hc hY hζ hXi) (by
        filter_upwards [hζeq] with ω hω
        rw [hω]
        by_cases h : ω ∈ {ω | c < ζ' ω}
        · simp only [Set.indicator_of_mem h]
          rw [hc (-N) hNa]
          nlinarith
        · simp only [Set.indicator_of_notMem h]
          nlinarith)
      have : (n : ℝ) * ∫ ω, {ω | c < ζ' ω}.indicator (fun ω => ζ' ω - c) ω ∂P ≤
          N * ∫ ω, {ω | c < ζ' ω}.indicator (fun ω => ζ' ω - c) ω ∂P :=
        mul_le_mul_of_nonneg_right hNn hK.le
      linarith
