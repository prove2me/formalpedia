-- Prove2me | solution 1 for MartOT.Shadow.lemma_4_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:54:34.434193+00:00
-- url     : https://prove2.me/submissions/ce9df0f3-91a4-4a66-877c-b7386ad97d77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MartOT_Shadow_lemma_4_6
import Theorems.Thm_MartOT_Shadow_lemma_4_12

namespace MartOT.Shadow.T413Aux

open MeasureTheory MartOT.Var Filter Topology

lemma inM_of_le {μ ν : Measure ℝ} (h : μ ≤ ν) (hν : InM ν) : InM μ := by
  haveI := hν.1
  exact ⟨isFiniteMeasure_of_le ν h, hν.2.mono_measure h⟩

lemma inM_add {μ ν : Measure ℝ} (hμ : InM μ) (hν : InM ν) : InM (μ + ν) := by
  haveI := hμ.1; haveI := hν.1
  exact ⟨inferInstance, hμ.2.add_measure hν.2⟩

lemma inM_zero : InM (0 : Measure ℝ) := ⟨inferInstance, integrable_zero_measure⟩

lemma inM_atom (α : NNReal) (x : ℝ) : InM ((α : ENNReal) • Measure.dirac x) := by
  haveI : IsFiniteMeasure ((α : ENNReal) • Measure.dirac x) := by
    constructor; simp
  refine ⟨inferInstance, ?_⟩
  exact (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top

lemma integralE_of_nonneg (μ : Measure ℝ) (φ : ℝ → ℝ) (h : ∀ x, 0 ≤ φ x) :
    integralE μ φ = ((∫⁻ x, ENNReal.ofReal (φ x) ∂μ : ENNReal) : EReal) := by
  unfold integralE ModelRiskOT.Duality.extIntegral
  have h2 : ∀ x, (-(φ x : EReal)).toENNReal = 0 := fun x => by
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal, ENNReal.ofReal_eq_zero]; linarith [h x]
  simp only [EReal.real_coe_toENNReal, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

lemma extLE_of_convexLE {μ η : Measure ℝ} (h : ConvexLE μ η) : ExtConvexLE μ η := by
  refine ⟨h.1, h.2.1, fun φ hφ h0 => ?_⟩
  have := h.2.2 φ hφ
  rwa [integralE_of_nonneg _ _ h0, integralE_of_nonneg _ _ h0,
    EReal.coe_ennreal_le_coe_ennreal_iff] at this

lemma extLE_mono {μ η η' : Measure ℝ} (h : ExtConvexLE μ η) (hle : η ≤ η') (hη' : InM η') :
    ExtConvexLE μ η' :=
  ⟨h.1, hη', fun φ hφ h0 => (h.2.2 φ hφ h0).trans (lintegral_mono' hle le_rfl)⟩

lemma extLE_left {μ μ' ν : Measure ℝ} (hle : μ ≤ μ') (hμ : InM μ) (h : ExtConvexLE μ' ν) :
    ExtConvexLE μ ν :=
  ⟨hμ, h.2.1, fun φ hφ h0 => (lintegral_mono' hle le_rfl).trans (h.2.2 φ hφ h0)⟩

lemma extLE_trans {μ η ν : Measure ℝ} (h1 : ExtConvexLE μ η) (h2 : ExtConvexLE η ν) :
    ExtConvexLE μ ν :=
  ⟨h1.1, h2.2.1, fun φ hφ h0 => (h1.2.2 φ hφ h0).trans (h2.2.2 φ hφ h0)⟩

lemma convexLE_refl {μ : Measure ℝ} (h : InM μ) : ConvexLE μ μ :=
  ⟨h, h, fun _ _ => le_rfl⟩

lemma sub_sub_eq {ν a b : Measure ℝ} [IsFiniteMeasure ν] (ha : a ≤ ν) (hb : b ≤ ν - a) :
    ν - a - b = ν - (a + b) := by
  haveI : IsFiniteMeasure a := isFiniteMeasure_of_le ν ha
  haveI : IsFiniteMeasure (ν - a) := isFiniteMeasure_of_le ν Measure.sub_le
  haveI : IsFiniteMeasure b := isFiniteMeasure_of_le (ν - a) hb
  have hab : a + b ≤ ν := by
    rw [Measure.le_iff] at hb ⊢
    intro s hs
    have := hb s hs
    rw [Measure.sub_apply hs ha] at this
    rw [Measure.add_apply]
    calc a s + b s ≤ a s + (ν s - a s) := add_le_add le_rfl this
      _ = ν s := add_tsub_cancel_of_le (ha s)
  ext s hs
  rw [Measure.sub_apply hs hb, Measure.sub_apply hs ha, Measure.sub_apply hs hab,
    Measure.add_apply, tsub_tsub]

lemma le_sub_of_add_le' {ν a b : Measure ℝ} [IsFiniteMeasure ν] (h : a + b ≤ ν) :
    b ≤ ν - a := by
  have ha : a ≤ ν := le_trans (Measure.le_add_right le_rfl) h
  haveI : IsFiniteMeasure a := isFiniteMeasure_of_le ν ha
  rw [Measure.le_iff] at h ⊢
  intro s hs
  rw [Measure.sub_apply hs ha]
  have := h s hs
  rw [Measure.add_apply] at this
  exact ENNReal.le_sub_of_add_le_left (measure_ne_top a s) this

lemma sub_mono_left' {η ν c : Measure ℝ} [IsFiniteMeasure ν] (hην : η ≤ ν) (hc : c ≤ η) :
    η - c ≤ ν - c := by
  haveI : IsFiniteMeasure c := isFiniteMeasure_of_le ν (hc.trans hην)
  apply Measure.sub_le_of_le_add
  rw [Measure.sub_add_cancel_of_le (hc.trans hην)]
  exact hην

lemma shadow_exists {μ ν : Measure ℝ} (hμ : InM μ) (hν : InM ν) (h : ExtConvexLE μ ν) :
    ∃ η, IsShadow ν μ η :=
  (lemma_4_6 μ ν hμ hν h).1.exists

lemma shadow_unique {μ ν a b : Measure ℝ} (hμ : InM μ) (hν : InM ν) (h : ExtConvexLE μ ν)
    (ha : IsShadow ν μ a) (hb : IsShadow ν μ b) : a = b :=
  (lemma_4_6 μ ν hμ hν h).1.unique ha hb

lemma isShadow_zero {ν : Measure ℝ} : IsShadow ν 0 0 :=
  ⟨Measure.zero_le _, convexLE_refl inM_zero, fun _ _ h => h⟩


open NNReal

/-- The partial sum `A_n = ∑_{i=1}^n α_i δ_{x_i}`. -/
noncomputable def A (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (n : ℕ) : Measure ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (α i : ENNReal) • Measure.dirac (x i)

lemma A_zero (x : ℕ → ℝ) (α : ℕ → ℝ≥0) : A x α 0 = 0 := by simp [A]

lemma A_succ (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (n : ℕ) :
    A x α (n + 1) = A x α n + (α (n + 1) : ENNReal) • Measure.dirac (x (n + 1)) := by
  unfold A; rw [Finset.sum_Icc_succ_top (by omega)]

lemma A_shift (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (m : ℕ) :
    A x α (m + 1) = (α 1 : ENNReal) • Measure.dirac (x 1) + A (fun i => x (i + 1)) (fun i => α (i + 1)) m := by
  induction m with
  | zero => simp [A]
  | succ m ih =>
    rw [A_succ, ih, A_succ, add_assoc]

lemma A_inM (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (n : ℕ) : InM (A x α n) := by
  induction n with
  | zero => rw [A_zero]; exact inM_zero
  | succ n ih => rw [A_succ]; exact inM_add ih (inM_atom _ _)

lemma A_mono (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (n : ℕ) : A x α n ≤ A x α (n + 1) := by
  rw [A_succ]; exact Measure.le_add_right le_rfl

lemma shadow_of_zero_eq {ν η : Measure ℝ} (h : IsShadow ν 0 η) : η = 0 := by
  have h0 : ConvexLE η 0 := h.2.2 0 (Measure.zero_le _) (convexLE_refl inM_zero)
  have h1 := h0.2.2 (fun _ => 1) (convexOn_const 1 convex_univ)
  rw [integralE_of_nonneg _ _ (fun _ => zero_le_one),
    integralE_of_nonneg _ _ (fun _ => zero_le_one)] at h1
  simp only [ENNReal.ofReal_one, lintegral_const, one_mul, Measure.coe_zero, Pi.zero_apply,
    EReal.coe_ennreal_le_coe_ennreal_iff, nonpos_iff_eq_zero, lintegral_zero_measure] at h1
  exact Measure.measure_univ_eq_zero.mp h1

/-- The inductive claim, for `n = m + 1`. -/
lemma claim (m : ℕ) : ∀ (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (ν : Measure ℝ),
    ExtConvexLE (A x α (m + 1)) ν → ∀ a b : Measure ℝ, IsShadow ν (A x α m) a →
      IsShadow ν (A x α (m + 1)) b →
      ∃ σ, IsShadow (ν - a) ((α (m + 1) : ENNReal) • Measure.dirac (x (m + 1))) σ ∧ b = a + σ := by
  induction m with
  | zero =>
    intro x α ν _ a b ha hb
    rw [A_zero] at ha
    have : a = 0 := shadow_of_zero_eq ha
    subst this
    refine ⟨b, ?_, by simp⟩
    rw [Measure.sub_zero]
    simpa [A] using hb
  | succ m ih =>
    intro x α ν hE a b ha hb
    have hν : InM ν := hE.2.1
    haveI := hν.1
    set x' : ℕ → ℝ := fun i => x (i + 1)
    set α' : ℕ → ℝ≥0 := fun i => α (i + 1)
    set δ1 : Measure ℝ := (α 1 : ENNReal) • Measure.dirac (x 1)
    have hδ1 : InM δ1 := inM_atom _ _
    have eN : A x α (m + 1 + 1) = δ1 + A x' α' (m + 1) := A_shift x α (m + 1)
    have eM : A x α (m + 1) = δ1 + A x' α' m := A_shift x α m
    have hEm : ExtConvexLE (A x α (m + 1)) ν :=
      extLE_left (A_mono x α (m + 1)) (A_inM x α _) hE
    have hEδ : ExtConvexLE δ1 ν := by
      refine extLE_left ?_ hδ1 hE
      rw [eN]; exact Measure.le_add_right le_rfl
    obtain ⟨ν1, hν1⟩ := shadow_exists hδ1 hν hEδ
    have hνν1 : InM (ν - ν1) := inM_of_le Measure.sub_le hν
    -- Lemma 4.12 for `A_{m+2} = δ1 + A'_{m+1}`
    have h412N := lemma_4_12 (α 1) (x 1) (A x' α' (m + 1)) ν (A_inM _ _ _) hν
      (by rw [← eN]; exact hE) ν1 hν1
    have h412M := lemma_4_12 (α 1) (x 1) (A x' α' m) ν (A_inM _ _ _) hν
      (by rw [← eM]; exact hEm) ν1 hν1
    obtain ⟨η2, hη2⟩ := shadow_exists (A_inM _ _ _) hνν1 h412N.1
    obtain ⟨η2', hη2'⟩ := shadow_exists (A_inM _ _ _) hνν1 h412M.1
    have hb' : b = ν1 + η2 := by
      refine shadow_unique (A_inM x α _) hν hE hb ?_
      rw [eN]; exact h412N.2 η2 hη2
    have ha' : a = ν1 + η2' := by
      refine shadow_unique (A_inM x α _) hν hEm ha ?_
      rw [eM]; exact h412M.2 η2' hη2'
    obtain ⟨σ, hσ, hσeq⟩ := ih x' α' (ν - ν1) h412N.1 η2' η2 hη2' hη2
    refine ⟨σ, ?_, ?_⟩
    · rw [ha', ← sub_sub_eq hν1.1 hη2'.1]; exact hσ
    · rw [hb', ha', hσeq, add_assoc]

end MartOT.Shadow.T413Aux

open MeasureTheory NNReal MartOT.Var MartOT.Shadow.T413Aux in
theorem solution (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (ν : Measure ℝ)
    (h : ∀ n, 1 ≤ n →
      MartOT.Var.ExtConvexLE (∑ i ∈ Finset.Icc 1 n, (α i : ENNReal) • Measure.dirac (x i)) ν)
    (νs : ℕ → Measure ℝ)
    (hS : ∀ n,
      MartOT.Var.IsShadow ν (∑ i ∈ Finset.Icc 1 n, (α i : ENNReal) • Measure.dirac (x i)) (νs n)) :
    νs 0 = 0 ∧
    ∀ n, 1 ≤ n → ∃ σ : Measure ℝ,
      MartOT.Var.IsShadow (ν - νs (n - 1)) ((α n : ENNReal) • Measure.dirac (x n)) σ ∧
      νs n = νs (n - 1) + σ := by
  refine ⟨shadow_of_zero_eq (by simpa using hS 0), fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact claim m x α ν (h (m + 1) hn) (νs m) (νs (m + 1)) (hS m) (hS (m + 1))
