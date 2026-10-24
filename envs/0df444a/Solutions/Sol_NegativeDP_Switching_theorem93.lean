-- Prove2me | solution 1 for NegativeDP.Switching.theorem93
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T12:43:46.020897+00:00
-- url     : https://prove2.me/submissions/f67f5655-deda-40c2-a7ab-49d74e1ca608

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

lemma measurable_stepLoss (P : Problem S A) (ρ : Plan (S := S) (A := A)) (n : ℕ) :
    Measurable (stepLoss P ρ n) := by
  haveI := P.q_markov
  haveI := ρ.κ_markov n
  have h1 : Measurable (fun p : S × A => ∫⁻ t, ENNReal.ofReal (-P.r (p.1, p.2, t)) ∂P.q p) := by
    refine Measurable.lintegral_kernel_prod_right
      (f := fun (p : S × A) (t : S) => ENNReal.ofReal (-P.r (p.1, p.2, t))) ?_
    exact ENNReal.measurable_ofReal.comp (P.r_measurable.comp (by fun_prop)).neg
  have h2 : Measurable (fun x : Hist S A n × A =>
      ∫⁻ t, ENNReal.ofReal (-P.r (x.1.2, x.2, t)) ∂P.q (x.1.2, x.2)) :=
    h1.comp (by fun_prop)
  exact Measurable.lintegral_kernel_prod_right (κ := ρ.κ n)
    (f := fun h a => ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) ∂P.q (h.2, a)) h2

lemma stepLoss_congr (P : Problem S A) (ρ ρ' : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) (hκ : ρ.κ n h = ρ'.κ n h) : stepLoss P ρ n h = stepLoss P ρ' n h := by
  simp only [stepLoss, hκ]

lemma map_congr_apply {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (κ₁ κ₂ : Kernel X Y) (f : Y → Z) (a : X) (H : κ₁ a = κ₂ a) :
    κ₁.map f a = κ₂.map f a := by
  by_cases hf : Measurable f
  · rw [Kernel.map_apply _ hf, Kernel.map_apply _ hf, H]
  · rw [Kernel.map_of_not_measurable _ hf, Kernel.map_of_not_measurable _ hf]

lemma stepKernel_congr (P : Problem S A) (ρ ρ' : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) (hκ : ρ.κ n h = ρ'.κ n h) :
    stepKernel P ρ n h = stepKernel P ρ' n h := by
  have := ρ.κ_markov n
  have := ρ'.κ_markov n
  have := P.q_markov
  have : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  simp only [stepKernel]
  apply map_congr_apply
  ext s hs
  rw [Kernel.compProd_apply hs, Kernel.compProd_apply hs, Kernel.prod_apply,
    Kernel.prod_apply, hκ]

lemma contKernel_succ_lintegral (P : Problem S A) (ρ : Plan (S := S) (A := A)) :
    ∀ (k : ℕ) (f : (m : ℕ) → Hist S A m → ℝ≥0∞), (∀ m, Measurable (f m)) →
    ∀ (n : ℕ) (h : Hist S A n),
    ∫⁻ h', f (n + (k + 1)) h' ∂contKernel P ρ n (k + 1) h =
      ∫⁻ h1, (∫⁻ h', f (n + 1 + k) h' ∂contKernel P ρ (n + 1) k h1) ∂stepKernel P ρ n h := by
  intro k
  induction k with
  | zero =>
    intro f hf n h
    show ∫⁻ h', f (n + 1) h' ∂(stepKernel P ρ n ∘ₖ Kernel.id) h =
      ∫⁻ h1, (∫⁻ h', f (n + 1) h' ∂(Kernel.id : Kernel (Hist S A (n + 1)) _) h1)
        ∂stepKernel P ρ n h
    rw [Kernel.comp_id]
    congr 1
    funext h1
    rw [Kernel.id_apply, lintegral_dirac' _ (hf _)]
  | succ k ih =>
    intro f hf n h
    have hg : ∀ m, Measurable (fun x : Hist S A m => ∫⁻ y, f (m + 1) y ∂stepKernel P ρ m x) :=
      fun m => (hf (m + 1)).lintegral_kernel
    have e1 : ∫⁻ h', f (n + (k + 1 + 1)) h' ∂contKernel P ρ n (k + 1 + 1) h
        = ∫⁻ h'', (∫⁻ y, f (n + (k + 1) + 1) y ∂stepKernel P ρ (n + (k + 1)) h'')
            ∂contKernel P ρ n (k + 1) h :=
      Kernel.lintegral_comp (stepKernel P ρ (n + (k + 1))) (contKernel P ρ n (k + 1)) h
        (hf (n + (k + 1) + 1))
    rw [e1]
    refine (ih (fun m x => ∫⁻ y, f (m + 1) y ∂stepKernel P ρ m x) hg n h).trans ?_
    congr 1
    funext h1
    exact (Kernel.lintegral_comp (stepKernel P ρ (n + 1 + k)) (contKernel P ρ (n + 1) k) h1
      (hf (n + 1 + k + 1))).symm

/-- The continuation loss: `contReturn = -U`. -/
noncomputable def U (P : Problem S A) (ρ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ h', stepLoss P ρ (n + k) h' ∂contKernel P ρ n k h

lemma contReturn_eq (P : Problem S A) (ρ : Plan (S := S) (A := A)) (n : ℕ) (h : Hist S A n) :
    contReturn P ρ n h = -((U P ρ n h : ℝ≥0∞) : EReal) := rfl

lemma measurable_U (P : Problem S A) (ρ : Plan (S := S) (A := A)) (n : ℕ) :
    Measurable (U P ρ n) :=
  Measurable.ennreal_tsum fun k => (measurable_stepLoss P ρ (n + k)).lintegral_kernel

lemma U_rec (P : Problem S A) (ρ : Plan (S := S) (A := A)) (n : ℕ) (h : Hist S A n) :
    U P ρ n h = stepLoss P ρ n h + ∫⁻ h1, U P ρ (n + 1) h1 ∂stepKernel P ρ n h := by
  unfold U
  rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · show ∫⁻ h', stepLoss P ρ n h' ∂(Kernel.id : Kernel (Hist S A n) _) h = _
    rw [Kernel.id_apply, lintegral_dirac' _ (measurable_stepLoss P ρ n)]
  · rw [lintegral_tsum (fun k => ((measurable_stepLoss P ρ (n + 1 + k)).lintegral_kernel).aemeasurable)]
    congr 1
    funext k
    exact contKernel_succ_lintegral P ρ k (stepLoss P ρ) (measurable_stepLoss P ρ) n h

lemma contKernel_start (P : Problem S A) (ρ : Plan (S := S) (A := A)) (s : S) :
    ∀ (k : ℕ) (f : (m : ℕ) → Hist S A m → ℝ≥0∞), (∀ m, Measurable (f m)) →
    ∫⁻ h', f (0 + k) h' ∂contKernel P ρ 0 k (Hist.start s) =
      ∫⁻ h', f k h' ∂historyLaw P ρ s k := by
  intro k
  induction k with
  | zero =>
    intro f hf
    show ∫⁻ h', f 0 h' ∂(Kernel.id : Kernel (Hist S A 0) _) (Hist.start s) =
      ∫⁻ h', f 0 h' ∂(Measure.dirac (Hist.start s))
    rw [Kernel.id_apply]
  | succ k ih =>
    intro f hf
    have hg : ∀ m, Measurable (fun x : Hist S A m => ∫⁻ y, f (m + 1) y ∂stepKernel P ρ m x) :=
      fun m => (hf (m + 1)).lintegral_kernel
    have e1 : ∫⁻ h', f (0 + (k + 1)) h' ∂contKernel P ρ 0 (k + 1) (Hist.start s)
        = ∫⁻ h'', (∫⁻ y, f (0 + k + 1) y ∂stepKernel P ρ (0 + k) h'')
            ∂contKernel P ρ 0 k (Hist.start s) :=
      Kernel.lintegral_comp (stepKernel P ρ (0 + k)) (contKernel P ρ 0 k) (Hist.start s)
        (hf (0 + k + 1))
    rw [e1]
    refine (ih (fun m x => ∫⁻ y, f (m + 1) y ∂stepKernel P ρ m x) hg).trans ?_
    show ∫⁻ x, (∫⁻ y, f (k + 1) y ∂stepKernel P ρ k x) ∂historyLaw P ρ s k =
      ∫⁻ h', f (k + 1) h' ∂(historyLaw P ρ s k).bind (stepKernel P ρ k)
    rw [Measure.lintegral_bind (stepKernel P ρ k).measurable.aemeasurable
      (hf (k + 1)).aemeasurable]

lemma telescope (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S)
    (W : (n : ℕ) → Hist S A n → ℝ≥0∞) (hW : ∀ n, Measurable (W n))
    (hstep : ∀ n h, stepLoss P π n h + ∫⁻ h1, W (n + 1) h1 ∂stepKernel P π n h ≤ W n h) :
    ∀ N, (∑ j ∈ Finset.range N, stageLoss P π s j) + ∫⁻ h, W N h ∂historyLaw P π s N
      ≤ W 0 (Hist.start s) := by
  intro N
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    show ∫⁻ h, W 0 h ∂Measure.dirac (Hist.start s) ≤ _
    rw [lintegral_dirac' _ (hW 0)]
  | succ N ih =>
    refine le_trans ?_ ih
    rw [Finset.sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    show ∫⁻ h, stepLoss P π N h ∂historyLaw P π s N +
        ∫⁻ h, W (N + 1) h ∂(historyLaw P π s N).bind (stepKernel P π N) ≤ _
    rw [Measure.lintegral_bind (stepKernel P π N).measurable.aemeasurable (hW _).aemeasurable,
      ← lintegral_add_left (measurable_stepLoss P π N)]
    exact lintegral_mono (fun h => hstep N h)

lemma I_eq (P : Problem S A) (ρ : Plan (S := S) (A := A)) (s : S) :
    I P ρ s = -((U P ρ 0 (Hist.start s) : ℝ≥0∞) : EReal) := by
  have : ∑' n, stageLoss P ρ s n = U P ρ 0 (Hist.start s) :=
    tsum_congr fun k => (contKernel_start P ρ s k (stepLoss P ρ) (measurable_stepLoss P ρ)).symm
  show -((∑' n, stageLoss P ρ s n : ℝ≥0∞) : EReal) = _
  rw [this]

end NegativeDP.Switching

open NegativeDP.Switching in open DiscountedDP.Stationary (Hist Plan) in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ : Plan (S := S) (A := A)) :
    (∃ π : Plan (S := S) (A := A), IsSwitch P σ τ π) ∧
    ∀ π : Plan (S := S) (A := A), IsSwitch P σ τ π →
      ∀ s, max (I P σ s) (I P τ s) ≤ I P π s := by
  have hset : ∀ n, {h : Hist S A n | contReturn P τ n h < contReturn P σ n h} =
      {h | U P σ n h < U P τ n h} := by
    intro n
    ext h
    simp only [Set.mem_setOf_eq, contReturn_eq, EReal.neg_lt_neg_iff,
      EReal.coe_ennreal_lt_coe_ennreal_iff]
  have hB : ∀ n, MeasurableSet {h : Hist S A n | contReturn P τ n h < contReturn P σ n h} := by
    intro n
    rw [hset n]
    exact measurableSet_lt (measurable_U P σ n) (measurable_U P τ n)
  refine ⟨⟨⟨fun n => Kernel.piecewise (hB n) (σ.κ n) (τ.κ n), fun n => ?_⟩, ?_⟩, ?_⟩
  · have := σ.κ_markov n
    have := τ.κ_markov n
    infer_instance
  · intro n h
    show Kernel.piecewise (hB n) (σ.κ n) (τ.κ n) h = _
    rw [Kernel.piecewise_apply]
    by_cases hc : contReturn P τ n h < contReturn P σ n h
    · rw [if_pos (show h ∈ {h : Hist S A n | contReturn P τ n h < contReturn P σ n h} from hc),
        if_pos hc]
    · rw [if_neg (show h ∉ {h : Hist S A n | contReturn P τ n h < contReturn P σ n h} from hc),
        if_neg hc]
  · intro π hπ s
    set W : (n : ℕ) → Hist S A n → ℝ≥0∞ := fun n h => min (U P σ n h) (U P τ n h) with hWdef
    have hW : ∀ n, Measurable (W n) := fun n => (measurable_U P σ n).min (measurable_U P τ n)
    have hstep : ∀ n h, stepLoss P π n h + ∫⁻ h1, W (n + 1) h1 ∂stepKernel P π n h ≤ W n h := by
      intro n h
      have hk := hπ n h
      have hiff : contReturn P τ n h < contReturn P σ n h ↔ U P σ n h < U P τ n h := by
        rw [contReturn_eq, contReturn_eq, EReal.neg_lt_neg_iff,
          EReal.coe_ennreal_lt_coe_ennreal_iff]
      by_cases hc : U P σ n h < U P τ n h
      · rw [if_pos (hiff.mpr hc)] at hk
        rw [stepLoss_congr P π σ n h hk, stepKernel_congr P π σ n h hk]
        calc stepLoss P σ n h + ∫⁻ h1, W (n + 1) h1 ∂stepKernel P σ n h
            ≤ stepLoss P σ n h + ∫⁻ h1, U P σ (n + 1) h1 ∂stepKernel P σ n h :=
              add_le_add le_rfl (lintegral_mono fun x => min_le_left _ _)
          _ = U P σ n h := (U_rec P σ n h).symm
          _ = W n h := (min_eq_left hc.le).symm
      · rw [if_neg (mt hiff.mp hc)] at hk
        rw [stepLoss_congr P π τ n h hk, stepKernel_congr P π τ n h hk]
        calc stepLoss P τ n h + ∫⁻ h1, W (n + 1) h1 ∂stepKernel P τ n h
            ≤ stepLoss P τ n h + ∫⁻ h1, U P τ (n + 1) h1 ∂stepKernel P τ n h :=
              add_le_add le_rfl (lintegral_mono fun x => min_le_right _ _)
          _ = U P τ n h := (U_rec P τ n h).symm
          _ = W n h := (min_eq_right (not_lt.mp hc)).symm
    have hloss : ∑' j, stageLoss P π s j ≤ W 0 (Hist.start s) :=
      ENNReal.tsum_le_of_sum_range_le fun N =>
        le_trans le_self_add (telescope P π s W hW hstep N)
    have hIπ : I P π s = -((∑' j, stageLoss P π s j : ℝ≥0∞) : EReal) := rfl
    rw [I_eq P σ s, I_eq P τ s, hIπ]
    refine max_le ?_ ?_
    · exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (hloss.trans (min_le_left _ _)))
    · exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (hloss.trans (min_le_right _ _)))
