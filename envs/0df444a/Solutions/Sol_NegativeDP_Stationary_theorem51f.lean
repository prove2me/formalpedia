-- Prove2me | solution 1 for NegativeDP.Stationary.theorem51f
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T01:34:38.793593+00:00
-- url     : https://prove2.me/submissions/ad85d48c-3c98-484d-9ae3-ea43fed56c03

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary.P4788

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Append `(a, t)` to a history (the map used in `historyLaw`). -/
def snoc {n : ℕ} (h : Hist S A n) (a : A) (t : S) : Hist S A (n + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
    ((h.2, a), h.1), t)

/-- Prepend the pair `(s, a)` to a history. -/
def consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) : Hist S A (k + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => S × A) 0).symm
    ((s, a), h.1), h.2)

/-- The empty history at state `s`. -/
def start (s : S) : Hist S A 0 := ((fun i : Fin 0 => Fin.elim0 i), s)

lemma measurable_snoc (n : ℕ) :
    Measurable (fun x : (Hist S A n × A) × S => snoc x.1.1 x.1.2 x.2) := by
  unfold snoc; fun_prop

lemma measurable_consH (s : S) (a : A) (k : ℕ) :
    Measurable (fun h : Hist S A k => consH s a h) := by
  unfold consH; fun_prop

lemma measurable_start : Measurable (fun s : S => (start s : Hist S A 0)) := by
  unfold start; fun_prop

lemma snoc_eq {n : ℕ} (h : Hist S A n) (a : A) (t : S) :
    snoc h a t = (Fin.snoc (α := fun _ => S × A) h.1 (h.2, a), t) := by
  show (Fin.insertNth (α := fun _ => S × A) (Fin.last n) (h.2, a) h.1, t) = _
  rw [Fin.insertNth_last']

lemma consH_eq (s : S) (a : A) {k : ℕ} (h : Hist S A k) :
    consH s a h = (Fin.cons (α := fun _ => S × A) (s, a) h.1, h.2) := by
  show (Fin.insertNth (α := fun _ => S × A) 0 (s, a) h.1, h.2) = _
  rw [Fin.insertNth_zero']

lemma snoc_consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) (b : A) (t : S) :
    snoc (consH s a h) b t = consH s a (snoc h b t) := by
  rw [snoc_eq, consH_eq, consH_eq, snoc_eq]
  simp only [Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma consH_start (s : S) (a : A) (t : S) :
    consH s a (start t : Hist S A 0) = snoc (start s) a t := by
  rw [snoc_eq, consH_eq]
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i
  rfl

lemma historyLaw_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    historyLaw P π s (n + 1) = (stageLaw P π s n).map (fun x => snoc x.1.1 x.1.2 x.2) := rfl

lemma historyLaw_zero (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    historyLaw P π s 0 = Measure.dirac (start s) := rfl

lemma isProb_historyLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ n, IsProbabilityMeasure (historyLaw P π s n)
  | 0 => by rw [historyLaw_zero]; infer_instance
  | n + 1 => by
    haveI := isProb_historyLaw P π s n
    haveI := π.κ_markov n
    haveI := P.q_markov
    haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
    haveI : IsProbabilityMeasure (stageLaw P π s n) := by
      show IsProbabilityMeasure ((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n)
      infer_instance
    rw [historyLaw_succ]
    exact Measure.isProbabilityMeasure_map (measurable_snoc n).aemeasurable

lemma lintegral_stageLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ)
    (G : (Hist S A n × A) × S → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂stageLaw P π s n =
      ∫⁻ h, ∫⁻ a, ∫⁻ t, G ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  haveI := isProb_historyLaw P π s n
  have hnk : ∀ ha : Hist S A n × A, nextKernel P n ha = P.q (ha.1.2, ha.2) := fun ha => by
    simp [nextKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  show ∫⁻ x, G x ∂((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n) = _
  rw [Measure.lintegral_compProd hG,
    Measure.lintegral_compProd (f := fun ha => ∫⁻ t, G (ha, t) ∂nextKernel P n ha)
      hG.lintegral_kernel_prod_right']
  simp only [hnk]

lemma lintegral_historyLaw_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S)
    (n : ℕ) (g : Hist S A (n + 1) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ h', g h' ∂historyLaw P π s (n + 1) =
      ∫⁻ h, ∫⁻ a, ∫⁻ t, g (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n := by
  rw [historyLaw_succ, lintegral_map hg (measurable_snoc n)]
  exact lintegral_stageLaw P π s n _ (hg.comp (measurable_snoc n))

lemma measurable_loss (P : Problem S A) :
    Measurable (fun x : S × A × S => ENNReal.ofReal (-P.r x)) :=
  ENNReal.measurable_ofReal.comp P.r_measurable.neg

lemma stageLoss_eq (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    stageLoss P π s n = ∫⁻ h, ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t))
      ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n :=
  lintegral_stageLaw P π s n (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
    ((measurable_loss P).comp (by fun_prop))

lemma meas_inner (P : Problem S A) {n : ℕ} (X : (Hist S A n × A) × S → ℝ≥0∞)
    (hX : Measurable X) :
    Measurable (fun ha : Hist S A n × A => ∫⁻ t, X (ha, t) ∂P.q (ha.1.2, ha.2)) := by
  haveI := P.q_markov
  have hm : Measurable (fun ha : Hist S A n × A => (ha.1.2, ha.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  haveI : IsMarkovKernel (P.q.comap _ hm) := Kernel.IsMarkovKernel.comap _ hm
  exact hX.lintegral_kernel_prod_right' (κ := P.q.comap _ hm)

lemma triple_add (P : Problem S A) (π : Plan (S := S) (A := A)) {n : ℕ}
    (μ : Measure (Hist S A n)) (X Y : (Hist S A n × A) × S → ℝ≥0∞) (hX : Measurable X) :
    ∫⁻ h, ∫⁻ a, ∫⁻ t, X ((h, a), t) + Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ =
      (∫⁻ h, ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ) +
      ∫⁻ h, ∫⁻ a, ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ := by
  haveI := P.q_markov
  haveI := π.κ_markov n
  have h1 := meas_inner P X hX
  have h2 : Measurable (fun h => ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h) :=
    h1.lintegral_kernel_prod_right'
  have e3 : ∀ h a, ∫⁻ t, X ((h, a), t) + Y ((h, a), t) ∂P.q (h.2, a) =
      ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) + ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) := fun h a =>
    lintegral_add_left (f := fun t => X ((h, a), t)) (hX.comp (by fun_prop)) _
  have e2 : ∀ h, ∫⁻ a, (∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) + ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a))
      ∂π.κ n h = ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h +
        ∫⁻ a, ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h := fun h =>
    lintegral_add_left (f := fun a => ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a))
      (h1.comp (measurable_const.prodMk measurable_id)) _
  simp_rw [e3, e2]
  exact lintegral_add_left h2 _

/-- Finite-horizon continuation loss: `N` more stages from a history at Lean stage `n`. -/
noncomputable def V (P : Problem S A) (π : Plan (S := S) (A := A)) :
    (N : ℕ) → (n : ℕ) → Hist S A n → ℝ≥0∞
  | 0, _, _ => 0
  | N + 1, n, h => ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + V P π N (n + 1) (snoc h a t)
      ∂P.q (h.2, a) ∂π.κ n h

lemma measurable_V (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ N n, Measurable (V P π N n)
  | 0, n => measurable_const
  | N + 1, n => by
    haveI := π.κ_markov n
    have hX : Measurable (fun x : (Hist S A n × A) × S =>
        ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) + V P π N (n + 1) (snoc x.1.1 x.1.2 x.2)) :=
      ((measurable_loss P).comp (by fun_prop)).add
        ((measurable_V P π N (n + 1)).comp (measurable_snoc n))
    exact (meas_inner P _ hX).lintegral_kernel_prod_right'

lemma V_le_succ (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ N n h, V P π N n h ≤ V P π (N + 1) n h
  | 0, n, h => by simp only [V]; exact bot_le
  | N + 1, n, h => by
    show ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + V P π N (n + 1) (snoc h a t)
      ∂P.q (h.2, a) ∂π.κ n h ≤ ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) +
        V P π (N + 1) (n + 1) (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h
    exact lintegral_mono fun a => lintegral_mono fun t =>
      add_le_add le_rfl (V_le_succ P π N (n + 1) (snoc h a t))

lemma V_mono (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (h : Hist S A n) :
    Monotone (fun N => V P π N n h) :=
  monotone_nat_of_le_succ fun N => V_le_succ P π N n h

lemma V_sum (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ N n, ∫⁻ h, V P π N n h ∂historyLaw P π s n =
      ∑ j ∈ Finset.range N, stageLoss P π s (n + j)
  | 0, n => by simp [V]
  | N + 1, n => by
    have hX : Measurable (fun x : (Hist S A n × A) × S =>
        ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2))) := (measurable_loss P).comp (by fun_prop)
    simp only [V]
    rw [triple_add P π _ (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
      (fun x => V P π N (n + 1) (snoc x.1.1 x.1.2 x.2)) hX,
      ← stageLoss_eq, ← lintegral_historyLaw_succ P π s n _ (measurable_V P π N (n + 1)),
      V_sum P π s N (n + 1), Finset.sum_range_succ', add_comm]
    simp only [add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + 1 + j = n + (j + 1) by omega]

/-- The total expected loss of a plan, so that `I P π s = -(L P π s)`. -/
noncomputable def L (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : ℝ≥0∞ :=
  ∑' n, stageLoss P π s n

lemma I_eq (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    I P π s = -((L P π s : ℝ≥0∞) : EReal) := rfl

lemma L_eq_iSup (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    L P π s = ⨆ N, V P π N 0 (start s) := by
  rw [L, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun N => ?_
  have := V_sum P π s N 0
  rw [historyLaw_zero, lintegral_dirac' _ (measurable_V P π N 0)] at this
  rw [this]
  simp

lemma measurable_L (P : Problem S A) (π : Plan (S := S) (A := A)) : Measurable (L P π) := by
  have : L P π = fun s => ⨆ N, V P π N 0 (start s) := funext (L_eq_iSup P π)
  rw [this]
  exact Measurable.iSup fun N => (measurable_V P π N 0).comp measurable_start

/-- The plan `π` seen after the first pair `(s, a)`. -/
noncomputable def shiftPlan (π : Plan (S := S) (A := A)) (s : S) (a : A) :
    Plan (S := S) (A := A) where
  κ k := (π.κ (k + 1)).comap (fun h => consH s a h) (measurable_consH s a k)
  κ_markov k := by
    haveI := π.κ_markov (k + 1)
    exact Kernel.IsMarkovKernel.comap _ _

lemma V_shift (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (a : A) :
    ∀ N k (h : Hist S A k), V P π N (k + 1) (consH s a h) = V P (shiftPlan π s a) N k h
  | 0, k, h => rfl
  | N + 1, k, h => by
    simp only [V, snoc_consH, V_shift P π s a N (k + 1)]
    rfl

lemma L_shift (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (a : A) (t : S) :
    L P (shiftPlan π s a) t = ⨆ N, V P π N 1 (snoc (start s) a t) := by
  rw [L_eq_iSup]
  refine iSup_congr fun N => ?_
  rw [← V_shift P π s a N 0, consH_start]

lemma V_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (N n : ℕ) (h : Hist S A n) :
    V P π (N + 1) n h = ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) +
      V P π N (n + 1) (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h := rfl


theorem plan_ext (π σ : Plan (S := S) (A := A)) (h : ∀ n, π.κ n = σ.κ n) : π = σ := by
  cases π
  cases σ
  congr
  funext n
  exact h n

lemma tail_consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) :
    Hist.tail (consH s a h) = h := by
  rw [consH_eq]
  rfl

/-- After the first pair, the prefixed plan `(f, π)` is `π` again. -/
lemma shift_prefix (f : {g : S → A // Measurable g}) (π : Plan (S := S) (A := A)) (s : S)
    (a : A) : shiftPlan (prefixPlan f π) s a = π := by
  refine plan_ext _ _ fun k => ?_
  ext1 h
  show ((π.κ k).comap Hist.tail (Hist.measurable_tail k)) (consH s a h) = π.κ k h
  rw [Kernel.comap_apply, tail_consH]

/-- The stationary plan `f^(∞)` equals `(f, f^(∞))`. -/
lemma stationary_prefix (f : {g : S → A // Measurable g}) :
    prefixPlan f (MarkovPlan.toPlan (stationary f)) = MarkovPlan.toPlan (stationary f) := by
  refine plan_ext _ _ fun n => ?_
  cases n with
  | zero => rfl
  | succ k =>
    ext1 h
    simp [MarkovPlan.toPlan, prefixPlan, Kernel.comap_apply, Kernel.deterministic_apply,
      Hist.tail, stationary]
    rfl

lemma V_prefix (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : Plan (S := S) (A := A)) (N : ℕ) (s : S) :
    V P (prefixPlan f π) (N + 1) 0 (start s) =
      ∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + V P π N 0 (start t) ∂P.q (s, f.1 s) := by
  have h0 : (prefixPlan f π).κ 0 (start s) = Measure.dirac (f.1 s) := rfl
  rw [V_succ, h0, lintegral_dirac]
  refine lintegral_congr fun t => ?_
  rw [← consH_start, V_shift, shift_prefix]
  rfl

lemma L_prefix (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : Plan (S := S) (A := A)) (s : S) :
    L P (prefixPlan f π) s =
      ∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + L P π t ∂P.q (s, f.1 s) := by
  have hshift : (⨆ N, V P (prefixPlan f π) N 0 (start s)) =
      ⨆ N, V P (prefixPlan f π) (N + 1) 0 (start s) := by
    refine le_antisymm (iSup_le fun N => ?_) (iSup_le fun N => le_iSup_of_le (N + 1) le_rfl)
    exact le_iSup_of_le N (V_mono P _ 0 (start s) (Nat.le_succ N))
  have hmeas : ∀ N, Measurable (fun t : S =>
      ENNReal.ofReal (-P.r (s, f.1 s, t)) + V P π N 0 (start t)) := fun N =>
    ((measurable_loss P).comp (by fun_prop)).add
      ((measurable_V P π N 0).comp measurable_start)
  have hmono : Monotone (fun N (t : S) =>
      ENNReal.ofReal (-P.r (s, f.1 s, t)) + V P π N 0 (start t)) := fun N M hNM t =>
    add_le_add le_rfl (V_mono P π 0 (start t) hNM)
  rw [L_eq_iSup, hshift]
  simp_rw [V_prefix]
  rw [← lintegral_iSup hmeas hmono]
  refine lintegral_congr fun t => ?_
  rw [← ENNReal.add_iSup, L_eq_iSup]

lemma part1 (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : Plan (S := S) (A := A)) : T P f (I P π) = I P (prefixPlan f π) := by
  funext s
  rw [I_eq P (prefixPlan f π) s, L_prefix]
  unfold T
  congr 3
  funext t
  rw [I_eq, neg_neg, EReal.toENNReal_coe]

lemma iter (P : Problem S A) (f : {g : S → A // Measurable g}) :
    ∀ n, (T P f)^[n] 0 = fun s =>
      -((V P (MarkovPlan.toPlan (stationary f)) n 0 (start s) : ℝ≥0∞) : EReal)
  | 0 => by
    funext s
    simp [V]
  | n + 1 => by
    rw [Function.iterate_succ_apply', iter P f n]
    funext s
    have h := V_prefix P f (MarkovPlan.toPlan (stationary f)) n s
    rw [stationary_prefix] at h
    rw [h]
    unfold T
    congr 3
    funext t
    rw [neg_neg, EReal.toENNReal_coe]

lemma main (P : Problem S A) (f : {g : S → A // Measurable g}) :
    (∀ π : Plan (S := S) (A := A), T P f (I P π) = I P (prefixPlan f π)) ∧
    T P f (I P (MarkovPlan.toPlan (stationary f))) = I P (MarkovPlan.toPlan (stationary f)) ∧
    ∀ s, Filter.Tendsto (fun n => (T P f)^[n] 0 s) Filter.atTop
      (nhds (I P (MarkovPlan.toPlan (stationary f)) s)) := by
  refine ⟨part1 P f, ?_, fun s => ?_⟩
  · rw [part1, stationary_prefix]
  · simp only [iter P f]
    rw [I_eq, L_eq_iSup]
    have hm := tendsto_atTop_iSup (V_mono P (MarkovPlan.toPlan (stationary f)) 0 (start s))
    exact (continuous_neg.tendsto _).comp
      ((continuous_coe_ennreal_ereal.tendsto _).comp hm)

end NegativeDP.Stationary.P4788

open MeasureTheory ProbabilityTheory Filter Topology in open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary) in open NegativeDP.Stationary in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (f : {g : S → A // Measurable g}) :
    (∀ π : Plan (S := S) (A := A), T P f (I P π) = I P (prefixPlan f π)) ∧
    T P f (I P (MarkovPlan.toPlan (stationary f))) = I P (MarkovPlan.toPlan (stationary f)) ∧
    ∀ s, Tendsto (fun n => (T P f)^[n] 0 s) atTop
      (𝓝 (I P (MarkovPlan.toPlan (stationary f)) s)) := by
  exact NegativeDP.Stationary.P4788.main P f
