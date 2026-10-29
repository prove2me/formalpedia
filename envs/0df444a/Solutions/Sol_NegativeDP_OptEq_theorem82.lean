-- Prove2me | solution 1 for NegativeDP.OptEq.theorem82
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T02:44:40.559356+00:00
-- url     : https://prove2.me/submissions/a2945b51-fc85-4c8a-9a4f-1475159c892a

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
import Theorems.Thm_NegativeDP_OptEq_theorem81
import Theorems.Thm_NegativeDP_Stationary_theorem51f

/-!
Strauch (1966), Theorem 8.2, negative case, from Theorem 8.1 (`theorem81`: `(p, ε)`-optimal
Markov plans exist for every probability `p`) and Theorem 5.1 (f) (`theorem51f`:
`T_f I(π) = I(f, π)`).

* `v* ≤ sup_a T_a v*`: apply 8.1 with `p = δ_s`; the Markov plan `m` is the prefix plan
  `(m₀, ¹m)`, so `I(m)(s) = T_{m₀} I(¹m)(s) ≤ T_{m₀(s)} v*(s)`.
* `T_a v* ≤ v*`: apply 8.1 with `p = q(· | s, a)`; the plan `(a, m)` has return
  `T_a I(m)(s) ≥ T_a v*(s) − ε` because `I(m) ≥ v* − ε` holds `q(· | s, a)`-a.e. and the
  lower integral is monotone a.e.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace NegativeDP.OptEq.Red52bb

theorem le_of_forall_pos_le_add' {x y : EReal} (h : ∀ ε : ℝ, 0 < ε → x ≤ y + ε) : x ≤ y := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top =>
    have h1 := h 1 one_pos
    induction y using EReal.rec with
    | bot => simp at h1
    | top => exact le_rfl
    | coe b =>
      exfalso
      have : ((b : EReal) + ((1 : ℝ) : EReal)) = ((b + 1 : ℝ) : EReal) := by norm_cast
      rw [this] at h1
      exact absurd (top_le_iff.1 h1) (EReal.coe_ne_top _)
  | coe a =>
    induction y using EReal.rec with
    | bot =>
      have h1 := h 1 one_pos
      simp at h1
    | top => exact le_top
    | coe b =>
      refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun ε hε => ?_)
      have := h ε hε
      have e : ((b : EReal) + (ε : EReal)) = ((b + ε : ℝ) : EReal) := by norm_cast
      rw [e] at this
      exact EReal.coe_le_coe_iff.1 this

theorem coe_ennreal_real (x : ℝ≥0∞) (hx : x ≠ ⊤) : (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  lift x to NNReal using hx
  rfl

/-- From `-W - ε ≤ -L` get `L ≤ W + ε`. -/
theorem key_le (L W : ℝ≥0∞) (ε : ℝ) (hε : 0 < ε)
    (h : -(W : EReal) - (ε : EReal) ≤ -(L : EReal)) : L ≤ W + ENNReal.ofReal ε := by
  by_cases hW : W = ⊤
  · simp [hW]
  by_cases hL : L = ⊤
  · exfalso
    rw [hL, coe_ennreal_real W hW] at h
    have e : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) = ((-W.toReal - ε : ℝ) : EReal) := by
      norm_cast
    have hne : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) ≠ ⊥ := by
      rw [e]; exact EReal.coe_ne_bot _
    exact hne (by simpa using h)
  rw [coe_ennreal_real W hW, coe_ennreal_real L hL] at h
  have e1 : (-((W.toReal : ℝ) : EReal) - (ε : EReal)) = ((-W.toReal - ε : ℝ) : EReal) := by
    norm_cast
  have e2 : (-((L.toReal : ℝ) : EReal)) = ((-L.toReal : ℝ) : EReal) := by norm_cast
  rw [e1, e2, EReal.coe_le_coe_iff] at h
  rw [← ENNReal.ofReal_toReal hL, ← ENNReal.ofReal_toReal hW,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- From `J ≤ W + ε` get `-W ≤ -J + ε`. -/
theorem neg_le_of_le (J W : ℝ≥0∞) (ε : ℝ) (hε : 0 < ε) (h : J ≤ W + ENNReal.ofReal ε) :
    -(W : EReal) ≤ -(J : EReal) + (ε : EReal) := by
  by_cases hW : W = ⊤
  · simp [hW]
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hW, ENNReal.ofReal_ne_top⟩) h
  rw [coe_ennreal_real W hW, coe_ennreal_real J hJ]
  have e1 : (-((J.toReal : ℝ) : EReal) + (ε : EReal)) = ((-J.toReal + ε : ℝ) : EReal) := by
    norm_cast
  have e2 : (-((W.toReal : ℝ) : EReal)) = ((-W.toReal : ℝ) : EReal) := by norm_cast
  rw [e1, e2, EReal.coe_le_coe_iff]
  rw [← ENNReal.ofReal_toReal hJ, ← ENNReal.ofReal_toReal hW,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le] at h
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  linarith

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- The total expected loss `Σₙ stageLoss`, so that `I = -L`. -/
noncomputable def L (P : NegativeDP.Stationary.Problem S A)
    (π : DiscountedDP.Stationary.Plan (S := S) (A := A)) (s : S) : ℝ≥0∞ :=
  ∑' n, NegativeDP.Stationary.stageLoss P π s n

theorem I_eq (P : NegativeDP.Stationary.Problem S A)
    (π : DiscountedDP.Stationary.Plan (S := S) (A := A)) (s : S) :
    NegativeDP.Stationary.I P π s = -((L P π s : ℝ≥0∞) : EReal) := rfl

/-- `W = -v*` as a loss in `[0, ∞]`. -/
noncomputable def W (P : NegativeDP.Stationary.Problem S A) (s : S) : ℝ≥0∞ :=
  (-(NegativeDP.Stationary.vstar P s)).toENNReal

theorem vstar_nonpos (P : NegativeDP.Stationary.Problem S A) (s : S) :
    NegativeDP.Stationary.vstar P s ≤ 0 := by
  unfold NegativeDP.Stationary.vstar
  refine iSup_le fun π => ?_
  rw [I_eq, EReal.neg_le_zero]
  exact EReal.coe_ennreal_nonneg _

theorem vstar_eq (P : NegativeDP.Stationary.Problem S A) (s : S) :
    NegativeDP.Stationary.vstar P s = -((W P s : ℝ≥0∞) : EReal) := by
  unfold W
  rw [EReal.coe_toENNReal (by simpa using vstar_nonpos P s), neg_neg]

theorem W_le_L (P : NegativeDP.Stationary.Problem S A)
    (π : DiscountedDP.Stationary.Plan (S := S) (A := A)) (s : S) : W P s ≤ L P π s := by
  have h : NegativeDP.Stationary.I P π s ≤ NegativeDP.Stationary.vstar P s :=
    le_iSup (fun σ => NegativeDP.Stationary.I P σ s) π
  rw [I_eq, vstar_eq, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff] at h
  exact h

/-- The shifted Markov plan `¹m = (m₁, m₂, …)`. -/
def tailM (m : DiscountedDP.Stationary.MarkovPlan S A) : DiscountedDP.Stationary.MarkovPlan S A :=
  fun k => m (k + 1)

theorem plan_ext (π σ : DiscountedDP.Stationary.Plan (S := S) (A := A))
    (h : ∀ n, π.κ n = σ.κ n) : π = σ := by
  cases π
  cases σ
  congr
  funext n
  exact h n

theorem markov_eq_prefix (m : DiscountedDP.Stationary.MarkovPlan S A) :
    DiscountedDP.Stationary.MarkovPlan.toPlan m =
      NegativeDP.Stationary.prefixPlan (m 0) (DiscountedDP.Stationary.MarkovPlan.toPlan (tailM m)) := by
  refine plan_ext _ _ fun n => ?_
  cases n with
  | zero => rfl
  | succ k =>
    ext1 h
    simp [DiscountedDP.Stationary.MarkovPlan.toPlan, NegativeDP.Stationary.prefixPlan,
      Kernel.comap_apply, Kernel.deterministic_apply, NegativeDP.Stationary.Hist.tail, tailM]
    rfl

/-- The `T`-integral of a loss function. -/
theorem T_eq (P : NegativeDP.Stationary.Problem S A) (f : {g : S → A // Measurable g})
    (π : DiscountedDP.Stationary.Plan (S := S) (A := A)) (s : S) :
    NegativeDP.Stationary.T P f (NegativeDP.Stationary.I P π) s =
      -(((∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + L P π t ∂P.q (s, f.1 s) : ℝ≥0∞)) : EReal) := by
  unfold NegativeDP.Stationary.T
  congr 3
  funext t
  rw [I_eq, neg_neg, EReal.toENNReal_coe]

theorem Ta_eq (P : NegativeDP.Stationary.Problem S A) (a : A) (s : S) :
    Ta P a (NegativeDP.Stationary.vstar P) s =
      -(((∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) + W P t ∂P.q (s, a) : ℝ≥0∞)) : EReal) := rfl

end NegativeDP.OptEq.Red52bb

open NegativeDP.OptEq NegativeDP.OptEq.Red52bb in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] (P : NegativeDP.Stationary.Problem S A) :
    ∀ s, NegativeDP.Stationary.vstar P s = ⨆ a : A, Ta P a (NegativeDP.Stationary.vstar P) s := by
  intro s
  have : IsMarkovKernel P.q := P.q_markov
  apply le_antisymm
  · -- `v* ≤ sup_a T_a v*`, via 8.1 at `δ_s`
    refine le_of_forall_pos_le_add' fun ε hε => ?_
    obtain ⟨m, -, hm⟩ := theorem81 P (Measure.dirac s) inferInstance ε hε
    rw [ae_dirac_eq] at hm
    have hms : NegativeDP.Stationary.vstar P s - (ε : EReal) ≤
        NegativeDP.Stationary.I P (DiscountedDP.Stationary.MarkovPlan.toPlan m) s := hm
    rw [vstar_eq, I_eq] at hms
    have h1 := key_le _ _ ε hε hms
    -- `I(m)(s) = T_{m₀} I(¹m)(s)`
    have hT := (NegativeDP.Stationary.theorem51f P (m 0)).1
      (DiscountedDP.Stationary.MarkovPlan.toPlan (tailM m))
    have hT' := congrFun hT s
    rw [← markov_eq_prefix, T_eq, I_eq, neg_inj, EReal.coe_ennreal_eq_coe_ennreal_iff] at hT'
    set a0 := (m 0).1 s
    have hJ : (∫⁻ t, ENNReal.ofReal (-P.r (s, a0, t)) + W P t ∂P.q (s, a0)) ≤
        W P s + ENNReal.ofReal ε := by
      rw [← hT'] at h1
      refine le_trans ?_ h1
      exact lintegral_mono fun t => add_le_add le_rfl (W_le_L P _ t)
    rw [vstar_eq]
    refine le_trans (neg_le_of_le _ _ ε hε hJ) ?_
    gcongr
    rw [← Ta_eq]
    exact le_iSup (fun a => Ta P a (NegativeDP.Stationary.vstar P) s) a0
  · -- `T_a v* ≤ v*`, via 8.1 at `q(· | s, a)`
    refine iSup_le fun a => ?_
    rw [Ta_eq, vstar_eq, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨m, -, hm⟩ := theorem81 P (P.q (s, a)) inferInstance (ε : ℝ) (by exact_mod_cast hε)
    let f : {g : S → A // Measurable g} := ⟨fun _ => a, measurable_const⟩
    have hT := congrFun ((NegativeDP.Stationary.theorem51f P f).1
      (DiscountedDP.Stationary.MarkovPlan.toPlan m)) s
    rw [T_eq, I_eq, neg_inj, EReal.coe_ennreal_eq_coe_ennreal_iff] at hT
    have hle : W P s ≤ L P (NegativeDP.Stationary.prefixPlan f
        (DiscountedDP.Stationary.MarkovPlan.toPlan m)) s := W_le_L P _ s
    rw [← hT] at hle
    refine le_trans hle ?_
    have hae : ∀ᵐ t ∂P.q (s, a),
        ENNReal.ofReal (-P.r (s, a, t)) + L P (DiscountedDP.Stationary.MarkovPlan.toPlan m) t ≤
          (ENNReal.ofReal (-P.r (s, a, t)) + W P t) + ENNReal.ofReal (ε : ℝ) := by
      filter_upwards [hm] with t ht
      rw [vstar_eq, I_eq] at ht
      rw [add_assoc]
      exact add_le_add le_rfl (key_le _ _ ε (by exact_mod_cast hε) ht)
    refine le_trans (lintegral_mono_ae hae) ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      ENNReal.ofReal_coe_nnreal]
