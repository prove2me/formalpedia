-- Prove2me | solution 1 for OAI.HadwigerCounterexample.StatusAnalysis.lightmap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:08:09.053973+00:00
-- url     : https://prove2.me/submissions/898ac5f3-538b-4947-bfe8-3fe69eff7a12

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ430Hc000
import Theorems.Thm_OAI_HadwigerCounterexample_PreparationParameters_veil_score_cost
import Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_Quill_sideRelease
import Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_Station_eclipse_beam
import Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_gauzeCalendar
import Theorems.Thm_OAI_HadwigerCounterexample_Template_controls

section
-- module Solutions.OAIQ430_HC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Laws -/

noncomputable section
open scoped BigOperators

namespace HadwigerCounterexample

variable {α β : Type*}

theorem ind_one {p : Prop} (h : p) : ind p = 1 := by classical simp [ind, h]
theorem ind_zero {p : Prop} (h : ¬p) : ind p = 0 := by classical simp [ind, h]
@[simp] theorem ind_true : ind True = 1 := ind_one trivial
@[simp] theorem ind_false : ind False = 0 := ind_zero (not_false)

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  by_cases h : p
  · exact le_of_lt (by rw [ind_one h]; norm_num)
  · rw [ind_zero h]

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  by_cases h : p
  · rw [ind_one h]
  · rw [ind_zero h]
    norm_num

theorem ind_mono {p q : Prop} (hp : p → q) : ind p ≤ ind q := by
  by_cases h : p
  · rw [ind_one h, ind_one (hp h)]
  · rw [ind_zero h]
    exact ind_nonneg _

theorem ind_not (p : Prop) : ind (¬p) = 1 - ind p := by
  by_cases h : p <;> simp [ind, h]

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases h : p <;> by_cases h2 : q <;> simp [ind, h, h2]

theorem ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases h : p
  · simp only [h, true_or, ind_true]
    have := ind_nonneg q
    linarith
  · simp [h]

theorem IsLaw.sub [Fintype α] {w : Wgt α} (hw : IsLaw w) : SubLaw w where
  nz := hw.nz
  total := hw.total.le

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

theorem tot_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ tot w := Finset.sum_nonneg fun x _ => hw x

theorem weight_le_tot (hw : ∀ x, 0 ≤ w x) (x) : w x ≤ tot w :=
  Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)

theorem avg_comm (w f : Wgt α) : avg w f = avg f w := by simp only [avg, mul_comm]

theorem avg_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

theorem avg_mono_left (hf : ∀ x, 0 ≤ f x) (h : ∀ x, w x ≤ v x) : avg w f ≤ avg v f := by
  rw [avg_comm w, avg_comm v]
  exact avg_mono hf h

theorem avg_nonneg (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

theorem avg_const (w : Wgt α) (a : ℝ) : avg w (fun _ => a) = tot w * a := by
  rw [avg, tot, Finset.sum_mul]

theorem IsLaw.avg_const (hw : IsLaw w) (a : ℝ) : avg w (fun _ => a) = a := by
  rw [HadwigerCounterexample.avg_const, hw.total, one_mul]

theorem SubLaw.avg_le (hw : SubLaw w) {b : ℝ} (hb : 0 ≤ b) (h : ∀ x, f x ≤ b) :
    avg w f ≤ b := by
  refine (avg_mono hw.nz h).trans ?_
  rw [avg_const]
  exact (mul_le_mul_of_nonneg_right hw.total hb).trans_eq (one_mul b)

theorem IsLaw.avg_le (hw : IsLaw w) {b : ℝ} (h : ∀ x, f x ≤ b) : avg w f ≤ b :=
  (avg_mono hw.nz h).trans (hw.avg_const _).le

theorem IsLaw.le_avg (hw : IsLaw w) {b : ℝ} (h : ∀ x, b ≤ f x) : b ≤ avg w f :=
  (hw.avg_const _).ge.trans (avg_mono hw.nz h)

theorem abs_avg_le (hw : ∀ x, 0 ≤ w x) : |avg w f| ≤ avg w (fun x => |f x|) := by
  rw [avg, avg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  simp_rw [abs_mul, abs_of_nonneg (hw _)]

theorem avg_add (w f g : Wgt α) : avg w (fun x => f x + g x) = avg w f + avg w g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (w f g : Wgt α) : avg w (fun x => f x - g x) = avg w f - avg w g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_mul (w f : Wgt α) (b : ℝ) : avg w (fun x => f x * b) = avg w f * b := by
  simp only [avg, Finset.sum_mul, mul_assoc]

theorem avg_mul' (w f : Wgt α) (b : ℝ) : avg w (fun x => b * f x) = b * avg w f := by
  simpa only [mul_comm b] using avg_mul w f b

theorem avg_div (w f : Wgt α) (b : ℝ) : avg w (fun x => f x / b) = avg w f / b := by
  simp_rw [div_eq_mul_inv]
  exact avg_mul _ _ _

theorem avg_congr (h : ∀ x, w x ≠ 0 → f x = g x) : avg w f = avg w g := by
  unfold avg
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : w x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

theorem avg_sum {ι : Type*} (w : Wgt α) (s : Finset ι) (f : ι → Wgt α) :
    avg w (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, avg w (f i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem avg_avg [Fintype β] (w : Wgt α) (v : Wgt β) (f : α → β → ℝ) :
    avg w (fun x => avg v (f x)) = avg v (fun y => avg w (fun x => f x y)) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem pr_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ pr w p :=
  avg_nonneg hw fun _ => ind_nonneg _

theorem pr_le_tot (hw : ∀ x, 0 ≤ w x) : pr w p ≤ tot w := by
  unfold pr
  refine (avg_mono hw fun x => ind_le_one (p x)).trans_eq ?_
  rw [avg_const, mul_one]

theorem pr_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, p x → q x) : pr w p ≤ pr w q :=
  avg_mono hw fun x => ind_mono (h x)

theorem pr_mono_left (h : ∀ x, w x ≤ v x) (p : α → Prop) : pr w p ≤ pr v p :=
  avg_mono_left (fun x => ind_nonneg (p x)) h

theorem pr_not (w : Wgt α) (p : α → Prop) : pr w (fun x => ¬p x) = tot w - pr w p := by
  simp_rw [pr, ind_not, avg_sub, avg_const, mul_one]

@[simp] theorem pr_true (w : Wgt α) : pr w (fun _ => True) = tot w := by simp [pr, avg, tot]
@[simp] theorem pr_false (w : Wgt α) : pr w (fun _ => False) = 0 := by simp [pr]

theorem pr_or_le (hw : ∀ x, 0 ≤ w x) :
    pr w (fun x => p x ∨ q x) ≤ pr w p + pr w q :=
  (avg_mono hw fun x => ind_or_le (p x) (q x)).trans_eq (avg_add _ _ _)

theorem pr_union_le (hw : ∀ x, 0 ≤ w x) {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    pr w (fun x => ∃ i ∈ s, p i x) ≤ ∑ i ∈ s, pr w (p i) := by
  let F : ι → Wgt α := fun i x => ind (p i x)
  change _ ≤ ∑ i ∈ s, avg w (F i)
  rw [← avg_sum]
  refine avg_mono hw fun x => ?_
  change ind (∃ i ∈ s, p i x) ≤ _
  by_cases h : ∃ i ∈ s, p i x
  · rw [ind_one h]
    obtain ⟨i, hi, hp⟩ := h
    have : F i x ≤ ∑ i ∈ s, F i x :=
      Finset.single_le_sum (fun (j : ι) _ => ind_nonneg (p j x)) hi
    simpa only [F, ind_one hp] using this
  · rw [ind_zero h]
    exact Finset.sum_nonneg fun i _ => ind_nonneg (p i x)

theorem pr_exists_le (hw : ∀ x, 0 ≤ w x) {ι : Type*} [Fintype ι] (p : ι → α → Prop) :
    pr w (fun x => ∃ i, p i x) ≤ ∑ i, pr w (p i) := by
  simpa using pr_union_le hw Finset.univ p

theorem weight_le_pr (hw : ∀ x, 0 ≤ w x) {x} (hx : p x) : w x ≤ pr w p := by
  have h := pr_mono (p:=fun y => x = y) (q:=p) hw (fun y e => e ▸ hx)
  simpa only [pr_point] using h

theorem exists_of_pr_pos (hw : ∀ x, 0 ≤ w x) (hp : 0 < pr w p) :
    ∃ x, p x ∧ 0 < w x := by
  by_contra! hn
  have h : pr w p = 0 := by
    unfold pr avg
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : p x
    · rw [le_antisymm (hn x hx) (hw x), zero_mul]
    · simp only [ind_zero hx, mul_zero]
  exact hp.ne' h

theorem carried_iff_pr (hw : ∀ x, 0 ≤ w x) : carried w p ↔ pr w p = tot w := by
  constructor
  · intro h
    unfold pr
    have e : avg w (fun x => ind (p x)) = avg w (fun _ => 1) := by
      refine avg_congr fun x hx => ind_one (Classical.byContradiction fun hn => hx (h x hn))
    rw [e, avg_const, mul_one]
  · intro he x hx
    have h := weight_le_pr (p:=fun x => ¬p x) hw hx
    rw [pr_not, he, sub_self] at h
    exact le_antisymm h (hw x)

theorem le_avg_markov (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) (b : ℝ) :
    b * pr w (fun x => b ≤ f x) ≤ avg w f := by
  unfold pr
  rw [← avg_mul']
  refine avg_mono hw fun x => ?_
  by_cases h : b ≤ f x
  · simpa [ind_one h] using h
  · simpa [ind_zero h] using hf x

end Basic

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}

omit [Fintype α] in
theorem subW_nonneg (hw : ∀ x, 0 ≤ w x) (p : α → Prop) : ∀ x, 0 ≤ subW w p x :=
  fun x => mul_nonneg (hw x) (ind_nonneg _)

omit [Fintype α] in
theorem subW_le (hw : ∀ x, 0 ≤ w x) (p : α → Prop) (x : α) : subW w p x ≤ w x :=
  (mul_le_mul_of_nonneg_left (ind_le_one _) (hw x)).trans_eq (mul_one _)

omit [Fintype α] in
theorem subW_carried (w : Wgt α) (p : α → Prop) : carried (subW w p) p :=
  fun x h => by rw [subW, ind_zero h, mul_zero]

theorem subLaw_sub (hw : SubLaw w) (p : α → Prop) : SubLaw (subW w p) :=
  ⟨subW_nonneg hw.nz p, (pr_le_tot hw.nz).trans hw.total⟩

theorem pr_sub (w : Wgt α) (p q : α → Prop) :
    pr (subW w p) q = pr w (fun x => p x ∧ q x) := by
  simp only [pr, avg, ind_and, subW, mul_assoc]

theorem normW_nonneg (hw : ∀ x, 0 ≤ w x) : ∀ x, 0 ≤ normW w x :=
  fun x => div_nonneg (hw x) (tot_nonneg hw)

theorem avg_norm (w f : Wgt α) : avg (normW w) f = avg w f / tot w := by
  rw [avg_comm, avg_comm w f]
  exact avg_div _ _ _

theorem tot_norm (w : Wgt α) : tot (normW w) = tot w / tot w := by
  simp only [tot, normW, div_eq_mul_inv, Finset.sum_mul]

theorem normW_law (hw : ∀ x, 0 ≤ w x) (hpos : 0 < tot w) : IsLaw (normW w) :=
  ⟨normW_nonneg hw, by rw [tot_norm, div_self hpos.ne']⟩

theorem normW_subLaw (hw : ∀ x, 0 ≤ w x) : SubLaw (normW w) := by
  refine ⟨normW_nonneg hw, ?_⟩
  rw [tot_norm]
  by_cases h : tot w = 0 <;> simp [h]

theorem unif_apply (x : α) : unif x = (Fintype.card α : ℝ)⁻¹ := by
  simp [unif, normW, tot]

theorem unif_subLaw : SubLaw (unif : Wgt α) :=
  normW_subLaw (fun _ => zero_le_one)

theorem unif_law [Nonempty α] : IsLaw (unif : Wgt α) := by
  refine normW_law (fun _ => zero_le_one) ?_
  simp [tot, Fintype.card_pos]

theorem unifOn_law (h : ∃ x, p x) : IsLaw (unifOn p) := by
  refine normW_law (fun _ => ind_nonneg _) ?_
  obtain ⟨x, hx⟩ := h
  have := weight_le_tot (fun x => ind_nonneg (p x)) x
  change 0 < tot _
  rw [ind_one hx] at this
  exact lt_of_lt_of_le zero_lt_one this

end Restrict

section Prod
variable [Fintype α] [Fintype β] {w : Wgt α} {v : Wgt β}

theorem pairW_avg (w : Wgt α) (v : Wgt β) (f : α × β → ℝ) :
    avg (pairW w v) f = avg w (fun x => avg v (fun y => f (x,y))) := by
  simp only [avg, Finset.mul_sum, Fintype.sum_prod_type, pairW, mul_assoc]

theorem pairW_separate (w f : Wgt α) (v g : Wgt β) :
    avg (pairW w v) (fun p => f p.1 * g p.2) = avg w f * avg v g := by
  simp only [pairW_avg, avg_mul', avg_mul]

theorem pairW_pr (w : Wgt α) (v : Wgt β) (p : α → Prop) (q : β → Prop) :
    pr (pairW w v) (fun x => p x.1 ∧ q x.2) = pr w p * pr v q := by
  simp_rw [pr, ind_and]
  exact pairW_separate w (fun x => ind (p x)) v (fun y => ind (q y))

theorem pairW_tot (w : Wgt α) (v : Wgt β) : tot (pairW w v) = tot w * tot v := by
  simpa using pairW_pr w v (fun _ => True) (fun _ => True)

theorem pairW_law (hw : IsLaw w) (hv : IsLaw v) : IsLaw (pairW w v) :=
  ⟨fun x => mul_nonneg (hw.nz _) (hv.nz _), by rw [pairW_tot, hw.total, hv.total, mul_one]⟩

theorem mixW_avg (w : Wgt α) (F : α → Wgt β) (g : Wgt β) :
    avg (mixW w F) g = avg w (fun x => avg (F x) g) := by
  simp only [avg, mixW, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem mixW_tot (w : Wgt α) (F : α → Wgt β) :
    tot (mixW w F) = avg w (fun x => tot (F x)) := by
  simpa only [avg_const, mul_one] using mixW_avg w F (fun _ => 1)

theorem mixW_law (hw : IsLaw w) {F : α → Wgt β} (hF : ∀ x, IsLaw (F x)) :
    IsLaw (mixW w F) := by
  refine ⟨fun x => avg_nonneg hw.nz (fun y => (hF y).nz _), ?_⟩
  rw [mixW_tot]
  simp_rw [(hF _).total]
  exact hw.avg_const _

theorem mapW_avg (w : Wgt α) (f : α → β) (g : Wgt β) :
    avg (mapW w f) g = avg w (fun x => g (f x)) := by
  classical
  change avg (mixW w (fun x y => ind (f x = y))) g = _
  rw [mixW_avg]
  simp [avg, ind]

theorem mapW_law (hw : IsLaw w) (f : α → β) : IsLaw (mapW w f) := by
  refine ⟨fun _ => pr_nonneg hw.nz, ?_⟩
  simpa only [avg_const, mul_one, hw.total] using mapW_avg w f (fun _ => 1)

theorem mapW_pr (w : Wgt α) (f : α → β) (q : β → Prop) :
    pr (mapW w f) q = pr w (fun x => q (f x)) := mapW_avg _ _ _

end Prod

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExponentialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential Rates -/

noncomputable section
namespace HadwigerCounterexample

open Filter Real
open scoped Topology

theorem bp_pos (x : ℝ) : 0 < bp x := by unfold bp; positivity
theorem bp_nat (x : ℕ) : bp x = (2:ℝ)^x := by simp [bp]
theorem bp_add (x y : ℝ) : bp (x+y) = bp x * bp y :=
  Real.rpow_add (by norm_num) _ _
theorem bp_sub (x y : ℝ) : bp (x-y) = bp x / bp y :=
  Real.rpow_sub (by norm_num) _ _
theorem bp_neg (x : ℝ) : bp (-x) = (bp x)⁻¹ := by simpa using bp_sub 0 x

theorem bp_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (a*x)) atTop atTop :=
  (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
    ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)

theorem bp_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (-a*x)) atTop (𝓝 0) := by
  simp_rw [neg_mul,bp_neg]
  exact (bp_tendsto ha).inv_tendsto_atTop

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}

namespace ExpSmall

theorem lim (hn : Tendsto n l atTop) (hf : ExpSmall l n f) :
    Tendsto f l (𝓝 0) := by
  obtain ⟨c,hc,h⟩ := hf
  have hl := (bp_tendsto_zero hc).comp hn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ hl
    (h.mono fun i hi => (abs_le.mp hi).1)
    (h.mono fun i hi => (abs_le.mp hi).2)
  simpa using hl.neg
end ExpSmall

theorem expO_const (hn : Tendsto n l atTop) (b : ℝ) :
    ExpO l n (fun _ => b) := fun _ hc =>
  ((bp_tendsto hc).comp hn).eventually (eventually_ge_atTop _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Laws -/

noncomputable section
open scoped BigOperators
namespace HadwigerCounterexample

theorem ind_all {ι : Type*} [Fintype ι] (p : ι → Prop) :
    ind (∀ i, p i) = ∏ i, ind (p i) := by
  classical
  simp [ind, Fintype.prod_ite_zero]

variable {ι κ α : Type*}
variable {β : ι → Type*}

section
variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]

theorem prodW_tot (w : ∀ i, Wgt (β i)) : tot (prodW w) = ∏ i, tot (w i) :=
  (Fintype.prod_sum w).symm

theorem prodW_avg (w f : ∀ i, Wgt (β i)) :
    avg (prodW w) (prodW f) = ∏ i, avg (w i) (f i) := by
  simp only [avg, prodW]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem prodW_pr (w : ∀ i, Wgt (β i)) (p : ∀ i, β i → Prop) :
    pr (prodW w) (fun x => ∀ i, p i (x i)) = ∏ i, pr (w i) (p i) := by
  simp_rw [pr, ind_all]
  exact prodW_avg w (fun i x => ind (p i x))

omit [DecidableEq ι] [∀ i, Fintype (β i)] in
theorem prodW_nonneg {w : ∀ i, Wgt (β i)} (h : ∀ i x, 0 ≤ w i x) (x) : 0 ≤ prodW w x :=
  Finset.prod_nonneg (fun i _ => h i _)

theorem prodW_law {w : ∀ i, Wgt (β i)} (hw : ∀ i, IsLaw (w i)) : IsLaw (prodW w) := by
  refine ⟨prodW_nonneg (fun i => (hw i).nz), ?_⟩
  rw [prodW_tot]
  simp_rw [(hw _).total]
  simp

end

section
variable [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ]
/-- Observe distinct coordinates of a (constant-type) product law. -/
theorem prodW_pr_inj {e : ι → κ} (he : Function.Injective e)
    {w : κ → Wgt α} (hw : ∀ k, IsLaw (w k)) (p : ι → α → Prop) :
    pr (prodW (β:=fun _ => α) w) (fun x => ∀ i, p i (x (e i))) =
      ∏ i, pr (w (e i)) (p i) := by
  classical
  let P (k : κ) (x : α) := ∀ i, e i = k → p i x
  have h (x : κ → α) : (∀ i, p i (x (e i))) ↔ ∀ k, P k (x k) :=
    ⟨fun h k i hi => hi ▸ h i, fun h i => h (e i) i rfl⟩
  simp_rw [h]
  rw [prodW_pr _ P]
  let f (k : κ) (i : ι) := if e i = k then pr (w k) (p i) else 1
  have hf (k : κ) : pr (w k) (P k) = ∏ i, f k i := by
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      have hP : P (e i) = p i := funext fun x => propext
        ⟨fun h => h i rfl, fun h j hj => (he hj).symm ▸ h⟩
      rw [hP]
      symm
      rw [Finset.prod_eq_single i]
      · simp [f]
      · intro j _ hj
        simp [f, show e j ≠ e i from he.ne hj]
      · simp
    · push Not at hk
      have hP : P k = (fun _ => True) := funext fun _ => propext
        ⟨fun _ => trivial, fun _ j hj => (hk j hj).elim⟩
      simp [hP, (hw k).total, f, hk]
  simp_rw [hf]
  rw [Finset.prod_comm]
  simp [f]

end
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! # Finite Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B : Type*} [Fintype A]

theorem nbr_eq_card (p : A → Prop) [Fintype {x // p x}] :
    nbr p = (Fintype.card {x // p x}:ℝ) := by
  classical
  rw [Fintype.card_subtype]
  simp [nbr,tot,ind]

theorem pr_unif (p : A → Prop) :
    pr unif p = nbr p / Fintype.card A := by
  simp only [pr, avg, nbr, tot, unif_apply, div_eq_mul_inv]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem unifOn_val (p : A → Prop) (x) :
    unifOn p x = ind (p x) / nbr p := rfl

theorem unifOn_sub (p : A → Prop) : SubLaw (unifOn p) :=
  normW_subLaw fun x => ind_nonneg (p x)

theorem unifOn_carried (p : A → Prop) : carried (unifOn p) p :=
  fun x h => by rw [unifOn_val,ind_zero h,zero_div]

theorem on_unif [Nonempty A] (p : A → Prop) : onW unif p = unifOn p := by
  have h : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  funext x
  simp only [onW, normW, subW_tot,subW,pr_unif,unifOn_val,unif_apply]
  by_cases hx : nbr p = 0
  · simp [hx]
  · field_simp

theorem unifOn_true : unifOn (fun _ : A => True) = unif := by
  simp [unifOn, unif]

theorem pr_on (w : Wgt A) (p q : A → Prop) :
    pr (onW w p) q = pr w (fun x => p x ∧ q x) / pr w p := by
  unfold onW
  change avg _ _ = _
  rw [avg_norm,subW_tot]
  exact congrArg (fun b => b / pr w p) (pr_sub w p q)

theorem pr_of_on {w : Wgt A} (hw : ∀ x, 0 ≤ w x) (p q : A → Prop) :
    pr w (fun x => p x ∧ q x) = pr w p * pr (onW w p) q := by
  rw [pr_on]
  by_cases h : pr w p = 0
  · rw [h,zero_mul]
    apply le_antisymm _ (pr_nonneg hw)
    rw [← h]
    exact pr_mono hw fun _ => And.left
  · field_simp

theorem onW_val (w : Wgt A) (p : A → Prop) (x) :
    onW w p x = w x * ind (p x) / pr w p := rfl

theorem on_mon {w : Wgt A} (hw : ∀ x, 0 ≤ w x) {p : A → Prop} {a : ℝ}
    (ha : 0 < a) (h : a ≤ pr w p) (x) : onW w p x ≤ a⁻¹ * w x :=
  calc onW w p x = (subW w p x) / pr w p := rfl
       _ ≤ w x / a := div_le_div₀ (hw x) (subW_le hw p x) ha h
       _ = _ := by rw [div_eq_mul_inv,mul_comm]

/-- Being a probability with support p and all point masses there equal
uniquely characterizes unifOn. -/
theorem uniform_support {w : Wgt A} {p : A → Prop} (hw : IsLaw w)
    (hp : carried w p) (he : ∀ x y, p x → p y → w x = w y) :
    w = unifOn p := by
  have h := (carried_iff_pr hw.nz).mp hp
  rw [hw.total] at h
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw.nz (h.trans_gt zero_lt_one)
  have e : ∀ y, w y = w x * ind (p y) := by
    intro y; by_cases h : p y
    · rw [ind_one h, mul_one, he _ _ h hx]
    · rw [hp y h,ind_zero h,mul_zero]
  have hsum : w x * nbr p = 1 := by
    calc w x * nbr p = tot w := by
           unfold nbr tot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => (e y).symm
         _ = 1 := hw.total
  have hn : nbr p ≠ 0 := right_ne_zero_of_mul (hsum.trans_ne one_ne_zero)
  funext y; rw [e,unifOn_val,eq_div_iff hn,mul_right_comm,hsum,one_mul]

theorem avg_bij (e : A ≃ A) (w f : Wgt A) :
    avg (fun x => w (e x)) (fun x => f (e x)) = avg w f := by
  unfold avg
  exact Equiv.sum_comp e (fun x => w x * f x)

variable [Fintype B]

omit [Fintype B] in
theorem mapW_carried {w : Wgt A} {p : A → Prop} {q : B → Prop} {f : A → B}
    (hw : carried w p) (h : ∀ x, p x → q (f x)) : carried (mapW w f) q := by
  intro y hy
  change ∑ x, w x * ind (f x=y) = 0
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases e : f x=y
  · rw [hw x (fun hp => hy (e ▸ h x hp)),zero_mul]
  · rw [ind_zero e,mul_zero]

/-- Pointwise transitivity transfer of a uniform law under observation. -/
theorem uniform_orbit {p : A → Prop} {q : B → Prop} (f : A → B) (hp : ∃ x, p x)
    (hq : ∀ x, p x → q (f x))
    (h : ∀ y z, q y → q z → ∃ e : A ≃ A, (∀ x, p x ↔ p (e x))
      ∧ ∀ x, f x = y ↔ f (e x)=z) :
    mapW (unifOn p) f = unifOn q := by
  refine uniform_support (mapW_law (unifOn_law hp) _) (mapW_carried (unifOn_carried p) hq)
    (fun y z hy hz => ?_)
  obtain ⟨e,he,hE⟩ := h y z hy hz
  unfold mapW pr
  rw [← avg_bij e (unifOn p) (fun x => ind (f x = z))]
  simp_rw [unifOn_val,← he,← hE]
  rfl

omit [Fintype B] in
/-- Mapping changes a density bound functorially. -/
theorem mapW_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c * v x) (f : A → B) (y) :
    mapW w f y ≤ c * mapW v f y := by
  unfold mapW
  refine (pr_mono_left (v:=fun x => c * v x) h _).trans_eq ?_
  simp only [pr,avg,Finset.mul_sum,mul_assoc]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMatrices
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Matrices -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix

theorem bit_cases (x : F) : x = 0 ∨ x = 1 :=
  (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! # Matrix Ranks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function

section Generic
variable {V W U : Type}
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup U] [Module F U]

theorem rk_surj {f : V →ₗ[F] W} [FiniteDimensional F W] : Surjective f ↔ rk f = dim W := by
  rw [← range_eq_top]
  constructor
  · intro h; unfold rk dim; rw [h]; exact finrank_top _ _
  exact Submodule.eq_top_of_finrank_eq

theorem rk_inj {f : V →ₗ[F] W} [FiniteDimensional F V] : Injective f ↔ rk f = dim V := by
  constructor
  · exact LinearMap.finrank_range_of_inj
  intro h
  rw [← ker_eq_bot, ← Submodule.finrank_eq_zero (R:=F)]
  have hj := f.finrank_range_add_finrank_ker
  dsimp only [rk,dim] at h
  omega

end Generic

variable {I J K : Type}
variable [Fintype I] [Fintype J]

omit [Fintype I] in
theorem rank_cast (P : Mat I J) : P.rank = rk P.mulVecLin := rfl
theorem dim_vec (K : Type) [Fintype K] : dim (Vec K) = Fintype.card K :=
  Module.finrank_pi F

omit [Fintype I] in
theorem mrk_inj {P : Mat I J} : Function.Injective P.mulVec ↔ P.rank = Fintype.card J := by
  rw [rank_cast,← dim_vec,rk_inj.symm]; rfl
theorem mrk_surj {P : Mat I J} : Function.Surjective P.mulVec ↔ P.rank = Fintype.card I := by
  rw [rank_cast,← dim_vec,rk_surj.symm]; rfl

theorem transpose_surj_iff {P : Mat I J} : Surjective Pᵀ.mulVec ↔ Injective P.mulVec := by
  rw [mrk_surj,mrk_inj,rank_transpose]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteAffineLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Affine Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap
open scoped BigOperators

section General
variable (V W : Type)
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem card_space [Fintype V] : (Fintype.card V : ℝ) = bp (dim V) := by
  rw [Module.card_eq_pow_finrank (K:=F)]
  rw [show Fintype.card F = 2 from ZMod.card 2, bp_nat]
  push_cast; rfl

variable {V W}

theorem add_polar (t : V) : ∀ x : V, x+t+t=x := by
  intro x; rw [add_assoc,char_two,add_zero]

/-- Equally likely images along every direction of an indexed family. The
translation hypothesis is before testing the specified targets. -/
theorem translate_cap [Fintype V] [Fintype W] {T : Type*} [Fintype T] [Nonempty T]
    {w : Wgt V} (hw : SubLaw w)
    (f : V →ₗ[F] W) (g : T ↪ W) (h : ∀ t, ∃ v, f v = g t ∧ ∀ x, w (x+v) = w x) (y : W) :
    pr w (fun x => f x=y) ≤ (Fintype.card T : ℝ)⁻¹ := by
  classical
  let u := mapW w f
  have h1 (t : T) : u (y+g t) = u y := by
    obtain ⟨v,hv,he⟩ := h t
    change avg w _ = avg w _
    let E : V ≃ V := ⟨(·+v),(·+v),add_polar v,add_polar v⟩
    rw [← avg_bij E w (fun x => ind (f x = y+g t))]
    change (avg (fun x => w (x+v)) (fun x => ind (f (x+v)=y+g t))) = _
    simp_rw [he,map_add,hv]
    simp
  have hu' : ∀ x, 0 ≤ u x := fun _ => pr_nonneg hw.nz
  have hut : tot u ≤ 1 := by
    have h : tot u = tot w := by simpa [u] using mapW_pr w f (fun _ => True)
    exact h.le.trans hw.total
  let k : T ↪ W := ⟨fun t => y+g t, fun i j h => g.injective (add_left_cancel h)⟩
  have h2 : (Fintype.card T:ℝ)*u y ≤ tot u := calc
    _ = ∑ t : T, u (y+g t) := by simp [h1]
    _ = ∑ x ∈ Finset.univ.map k, u x := by rw [Finset.sum_map]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hu' i)
  change u y ≤ _
  rw [←one_div,le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  rw [mul_comm]
  exact h2.trans hut

theorem unif_lin [Fintype V] [Fintype W] (f : V →ₗ[F] W) :
    mapW unif f = unifOn (fun y => y ∈ range f) := by
  rw [← unifOn_true]
  refine uniform_orbit _ ⟨0,trivial⟩ (fun x _ => ⟨x,rfl⟩) ?_
  rintro _ _ ⟨y,rfl⟩ ⟨z,rfl⟩
  let d := z-y
  let E : V ≃ V := ⟨(·+d),(·+d),add_polar d,add_polar d⟩
  refine ⟨E,fun _ => Iff.rfl, fun x => ?_⟩
  change f x = f y ↔ f (x+(z-y))=f z
  rw [map_add,map_sub]
  constructor
  · intro h; rw [h,add_sub_cancel]
  · intro h
    apply add_right_cancel (b := f z-f y)
    rw [h,add_sub_cancel]

theorem pr_unif_lin [Fintype V] [Fintype W] (f : V →ₗ[F] W) (y : W) :
    pr unif (fun x => f x=y) = ind (y ∈ range f) * bp (-(rk f:ℝ)) := by
  classical
  change mapW unif f y = _
  rw [unif_lin,unifOn_val,nbr_eq_card]
  rw [card_space,bp_neg,div_eq_mul_inv]

end General

theorem dim_mat (I J : Type) [Fintype I] [Fintype J] :
    dim (Mat I J) = Fintype.card I * Fintype.card J := by
  simp only [dim,Mat,finrank_matrix,finrank_self,mul_one]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Walsh Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

variable {A B V W : Type} [Fintype A] [Fintype B]

theorem avg_CS {w : Wgt A} (h : ∀ x, 0 ≤ w x) (f g : Wgt A) :
    (avg w (fun x => f x*g x))^2 ≤ avg w (fun x => f x^2)*avg w (fun x => g x^2) := by
  let F (f : Wgt A) (x) := Real.sqrt (w x)*f x
  have hg (f : Wgt A) (x) : (F f x)^2=w x*f x^2 := by
    unfold F; rw [mul_pow, Real.sq_sqrt (h x)]
  have hx (x) : F f x*F g x=w x*(f x*g x) := by
    unfold F; rw [mul_mul_mul_comm,← pow_two,Real.sq_sqrt (h _)]
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (F f) (F g)
  simp_rw [hg,hx] at he
  exact he

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
theorem map_nz {p : Wgt A} (hp : ∀ i, 0 ≤ p i) (f : A→B) (i : B) :
    0 ≤ mapW p f i := pr_nonneg hp
omit [Fintype B] in
theorem lsupp_witness {p : Wgt A} {f : A→B} {i}
    (h : mapW p f i≠0) : ∃ x,p x≠0 ∧ f x=i := by
  classical
  by_contra! hh
  refine h (Finset.sum_eq_zero (fun x _ => ?_))
  by_cases h : p x=0
  · change p x * ind _=0
    rw [h,zero_mul]
  exact (congrArg (p x * ·) (ind_zero (hh x h))).trans (mul_zero _)

omit [Fintype B] in
theorem lsupp_hit {p : Wgt A} (hp : ∀ i,0 ≤ p i) (f : A→B) (x : A) (h : p x≠0) :
    mapW p f (f x)≠0 := by
  have h' := lt_of_le_of_ne (hp x) (Ne.symm h)
  have he := weight_le_tot (fun y => mul_nonneg (hp y) (ind_nonneg (f y = f x))) x
  simp only [ind_true,mul_one] at he
  exact (h'.trans_le he).ne'

omit [Fintype B] in
theorem lsupp.map {p q : Wgt A} (h : lsupp p q) (hq : ∀ i,0 ≤ q i)
    (f : A→B) : lsupp (mapW p f) (mapW q f) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := lsupp_witness hi
  exact lsupp_hit hq f x (h x hx)

omit [Fintype B] in
theorem map_resize (p : Wgt A) (f : A→B) (u : Wgt B) :
    mapW (fun i => p i*u (f i)) f = (fun i => mapW p f i * u i) := by
  funext i
  unfold mapW pr avg
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  by_cases h : f j=i
  · simp only [h,ind_true,mul_one]
  simp only [ind_zero h,mul_zero,zero_mul]

omit [Fintype B] in
theorem map_pour (q : Wgt A) (f : A → B) (w : Wgt B) (h : lsupp w (mapW q f)) :
    mapW (pour q f w) f=w := by
  unfold pour
  rw [map_resize (u:=fun i => w i / mapW q f i)]
  funext i
  by_cases he : w i=0
  · simp only [he,zero_div,mul_zero]
  have hm := h i he
  field_simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalProductLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Product Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B I : Type} [Fintype A] [Fintype B]

theorem pair_unif :
    unif (α:=A×B) = pairW unif unif := by
  funext x; simp [pairW,unif_apply,mul_comm]

theorem semi_avg (w : Wgt A) (k : A → Wgt B) (f : A × B → ℝ) :
    avg (semi w k) f = avg w (fun x => avg (k x) (fun y => f (x,y))) := by
  simp only [avg,semi,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramProbabilities
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Probabilities -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Function LinearMap

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]

omit [Fintype U] in
theorem outer_act (x : Vec U) (v z : Vec I) :
    vecMulVec x v *ᵥ z = dotProduct v z • x := by rw [vecMulVec_mulVec,op_smul_eq_smul]

omit [Fintype U] in
theorem colSp_outer {x : Vec U} {T : Space (Vec U)} (h : x ∈ T) (v : Vec I) :
    colSp (vecMulVec x v) ≤ T := by
  rintro y ⟨z,rfl⟩
  rw [mulVecLin_apply,outer_act]
  exact T.smul_mem _ h

variable [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem shift_pmax {w : Wgt (Mat U I)} (hw : SubLaw w) (T : Space (Vec U))
    (h : columnInv (w:=w) T) {x : Vec I} (hx : x ≠ 0) (y : Vec U) :
    pr w (fun M => M *ᵥ x = y) ≤ bp (-(dim T:ℝ)) := by
  classical
  have hh : ∃ v : Vec I, dotProduct v x = 1 := by
    simp only [ne_eq,funext_iff,Pi.zero_apply, not_forall] at hx
    obtain ⟨i,hi⟩ := hx
    exact ⟨Pi.single i 1,(single_one_dotProduct _ _).trans ((bit_cases _).resolve_left hi)⟩
  obtain ⟨v,hv⟩ := hh
  let f : Mat U I →ₗ[F] Vec U := (Matrix.mulVecBilin F F).flip x
  let g : T ↪ Vec U := ⟨Subtype.val,Subtype.val_injective⟩
  have he : ∀ (t:T), ∃ A : Mat U I, f A = g t ∧ ∀ B, w (B+A)=w B := fun t =>
    ⟨vecMulVec t.val v,by change vecMulVec t.val v *ᵥ x = t.val; rw [outer_act,hv,one_smul],
      fun B => h B _ (colSp_outer t.property _)⟩
  have h' := translate_cap hw f g he y
  rw [bp_neg,← card_space]
  exact h'

theorem shift_fail {w : Wgt (Mat U I)} (hw : SubLaw w) (T : Space (Vec U))
    (h : columnInv (w:=w) T) :
    pr w (fun M => ¬ Injective M.mulVec) ≤ bp (num I - dim T) := by
  classical
  let p (x : Vec I) (M : Mat U I) := x ≠ 0 ∧ M *ᵥ x = 0
  have e1 : pr w (fun M => ¬ Injective M.mulVec) ≤ ∑ i : Vec I, pr w (p i) := by
    refine le_trans (pr_mono hw.nz (fun M hm => ?_)) (pr_exists_le hw.nz p)
    rw [← coe_mulVecLin,← ker_eq_bot,ker_mulVecLin_eq_bot_iff] at hm
    push Not at hm
    obtain ⟨x,h1,h2⟩ := hm
    exact ⟨x,h2,h1⟩
  have he (i : Vec I) : pr w (p i) ≤ bp (-(dim T:ℝ)) := by
    by_cases hi : i = 0
    · simp only [p,hi,ne_eq,not_true,false_and,pr_false]
      exact (bp_pos _).le
    · simpa only [p,hi,true_and, ne_eq, not_false_eq_true] using shift_pmax hw T h hi 0
  refine e1.trans ((Finset.sum_le_sum (fun i _ => he i)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,card_space,
    dim_vec,sub_eq_add_neg,bp_add,num]

theorem unif_fail :
    pr (unif : Wgt (Mat U I)) (fun M => ¬ Injective M.mulVec) ≤ bp (num I - num U) := by
  have h := shift_fail (@unif_subLaw (Mat U I) _) ⊤ (fun _ _ _ => rfl)
  unfold dim at h
  rw [finrank_top,show Module.finrank F (Vec U) = Fintype.card U from dim_vec _] at h
  exact h

omit [DecidableEq U] in
theorem gramL_surj (J : Type) {P : Mat U I} (h : Injective P.mulVec) :
    Surjective (GramL J P) := by
  obtain ⟨Q,hQ⟩ := mat_left_inv h
  intro x
  exact ⟨Qᵀ * x,by change Pᵀ * (Qᵀ * x) = x; rw [← Matrix.mul_assoc,← transpose_mul,
    hQ,Matrix.transpose_one, Matrix.one_mul]⟩

theorem pr_gram_fixed {P : Mat U I} (h : Injective P.mulVec) (G : Mat I J) :
    pr unif (fun Q : Mat U J => Pᵀ * Q = G) = bp (-num I * num J) := by
  have hh := gramL_surj J h
  have hf := pr_unif_lin (GramL J P) G
  rw [ind_one (show G ∈ range _ from hh G),one_mul,rk_surj.mp hh,dim_mat] at hf
  change pr unif _ = _
  exact hf.trans (congrArg bp (by push_cast; unfold num; ring))

omit [Fintype I] [DecidableEq I] in
/-- Conditional minus columns: adding columns in the annihilator of P
doesn't change the pre-injectivity Gram law. -/
theorem gram_shift (P : Mat U I) (G : Mat I J) :
    columnInv (w:=unifOn (fun Q : Mat U J => Pᵀ * Q = G)) (ker (Pᵀ.mulVecLin)) := by
  intro M A hA
  have h : Pᵀ * A = 0 := by
    apply coe_mv_inj
    change (Pᵀ * A).mulVecLin = (0:Mat I J).mulVecLin
    rw [mulVecLin_mul,mulVecLin_zero]
    exact LinearMap.ext fun x => hA (show A.mulVecLin x ∈ colSp A from ⟨x,rfl⟩)
  rw [unifOn_val, Matrix.mul_add,h,add_zero,unifOn_val]

theorem pr_gram_inj_fixed {P : Mat U I} (h : Injective P.mulVec) (G : Mat I J) :
    bp (-num I * num J) * (1 - bp (num I + num J - num U)) ≤
      pr unif (fun Q : Mat U J => Pᵀ * Q = G ∧ Injective Q.mulVec) := by
  let q (Q : Mat U J) := Pᵀ*Q = G
  let f := unifOn q
  have hf := unifOn_law (show ∃ Q : Mat U J, q Q from gramL_surj J h G)
  let T := ker (Pᵀ.mulVecLin)
  have hh := shift_fail hf.sub T (gram_shift _ _)
  have he : num U = num I + dim T := by
    have hj := Pᵀ.mulVecLin.finrank_range_add_finrank_ker
    change rk (Pᵀ.mulVecLin)+dim T = dim (Vec U) at hj
    have h' : Surjective Pᵀ.mulVecLin := transpose_surj_iff.mpr h
    rw [rk_surj.mp h',dim_vec,dim_vec] at hj
    exact_mod_cast hj.symm
  have hi (p : Mat U J → Prop) : pr f (fun x => ¬p x) = 1-pr f p := by
    rw [pr_not,hf.total]
  change bp _ * (1-_) ≤ pr unif (fun x => q x ∧ Injective x.mulVec)
  rw [pr_of_on unif_subLaw.nz q, on_unif, show pr unif q = _ from pr_gram_fixed h G]
  apply mul_le_mul_of_nonneg_left _ (bp_pos _).le
  change pr f _ ≤ _ at hh
  rw [hi (fun x => Injective x.mulVec)] at hh
  rw [show num I+num J-num U = num J - dim T by rw [he]; ring]
  linarith only [hh]

/-- Uniform lower and upper estimates including the full Gram normalization. -/
theorem gram_norm (G : Mat I J) (hsize : num I + num J ≤ num U) :
    let v := (pairW unif unif : Wgt (Mat U I × Mat U J))
    let p := bp (- num I * num J)
    pr v (gramGood G) ≤ p ∧
      p * (1-bp (num I-num U)) * (1-bp (num I+num J-num U)) ≤
      pr v (gramGood G) := by
  let f (P : Mat U I) := pr unif (fun Q : Mat U J => gramGood G (P,Q))
  let a := bp (-num I*num J)
  let b := bp (num I+num J-num U)
  dsimp only
  rw [pr,pairW_avg]
  change avg unif f ≤ a ∧ _ ≤ avg unif f
  have h (P : Mat U I) :
      f P ≤ a ∧ a*(1-b) * ind (Injective P.mulVec) ≤ f P := by
    by_cases hp : Injective P.mulVec
    · have e : f P = pr unif (fun Q : Mat U J => Pᵀ * Q = G ∧ Injective Q.mulVec) := by
        simp [f,gramGood,hp]
      rw [e,ind_one hp,mul_one]
      exact ⟨(pr_mono unif_subLaw.nz fun _ => And.left).trans_eq (pr_gram_fixed hp G),
        pr_gram_inj_fixed hp _⟩
    · have e : f P = 0 := by simp [f,gramGood,hp]
      rw [e,ind_zero hp,mul_zero]
      exact ⟨(bp_pos _).le,le_rfl⟩
  refine ⟨unif_law.avg_le (fun i => (h i).1),?_⟩
  apply le_trans _ (avg_mono unif_subLaw.nz fun i => (h i).2)
  rw [avg_mul']
  have hi := @unif_fail I U _ _ _ _
  rw [pr_not,unif_law.total] at hi
  have ha : 0 ≤ a*(1-b) := by
    refine mul_nonneg (bp_pos _).le (sub_nonneg.mpr ?_)
    simpa [b] using bp_le (show num I+num J-num U ≤ 0 by linarith)
  have hh : 1 - bp (num I-num U) ≤ pr unif (fun M : Mat U I => Injective M.mulVec) := by
    linarith only [hi]
  exact (by
    change a * (1 - bp _) * (1-b) ≤ a * (1-b) * pr _ _
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left hh ha)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

theorem raw_nonneg (m : Mixer p n) (X : Orient p n N) : 0 ≤ raw m N X :=
  prodW_nonneg (fun _ _ => (unifOn_sub _).nz _) _

theorem bp_sum {A : Type*} (s : Finset A) (f : A → ℝ) :
    bp (∑ i ∈ s, f i) = ∏ i ∈ s, bp (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi => rw [Finset.sum_insert ha, Finset.prod_insert ha,bp_add,hi]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SumRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sum Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]

theorem draws_law {w : Wgt A} (h : IsLaw w) :
    IsLaw (draws I w) := prodW_law (fun _ => h)

theorem fresh_avg (w : Wgt A) (hw : IsLaw w) (J : Finset I) (f : Wgt (I→A)) :
    avg (draws I w) f =
    avg (draws I w) (fun x => avg (draws I w) (fun y => f (refresh J x y))) := by
  classical
  let P := draws I w
  have hP : IsLaw P := draws_law hw
  let E := fun x : (I→A)×(I→A) => (refresh J x.1 x.2, refresh J x.2 x.1)
  have hE x : E (E x)=x := by
    apply Prod.ext
    · funext i; change refresh _ _ _ _=_; by_cases h : i∈J <;> simp [refresh,E,h]
    · funext i; change refresh _ _ _ _=_; by_cases h : i∈J <;> simp [refresh,E,h]
  let e : (I→A)×(I→A) ≃ _ := ⟨E,E,hE,hE⟩
  have he x : pairW P P (E x)=pairW P P x := by
    unfold pairW P draws prodW
    rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [E,refresh]
    split <;> ring
  have ht := avg_bij e (pairW P P) (fun x => f x.1)
  change avg (fun x => pairW P P (E x)) (fun x => f (E x).1)=_ at ht
  simp_rw [he] at ht
  rw [pairW_avg,pairW_avg] at ht
  simp_rw [hP.avg_const] at ht
  exact ht.symm

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Channel Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators

variable {A B : Type} [Fintype A] [Fintype B]

theorem gram_norm_quarter {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L] (G : Mat I J)
    (h : num I + num J-num L ≤ -1) :
    bp (-num I * num J)/4 ≤ pr unif (gramGood (U:=L) G) := by
  have hn := (gram_norm G (by linarith : num I+num J≤num L)).2
  rw [pair_unif]
  refine le_trans ?_ hn
  have he {x : ℝ} (hx : x ≤ -1) : (1/2 : ℝ)≤ 1-bp x := by
    have ht := bp_le hx
    rw [bp_neg,bp_one] at ht
    linarith only [ht]
  let d := bp (-num I*num J)
  change d/4 ≤ d* _ * _
  have hk : 0 < d := bp_pos _
  have h1 := he (x:= num I-num L) (by
    have hg : 0≤num J := Nat.cast_nonneg _
    linarith)
  calc d/4 = d*(1/2)*(1/2) := by ring
       _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1 hk.le) (he h) (by norm_num)
         (mul_nonneg hk.le (le_trans (by norm_num) h1))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AtomFlavors
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Atom Flavors -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Finset Function
open scoped BigOperators
variable {g r n b : ℕ} {p : Shape}

theorem asBlock_inj {g : ℕ} : Injective (@asBlock g) := by
  rintro (⟨i,j⟩|⟨⟩) (⟨k,l⟩|⟨⟩) e <;> simp_all [asBlock,Block.O,Block.S]

theorem spins_law (p : Shape) (n : ℕ) : IsLaw (spins p n) := draws_law unif_law

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseAlternativeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Alternative Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}
variable {A : Type} [Fintype A]

theorem on_law {w : Wgt A} (hw : ∀ x,0 ≤ w x) {P : A→Prop} (hp : 0<pr w P) :
    IsLaw (onW w P) := normW_law (subW_nonneg hw _) hp
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterSummaryMass
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tester Summary Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Function
open scoped BigOperators
variable {p : Shape} {r n : ℕ} {A I : Type} [Fintype A] [Fintype I]
variable [DecidableEq I]

theorem draws_unif :
    unif (α:=I → A)=draws I (unif : Wgt A) := by
  classical funext i
            simp [draws,prodW,unif_apply]

set_option maxHeartbeats 600000 in
theorem tested_fraction (r n : ℕ) (hr : 1 ≤ r) (hn : 2*r≤n) (q : F) :
    1/4 ≤ pr unif (fun x : Vec (Fin n) => tested r x=q) := by
  classical
  let w := draws (Fin n) (unif (α:=F))
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let Z : Finset (Fin n) := {a,b}
  have hh : pr unif (fun x : Vec (Fin n) => tested r x=q) =
      avg w (fun x => pr w (fun y => tested r (refresh Z x y)=q)) := by
    unfold pr; rw [draws_unif]
    exact fresh_avg _ unif_law _ _
  rw [hh]
  refine (draws_law unif_law).le_avg (fun v => ?_)
  let i0 : Fin r := ⟨0,hr⟩
  let S : Finset (Fin r) := Finset.univ.erase i0
  let h (y : Vec (Fin n)) (i : Fin r) := zget y (2*i.val)*zget y (2*i.val+1)
  let t := ∑ i∈S,h v i
  have hg (y) (ha : y a=1) (hb : y b=q-t) :
      tested r (refresh Z v y) = q := by
    have hu (i : Fin r) (hh : i∈ S) : h (refresh Z v y) i=h v i := by
      have hi := (mem_erase.mp hh).1
      have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have heq (j : ℕ) (h : 1<j) : zget (refresh Z v y) j=zget v j := by
        by_cases hj : j<n
        · let x : Fin n := ⟨j,hj⟩
          have hr : x∉Z := by simp [x,Z,a,b]; omega
          simp only [zget,dite_eq_left hj,refresh,show (⟨j,hj⟩ : Fin n) ∉ Z from hr,ite_false, if_false]
        simp [zget,hj]
      unfold h
      rw [heq (2*i.val) (by omega),heq _ (by omega)]
    change ∑ i,h _ i=q
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    change h _ i0 + ∑ i∈S, _=_
    rw [show (∑ i∈S,h (refresh Z v y) i)=t from sum_congr rfl hu]
    have h0 := a.isLt
    have h1 := b.isLt
    change 0<n at h0; change 1<n at h1
    have hx : h (refresh Z v y) i0=y a*y b := by
      simp only [h,i0,zget,Nat.mul_zero,Nat.zero_add,dite_eq_left h0,dite_eq_left h1,refresh]
      simp [a,b,Z]
    rw [hx,ha,hb,one_mul,sub_add_cancel]
  let f (i : Bool) := if i then a else b
  let P (i : Bool) (y : F) := y=if i then 1 else q-t
  have he : Injective f := by intro i j; cases i <;> cases j <;> simp [f,a,b]
  have hi : pr w (fun x => ∀ i,P i (x (f i)))=1/4 := by
    change pr (prodW _) _ = _
    rw [prodW_pr_inj he (fun _ => unif_law) P]
    simp only [Fintype.prod_bool,P,pr_point',unif_apply,F]
    norm_num [ZMod.card]
  rw [←hi]
  exact pr_mono (draws_law unif_law).nz (fun y h => hg _ (h true) (h false))

theorem scan_fraction (l : Tag p.g) (f : Flavor p.g) (x : Digest p.g)
    (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (hx : x.feasible l f) :
    scanPrice p ≤ pr (spins p n) (fun y => scan p l f y=x) := by
  classical
  let P (i : ProbeIdx p.g) (v : Vec (Fin n)) :=
    (if f.keeps l (asBlock i) then tested p.r v else 0)=x i
  have h (i) : 1/4 ≤ pr unif (P i) := by
    by_cases h : f.keeps l (asBlock i)
    · simpa only [P,h,ite_true, if_true] using tested_fraction _ _ hr hn (x i)
    simp [P,h,hx _ h,unif_law.total] <;> norm_num
  have hi y : scan p l f y=x ↔ ∀ i,P i (y (asBlock i)) := funext_iff
  change _ ≤ pr (draws _ _) _
  simp_rw [hi]
  rw [draws,prodW_pr_inj asBlock_inj (fun _ => unif_law) P]
  refine le_trans ?_ (Finset.prod_le_prod (fun i _ => ?_) fun i _ => h i)
  · simp [scanPrice]
  norm_num

theorem dial_fraction (p : Shape) (n : ℕ) (l) (f : Flavor p.g) (x : F)
    (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (hx : canDial p l f x) :
    scanPrice p ≤ pr (spins p n) (fun y => dialed p l f y=x) := by
  obtain ⟨v,hv,h⟩ := hx
  exact (scan_fraction l f v hr hn hv).trans
    (pr_mono (spins_law p n).nz fun i hi => (congrArg Digest.sumBit hi).trans h)

theorem scanPrice_pos (p : Shape) : 0 < scanPrice p := by unfold scanPrice; positivity

theorem dial_law (p : Shape) (n : ℕ) (l) (f : Flavor p.g) (x : F)
    (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (hx : canDial p l f x) :
    IsLaw (scopedBit p n l f x) := on_law (spins_law p n).nz
      ((scanPrice_pos p).trans_le (dial_fraction p n _ _ _ hr hn hx))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AmbientBatchSlots
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient Batch Slots -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Function
open scoped BigOperators
variable {I J G A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {p : Shape} {n N : ℕ}

omit [Fintype B] in
theorem mapW_equiv_val (e : A≃B) (w : Wgt A) (y : B) :
    mapW w e y=w (e.symm y) := by
  classical
  have h : (fun x => e x=y)=(fun x => x=e.symm y) := by
    funext x; apply propext
    exact ⟨fun h => by rw [← h,Equiv.symm_apply_apply],fun h => by rw [h,Equiv.apply_symm_apply]⟩
  unfold mapW; rw [h]; simp

theorem unif_equiv (e : A≃B) : mapW unif e = unif := by
  funext x; rw [mapW_equiv_val, unif_apply, unif_apply, Fintype.card_congr e]

variable [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {f : Route I G}

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
theorem part_scores (x : Rack I N) (A : GeoM f) :
    gramPart A x↔ ∀ i, ∀ a b : Port f i,scoreR x a.val b.val=A i a b := by
  constructor
  · intro h i a b; exact congr_fun (congr_fun (h i) a) b
  intro h i; exact Matrix.ext (fun a b => h i a b)

omit [Fintype G] [DecidableEq I] in
theorem both_test (A : GeoM f) (x : Rack I N) :
    bothPart A x↔ gramPart A x ∧injPart f x := by simp [gramPart,injPart,bothPart,gramGood,forall_and]

private theorem pi_unif {I : Type} [Fintype I] [DecidableEq I]
    {A : I→Type} [∀ i,Fintype (A i)] :
    unif (α:=(∀ i,A i)) = prodW (fun i => unif (α:=A i)) := by
  classical
  funext x
  simp [unif_apply,prodW,Fintype.card_pi]

omit [DecidableEq I] in
theorem netFact_pos : 0<netFact f := mul_pos (pow_pos (by norm_num) _) (bp_pos _)

theorem net_norm (A : GeoM f) (N : ℕ)
    (h : ∀ i,2*num (Port f i)-N≤ -1) :
    (netFact f)⁻¹ ≤ pr unif (bothPart (N:=N) A) ∧
      pr unif (bothPart (N:=N) A) ≤ bp (-netSize f) := by
  classical
  let p := fun i => gramGood (U:=Fin N) (A i)
  have hnum (t : ℕ) : num (Fin t)=(t:ℝ) := by simp [num]
  have ht i : num (Port f i) + num (Port f i)-num (Fin N)≤ -1 := by rw [←two_mul,hnum]; exact h _
  have he : pr unif (bothPart (N:=N) A) = ∏ i,pr unif (p i) := by
    unfold bothPart
    rw [←mapW_pr unif (rackEquiv f N) (fun x => ∀ i,p i (x i)), unif_equiv]
    conv_lhs => rw [pi_unif]
    exact prodW_pr ..
  rw [he]; constructor
  · let h' (i : G) := bp (-(num (Port f i))*num (Port f i))/4
    have hh i : h' i ≤ pr unif (p i) := gram_norm_quarter _ (ht _)
    refine le_trans ?_ (Finset.prod_le_prod (fun i _ => div_nonneg (bp_pos _).le
      (by norm_num)) fun i _ => hh i)
    unfold netFact
    rw [_root_.mul_inv_rev,Finset.prod_div_distrib,←bp_sum,netSize,Finset.prod_const,
      ← bp_neg, ← Finset.sum_neg_distrib]
    simp_rw [neg_mul, Finset.card_univ,div_eq_mul_inv]
    exact le_rfl
  · have h i :=
      (gram_norm (U:=Fin N) (A i) (show _≤ _ by linarith only [ht i])).1
    unfold netSize
    rw [← Finset.sum_neg_distrib, bp_sum]
    apply Finset.prod_le_prod (fun i _ => pr_nonneg unif_law.nz)
    intro i _
    rw [pair_unif,←neg_mul]
    exact h i

theorem wave_norm (A : GeoM f) (N : ℕ)
    (h : ∀ i,2*num (Port f i)-N≤ -1) :
    (netFact f)⁻¹ ≤ pr unif (gramPart (N:=N) A) :=
  ((net_norm A N h).1).trans
    (pr_mono unif_law.nz (fun _ hx => ((both_test ..).mp hx).1))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GroupedQueryIndependence
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouped Query Independence -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N : ℕ}
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

theorem spin_scan_free (p : Shape) (n) (l) (f : Flavor p.g) :
    ∀ (x : Knobs p.g n) y,scan p l f (x+Pi.single Block.Z y)=scan p l f x := by
  classical
  intro x y; funext i
  have hx : asBlock i ≠ Block.Z := by rcases i with (⟨i,j⟩|_) <;> simp [asBlock]
  simp only [scan,Pi.add_apply,Pi.single_eq_of_ne hx,add_zero]

theorem fresh_Z (p : Shape) (n) (P : Knobs p.g n→ Prop)
    (h : frozenZ p P) (hh : IsLaw (onW (spins p n) P)) :
    mapW (onW (spins p n) P) (freePart p) = unif := by
  classical
  let w := onW (spins p n) P
  have he (c : Vec (Fin n)) (x : Knobs p.g n) :
      w (x+Pi.single Block.Z c)=w x := by
    have hv (x : Knobs p.g n) : spins p n x=unif x := congr_fun
      (Eq.symm draws_unif) x
    simp only [w,onW_val,hv,unif_apply,← h x c]
  have hv (x y : Vec (Fin n)) :
      mapW w (freePart p) x=mapW w (freePart p) y := by
    let t : Knobs p.g n := Pi.single Block.Z (x-y)
    let e : Knobs p.g n ≃ Knobs p.g n :=
      { toFun := (·+t)
        invFun := (·-t)
        left_inv a := add_sub_cancel_right ..
        right_inv a := sub_add_cancel .. }
    have hh (b : Knobs p.g n) :
        freePart p (e b)=x ↔ freePart p b=y := by
      unfold freePart
      change b Block.Z+t Block.Z=x ↔ _
      rw [show t Block.Z=x-y from Pi.single_eq_same _ _]; constructor <;> intro h
      · apply add_right_cancel (b:=x-y)
        rw [h,add_sub_cancel]
      rw [h,add_sub_cancel]
    unfold mapW pr
    rw [← avg_bij e]
    have hf i : w (e i)=w i := he _ i
    simp_rw [hf,hh]
  rw [←unifOn_true (A:=Vec (Fin n))]
  exact uniform_support (mapW_law hh _) (by intro x h; exact (h trivial).elim) (fun i j _ _ => hv i j)

theorem scopedZ_bit (p : Shape) (n l f x) (h : IsLaw (scopedBit p n l f x)) :
    mapW (scopedBit p n l f x) (freePart p)=unif :=
  fresh_Z p n _ (fun v y => by
    simp only [dialed,spin_scan_free]) h

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConcentrationScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration Scales -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Finset Filter Real Function
open scoped BigOperators Topology
variable {X : Type*}

variable {p : Shape} {M n N : ℕ}
variable {I J K G A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
variable [Fintype A] [Fintype B]
variable {g : Route J G}

omit [Fintype G] [DecidableEq J] in
theorem port_limit (g : Route J G) (i : G) :
    num (Port g i) ≤ num J := by
  exact_mod_cast Fintype.card_subtype_le _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalFlags
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Flags -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]
variable {w : Wgt X}

theorem stained_law (f : X→Y) (hw : IsLaw w) (i : Y) : IsLaw (stained w f i) := by
  unfold stained; split
  next h => exact on_law hw.nz (lt_of_le_of_ne ((mapW_law hw f).nz _) (Ne.symm h))
  next => exact hw

variable {μ : Wgt A}

theorem semi_total (μ : Wgt A) (v : A → Wgt Y) :
    tot (semi μ v)=avg μ (fun i=>tot (v i)) := by
  simpa only [avg_const,mul_one] using semi_avg μ v (fun i=>1)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RestrictedComparisonLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricted Comparison Laws -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

variable [Nonempty B]

omit [Nonempty B] in
theorem density_hung (P : B→Prop) (w : Wgt B) (hw : carried w P) :
    ∀ i, unifOn P i * density (unifOn P) w i=w i := by
  classical
  intro i
  by_cases h : w i =0
  · simp only [density,h,zero_div,mul_zero]
  have ht : P i := not_not.mp fun hi => h (hw i hi)
  have hn := unifOn_law (p:=P) ⟨i,ht⟩
  have he : unifOn P i≠0 := by
    rw [unifOn_val,ind_one ht]
    have hh : nbr P ≠0 := by
      have he := weight_le_tot (fun j => ind_nonneg (P j)) i
      rw [ind_one ht] at he
      exact (lt_of_lt_of_le zero_lt_one he).ne'
    exact div_ne_zero one_ne_zero hh
  unfold density; field_simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Projection -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

theorem ode_nonneg {μ : Wgt A} (hμ : ∀ i,0 ≤ μ i) (f : Wgt A) : 0≤ ode μ f :=
  avg_nonneg hμ (fun _ => mul_self_nonneg _)
theorem ode_upper {μ : Wgt A} (hμ : SubLaw μ) (f : Wgt A) (B : ℝ)
    (hf : ∀ i,|f i|≤B) : ode μ f ≤ B^2 := by
  apply hμ.avg_le (sq_nonneg _)
  intro i
  exact (le_of_eq (Eq.symm (pow_two _))).trans
    ((le_of_eq (sq_abs (f i)).symm).trans (pow_le_pow_left₀ (abs_nonneg _) (hf i) 2))

theorem dip_sym (μ f g : Wgt A) : dip μ f g=dip μ g f := by unfold dip; simp only [mul_comm]
theorem dip_sub (μ f g h : Wgt A) :
    dip μ (fun i=> f i-g i) h=dip μ f h-dip μ g h := by
  unfold dip; simp only [sub_mul,avg_sub]

omit [Fintype B] in
theorem cashbook_bound (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : A→B) (g : Wgt A)
    (b : ℝ) (hb : 0≤b) (h : ∀ i,|g i|≤b) (i) : |cashbook μ f g i| ≤ b := by
  have he : cashbook μ f g i=avg (onW μ (fun x=>f x=i)) g := by
    unfold cashbook onW
    rw [avg_norm,subW_tot]
    unfold mapW pr avg subW; congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hw : SubLaw (onW μ (fun x=>f x=i)) := normW_subLaw (subW_nonneg hμ _)
  rw [he]
  exact (abs_avg_le hw.nz).trans (hw.avg_le hb h)

theorem cash_orth (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : A→B) (g : Wgt A) (h : Wgt B) :
    dip μ (banner μ f g) (h ∘ f)=dip μ g (h ∘ f) := by
  classical
  let w := fun x=> μ x*g x
  have he : pour μ f (mapW w f) = fun i => μ i*banner μ f g i := rfl
  have hz : lsupp w μ := fun _ hi => left_ne_zero_of_mul hi
  have ht := map_pour μ f _ (hz.map hμ f)
  rw [he] at ht
  have hi := congrArg (fun w' => avg w' h) ht
  simp_rw [mapW_avg] at hi
  simpa only [w,dip,avg,mul_assoc,Function.comp_apply] using hi

theorem ode_step (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : Wgt A)
    (p : A→B) (q : B→C) :
    ode μ (banner μ p f)=ode μ (banner μ (q∘p) f)+
      ode μ (fun i => banner μ p f i - banner μ (q∘p) f i) := by
  classical
  let g := banner μ p f; let h := banner μ (q ∘ p) f
  have hh : ode μ h=dip μ g h :=
    (cash_orth μ hμ (q∘p) f (cashbook μ (q∘p) f)).trans
      (cash_orth μ hμ p f (cashbook μ (q∘p) f ∘ q)).symm
  have hi i : (g i - h i)*(g i-h i)=g i*g i - 2*(g i*h i)+h i*h i := by ring
  change ode μ g=ode μ h+dip μ (fun i => g i-h i) (fun i=>g i-h i)
  unfold dip
  simp_rw [hi,avg_add,avg_sub,avg_mul']
  change ode μ g=ode μ h+(ode μ g-2*dip μ g h + ode μ h)
  linarith only [hh]

theorem archive_gain {μ : Wgt A} (hw : SubLaw μ) (f : Wgt A)
    (p : A→B) (q : B→ C)
    (h : Wgt B) (hh : ∀ i:A,|h (p i)| ≤1) :
    (dip μ (fun i => f i - banner μ (q∘p) f i) (h ∘ p))^2 ≤
      ode μ (banner μ p f)-ode μ (banner μ (q∘p) f) := by
  let u := banner μ p f; let v := banner μ (q∘p) f
  let w i := u i-v i
  rw [ode_step μ hw.nz f p q]
  have he : dip μ (fun i=> f i - banner μ (q∘p) f i) (h∘p)=dip μ w (h∘p) := by
    unfold w
    rw [dip_sub,dip_sub,cash_orth μ hw.nz p f h]
  have ht : ode μ (h∘p) ≤ 1 := (ode_upper hw (h∘p) 1 hh).trans_eq (by ring)
  have hq : dip μ w (h∘p)^2≤ode μ w*ode μ (h∘p) := by
    simpa only [ode,dip,pow_two] using avg_CS hw.nz w (h∘p)
  rw [he]
  apply le_trans hq
  refine (mul_le_mul_of_nonneg_left ht (ode_nonneg hw.nz w)).trans_eq ?_
  unfold w u v
  ring
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RectangleRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

theorem swab_abs (x) : |swab x|=1 := by cases x <;> simp [swab]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResidualRegularity
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residual Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter Real
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

private theorem twistabs (b : ℝ) : b*swab (twistSign b)=|b| := by
  classical by_cases h : 0≤b <;> simp [swab,twistSign,h,abs_of_nonneg,abs_of_neg,lt_of_not_ge]

set_option maxHeartbeats 600000 in
theorem tilt_test (w : Wgt A) (u : Wgt I) (hu : ∀ i,0 ≤ u i) (f : I → Wgt A) (h : Wgt A)
    (hh : ∀ x,|h x|≤1) :
    ∃ p : A→Bool, avg u (fun i=>|dip w (f i) h|) ≤ avg u (fun i => |dip w (f i) (swab∘ p)|) := by
  classical
  let q (i:I) := swab (twistSign (dip w (f i) h))
  let V (x) := avg u (fun i=> f i x * q i)
  have hx (h : Wgt A) :
      avg u (fun i=> dip w (f i) h * q i)=dip w V h := by
    unfold V dip; simp_rw [← avg_mul]
    rw [avg_avg]
    refine avg_congr fun i _=> avg_congr fun j _=>by ring
  let p (x:A) := twistSign (w x*V x)
  refine ⟨p,?_⟩
  have hV : dip w V h ≤ dip w V (swab ∘ p) := by
    unfold dip avg; refine Finset.sum_le_sum fun i _=> ?_
    dsimp only [Function.comp_apply,p]
    set t := w i*V i with ht
    rw [←mul_assoc,←mul_assoc,←ht,twistabs]
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hh _) (abs_nonneg _)).trans_eq (mul_one _)
  have h0 i :
      |dip w (f i) h|=dip w (f i) h*q i := (twistabs ..).symm
  simp_rw [h0,hx]; rw [←hx (swab ∘ p)] at hV
  apply le_trans hV
  apply avg_mono hu
  intro i
  rw [← show |dip w (f i) (swab∘p)* q i|=|dip w (f i) (swab∘p)| by rw [abs_mul,swab_abs,mul_one]]
  exact le_abs_self _

theorem mean_sq (u : Wgt I) (hu : IsLaw u) (f : Wgt I) :
    avg u f ^ 2 ≤ avg u (fun i=> f i^2) := by
  simpa only [mul_one,one_pow, hu.avg_const] using avg_CS hu.nz f (fun _=>1)

set_option maxHeartbeats 800000 in
theorem erosive (M ε : ℝ) (hM : 0≤M) (hε : 0<ε) :
    ∃ k:ℕ,∀ (A I : Type) [Fintype A] [Fintype I]
      (u : Wgt I) (w : Wgt A) (f : I→Wgt A),
      IsLaw u → IsLaw w → (∀ i j,|f i j|≤ M) →
      ∃ l:ℕ,l≤ k∧∃ p:A→Fin l,wanes u w f p ε := by
  classical
  obtain ⟨n,hn⟩:=exists_nat_gt (M^2/ε^2)
  rw [div_lt_iff₀ (by positivity)] at hn
  refine ⟨2^n,fun A I _ _ u w f hu hw hf =>?_⟩
  by_contra! h
  have hh (i:ℕ) (hi : i≤ n) :
      ∃ p : A→ Fin (2^i),i*ε^2 ≤ hits u w f p := by
    induction i with
    | zero => exact ⟨fun _=>0,(by simp only [Nat.cast_zero,zero_mul,hits]; exact avg_nonneg hu.nz (fun i=>ode_nonneg hw.nz _))⟩
    | succ i ih =>
      obtain ⟨p,hp⟩:=ih (by omega)
      obtain h := h (2^i) (Nat.pow_le_pow_right (by decide) (by omega)) p
      let T (i:I) (x:A) := f i x-banner w p (f i) x
      unfold wanes at h; push Not at h; obtain ⟨a,ha,h⟩:=h
      obtain ⟨s,hs⟩:=tilt_test w u hu.nz T a ha
      let q:= swab∘s
      let e : (Fin (2^i) × Bool)≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ])
      let b x := e (p x,s x)
      let P := Prod.fst ∘ e.symm; let Q:= swab ∘ Prod.snd ∘ e.symm
      have hP : P∘b=p := by funext i; simp [P,b]
      have hQ : Q∘b=q := by funext i; simp [q,Q,b]
      have he x : ode w (banner w p (f x)) + dip w (T x) q ^2 ≤ ode w (banner w b (f x)) := by
        have he := archive_gain hw.sub (f x) b P Q (fun i=>by unfold Q; simp [swab_abs])
        rw [hP,hQ] at he
        change ode _ _+dip w (fun i=> f x i-banner w p (f x) i) q ^2≤_
        linarith only [he]
      let V i:= |dip w (T i) q|
      have hz : ε ≤ avg u V := h.le.trans hs
      have hb := (pow_le_pow_left₀ hε.le hz 2).trans (mean_sq u hu V)
      have hh := avg_mono hu.nz he
      rw [avg_add] at hh
      change hits u w f p + _ ≤ hits u w f b at hh
      unfold V at hb; simp_rw [sq_abs] at hb
      refine ⟨b,?_⟩
      push_cast; linarith only [hp,hb,hh]
  obtain ⟨p,hp⟩ := hh n le_rfl
  have h (i:I) : ∀ x:A,|banner w p (f i) x|≤ M :=
    fun i'=> cashbook_bound w hw.nz p _ _ hM (hf i) (p i')
  exact not_lt_of_ge (hp.trans (hu.avg_le (fun i=> ode_upper hw.sub _ M (h i)))) hn
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionError
attribute [-instance] _root_.OAI.HadwigerCounterexample.idxDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Error -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Module Filter Function
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

omit [Fintype B] in
theorem rebate_sym (u f g : Wgt A) (p : A→B) :
    rebate u f g p=rebate u g f p := by unfold rebate; rw [dip_sym u f,dip_sym u (banner u p f)]
theorem rebate_calc (u f g : Wgt A) (p : A→B) (hu : ∀ i,0≤u i) :
    rebate u f g p=dip u (fun i=>f i-banner u p f i) g := by
  unfold rebate
  rw [dip_sub,dip_sym u (banner u p f) (banner u p g)]
  exact congrArg (dip u f g - ·) ((show dip u (banner u p g) (banner u p f)=dip u g (banner u p f) from
    cash_orth u hu p g (cashbook u p f)).trans (dip_sym ..))

theorem rebate_cost (u f g f' : Wgt A) (p : A→B) (hu : ∀ i,0≤u i)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ i,|g i| ≤ r) :
    |rebate u f g p-rebate u f' g p| ≤ lcost u f f' * (2*r) := by
  rw [rebate_sym u f g,rebate_sym u f' g,rebate_calc u g f p hu,rebate_calc u g f' p hu]
  unfold dip; rw [←avg_sub]
  apply (abs_avg_le hu).trans
  have hz i : |g i-banner u p g i|≤2*r :=
    ((abs_sub ..).trans (add_le_add (h i) (cashbook_bound u hu p g r hr h (p i)))).trans_eq
      (two_mul _).symm
  unfold lcost; rw [←avg_mul]; apply avg_mono hu
  intro i
  dsimp only
  rw [←mul_sub,abs_mul,mul_comm]
  exact mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)

theorem syrup_range (r x : ℝ) (h : 0 ≤ r) :
    0≤ syrup r x∧ syrup r x ≤ r := ⟨le_min (le_max_right ..) h,min_le_right ..⟩
omit [Fintype A] in
theorem mcut_range (r : ℝ) (u f : Wgt A) (h : 0 ≤ r) (x) :
    0 ≤ mcut r u f x∧mcut r u f x ≤ r := syrup_range _ _ h

private theorem jelly (r x y : ℝ) :
    |syrup r x-syrup r y| ≤ |x-y| := by
  wlog hh : x≤y generalizing x y
  · rw [abs_sub_comm,abs_sub_comm x y]; exact this y x (le_of_not_ge hh)
  have hr : syrup r x ≤ syrup r y := min_le_min (max_le_max hh le_rfl) le_rfl
  rw [abs_of_nonpos (sub_nonpos.mpr hh),abs_of_nonpos (sub_nonpos.mpr hr)]
  unfold syrup
  rcases le_total x 0 with h|h <;> rcases le_total y 0 with he|he
  · rw [max_eq_right h,max_eq_right he]; linarith only [hh]
  · rw [max_eq_right h,max_eq_left he]; rcases le_total 0 r with h'|h'
    · rw [min_eq_left h']
      linarith only [h, min_le_left y r]
    rw [min_eq_right h',min_eq_right (by linarith)]
    linarith
  · obtain rfl : x=y := by linarith
    simp
  rw [max_eq_left h,max_eq_left he]
  rcases le_total x r with h'|h'
  · rw [min_eq_left h']; linarith only [min_le_left y r]
  rw [min_eq_right h',min_eq_right (by linarith)]; linarith

theorem mcut_cost (r : ℝ) (u f g : Wgt A) (hu : ∀ i,0≤u i) :
    lcost u (mcut r u f) (mcut r u g)≤ varOne f g := by
  unfold lcost avg varOne; refine sum_le_sum fun i _ => ?_
  apply (mul_le_mul_of_nonneg_left (jelly r (density u f i) (density u g i)) (hu i)).trans
  by_cases hx : u i=0
  · rw [hx,zero_mul]; exact abs_nonneg _
  unfold density; rw [←sub_div,abs_div,abs_of_nonneg (hu _)]
  exact le_of_eq (by field_simp)

set_option maxHeartbeats 500000 in
theorem roster_clip (r : ℝ) (u : Wgt A) (hu : IsLaw u) (hr : 0 ≤ r) (Q : Wgt A→ Prop)
    (k : ℕ) (ε : ℝ) (h : roster Q k ε) :
    ∃ f : Fin (k+1)→Wgt A,(∀ i x,|f i x| ≤ r) ∧
      ∀ w,Q w→∃ i,lcost u (mcut r u w) (f i)≤ ε := by
  classical
  obtain ⟨t,ht,v,hv⟩:=h
  let W:= fun i : Fin (k+1)=> if h:i.val<t then mcut r u (v (⟨i.val,h⟩)) else (fun i:A => 0)
  refine ⟨W,fun i x=>?_,fun i hi=>?_⟩
  · unfold W; split
    next h =>
      obtain ⟨he,hy⟩:=mcut_range r u (v (⟨i.val,h⟩)) hr x
      rwa [abs_of_nonneg he]
    simpa only [abs_zero] using hr
  obtain ⟨j,hj⟩:=hv i hi
  exact ⟨⟨j.val,Nat.lt_succ_of_lt (j.isLt.trans_le ht)⟩,by
    unfold W; rw [dite_eq_left j.isLt]; exact (mcut_cost r u i _ hu.nz).trans hj⟩
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CommonPartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common Partitions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Module Matrix Filter Function
open scoped BigOperators
variable {A B I J X : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype X]
variable (u : Wgt A) (w : Wgt I) (v : Wgt J)

set_option maxHeartbeats 800000 in
theorem rollup [Nonempty B] (hw : IsLaw w) (hv : IsLaw v) (hu : IsLaw u)
    (f : I×B→Wgt A) (g : J×B→Wgt A) (h k : I×J→ B) (R : ℝ) (hr : 0<R)
    (hg : ∀ i x, |g i x|≤R)
    (p : A→X) (ε : ℝ) (hx : wanes (pairW w unif) u f p ε) :
    avg (pairW w v) (fun i=> |rebate u (f (i.1,h i)) (g (i.2,k i)) p|) ≤
      num B ^ 2 * (R*ε) := by
  classical
  let H (i : I × B) (j : J × B) := |rebate u (f i) (g j) p|
  let T := num B
  have ht : 0<T := by unfold T num; positivity
  have he j :
      avg (pairW w (unif : Wgt B)) (fun i=> H i j)≤ R*ε := by
    let g' (i:A) := g j i/R
    have hh (i) : |g' i|≤1 := by
      unfold g'; rw [abs_div,abs_of_pos hr,div_le_one hr]; exact hg _ _
    have hz (i) :
        H i j=R* |dip u (fun x=> f i x-banner u p (f i) x) g'| := by
      unfold H; rw [rebate_calc _ _ _ _ hu.nz]
      unfold g' dip; simp_rw [←mul_div_assoc,avg_div]
      rw [abs_div,abs_of_pos hr]; field_simp
    simp_rw [hz,avg_mul']; exact mul_le_mul_of_nonneg_left (hx g' hh) hr.le
  have hh i j :
      H (i,h (i,j)) (j,k (i,j))≤ ∑ b : B,∑ c : B,H (i,b) (j,c) :=
    (Finset.single_le_sum (f:=fun x=> H (i,h (i,j)) (j,x)) (fun _ _ => abs_nonneg _) (mem_univ (k (i,j)))).trans
      (Finset.single_le_sum (f:=fun x => ∑ c:B,H (i,x) (j,c)) (fun _ _=> Finset.sum_nonneg (fun _ _=>abs_nonneg _)) (mem_univ (h (i,j))))
  have hi j c :
      avg w (fun i=>∑ b : B,H (i,b) (j,c))≤ T*(R*ε) := by
    have hg : ∀ i : I,(∑ b:B,H (i,b) (j,c))=T*avg unif (fun b=> H (i,b) (j,c)) := by
      intro i; simp only [avg,unif_apply,← Finset.mul_sum]
      change _ = T*(T⁻¹ * _)
      rw [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
    simp_rw [hg,avg_mul']
    refine mul_le_mul_of_nonneg_left ?_ ht.le; rw [← pairW_avg w unif (fun p : I×B=>H p (j,c))]
    exact he _
  change avg (pairW w v) _ ≤ T^2*(R*ε)
  rw [pairW_avg,avg_avg]
  refine hv.avg_le fun j=> ?_
  have hz i : ∑ b:B,∑ c:B,H (i,b) (j,c)=∑ c:B,∑ b:B,H (i,b) (j,c) :=
    Finset.sum_comm
  apply (avg_mono hw.nz (fun i => (hh i j).trans_eq (hz i))).trans
  rw [avg_sum]
  exact (Finset.sum_le_sum fun i _=>hi j i).trans_eq (by
    simp only [sum_const,nsmul_eq_mul,Finset.card_univ,T,num] <;> ring)

set_option maxHeartbeats 1200000 in
theorem global_net (R ε : ℝ) (hr : 0<R) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ r : ℕ,∃ l : ℕ,∀ (I J A : Type) [Fintype I] [Fintype J] [Fintype A]
      (w : Wgt I) (v : Wgt J) (u : Wgt A), IsLaw w→IsLaw v →IsLaw u →
      ∀ (P : I→Wgt A→Prop) (Q : J→Wgt A→Prop), (∀ i,roster (P i) r δ) →
        (∀ i,roster (Q i) r δ) →
        ∃ k : ℕ,k ≤ l∧ ∃ p:A→Fin k,
          ∀ f g:I × J→Wgt A,(∀ i,P i.1 (f i)) → (∀ i,Q i.2 (g i)) →
          avg (pairW w v) (fun i => |rebate u (mcut R u (f i)) (mcut R u (g i)) p|)≤ ε := by
  classical
  let δ := ε/(8*R)
  have hd : 0<δ := by positivity
  refine ⟨δ,hd,fun r=>?_⟩
  let B:=Fin (r+1); let t:=num B
  have ht : 0<t := by unfold t num; positivity
  let c:=ε/(2*(t^2)*R)
  have hc : 0 < c := by positivity
  obtain ⟨l,hl⟩:= erosive R c hr.le hc
  refine ⟨l,fun I J A _ _ _ w v u hw hv hu P Q hp hq=>?_⟩
  choose s hs h1 using fun i=> roster_clip R u hu hr.le (P i) r δ (hp i)
  choose y hy h2 using fun i=> roster_clip R u hu hr.le (Q i) r δ (hq i)
  let F : I×B→Wgt A := uncurry s
  let G : J×B→Wgt A := uncurry y
  obtain ⟨m,hm,p,hP⟩:= hl A (I×B) (pairW w unif) u F (pairW_law hw unif_law) hu (fun i j=> hs _ _ _)
  refine ⟨m,hm,p,fun f g hf hg=>?_⟩
  let f' (i : I×J):= mcut R u (f i)
  let g' (i : I×J):= mcut R u (g i)
  choose a hA using fun i:I×J => h1 i.1 (f i) (hf i)
  choose b hB using fun i:I×J => h2 i.2 (g i) (hg i)
  let H (i:I×J) := |rebate u (F (i.1,a i)) (G (i.2,b i)) p|
  let D:=pairW w v; have hD:= pairW_law hw hv
  have he := rollup u w v hw hv hu F G a b R hr (fun i j=> hy _ _ _) p c hP
  have hb : 0≤2*R := by linarith only [hr]
  have hi (i:I×J) : |rebate u (f' i) (g' i) p|≤ H i+(δ*(4*R)) := by
    let A' := F (i.1,a i); let B' := G (i.2,b i)
    have h1 (j) : |g' i j|≤R := by
      rw [abs_of_nonneg ((mcut_range _ _ _ hr.le j).1)]
      exact (mcut_range _ _ _ hr.le j).2
    have h3 : |rebate u (f' i) (g' i) p - rebate u A' (g' i) p|≤ δ*(2*R) := by
      exact (rebate_cost u _ _ A' p hu.nz R hr.le h1).trans (mul_le_mul_of_nonneg_right (hA i) hb)
    have h4 : |rebate u A' (g' i) p - rebate u A' B' p|≤δ*(2*R) := by
      rw [rebate_sym u A',rebate_sym u A']
      exact (rebate_cost u _ _ B' p hu.nz R hr.le (fun i=>hs _ _ _)).trans
        (mul_le_mul_of_nonneg_right (hB i) hb)
    let U:=rebate u A' B' p
    let X:=rebate u (f' i) (g' i) p
    have hz:= (abs_sub_le X (rebate u A' (g' i) p) U).trans (add_le_add h3 h4)
    calc |X| = |(X-U)+U| := by rw [sub_add_cancel]
         _ ≤ _ := ((abs_add_le _ _).trans (add_le_add_left hz _)).trans_eq (by
           change _+ |U| = |U|+δ*(4*R)
           ring)
  refine (avg_mono hD.nz hi).trans ?_
  rw [avg_add,hD.avg_const]
  exact (add_le_add_left he _).trans_eq (by
    change t^2*(R*c)+δ*(4*R)=_
    unfold δ c; field_simp <;> ring)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectedSurrogates
attribute [-instance] _root_.OAI.HadwigerCounterexample.idxDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projected Surrogates -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

omit [Fintype B] in
theorem book_order (w : Wgt A) (p : A→ B) (hw : IsLaw w)
    (f g : Wgt A) (h : ∀ i, f i≤ g i) (x) :
    cashbook w p f x ≤ cashbook w p g x := by
  apply div_le_div_of_nonneg_right _ (map_nz hw.nz p x)
  exact pr_mono_left (fun i=> mul_le_mul_of_nonneg_left (h i) (hw.nz i)) _
omit [Fintype B] in
theorem book_nonneg (w : Wgt A) (p : A→B) (hw : IsLaw w) (f : Wgt A) (hf : ∀ i,0 ≤ f i) (x) :
    0 ≤ cashbook w p f x := div_nonneg (pr_nonneg (fun i=>mul_nonneg (hw.nz i) (hf i))) (map_nz hw.nz p x)
omit [Fintype B] in
theorem garden (w f : Wgt A) (p : A→B) (hw : IsLaw w) (hf : bower f) :
    bower (banner w p f) := by
  refine ⟨fun i=> book_nonneg w p hw f hf.1 _,fun i=>?_⟩
  exact (le_abs_self _).trans (cashbook_bound w hw.nz p f 1 zero_le_one (fun i=>by
    rw [abs_of_nonneg (hf.1 _)]; exact hf.2 _) _)
theorem projected_min (w : Wgt A) (p : A→B) (hw : IsLaw w) (f g : Wgt A)
    (hf : bower f) (hg : bower g) :
    dip w f g ^2 ≤ dip w (banner w p f) (banner w p g) := by
  let h i := f i*g i
  let u := banner w p h
  have hi : dip w f g=avg w u := by
    have hh := cash_orth w hw.nz p h (fun _=>1)
    simpa only [dip,u,Function.comp_apply,mul_one,h] using hh.symm
  have hh (i) :
      u i^2 ≤ banner w p f i*banner w p g i := by
    have h0 : bower u := garden w h p hw ⟨fun i=>mul_nonneg (hf.1 _) (hg.1 _),fun i=>
      (mul_le_mul (hf.2 _) (hg.2 _) (hg.1 _) zero_le_one).trans_eq (one_mul _)⟩
    have h1 (i) : h i≤ f i :=
      ((mul_le_mul_of_nonneg_left (hg.2 _) (hf.1 _)).trans_eq (mul_one _))
    have h2 (i) : h i≤g i :=
      ((mul_le_mul_of_nonneg_right (hf.2 _) (hg.1 _)).trans_eq (one_mul _))
    rw [pow_two]; exact mul_le_mul (book_order w p hw h f h1 _) (book_order w p hw h g h2 _)
      (h0.1 i) ((garden w f p hw hf).1 i)
  rw [hi]; exact (mean_sq w hw u).trans (avg_mono hw.nz hh)

omit [Fintype A] in
theorem dresso (u f : Wgt A) (h : lsupp f u) : f = fun i => u i*density u f i := by
  funext i; unfold density
  by_cases he : f i=0
  · simp only [he,zero_div,mul_zero]
  have hh := h i he
  field_simp

theorem density_error (w : Wgt A) (p : A→B) (hw : IsLaw w) (f g : Wgt A) (hz : lsupp g w) :
    lcost w (banner w p f) (banner w p (density w g))≤
      varOne (mapW (fun i=>w i*f i) p) (mapW g p) := by
  classical
  let x i := |cashbook w p f i-cashbook w p (density w g) i|
  have he :
      lcost w (banner w p f) (banner w p (density w g))=avg (mapW w p) x :=
    (mapW_avg w p x).symm
  rw [he]; unfold avg varOne
  refine sum_le_sum fun i _=>?_
  let V:=mapW w p i; let A:= mapW (fun i=> w i*f i) p i; let B:= mapW g p i
  have hh : x i= |A-B|/V := by
    unfold x cashbook A B V
    rw [← dresso w g hz,←sub_div,abs_div,abs_of_nonneg (map_nz hw.nz ..)]
  rw [hh]
  by_cases h : V=0
  · change V*_ ≤_
    rw [h,zero_mul]; exact abs_nonneg _
  change V*(|A-B|/V)≤ |A-B|
  exact le_of_eq (by field_simp)

theorem density_trim (u f : Wgt A) (h : ∀ i,0≤f i) (hu : IsLaw u)
    (R : ℝ) (hR : 0≤R) :
    (∀ i,mcut R u f i ≤ density u f i) ∧ lcost u (density u f) (mcut R u f)≤trayLoss R u f := by
  have h1 (i:A) : 0≤density u f i := div_nonneg (h _) (hu.nz _)
  have h2 (i) :
      mcut R u f i=min (density u f i) R := congrArg (fun x=>min x R) (max_eq_left (h1 _))
  have h3 (i) := show mcut R u f i ≤ density u f i from le_trans (le_of_eq (h2 i)) (min_le_left ..)
  refine ⟨h3,Finset.sum_le_sum (fun i _=>?_)⟩
  change u i*|density u f i-mcut R u f i| ≤ f i* ind _
  rw [abs_of_nonneg (sub_nonneg.mpr (h3 _)),h2]
  by_cases hz : R≤density u f i
  · rw [ind_one hz,mul_one,min_eq_right hz]
    have hm := hu.nz i
    by_cases hg : u i=0
    · rw [hg,zero_mul]; exact h _
    apply le_trans (mul_le_mul_of_nonneg_left (sub_le_self _ hR) hm) (le_of_eq ?_)
    unfold density; field_simp
  rw [ind_zero hz,mul_zero,min_eq_left (le_of_not_ge hz),sub_self,mul_zero]

private theorem cost_gap (u : Wgt A) (p : A→B) (f g : Wgt A) (h : ∀ i,g i≤ f i)
    (hu : IsLaw u) :
    lcost u (banner u p f) (banner u p g)=lcost u f g := by
  have hf (i : A) : |banner u p f i-banner u p g i|=banner u p f i-banner u p g i :=
    abs_of_nonneg (sub_nonneg.mpr (book_order u p hu g f h _))
  have hg (f : Wgt A) : avg u f = avg u (banner u p f) := by
    have hh := cash_orth u hu.nz p f (fun _=>1); simpa only [dip,Function.comp_apply,mul_one] using hh.symm
  unfold lcost; simp_rw [hf, abs_of_nonneg (sub_nonneg.mpr (h _)), avg_sub]
  rw [← hg f, ← hg g]

set_option maxHeartbeats 800000 in
theorem density_mend (u : Wgt A) (hu : IsLaw u) (p : A→B) (R : ℝ) (hR : 0≤ R)
    (f g x y : Wgt A) (hf : bower f) (hg : bower g) (hx : SubLaw x)
    (hy : SubLaw y) (h1 : lsupp x u) (h2 : lsupp y u) :
    let V f g := varOne (mapW (fun i=>u i*f i) p) (mapW g p)+trayLoss R u g
    dip u f g ^ 2 ≤ overlap u x y + |rebate u (mcut R u x) (mcut R u y) p|+
      (V f x+V g y) := by
  classical
  intro V
  let F:=banner u p f; let G:=banner u p g
  let X:=banner u p (mcut R u x); let Y:=banner u p (mcut R u y)
  have he (f x : Wgt A) (hx : SubLaw x) (h : lsupp x u) :
      lcost u (banner u p f) (banner u p (mcut R u x)) ≤ V f x := by
    let F := banner u p f; let X:=banner u p (density u x); let Z:=banner u p (mcut R u x)
    obtain ⟨h1,h2⟩:=density_trim u x hx.nz hu R hR
    have hh : lcost u F Z≤lcost u F X+lcost u X Z := by
      unfold lcost; rw [← avg_add]; exact avg_mono hu.nz fun i=>abs_sub_le _ _ _
    exact hh.trans (add_le_add (density_error u p hu f x h)
      (le_trans (cost_gap u p (density u x) _ h1 hu).le h2))
  have hh i : F i*G i ≤ X i*Y i + (|F i-X i|+|G i-Y i|) := by
    have hA := (garden u f p hu hf).2 i; have hB := (garden u g p hu hg).2 i
    have ht : 0≤X i := book_nonneg u p hu _ (fun i=> (mcut_range _ _ _ hR i).1) _
    have hq : 0≤Y i := book_nonneg u p hu _ (fun i=> (mcut_range _ _ _ hR i).1) _
    have hp := (garden u f p hu hf).1 i
    by_cases h : X i≤F i
    · by_cases h' : Y i≤ G i
      · nlinarith only [ht,hq,h,h',hA,hB, le_abs_self (F i-X i),le_abs_self (G i-Y i)]
      have hz := le_of_not_ge h'
      nlinarith only [h,hB,hz,le_abs_self (F i-X i),abs_nonneg (G i-Y i),ht]
    have hz := le_of_not_ge h
    by_cases h' : Y i≤ G i
    · nlinarith only [hA,hq,h',hz,abs_nonneg (F i-X i),le_abs_self (G i-Y i)]
    have hi := le_of_not_ge h'
    nlinarith only [hz,hq,hi,hp,abs_nonneg (F i-X i), abs_nonneg (G i-Y i)]
  let A:= mcut R u x; let B:=mcut R u y
  have hz : dip u A B≤overlap u x y :=
    avg_mono hu.nz (fun i=>mul_le_mul ((density_trim u x hx.nz hu _ hR).1 _)
      ((density_trim u y hy.nz hu _ hR).1 _) ((mcut_range R u y hR i).1)
      (div_nonneg (hx.nz _) (hu.nz _)))
  have h :
      dip u X Y≤overlap u x y + |rebate u A B p| := by
    have h : dip u X Y-dip u A B ≤|dip u A B-dip u X Y| := by rw [abs_sub_comm]; exact le_abs_self _
    change _≤ _+ |dip u A B - dip u X Y|; linarith only [h,hz]
  have hp := avg_mono hu.nz hh
  rw [avg_add,avg_add] at hp
  exact (le_trans (projected_min u p hu f g hf hg) hp).trans
    (add_le_add h (add_le_add (he f x hx h1) (he g y hy h2)))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyReferenceLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Reference Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

theorem channelTag_inj (p : Shape) (l : Tag p.g) : Injective (channelTag p l) :=
  Subtype.val_injective.comp (outlet p l).injective

theorem tray_wave (p : Shape) (t : Tagging p I) (q : I→ F) (x : Keys (p:=p) t N) :
    ownPart (p:=p) t q x↔ gramPart (trayMap p t q) (tray p t N x) := by
  classical
  unfold ownPart
  rw [part_scores,part_scores]
  let y := scatter t N x
  let z := tray p t N x
  let A := trayMap p t q
  let g := handles p t
  have hi i j : scoreR z i j=scoreR y (g i) (g j) := rfl
  constructor
  · exact fun h i a b => h i (trayJoin p t i a) (trayJoin p t i b)
  intro hh i a b
  obtain ⟨a,rfl⟩ := (trayJoin p t i).surjective a
  obtain ⟨b,rfl⟩ := (trayJoin p t i).surjective b
  exact hh i a b

omit [Fintype I] in
theorem mug_wave (p : Shape) (t : Tagging p I) (q : I→F) (i : I)
    (x : AtomKey (p:=p) (t i) N) :
    ownOne p (t i) (q i) x ↔ gramPart (laneM (trayMap p t q) i) (mug p (t i) N x) := by
  classical
  rw [part_scores]
  let g := trayPort p t; let b := street g i
  let X := mug p (t i) N x
  let A := laneM (trayMap p t q) i
  have hi {j} (a : Port b j) :
      scoreR X a.val a.val=dotProduct (x (outlet p (t i) a.val) true)
        (x (outlet p (t i) a.val) false) := rfl
  have hj {j} (a : Port b j) : A j a a=q i := by
    let s := trayJoin p t j (condLane (trayPort p t) i j a)
    exact Matrix.diagonal_apply_eq (fun i : Port (ownPort (p:=p) t) j => q i.val.1) s
  have hh (a c : Toast p) (h : b a=b c) : a=c := channelTag_inj p (t i) h
  constructor
  · intro he j a c
    have h : c=a := Subtype.ext (hh _ _ (c.property.trans a.property.symm)); subst c
    exact (hi a).trans ((he _).trans (hj a).symm)
  intro h j
  obtain ⟨a,rfl⟩ := (outlet p (t i)).surjective j
  let e := b a
  let c : Port b e := ⟨a,rfl⟩
  exact (hi c).symm.trans ((h e c c).trans (hj c))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ReferenceProductTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reference Product Tests -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Function Finset Filter
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

theorem priceNu (t : Tagging p I) (q : I→F) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    (netFact (trayPort p t))⁻¹ ≤ pr unif (ownPart (p:=p) t q (N:=N)) := by
  classical
  let g := trayPort p t; let A := trayMap p t q
  have hpL i := show 2*num (Port g i)-(N:ℝ)≤ -1 by linarith only [hN,port_limit g i]
  have he : pr unif (gramPart A (N:=N))=pr unif (ownPart (p:=p) t q (N:=N)) := by
    rw [← unif_equiv (tray p t N),mapW_pr]
    unfold A
    congr 1; ext i
    exact (tray_wave ..).symm
  rw [←he]
  exact wave_norm A N hpL
theorem nuLaw (t : Tagging p I) (q : I → F) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    IsLaw (lawNu p N t q) := by
  classical
  rw [lawNu,←on_unif]
  exact on_law unif_law.nz ((inv_pos_of_pos netFact_pos).trans_le (priceNu t q hN))

theorem priceOmega (t : Tagging p I) (q : I→F) (i : I) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    (netFact (street (trayPort p t) i))⁻¹ ≤ pr unif (ownOne p (t i) (q i) (N:=N)) := by
  classical
  let g := street (trayPort p t) i; let A := laneM (trayMap p t q) i
  have hh j : num (Port g j)≤num (I×Toast p) := by
    apply le_trans (port_limit g j)
    exact_mod_cast Fintype.card_le_of_injective (fun j : Toast p => (i,j)) (fun i j h =>
      congrArg Prod.snd h)
  have hpL j := show 2*num (Port g j)-(N:ℝ)≤ -1 by linarith only [hN,hh j]
  have he : pr unif (gramPart A (N:=N))=pr unif (ownOne p (t i) (q i) (N:=N)) := by
    rw [← unif_equiv (mug p (t i) N),mapW_pr]
    unfold A
    congr 1; ext x
    exact (mug_wave ..).symm
  rw [←he]
  exact wave_norm A N hpL

theorem omegaLaw (p : Shape) (l : Tag p.g) (q : F) (hN : 2*num (Toast p)-(N:ℝ)≤ -1) :
    IsLaw (lawOmega p N l q) := by
  classical
  let t := fun (_ : Unit) => l
  have hh : 2*num (Unit×Toast p)-(N:ℝ)≤ -1 := by simpa [num] using hN
  rw [lawOmega,←on_unif]
  exact on_law unif_law.nz ((inv_pos_of_pos netFact_pos).trans_le
    (priceOmega t (fun _ : Unit => q) () hh))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairIndexedTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair Indexed Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function
open scoped BigOperators
variable {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
variable {s : Stage I J} {B : J→ Type}
variable [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

omit [DecidableEq J] in
theorem wavelength_pos (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    0<wavelength B := prod_pos (fun i _ => by simp only [unif_apply] <;> positivity)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMixingBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Mixing Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

omit [DecidableEq I] in
theorem kappa_pos : 0<v.kappa := wavelength_pos _

end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Parameters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators Topology
open Filter
variable {p : Shape} {n N : ℕ}

theorem bp_nat_vanish {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => bp (-c*n)) atTop (𝓝 0) :=
  (bp_tendsto_zero hc).comp tendsto_natCast_atTop_atTop

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WeightedPartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted Partitions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A : Type} [Fintype A]

variable {w : Wgt A} {T : Tiles A}

omit [Fintype A] in
theorem ind_tiles (ht : apart T) (x : A) :
    ind (inTiles T x)= ∑ i∈T,ind (x∈i) := by
  classical
  by_cases hh : inTiles T x
  · rw [ind_one hh]
    obtain ⟨i,hi,hx⟩ := hh
    rw [Finset.sum_eq_single i]
    · rw [ind_one hx]
    · intro j hj h; exact ind_zero (fun hc => h (ht x j hj i hi hc hx))
    simp [hi]
  rw [ind_zero hh]
  exact (Finset.sum_eq_zero (fun i hi => ind_zero (fun h => hh ⟨i,hi,h⟩))).symm

theorem tiles_inter (w : Wgt A) (T : Tiles A) (P : A→Prop) (hT : apart T) :
    pr w (fun x => inTiles T x∧P x)= ∑ i∈T,pr w (fun x => x∈i ∧ P x) := by
  unfold pr
  simp_rw [ind_and, ind_tiles hT,Finset.sum_mul,avg_sum]

theorem mass_apart (h : apart T) : allMass w T=∑ i∈T,partMass w i := by
  simpa only [and_true,allMass,partMass] using tiles_inter w T (fun x => True) h

theorem rebuild {T : Tiles A} (hw : ∀ x, 0 ≤ w x)
    (hT : apart T) (he : ∀ i ∈ T, 0 < partMass w i)
    (h : 0 < allMass w T) :
    IsLaw (portionW w T) ∧ allW w T = mixW (portionW w T) (fun i => partW w i.val) := by
  classical
  constructor
  · refine ⟨fun i => div_nonneg (pr_nonneg hw) h.le,?_⟩
    unfold tot portionW
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul,Finset.sum_coe_sort,← mass_apart hT,mul_inv_cancel₀ h.ne']
  funext x
  rw [allW,onW_val,ind_tiles hT]
  unfold mixW avg
  have hg (i:T) :
      portionW w T i* partW w i.val x = w x*ind (x∈i.val)/allMass w T := by
    have hx : pr w (fun x => x∈i.val) ≠ 0 := (he _ i.property).ne'
    unfold portionW partW partMass
    rw [onW_val]; field_simp
  change w x * _ / allMass w T=_
  simp_rw [hg]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul,← Finset.mul_sum, Finset.sum_coe_sort T (fun y => ind (x∈y))]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UltrafilterRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ultrafilter Rates -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset
open scoped Topology

variable {A B : Type} {l : Filter A} {U : Ultrafilter A} {x y z v a : A → ℝ}

namespace warm

theorem positive (h : warm l z x) : ∀ᶠ i in l,0<x i :=
  (h 1 zero_lt_one).mono (fun _ hi => (bp_pos _).trans_le hi)

theorem inv_cap (h : warm l z x) : ExpO l z (fun i=> (x i)⁻¹) := by
  intro c hc
  filter_upwards [h c hc] with i hi
  rw [abs_of_nonneg (inv_nonneg.mpr ((bp_pos _).le.trans hi))]
  exact le_trans (inv_anti₀ (bp_pos _) hi) (le_of_eq (by rw [neg_mul,bp_neg,inv_inv]))

end warm

theorem trend_sizes (l : Filter ℕ) (h : l ≤ atTop) {M : ℕ} (hM : 1≤ M) :
    Tendsto (fun n=> M*n) l atTop ∧ Tendsto (fun n=> ((M*n:ℕ):ℝ)) l atTop := by
  have hh : Tendsto (fun n : ℕ=> M*n) atTop atTop := tendsto_atTop.mpr (fun a =>
    (eventually_ge_atTop a).mono (fun k hk=> le_trans hk (by nlinarith)))
  exact ⟨hh.mono_left h, tendsto_natCast_atTop_atTop.comp (hh.mono_left h)⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafMixtures
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf Mixtures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ}

namespace LeafMixture

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
variable {D E ζ η : ℝ} {K L : ℕ}

theorem sapLaw (h : 0 < s.amount w) (hw : IsLaw w) : IsLaw (s.sap w) := on_law hw.nz h

theorem upper_sap (hw : IsLaw w) (hp : 0 < s.amount w) (x) :
    s.sap w x ≤ (s.amount w)⁻¹*w x :=
  on_mon hw.nz hp le_rfl x
theorem upperSide {N n} {Lr K' : ℝ} {w v : Wgt (X p n N)} {m : Mixer p n} (hp : bySide p w m Lr)
    {Lr' : ℝ} (h : ∀ x,v x≤K'*w x) (hk : 0≤K') (hh : K'*Lr ≤ Lr') :
    bySide p v m Lr' := by
  intro i x
  refine (mapW_cap h _ x).trans ?_
  calc _ ≤ K'*(Lr*raw m N x) := mul_le_mul_of_nonneg_left (hp i _) hk
       _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hh (raw_nonneg m _)

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedOptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Options -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ}

variable {q : Format} {d e : Rates}

namespace Quill
variable {b : Bool} (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)

theorem canDraw {w : Quill p q d b} (h : w.moral t z) (i : Messenger q) :
    canDial p (t i) (w.flav i) (z i) :=
  ⟨_,h.2.2 i,h.2.1 i⟩

end Quill

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedMassIdentities
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Mass Identities -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K M: ℕ} {q : Format} {d e : Rates}

namespace Quill
variable {i:Bool} (w : Quill p q d i)
    (μ : Wgt (UnitType p n N)) (s : Charts p n d)
    (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (m : Mixer p n)
    (P : UnitType p n N→Prop)

theorem sales_core :
    w.sales t z μ P m s=flaggedW μ ((w.pen t).state z n) (w.billboard (N:=N) s t z m)
    ((w.pen t).resultKey) (fun o b=> P o ∧ b) := by
  classical
  funext x; unfold sales Volley.hist
  simp_rw [pr]; rw [avg_avg]
  unfold flaggedW mixW mapW
  apply avg_congr; intro i hi
  simp only [pr,avg,Function.comp_apply,subW,billboard,decide_eq_true_eq]
  refine Finset.sum_congr rfl fun a _=> ?_
  rw [mul_assoc,← ind_and]; rfl

theorem sales_receipt : customer w μ s t z m (w.sales t z μ P m s) :=
  ⟨_,w.sales_core μ s t z m P⟩

theorem sales_part : carried (w.sales t z μ P m s) (ownPart t z) := by
  intro o ho
  unfold sales Volley.hist
  let A:=w.pen t
  have hi (x : Inputs p n (Messenger q)) :
      pr μ (fun i=>(P i ∧ w.deposit t z m i s x)∧(A.draw x).keys t i=o) = 0 := by
    have h i : ¬((P i∧ w.deposit t z m i s x)∧(A.draw x).keys t i=o) := by
      rintro ⟨⟨hp,hg⟩,hk⟩
      apply ho; rw [←hk]; exact hg.2.2
    unfold pr;simp only [ind_zero (h _),avg_const,mul_zero]
  change avg (A.state z n) _=_
  exact (avg_congr (g:=fun _ => 0) (fun x _ => hi x)).trans (by rw [avg_const,mul_zero])

theorem sales_custom : custom w μ s t z m (w.sales t z μ P m s) := by
  let v:= w.sales t z μ P m s
  refine ⟨v,w.sales_receipt μ s t z m P, funext fun i =>?_⟩
  change v i=_
  unfold subW
  by_cases hi : ownPart t z i
  · rw [ind_one hi,mul_one]
  rw [show v i=0 from w.sales_part μ s t z m P i hi,zero_mul]

theorem sales_mean (W : Wgt (Keys (p:=p) t N)) :
    avg (w.sales t z μ P m s) W =
      avg μ (fun o=> ind (P o) * prowl w s t z m o W) := by
  classical
  rw [sales_core, flaggedW]
  refine (mixW_avg μ _ (show Wgt (Keys (p:=p) ((w.pen t).t) N) from W)).trans ?_
  refine avg_congr fun i _ => ?_
  rw [mapW_avg]
  unfold prowl subW
  simp only [avg,Finset.mul_sum,Function.comp_apply,billboard,decide_eq_true_eq,ind_and]
  refine Finset.sum_congr rfl fun _ _=>?_
  ring

end Quill

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AnalyticParameters
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic Parameters -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

namespace PreparationParameters
variable {b : PreparationParameters} {p : Shape} {N M r : ℕ} {l : Filter ℕ} {m : cycleM p}
  {s : rhythms p M} {w : tale p M}

set_option maxHeartbeats 1200000 in
theorem veil.upright (h : veil p M b r l m s w) :
    ∀ᶠ n in l,Align b r p M n (m n) ((s n).sap (w n)) := by
  let z n:= ((M*n:ℕ):ℝ)
  have ht := h.easel.enter.first
  have hM : 1 ≤ (M:ℝ) := by exact_mod_cast ht.hM
  let e : ℝ := 1/(128*M)
  have he : 0< e:=by unfold e; positivity
  have hz := (trend_sizes l h.timeL ht.hM).2
  let D n:=((s n).amount (w n))⁻¹
  filter_upwards [h.moment,h.durableS.mass.inv_cap e he,
    h.durableS.mass.positive,expO_const hz b.L e he, ht.wrap.filter_mono h.timeL,
    (eventually_ge_atTop (2*p.r)).filter_mono h.timeL] with n hn he' ht' hL hG hH
  have hw := hn.1.law
  have h1 (i) := LeafMixture.upper_sap hw ht' i
  have h2 : 0≤D n := (inv_pos_of_pos ht').le
  have hB : D n * b.L ≤ bp (1/32*(n:ℝ)) := by
    have hi : e*z n=(1/128)*(n:ℝ) := by unfold e z; push_cast; field_simp
    calc _ ≤ bp (e*z n)*bp (e*z n) :=
           mul_le_mul ((le_abs_self _).trans he') ((le_abs_self _).trans hL) ht.early.hL
             (bp_pos _).le
         _ ≤ _ := by rw [←bp_add,hi]; apply bp_le; linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hv := LeafMixture.upperSide hn.1.border h1 h2 hB
  refine ⟨hn.2.2.1,hn.2.1,hH,hG.1, LeafMixture.sapLaw ht' hw, hv true,hv false,fun i=>?_⟩
  have hh := hn.1.total i
  apply ((h1 i).trans (mul_le_mul_of_nonneg_left hh h2)).trans
  rw [←mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (raw_nonneg ..) (raw_nonneg ..))
  have hx : e ≤1 := by unfold e; exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  refine (mul_le_mul_of_nonneg_right ((le_abs_self _).trans he') (bp_pos _).le).trans ?_
  rw [←bp_add]
  unfold spJoint; refine bp_le ?_; rw [←add_mul]
  exact mul_le_mul_of_nonneg_right (by linarith only [hx]) (by positivity)
end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateStatusLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Status Laws -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology

variable {A B C H : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype H]
variable {p : Shape} {n N K M r : ℕ}

namespace StatusAnalysis

namespace Appearance
variable (x : Appearance p)
theorem witLaw {x : Appearance p} (h : x.apt) (hq : 1≤p.r) (hn : 2*p.r≤n) :
    IsLaw (x.wit n) := dial_law _ _ _ _ _ hq hn h

variable (Y : Silhouette p N r)

variable {d : ℕ}

theorem reflectedLaw (h : IsLaw (x.wit n)) (i : Nodes)
    (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (a : Fin r) : IsLaw (x.reflected Y i o m v a) :=
  mapW_law (stained_law _ h _) _

end Appearance

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalSignaturePositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Signature Positivity -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r d : ℕ}
namespace StatusAnalysis
open Template

theorem haze_small (w : Wgt (Fin r)) (δ : ℝ) (hδ : 0≤δ) :
    pr w (fun x=> w x < δ) ≤ r*δ := by
  classical
  unfold pr avg
  refine (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>δ) (fun i _=>?_)).trans_eq (by simp)
  dsimp only
  by_cases h:w i<δ
  · rw [ind_one h,mul_one]; exact h.le
  rw [ind_zero h,mul_zero]; exact hδ

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateQueryScores
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Query Scores -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p : Shape} {n N K M r : ℕ}
namespace StatusAnalysis
variable {q:Format} {d : Rates} {b:Bool}
namespace Quill

variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

theorem allure_apt (h : w.moral t z) (i : Messenger q) :
    (w.allure t z i).apt := canDraw t z h i

variable (o : UnitType p n N)

variable (m : Mixer p n)

theorem seraphFloor (s : Charts p n d) (Y:Silhouette p N r) (i:Messenger q)
    (hw : IsLaw (w.policies t z n i)) (x) :
    0≤ seraph w t z o m s Y i x ∧ seraph w t z o m s Y i x≤1 :=
  let h:= Appearance.reflectedLaw (w.allure t z i) Y hw (parcel b i) o m _ (Y _ (z i) x)

  ⟨h.nz _,(weight_le_tot h.nz _).trans h.total.le⟩

theorem kappaTop : (w.pen t).kappa ≤1 := by
  unfold kappa wavelength
  classical
  have hh : IsLaw (prism (w.pen t).Abbey) := prodW_law (fun _ => unif_law)
  exact (weight_le_tot hh.nz _).trans hh.total.le

theorem mirror_floor (s : Charts p n d) (Y:Silhouette p N r)
    (hw : ∀ i,IsLaw (w.policies t z n i))
    (x:Keys (p:=p) t N) :
    0≤ w.mirror t z o m s Y x ∧ w.mirror t z o m s Y x≤1 := by
  let f:= w.seraph t z o m s Y
  let v:= w.pen t
  have hh i:= seraphFloor w t z o m s Y i (hw i) (x i)
  have h0 : 0 ≤ prodW f x:= prodW_nonneg (fun i y=> (seraphFloor w t z o m s Y i (hw i) y).1) _
  have h1 : prodW f x≤1 := (Finset.prod_le_prod (s:=Finset.univ)
    (g:=fun i: Messenger q=> (1:ℝ)) (fun i _=> (hh i).1) (fun i _=> (hh i).2)).trans_eq
    (by simp)
  exact ⟨mul_nonneg v.kappa_pos.le h0,(mul_le_mul (kappaTop w t) h1 h0 zero_le_one).trans_eq
    (one_mul _)⟩

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CommonPartitionRefinement
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common Partition Refinement -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}

theorem refines_next {r s t:ℕ} {Y:Silhouette p N r} {X:Silhouette p N s}
    {Z:Silhouette p N t} (h : refines Y X) (hg : refines X Z) :
    refines Y Z := by
  intro l q
  obtain ⟨f,hf⟩:=h l q; obtain ⟨g,hg⟩:=hg l q
  refine ⟨g∘ f,fun x => ?_⟩; rw [hg,hf]; rfl

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem bundle_refines (f:A→ℕ) (w:(i:A)→ Silhouette p N (f i)) :
    ∀ i,refines (bundleY f w) (w i) := by
  intro i l q
  let e:= Fintype.equivFin ((i:A)→Fin (f i))
  exact ⟨fun x=> e.symm x i,fun x=>(congr_fun (e.symm_apply_apply (fun i=> w i l q x)) i).symm⟩

theorem duo_good {r s} (Y : Silhouette p N r) (X : Silhouette p N s) :
    refines (duoY Y X) Y ∧ refines (duoY Y X) X := by
  let e : Fin r × Fin s ≃ Fin (r*s):=finProdFinEquiv
  constructor
  · intro i j; exact ⟨fun k=>(e.symm k).1,fun x=> (congrArg Prod.fst
      (e.symm_apply_apply (Y i j x,X i j x))).symm⟩
  intro i j; exact ⟨fun k=>(e.symm k).2,fun x=> (congrArg Prod.snd
    (e.symm_apply_apply (Y i j x,X i j x))).symm⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateAggregation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Aggregation -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Filter Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
variable {p : Shape} {n N K M r : ℕ}
variable {q:Format} {d e : Rates} {b:Bool}

namespace Quill
variable (w:Quill p q d b) (t: Tagging p (Messenger q))
  (z : Messenger q→F) (μ:Wgt (UnitType p n N)) (P:UnitType p n N→Prop)
  (m:Mixer p n) (s:Charts p n d) (Y: Silhouette p N r)

theorem bower_case (hw:IsLaw μ) (h:∀ i,IsLaw (w.policies t z n i)) :
    bower (w.showcase t z μ P m s Y) := by
  let f i := w.mirror t z i m s Y
  have he i x := mirror_floor w t z i m s Y h x
  constructor
  · intro i; exact avg_nonneg hw.nz fun j=>mul_nonneg (ind_nonneg _) (he j i).1
  intro i; exact hw.avg_le fun j=>(mul_le_mul (ind_le_one (P j)) (he j i).2 (he j i).1
    zero_le_one).trans_eq (one_mul _)

theorem display_mean (W : Wgt (Keys (p:=p) t N)) :
    avg (w.displayMass t z μ P m s Y) W=avg μ (fun o=>ind (P o)*w.sheen t z o m s Y W) := by
  unfold sheen displayMass showcase
  simp only [avg,mul_assoc]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 900000 in
theorem display_test (H : Keys (p:=p) t N→ Prop)
    (hw:IsLaw μ) (h:∀ i,IsLaw (w.policies t z n i)) (hn:IsLaw (lawNu p N t z))
    (Z : UnitType p n N→Prop)
    {ε : ℝ} (he:0≤ε)
    (hg : ∀ x,P x → |w.prowl s t z m x (fun x=>ind (H x))-w.sheen t z x m s Y
      (fun x=>ind (H x))| > ε → Z x) :
    |pr (w.displayMass t z μ P m s Y) H- pr (w.sales t z μ P m s) H| ≤ ε+2*pr μ Z := by
  classical
  let W := fun x=>ind (H x)
  let f x:=w.prowl s t z m x W; let g x:=w.sheen t z x m s Y W
  have heq x :
      |ind (P x)*g x-ind (P x)*f x|≤ ε+ 2*ind (Z x) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (ind_nonneg _)]
    have hh (x): |ind (Z x)|≤1:=by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
    by_cases hP:P x
    · rw [ind_one hP,one_mul]
      by_cases h0 : Z x
      · have hh (x'): |W x'|≤1 := by unfold W; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
        have h1 : |f x|≤1 := by
          let F:=w.pen t
          have hv : IsLaw (F.state z n):=prodW_law h
          unfold f prowl; refine (abs_avg_le hv.nz).trans (hv.avg_le fun j=>?_)
          rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
          exact (mul_le_mul (ind_le_one _) (hh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
        have h2 : |g x|≤1 := by
          unfold g sheen; refine (abs_avg_le hn.nz).trans (hn.avg_le fun j=>?_)
          have hm:=mirror_floor w t z x m s Y h j
          rw [abs_mul,abs_of_nonneg hm.1]
          exact (mul_le_mul hm.2 (hh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
        rw [ind_one h0]
        have hi := abs_sub (g x) (f x)
        linarith only [hi,h1,h2,he]
      rw [ind_zero h0,abs_sub_comm,mul_zero,add_zero]
      exact le_of_not_gt (fun h=> h0 (hg x hP h))
    rw [ind_zero hP,zero_mul]
    exact add_nonneg he (mul_nonneg (by norm_num) (ind_nonneg _))
  unfold pr; rw [sales_mean,display_mean,← avg_sub]
  exact (abs_avg_le hw.nz).trans ((avg_mono hw.nz heq).trans_eq (by rw [avg_add,
    avg_mul',hw.avg_const]))

end Quill

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafSurrogateExperiments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf Surrogate Experiments -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Function Finset Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K s M : ℕ}
  {w : LeafMixture p n N} {q : Format} {d e : Rates}

variable {I : Type} [Fintype I]
theorem skylineMean (w : Wgt I) (f g c : Wgt I) (ε : ℝ) (he:0≤ε) (hw:IsLaw w)
    (h : avg w c≤ (ε/2)^2) (hc : ∀ i,g i^2 ≤ c i)
    (hg:∀ i,f i - g i ≤ ε/2) : avg w f ≤ ε := by
  have h1 := (mean_sq _ hw g).trans ((avg_mono hw.nz hc).trans h)
  have h2 : avg w f-avg w g≤ ε/2 := by rw [←avg_sub]; exact hw.avg_le hg
  nlinarith only [he,h1,h2]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UniformLeafComparisons
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Leaf Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Function Matrix Finset
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p:Shape} {M n N s0 K r:ℕ} {q:Format} {d e:Rates} {b:Bool} {b':PreparationParameters}

namespace Quill
variable (w:Quill p q d b)
  (t:Tagging p (Messenger q)) (z: Messenger q→F)

set_option maxHeartbeats 900000 in
theorem ownCertificate (M:ℕ) (h:AnalyticParameters p M b' s0) (hw : w.moral t z)
    (ε η:ℝ) (he:0<ε) (hη:0<η) :
    ∃ (r:ℕ) (δ R:ℝ),0<δ∧0<R∧ ∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (s:Charts p n d) (μ:Wgt (UnitType p n N)),
      2*num (Full p n)<(N:ℝ) → IsLaw μ →
        (∀ i,μ i ≤ bp (b'.leafNew*N)*PreparationParameters.usual p m N i) →
        w.accounting t z m s μ r δ R ε η := by
  classical
  let v:= w.pen t
  have hc : 0≤b'.leafNew := by unfold PreparationParameters.leafNew PreparationParameters.leafOld; positivity
  have ht:= h.enter.first
  obtain ⟨r,δ,R,hd,hR,hV⟩:= v.controls M ht.hM Bool b'.leafNew η ε hc hη he
  refine ⟨r,δ,R,hd,hR,?_⟩
  filter_upwards [hV,eventually_ge_atTop (2*p.r)] with n hn ht' N m s μ hN hμ hv
  let u:=w.policies t z n
  have hu i:IsLaw (u i) := Appearance.witLaw (w.allure_apt t z hw i) ht.hR ht'
  have ha := hn m hN μ hμ hv u hu (fun i=>scopedZ_bit p n _ _ _ (hu _))
    (w.billboard (N:=N) s t z m)
  let P:=ownPart (p:=p) (N:=N) t z
  obtain ⟨hh,_,_,hQ⟩:=ha
  have hv : roster (w.custom μ s t z m) r ε∧ smallSet (w.custom μ s t z m) (lawNu p N t z) δ η ∧
      rosterTail (w.custom μ s t z m) (lawNu p N t z) R η := hQ P
  refine ⟨fun i hi=>?_,hv⟩
  obtain ⟨x,hp,rfl⟩:= hi
  refine ⟨subLaw_sub (hh x hp) P,fun i hi=>?_⟩
  have ht:= density_hung P (subW x P) (subW_carried x P) i
  exact left_ne_zero_of_mul (ht.symm ▸ hi)

theorem pennyLarge (R η ε : ℝ) (r:ℕ) (m:Mixer p n) (s:Charts p n d)
    (μ:Wgt (UnitType p n N)) (h:w.penny t z m s μ R η ε r) {R' : ℝ} {r':ℕ}
    (h1:R≤R') (h2:r ≤ r') : w.penny t z m s μ R' η ε r' := by
  refine ⟨h.sales,?_,fun f hf=>?_⟩
  · obtain ⟨q,hq,hh⟩:= h.roll; exact ⟨q,hq.trans h2,hh⟩
  exact le_trans (pr_mono (h.sales f hf).1.nz (fun i hi=>h1.trans hi)) (h.tailS f hf)

theorem pennywise (M:ℕ) (h:AnalyticParameters p M b' s0) (hw:w.moral t z) (η:ℝ) (hη:0<η) :
    ∃ R:ℝ,0<R∧∀ ε:ℝ,0<ε→ ∃ r:ℕ,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m:Mixer p n) (s:Charts p n d) (μ:Wgt (UnitType p n N)),
      2*num (Full p n)<(N:ℝ) → IsLaw μ →
        (∀ i,μ i ≤ bp (b'.leafNew*N)*PreparationParameters.usual p m N i) →
        w.penny t z m s μ R η ε r := by
  obtain ⟨r,a,R,ha,hR,hV⟩:= w.ownCertificate t z M h hw 1 η zero_lt_one hη
  refine ⟨R,hR,fun ε he=>?_⟩
  obtain ⟨r',d',R',hd,hR',he'⟩:= w.ownCertificate t z M h hw ε η he hη
  refine ⟨r',?_⟩
  filter_upwards [hV,he'] with n hn ht N m s μ hN hμ hl
  obtain ⟨hx,_,_,he⟩:= hn m s μ hN hμ hl
  exact ⟨hx,(ht m s μ hN hμ hl).2.1, he⟩
end Quill

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
omit [Fintype B] [Fintype C] in
theorem rebate_thick (w : Wgt A) (f : A→B) (g : B→C) (h : Injective g) (p q: Wgt A) :
    rebate w p q (g∘f)=rebate w p q f := by
  have ht (a : Wgt A) : banner w (g∘f) a = banner w f a := by
    funext x; unfold banner cashbook mapW
    simp_rw [Function.comp_apply,h.eq_iff]
  unfold rebate; rw [ht,ht]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyProjectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Projection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap
open scoped BigOperators Topology
variable {p:Shape} {n N M K r s0 : ℕ}
namespace StatusAnalysis
open Station

open PreparationParameters
variable {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {s : rhythms p M} {w:tale p M}

set_option maxHeartbeats 1800000 in
theorem projectCut {q:Format} {d e:Rates} (x:Typus p q d e)
    (h:x.permission)
    (k:Fin (2^deckMax p b.pins))
    (hv:veil p M b s0 l m s w) (t:Stations p M b.pins s)
    (ε:ℝ) (he:0<ε) :
    ∃ (r:ℕ) (η:ℝ), 0<η∧∀ᶠ n in l, let N:=M*n;
      ∃ P:Keys (p:=p) x.t N→Fin r,
      dueEnough (t n) x (m n) (w n) k ε η P := by
  classical
  let H := (ε/2)^2/8
  have hH : 0<H:=by unfold H; positivity
  have hE:=hv.easel
  have ht:=hE.enter.first
  obtain ⟨Ra,ha,hA⟩:= x.qA.pennywise x.t x.z M hE h.2.1 H hH
  obtain ⟨Rb,hβ,hB⟩:= x.qB.pennywise x.t x.z M hE h.2.2.1 H hH
  let R:= max Ra Rb
  have hr :0<R:=lt_max_of_lt_left ha
  obtain ⟨δ,hd,hG⟩:=global_net R H hr hH
  obtain ⟨a,hJ⟩:=hA δ hd; obtain ⟨b1,hY⟩:=hB δ hd
  obtain ⟨r,hk⟩:=hG (max a b1)
  obtain ⟨u,hu,hd'⟩:=veil.score_cost hv t
  refine ⟨r,H,hH,?_⟩
  have hl:= hv.timeL
  have hz:=(trend_sizes l hl ht.hM).2
  let L:= 2*netFact (trayPort p x.t)
  have hg : ∀ᶠ n in l, L*bp (-((M*n:ℕ):ℝ)/2)≤ ε/2 := by
    have hx:=(((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul L)
    have heq : ∀ᶠ n in l,L*bp (-(1/2:ℝ)*((M*n:ℕ):ℝ))≤ ε/2 :=
      hx.eventually (eventually_le_nhds (by rw [mul_zero]; linarith only [he]))
    filter_upwards [heq] with n hn; rw [show -((M*n:ℕ):ℝ)/2= -(1/2:ℝ)*((M*n:ℕ):ℝ) from by ring]; exact hn
  filter_upwards [hv.upright,hv.moment, hv.durableS.mass.positive,hv.durableS.shape,hJ.filter_mono hl,
    hY.filter_mono hl,hd',(hu.lim hz).eventually (eventually_le_nhds hH),hg,
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
    with n hn ht' hm he' hx hy hh h' hR hN N
  let v:= t n
  let w':=w n; let s':= s n
  let I := s'.T
  let F (i : ↑I):= partW w' i.val
  let A (i : ↑I) := x.qA.custom (F i) (v.cAxes i d) x.t x.z (m n)
  let B (i : ↑I) := x.qB.custom (F i) (v.cAxes i e) x.t x.z (m n)
  let u:=portionW w' I; let ν:=lawNu p N x.t x.z
  have ht0 : IsLaw w':=ht'.1.law
  have hF i (hi : i∈I): IsLaw (partW w' i):= on_law ht0.nz
    (he'.1.leaf i hi).pos
  have hX i (hi : i∈I) := (he'.1.leaf _ hi).density
  have hA' (i:↑I) :
      x.qA.penny x.t x.z (m n) (v.cAxes i d) (F i) R H δ (max a b1) :=
    Quill.pennyLarge x.qA x.t x.z _ _ _ _ _ _ _ (hx (m n) _ (F i) hn.cols (hF _ i.property)
      (hX _ i.property)) (le_max_left ..) (le_max_left ..)
  have hB' (i:↑I) : x.qB.penny x.t x.z (m n) (v.cAxes i e) (F i) R H δ (max a b1) :=
    Quill.pennyLarge x.qB x.t x.z _ _ _ _ _ _ _ (hy (m n) _ (F i) hn.cols (hF _ i.property)
      (hX _ i.property)) (le_max_right ..) (le_max_right ..)
  have hu :IsLaw u := (rebuild ht0.nz he'.1.part (fun i hi=>(he'.1.leaf _ hi).pos) hm).1
  have hhN : 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1 := by
    change _≤(N:ℝ) at hN; linarith only [hN]
  have hν : IsLaw ν := nuLaw x.t x.z hhN
  obtain ⟨j,hj,P,hP⟩:= hk (↑I) (↑I) (Keys (p:=p) x.t N) u u ν hu hu hν A B
    (fun i=>(hA' i).roll) (fun i=>(hB' i).roll)
  let Q := (Fin.castLE hj) ∘ P
  refine ⟨Q,fun z Y hs=>?_⟩
  let W := pairW u u
  have hW:=pairW_law hu hu
  let L := fun x':↑I×↑I =>t n|>.leftSales x (m n) (w n) x'.1 x'.2 k
  let U' := fun x':↑I×↑I =>t n|>.rightSales x (m n) (w n) x'.1 x'.2 k

  have hχ (i:↑I×↑I) : A i.1 (L i) := x.qA.sales_custom _ _ _ _ _ _
  have hν' (i:↑I×↑I) : B i.2 (U' i) := x.qB.sales_custom _ _ _ _ _ _
  let J(i:↑I×↑I):=|rebate ν (mcut R ν (L i)) (mcut R ν (U' i)) Q|
  have he1 :
      avg W J≤H := by
    unfold J Q; simp_rw [rebate_thick ν _ _ (Fin.castLE_injective hj)]; exact hP L U' hχ hν'
  let g := fun i : ↑I×↑I=> stagePlane v x (m n) (w n) k Y i.1 i.2
  let f := fun i : ↑I×↑I=> Station.eclipse v x (m n) (w n) k Y i.1 i.2
  let C := fun i : ↑I×↑I=> matchScore v x (m n) (w n) i.1 i.2 k
  let D := fun i:↑I×↑I=> taxLeft v x (m n) (w n) k Y Q i.1 i.2+taxRight v x
    (m n) (w n) k Y Q i.1 i.2
  have hA1 i : IsLaw (x.qA.policies x.t x.z n i) :=
    Appearance.witLaw (x.qA.allure_apt _ _ h.2.1 _) ht.hR hn.age
  have hB1 i : IsLaw (x.qB.policies x.t x.z n i) :=
    Appearance.witLaw (x.qB.allure_apt _ _ h.2.2.1 _) ht.hR hn.age
  let X i:= C i+J i+D i+(2*H)
  have hP : ∀ i,g i^2≤ X i := by
    intro i
    let A' := stageLeft v x (m n) (w n) k Y i.1 i.2
    let B' := stageRight v x (m n) (w n) k Y i.1 i.2
    have hh := hχ i; have hk:= hν' i
    obtain ⟨h1,h2⟩:= (hA' _).sales _ hh
    obtain ⟨h3,h4⟩:= (hB' _).sales _ hk
    have h := density_mend ν hν Q R hr.le A' B' (L i) (U' i) (x.qA.bower_case _ _ _ _ _ _ _ (hF _ i.1.property)
      hA1) (x.qB.bower_case _ _ _ _ _ _ _ (hF _ i.2.property) hB1) h1 h3 h2 h4
    have he1 : trayLoss R ν (L i) ≤ H := (hA' _).tailS _ hh
    have he2 : trayLoss R ν (U' i)≤ H := (hB' _).tailS _ hk
    let a:=taxLeft v x (m n) (w n) k Y Q i.1 i.2
    let b0:=taxRight v x (m n) (w n) k Y Q i.1 i.2
    change g i^2 ≤ C i+ J i+(a+trayLoss R ν (L i)+(b0+trayLoss R ν (U' i))) at h
    change _ ≤ C i+J i+(a+b0)+2*H
    linarith only [he1,he2,h]
  refine skylineMean W f g X ε he.le hW ?_ hP (fun i=> (eclipse_beam v x (m n) (w n)
    k Y i.1 i.2 hF hA1 hB1 hhN).trans hR)
  have hc : avg W C≤ H := le_trans ((le_abs_self _).trans (hh q d e x k)) h'
  unfold X; rw [avg_add,avg_add,avg_add]
  have hj : avg W (fun _=> 2*H)=2*H := hW.avg_const _
  rw [hj]
  change avg W D≤ H at hs
  rw [show (ε/2)^2=8*H from by unfold H; ring]; linarith only [hc,he1,hs,hH]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AdaptiveProjectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive Projection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
variable {p:Shape} {n N K M r z s0:ℕ} {q:Format} {d e:Rates} {b:Bool}

private theorem avg_side_bounds {A : Type} [Fintype A] (w : Wgt A) (hw:IsLaw w)
    (b:Bool) (f : Wgt A) (F:A×A→ℝ) (h:∀ i,F i≤f (onSide i b)) :
    avg (pairW w w) F≤avg w f := by
  apply (avg_mono (pairW_law hw hw).nz h).trans
  cases b
  · rw [pairW_avg]
    simp [onSide,hw.avg_const]
  rw [pairW_avg]; simp only [onSide,ite_true, if_true,hw.avg_const]; rfl

namespace Quill
variable (w:Quill p q d b)
  (m:Mixer p n) (t:Tagging p (Messenger q)) (φ:Messenger q→F)
  (u:LeafMixture p n N) (Y:Silhouette p N r)

set_option maxHeartbeats 1200000 in
theorem oneTrestle (omega_:Wgt u.T) (hv:IsLaw omega_) (s:u.T→ Charts p n d)
    (μ:u.T→Wgt (UnitType p n N)) (hμ:∀ i,IsLaw (μ i))
    (P : Keys (p:=p) t N→ Fin z) (F:u.T×u.T → UnitType p n N→Prop)
    (hF : ∀ i o,F i o→PreparationParameters.frameSide p m o)
    (hw:∀ i,IsLaw (w.policies t φ n i)) (hν:IsLaw (lawNu p N t φ))
    (ε v A B:ℝ) (he:0≤ε)
    (ha:∀ i:Fin z,
       pr (mixW omega_ μ) (w.flunk t φ Y (fun x=>ind (P x=i)) m v ε) ≤ A)
    (hh: pr (mixW omega_ μ) (fun x=>¬ w.matchesArea t φ Y x v)≤B) :
    let L (i:u.T×u.T):=onSide i b
    avg (pairW omega_ omega_) (fun i=>varOne (mapW (w.displayMass t φ (μ (L i)) (F i) m (s (L i)) Y) P)
       (mapW (w.sales t φ (μ (L i)) (F i) m (s (L i))) P)) ≤ z*(ε+2*(A+B)) := by
  classical
  intro L
  let Q (i:u.T×u.T) (x:Fin z):=
    |mapW (w.displayMass t φ (μ (L i)) (F i) m (s (L i)) Y) P x-
      mapW (w.sales t φ (μ (L i)) (F i) m (s (L i))) P x|
  let V:= pairW omega_ omega_
  have h (x : Fin z) :
      avg V (fun i=>Q i x) ≤ ε+ 2*(A+B) := by
    let H k:= P k=x
    let R:= w.flunk t φ Y (fun i=>ind (H i)) m v ε
    let Z (i:UnitType p n N):= ¬ w.matchesArea t φ Y i v
    let S o:=R o∨ Z o
    have heq (i): Q i x≤ ε+2*pr (μ (L i)) S := by
      refine w.display_test t φ (μ (L i)) (F i) m (s (L i)) Y H (hμ _) hw hν S he
        (fun y hy hz=> ?_)
      by_cases hf :Z y
      · exact Or.inr hf
      exact Or.inl ⟨hF _ _ hy,not_not.mp hf,s (L i),hz⟩
    let U:=mixW omega_ μ
    have hu : IsLaw U:=mixW_law hv hμ
    have hm (o) : avg omega_ (fun i=>pr (μ i) o)= pr U o := (mixW_avg ..).symm
    apply (avg_side_bounds omega_ hv b (fun i=>ε+2*pr (μ i) S) _ heq).trans
    rw [avg_add,avg_mul',hm,hv.avg_const]
    exact add_le_add_right (mul_le_mul_of_nonneg_left ((pr_or_le hu.nz).trans
      (add_le_add (ha _) hh)) (by norm_num)) _
  change avg V (fun x=> ∑ i,Q x i) ≤ _
  rw [avg_sum]; exact (Finset.sum_le_sum fun i _=> h i).trans_eq (by simp <;> ring)
end Quill

open Station PreparationParameters
namespace Station
variable {w:LeafMixture p n N} (t:Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (k: Fin (2^deckMax p K))
    (μ:Wgt (UnitType p n N)) (Y:Silhouette p N r)

theorem gauzed_area (Y:Silhouette p N r) (w : Quill p q d b)
    (t: Tagging p (Messenger q)) (u : Messenger q → F)
    (h:w.moral t u) (δ:ℝ)
    {K : ℕ} {m:Mixer p n} {ε v:ℝ} (he:ε≤v)
    (o : UnitType p n N) (hc:gauze p ε δ Y m K o) :
    w.matchesArea t u Y o v := by
  intro i; have heq := w.allure_apt t u h i
  exact ((hc _ (w.allure t u i)).1 heq).trans he

set_option maxHeartbeats 1200000 in
theorem projectSum (P : Keys (p:=p) x.t N→Fin z)
    (h :apart w.T) (hm:IsLaw μ) (hw :∀ i∈w.T,0<partMass μ i) (hs : 0<w.amount μ)
    (ha : ∀ i,IsLaw (x.qA.policies x.t x.z n i)) (hb:∀ i,IsLaw (x.qB.policies x.t x.z n i))
    (hν : IsLaw (lawNu p N x.t x.z)) (ε v v' τ B δ : ℝ) (he:0≤ε)
    (hf : x.permission)
    (ht : τ ≤ v ∧ τ≤v')
    (hh : pr (w.sap μ) (fun i=>¬gauze p τ δ Y m K i)≤B)
    (hx : ∀ i:Fin z,pr (w.sap μ) (x.qA.flunk x.t x.z Y (fun y=>ind (P y=i)) m v ε)≤B)
    (hy : ∀ i:Fin z,pr (w.sap μ) (x.qB.flunk x.t x.z Y (fun y=>ind (P y=i)) m v' ε)≤B) :
    t.due x m μ k Y P≤2*(z*(ε+2*(B+B))) := by
  classical
  obtain ⟨hp,hq⟩:=rebuild hm.nz h hw hs
  let A (i:w.T):=partW μ i.val
  let u:=portionW μ w.T
  have hQ : w.sap μ=mixW u A :=hq
  let V:=pairW u u; have hA i:IsLaw (A i):=on_law hm.nz (hw i.val i.property)
  have hL : avg V (fun i=> taxLeft t x m μ k Y P i.1 i.2) ≤ z*(ε+2*(B+B)) := by
    refine x.qA.oneTrestle m x.t x.z w Y u hp (fun i=>t.cAxes i d) A hA P
      (fun i=> t.frontPage x m i.1 i.2 k) (fun i o h => h.2.2.1) ha hν ε v B B he
      (fun i=>by rw [←hQ]; exact hx i) ?_
    rw [←hQ]; apply (pr_mono (LeafMixture.sapLaw hs hm).nz ?_).trans hh
    exact fun i hi h=> hi (gauzed_area _ _ _ _ hf.2.1 δ ht.1 i h)
  have hR : avg V (fun i=> taxRight t x m μ k Y P i.1 i.2) ≤ z*(ε+2*(B+B)) := by
    refine x.qB.oneTrestle m x.t x.z w Y u hp (fun i=>t.cAxes i e) A hA P
      (fun i=> t.backPage x m i.1 i.2 k) (fun i o h => h.2.2.1) hb hν ε v' B B he
      (fun i=>by rw [←hQ]; exact hy i) ?_
    rw [←hQ]; apply (pr_mono (LeafMixture.sapLaw hs hm).nz ?_).trans hh
    exact fun i hi h=>hi (gauzed_area _ _ _ _ hf.2.2.1 δ ht.2 i h)
  unfold due; rw [avg_add,two_mul]
  exact add_le_add hL hR

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SimultaneousProjection
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous Projection -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
namespace StatusAnalysis
open Station PreparationParameters

variable {p : Shape} {M s0 n N K : ℕ} {q:Format} {d e:Rates}
    {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {w:tale p M} {s:rhythms p M}

set_option maxHeartbeats 2400000 in
theorem glowLamp (v:Stations p M b.pins s) (h:veil p M b s0 l m s w) (x:Typus p q d e)
    (k:Fin (2^deckMax p b.pins)) (hP:x.permission) (ε:ℝ) (he:0<ε) :
    ∃ (r : ℕ) (τ u:ℝ), 0<τ∧0<u∧∀ᶠ n in l,∃ Y:Silhouette p (M*n) r,
      bullseye v m w x k ε n Y τ u := by
  classical
  have hq:=h.easel; have ht:=hq.enter.first
  obtain ⟨z,η,hη,hX⟩:=projectCut x hP k h v ε he
  let a:= η/(12*(z+1:ℝ))
  have ha:0<a:=by unfold a; positivity
  obtain ⟨i,u,c,hi,hc,hA⟩:= x.qA.sideRelease x.t x.z M hq hP.2.1 a ha
  obtain ⟨j,v',C,hj,hC,hB⟩:= x.qB.sideRelease x.t x.z M hq hP.2.2.1 a ha
  let f:=fun _ : Fin z=>i*j; let r:=bouquet f
  let τ:= min u v'
  refine ⟨r,τ,a,lt_min hi hj,ha,?_⟩
  have hz:= (trend_sizes l h.timeL ht.hM).2
  filter_upwards [hX,h.upright,h.durableS.shape,h.durableS.mass.positive,h.moment,
    hA.filter_mono h.timeL,hB.filter_mono h.timeL,
    ((bp_nat_vanish hc).eventually (eventually_le_nhds ha)).filter_mono h.timeL,
    ((bp_nat_vanish hC).eventually (eventually_le_nhds ha)).filter_mono h.timeL,
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
    with n hn ha' hB' hW he' hA hB hM hV hG
  let N:=M*n; let p0:=s n
  obtain ⟨P,hP'⟩:=hn
  let e k y:=ind (P y=k)
  have heq k y : |e k y| ≤1 := by unfold e; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  choose X hF using fun i:Fin z=> hA (e i) (heq i)
  choose Z hF' using fun i:Fin z=> hB (e i) (heq i)
  let Y k:=duoY (X k) (Z k)
  refine ⟨bundleY f Y,fun r Y' hR τ' δ hτ hpos=>?_⟩
  apply hP' r Y'
  have hw:=he'.1.law
  let hh:=hB'.1
  have hx' i : IsLaw (x.qA.policies x.t x.z n i) :=
    Appearance.witLaw (x.qA.allure_apt _ _ hP.2.1 _) ht.hR ha'.age
  have hy' i : IsLaw (x.qB.policies x.t x.z n i) :=
    Appearance.witLaw (x.qB.allure_apt _ _ hP.2.2.1 _) ht.hR ha'.age
  have hN:= show 2*num (Messenger q×Toast p)-(N:ℝ) ≤ -1 from by
    change _ ≤ (N:ℝ) at hG; linarith only [hG]
  have hp := nuLaw x.t x.z hN
  have ht' : ∀ i:Fin z,refines Y' (Y i) := fun i=> refines_next hR (bundle_refines f Y i)
  refine (projectSum (v n) x (m n) k (w n) Y' P hh.part hw (fun i hi=>(hh.leaf i hi).pos)
    hW hx' hy' hp a u v' τ' a δ ha.le hP ⟨hτ.trans (min_le_left ..),hτ.trans (min_le_right ..)⟩
    hpos (fun i=>?_) (fun i=>?_)).trans ?_
  · exact (hF i _ Y' (refines_next (ht' i) (duo_good ..).1) _ _ ha').trans hM
  · exact (hF' i _ Y' (refines_next (ht' i) (duo_good ..).2) _ _ ha').trans hV
  have hi : 12*(z+1:ℝ)*a=η := by unfold a; field_simp
  nlinarith only [hi,ha,(Nat.cast_nonneg z : 0≤(z:ℝ))]

private theorem minimums {A:Type} [Fintype A] (x : Wgt A) (hx:∀ i,0<x i) :
    ∃ ε : ℝ,0<ε ∧ ∀ i, ε ≤ x i := by
  classical
  cases isEmpty_or_nonempty A
  next he => exact ⟨1,zero_lt_one,fun i=> (he.false i).elim⟩
  next he =>
    let f:= univ.image x
    have hf : f.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    obtain ⟨i,hi,ht⟩:= mem_image.mp (Finset.min'_mem _ hf)
    exact ⟨f.min' hf,ht ▸ hx i,fun i=>Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ i))⟩

set_option maxHeartbeats 1400000 in
theorem twinkle (v:Stations p M b.pins s) (h:veil p M b s0 l m s w)
    (ε:ℝ) (he:0<ε) :
    ∃ (r : ℕ) (τ u:ℝ),0<τ∧0<u∧∀ᶠ n in l,∃ Y:Silhouette p (M*n) r,
      ∀ i:Scrip p b.pins, i.2.2.permission → bullseye v m w i.2.2 i.2.1 ε n Y τ u := by
  classical
  choose r q A hr hq hh using
    (fun i:Scrip p b.pins=> show ∃ (r : ℕ) (τ u:ℝ),0<τ∧0<u∧∀ᶠ n in l,
      ∃ Y:Silhouette p (M*n) r, i.2.2.permission → bullseye v m w i.2.2 i.2.1 ε n Y τ u from by
       by_cases hP : i.2.2.permission
       · obtain ⟨r,τ,u,hτ,hu,hh⟩:=glowLamp v h i.2.2 i.2.1 hP ε he
         refine ⟨r,τ,u,hτ,hu, hh.mono (fun i hi=> ?_)⟩
         obtain ⟨Y,hY⟩:=hi; exact ⟨Y,fun _=>hY⟩
       exact ⟨1,1,1,zero_lt_one,zero_lt_one,.of_forall (fun n=> ⟨fun _ _ _=>0,fun hi=>(hP hi).elim⟩)⟩)
  obtain ⟨δ,hd,hd'⟩:=minimums q hr
  obtain ⟨e,he,he'⟩:=minimums A hq
  refine ⟨bouquet r,δ,e,hd,he,?_⟩
  filter_upwards [eventually_all.mpr hh] with n hn
  choose F hF using hn
  refine ⟨bundleY r F,fun i hi r' Y' hR τ' δ' hτ hp=> ?_⟩
  exact hF i hi r' Y' (refines_next hR (bundle_refines r F i)) _ _ (hτ.trans (hd' _)) (hp.trans (he' _))

set_option maxHeartbeats 1200000 in
theorem lateSilk (v:Stations p M b.pins s) (h:veil p M b s0 l m s w)
    (ε η:ℝ) (he:0<ε) (hη:0<η) (L:ℕ) :
    ∃ (r:ℕ) (δ:ℝ),0<δ ∧ (r+1:ℝ)*δ≤η ∧ ∀ᶠ n in l,
    ∀ Y:Silhouette p (M*n) L,∃ X:Silhouette p (M*n) r, refines X Y ∧
      pr ((s n).sap (w n)) (fun i=>¬ gauze p δ δ X (m n) b.pins i)≤ η ∧
      ∀ i:Scrip p b.pins,i.2.2.permission →
         sparks (b:=b) v i m w n X ≤ ε := by
  classical
  obtain ⟨r,τ,u,hτ,hu,hg⟩:= twinkle v h ε he
  let d:=r*L
  let a:= d+1; let δ := min τ (η/(a:ℝ))
  have hD : 0<(a:ℝ):=by unfold a; positivity
  have hd : 0<δ:=lt_min hτ (by positivity)
  have hb := gauzeCalendar p d M h.easel δ δ hd hd
  refine ⟨d,δ,hd,?_,?_⟩
  · have hh := (le_div_iff₀ hD).mp (show δ ≤ η/(a:ℝ) from min_le_right ..)
    rw [mul_comm]; simpa [a] using hh
  filter_upwards [hg,hb.filter_mono h.timeL,h.upright,((bp_nat_vanish (by norm_num :
    (0:ℝ)<1/100)).eventually (eventually_le_nhds (lt_min hu hη))).filter_mono h.timeL]
    with n hn hb hc hz Y
  obtain ⟨X,hX⟩:=hn
  let Z:= duoY X Y
  have hm := (hb _ _ hc Z).trans hz
  exact ⟨Z,(duo_good X Y).2,hm.trans (min_le_right ..),fun i h=> hX i h d Z (duo_good X Y).1
    δ δ (min_le_left ..) (hm.trans (min_le_left ..))⟩
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PositiveTestMass
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Test Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Filter Finset LinearMap Module
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M s0 r :ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {q:PreparationParameters} {w:LeafMixture p n N}

variable {U : Wgt (UnitType p n N)} {m : Mixer p n}

theorem troupe_bill (h:Lead U w m q) :
    IsLaw (troupe w U) ∧ mapW (troupe w U) Prod.snd=w.sap U := by
  classical
  obtain ⟨h1,h2⟩:=rebuild h.law.nz h.strength.part
    (fun i hi=>(h.strength.leaf _ hi).pos) h.amount
  have hk i:IsLaw (partW U (Subtype.val (show w.T from i))):=on_law h.law.nz (h.strength.leaf _
    i.property).pos
  constructor
  · constructor
    · intro x; exact mul_nonneg (h1.nz _) ((hk _).nz _)
    unfold troupe; rw [semi_total]; simp_rw [(hk _).total]; exact h1.avg_const _
  change _=allW U w.T; rw [h2]; funext i
  unfold mapW mixW pr troupe; rw [semi_avg]
  simp_rw [show ∀ w':↥w.T,avg (partW U w'.val) (fun x=> ind (x=i))=partW U w'.val i from
    (fun w=> pr_point' ..)]

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AggregateCostBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Aggregate Cost Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N r M s0 K:ℕ}
namespace StatusAnalysis
open PreparationParameters Station DualAnalysis

theorem couplings {I A : Type} [Fintype I] [Fintype A] (p:Wgt I)(f:I→ Wgt A)
    (F:(I×A)×(I×A)→ℝ):
    avg (pairW (semi p f) (semi p f)) F=
      avg (pairW p p) (fun i=>avg (pairW (f i.1) (f i.2)) (fun a=>F ((i.1,a.1),(i.2,a.2)))) := by
  rw [pairW_avg,pairW_avg]
  simp_rw [semi_avg,pairW_avg]
  refine avg_congr (fun i _=>?_); exact avg_avg ..

theorem ship_cost (w:LeafMixture p n N)(U:Wgt (UnitType p n N))(m:Mixer p n)
    (v:Station p n N K w) (i:Scrip p K) (Y:Silhouette p N r) :
    avg (cirque w U) (fun x=>v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2))
     = v.stratum i.2.2 m U i.2.1 Y := couplings (portionW U w.T) (fun i=>partW U i.val) _

theorem ship_pos (w:LeafMixture p n N) (m:Mixer p n)
    (v:Station p n N K w) (i:Scrip p K) (Y:Silhouette p N r)
    (h:i.2.2.permission)(hp:1≤p.r)(hn:2*p.r≤n)
    (x:ViewPair p n N w):
    0≤ v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2) := by
  classical
  let a:=i.2.2
  have hA j:= Appearance.witLaw (a.qA.allure_apt a.t a.z h.2.1 j) hp hn
  have hB j:= Appearance.witLaw (a.qB.allure_apt a.t a.z h.2.2.1 j) hp hn
  let s:= v.cAxes x.1.1 (toRates i.1.2.1)
  let t:= v.cAxes x.2.1 (toRates i.1.2.2)
  have hc (j) : 0≤ a.chimera x.1.2 x.2.2 s t m Y j := avg_nonneg (unifOn_sub _).nz
    (fun k=> mul_nonneg (a.qA.seraphFloor a.t a.z x.1.2 m s Y j (hA j) k).1
      (a.qB.seraphFloor a.t a.z x.2.2 m t Y j (hB j) k).1)
  have hM : 0≤a.momus:= mul_nonneg (kappa_pos _).le (kappa_pos _).le
  exact mul_nonneg (ind_nonneg _) (mul_nonneg hM (Finset.prod_nonneg fun i _=>hc i))

theorem prognosis (w:LeafMixture p n N) (U: Wgt (UnitType p n N)) (m:Mixer p n)
    (b:PreparationParameters) (v:Station p n N b.pins w) (Y:Silhouette p N r)
    {ε a : ℝ} (he:0 ≤ ε)(ha:0<a) (hp:1≤p.r)(hn:2*p.r≤n)
    (hs:Lead U w m b)
    (h:∀ i:Scrip p b.pins,i.2.2.permission→v.stratum i.2.2 m U i.2.1 Y ≤ ε):
    pr (cirque w U) (fun x=> eligiblePair v m x.1 x.2 Y a)≤ num (Scrip p b.pins)*(ε/a) := by
  classical
  let J:= Scrip p b.pins; let I:=ViewPair p n N w; let V:=cirque w U
  let Q (i:J)(x:I):= v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2)
  have ht:= (troupe_bill hs).1; have hv:IsLaw V:=pairW_law ht ht
  let P (i:J)(x:I):= i.2.2.permission∧ a ≤ Q i x
  have hF (i:J): pr V (P i)≤ ε/a := by
    by_cases ht:i.2.2.permission
    · simp only [P,ht,true_and]
      refine (le_div_iff₀ ha).mpr ?_
      rw [mul_comm]
      exact ((le_avg_markov hv.nz (ship_pos w m v i Y ht hp hn) a).trans_eq (ship_cost ..)).trans
        (h i ht)
    rw [show P i=(fun _=>False) from funext fun a=>eq_false fun hh=>ht hh.1,pr_false]; exact div_nonneg he ha.le
  change pr V (fun x=>∃ i,P i x)≤ _
  exact ((pr_exists_le hv.nz P).trans (Finset.sum_le_sum fun i _=> hF i)).trans_eq (by simp [J,num])

variable {l:Filter ℕ} {m:cycleM p} {U:tale p M} {w:rhythms p M} {b:PreparationParameters}
set_option maxHeartbeats 1400000 in
theorem lightmap_oai (v:Stations p M b.pins w) (h:veil p M b s0 l m w U)
    (a ε τ:ℝ) (ha:0<a)(he:0<ε)(hτ:0<τ)
    (k:ℕ)(Y:∀ n,Silhouette p (M*n) k):
    ∃ (r:ℕ) (δ:ℝ), ∀ᶠ n in l,
      ∃ X:Silhouette p (M*n) r,refines X (Y n)∧
        Beams b (m n) X (w n) (U n) (v n) a ε δ τ := by
  classical
  let L:= num (Scrip p b.pins); have hL:0≤L:=Nat.cast_nonneg _
  let η := a*τ/(L+1)
  have hη:0<η:=by unfold η; positivity
  let u:= min τ (min ε (1/4))
  have hu :0<u:=lt_min hτ (lt_min he (by norm_num))
  obtain ⟨r,δ,hd,hV,hT⟩:= lateSilk v h η u hη hu k
  refine ⟨r,δ,?_⟩; have he:= h.easel.enter.first
  filter_upwards [h.upright,hT,h.moment,h.durableS.shape,h.durableS.mass.positive,
    (trend_sizes l h.timeL he.hM).2.eventually (eventually_ge_atTop (2*num (Toast p)+1))]
    with n hn ht hp hC hP hN
  obtain ⟨X,hX,hW,hY⟩:=ht (Y n)
  let N:=M*n
  refine ⟨X,hX, ?_,hW.trans (min_le_left ..),?_, hd,?_⟩
  · have h0 i j:IsLaw (wisp p X i j):=
      mapW_law (omegaLaw p i j (show 2*num (Toast p)-(N:ℝ)≤-1 by
        change _≤(N:ℝ) at hN
        linarith only [hN])) _
    refine ⟨h0,fun i j=>?_⟩
    let ν:=wisp p X i j
    have hs : pr ν (fun i=>¬δ≤ν i) = 1-pr ν (fun i=>δ≤ν i) :=by rw [pr_not,(show tot ν=1
      from (h0 i j).total)]
    have hi:u≤1/4:=le_trans (min_le_right ..) (min_le_right ..)
    simp_rw [not_le] at hs
    have hf:= haze_small ν δ hd.le
    linarith only [hf,hs,hV,hi,hd]
  · apply (prognosis (w n) (U n) (m n) b (v n) X hη.le ha he.hR hn.age
      ⟨hC.1,hP,hp.1.law,hC.2⟩ hY).trans
    change L*(η/a)≤τ
    have h : η/a= τ/(L+1) := by unfold η; field_simp
    rw [h,mul_div_assoc',div_le_iff₀ (by linarith)]
    linarith only [hτ]
  have hi:u≤ε:=le_trans (min_le_right ..) (min_le_left ..)
  nlinarith only [hi,hV,hd,Nat.cast_nonneg (α:=ℝ) r]

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.StatusAnalysis.lightmap_oai := @OAI.HadwigerCounterexample.StatusAnalysis.lightmap_oai
