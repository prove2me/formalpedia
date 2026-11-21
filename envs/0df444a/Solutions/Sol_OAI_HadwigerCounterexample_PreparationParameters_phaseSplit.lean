-- Prove2me | solution 1 for OAI.HadwigerCounterexample.PreparationParameters.phaseSplit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:00.207502+00:00
-- url     : https://prove2.me/submissions/e42da537-ee94-49a0-a1be-aca9f146b1cb

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

theorem tot_mono (h : ∀ x, w x ≤ v x) : tot w ≤ tot v :=
  Finset.sum_le_sum fun x _ => h x

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

theorem normW_carried (hp : carried w p) : carried (normW w) p :=
  fun x h => by rw [normW, hp x h, zero_div]

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

/-- A pointwise fiber disintegration. -/
theorem disintegrate {w : Wgt A} (hw : ∀ x, 0 ≤ w x) (f : A → B) :
    w = mixW (mapW w f) (fun y => onW w (fun x => f x = y)) := by
  funext x
  unfold mixW avg
  rw [Finset.sum_eq_single (f x)]
  · simp only [mapW,onW_val,ind_true,mul_one]
    by_cases h : pr w (fun z => f z = f x) = 0
    · rw [h,zero_mul]
      apply le_antisymm _ (hw x)
      rw [← h]; exact weight_le_pr hw rfl
    · field_simp
  · intro i _ hi; simp [onW_val, ind, Ne.symm hi]
  · simp

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

theorem pr_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c*v x) (p : A → Prop) :
    pr w p ≤ c*pr v p := calc
  _ ≤ pr (fun x => c*v x) p := pr_mono_left (w:=w) (v:=fun x => c*v x) h _
  _ = _ := by simp only [pr,avg,Finset.mul_sum,mul_assoc]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CellPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cell Pruning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

theorem sum_pr_tag (w : Wgt A) (P : A → Prop) (f : A→I) :
    ∑ i:I,pr w (fun x => P x ∧ f x=i) = pr w P := by
  classical
  unfold pr
  rw [← avg_sum]
  refine avg_congr fun x _ => ?_
  simp only [ind_and, ← Finset.mul_sum]
  rw [Finset.sum_eq_single (f x)]
  · rw [ind_one rfl,mul_one]
  · intro j _ hj; exact ind_zero hj.symm
  simp

/-- implication needed only almost surely for finite measures. -/
theorem pr_on_mono {w : Wgt A} (hw : ∀ x,0≤w x) {P Q : A→Prop}
    (h : ∀ x,w x≠0→ P x→ Q x) : pr w P ≤ pr w Q :=
  Finset.sum_le_sum (fun x _ => by
    by_cases he : w x=0
    · simp [he]
    exact mul_le_mul_of_nonneg_left (ind_mono (h x he)) (hw x))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMatrices
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

section Linear

variable {I J K L R S : Type} [Fintype I] [Fintype J]

theorem mpair_outer (M : Mat I J) (x : Vec I) (y : Vec J) :
    mpair M (vecMulVec x y) = evmat M x y := by
  dsimp [mpair,evmat,mulVec,dotProduct,vecMulVec]
  simp only [Finset.mul_sum,mul_left_comm]

theorem liftM_outer (P : Mat K I) (Q : Mat L J) (x : Vec I) (y : Vec J) :
    liftM P Q (vecMulVec x y) = vecMulVec (P *ᵥ x) (Q *ᵥ y) := by
  rw [liftM_def,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

variable [Fintype K] [Fintype L]

theorem mpair_liftM (P : Mat K I) (Q : Mat L J) (M : Mat K L) (A : Mat I J) :
    mpair M (liftM P Q A) = mpair (liftM Pᵀ Qᵀ M) A := by

  simp only [liftM_def, mpair, transpose_transpose, LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, transpose_apply]

  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end Linear
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LinearExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear Extension -/

noncomputable section
namespace HadwigerCounterexample

open Matrix Module Submodule LinearMap Function

variable {V W U V' : Type}
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
variable [AddCommGroup U] [Module F U] [AddCommGroup V'] [Module F V']

theorem mem_range_comp {f : V →ₗ[F] W} {g : V →ₗ[F] U} (h : ker f ≤ ker g) :
    ∃ L : W →ₗ[F] U, L ∘ₗ f = g := by
  obtain ⟨i,hi⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨L,hL⟩ := (g ∘ₗ i).exists_extend
  refine ⟨L,LinearMap.ext fun x => ?_⟩
  have hm := LinearMap.congr_fun hL (f.rangeRestrict x)
  change L (f x) = g _ at hm
  change L (f x) = _
  rw [hm]
  have heq : f (i (f.rangeRestrict x)) = f x :=
    congrArg Subtype.val (LinearMap.congr_fun hi (f.rangeRestrict x))
  have ha : i (f.rangeRestrict x) - x ∈ ker f := by rw [mem_ker,map_sub,heq,sub_self]
  simpa only [mem_ker,map_sub,sub_eq_zero] using h ha

/-- Transport equal-sized domain embeddings in equal-dimensional spaces. -/
theorem equate {f : U →ₗ[F] V} {g : U →ₗ[F] V'} [FiniteDimensional F V]
    [FiniteDimensional F V'] (hf : Injective f) (hg : Injective g)
    (h : dim V = dim V') :
    ∃ A : V ≃ₗ[F] V', ∀ x, A (f x) = g x := by
  let p := LinearMap.range f
  let p' := LinearMap.range g
  let e := LinearEquiv.ofInjective f hf
  let e' := LinearEquiv.ofInjective g hg
  obtain ⟨q,hq⟩ := p.exists_isCompl
  obtain ⟨q',hq'⟩ := p'.exists_isCompl
  let B := Submodule.prodEquivOfIsCompl p q hq
  let B' := Submodule.prodEquivOfIsCompl p' q' hq'
  have hk : dim q = dim q' := by
    have h₁ := B.finrank_eq
    have h₂ := B'.finrank_eq
    rw [finrank_prod] at h₁ h₂
    have h₃ : dim p = dim p' := (e.symm.trans e').finrank_eq
    dsimp only [dim] at *
    omega
  let C : q ≃ₗ[F] q' := LinearEquiv.ofFinrankEq _ _ hk
  refine ⟨B.symm.trans ((LinearEquiv.prodCongr (e.symm.trans e') C).trans B'), fun x => ?_⟩
  have hb : B.symm (f x) = (e x,0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left p q hq (e x)
  change B' ((e.symm.trans e') (B.symm (f x)).1, C (B.symm (f x)).2) = _
  rw [hb]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,map_zero]
  change (e' x).val + (0:q').val = g x
  simp only [Submodule.coe_zero,add_zero]
  rfl

/-- Split projection into kernel plus section. -/
theorem lin_split (f : V →ₗ[F] W) (h : Surjective f) :
    ∃ (B : W →ₗ[F] V) (k : V →ₗ[F] ker f), (∀ x, f (B x) = x) ∧
      ∀ x, B (f x) + (k x).val = x := by
  obtain ⟨B,hB⟩ := f.exists_rightInverse_of_surjective (range_eq_top.mpr h)
  have hb x : f (B x) = x := LinearMap.congr_fun hB x
  let K := LinearMap.id - B ∘ₗ f
  have hk x : K x ∈ ker f := by
    change f (x - B (f x)) = 0
    rw [map_sub,hb,sub_self]
  exact ⟨B,K.codRestrict _ hk,hb,fun x => by change B _ + (x-B _) = x; abel⟩

/-- Extend simultaneous diagram A' = L A, G = G' L to some change of basis L.
Here the two maps A, A' are injective, G, G' are onto, and G A = G' A'. -/
theorem equate_pair {A A' : U →ₗ[F] V} {G G' : V →ₗ[F] W}
    [FiniteDimensional F V] (hA : Injective A) (hA' : Injective A')
    (hG : Surjective G) (hG' : Surjective G') (h : G ∘ₗ A = G' ∘ₗ A') :
    ∃ L : V ≃ₗ[F] V, (∀ x, L (A x) = A' x) ∧ (∀ y, G y = G' (L y)) := by
  let f := G ∘ₗ A
  obtain ⟨B,k,hB,hk⟩ := lin_split G hG
  obtain ⟨B',k',hB',hk'⟩ := lin_split G' hG'
  have eqn x : G (A x) = G' (A' x) := LinearMap.congr_fun h x
  have hh {A : U →ₗ[F] V} {G : V →ₗ[F] W} (hA : Injective A)
      (hg : ∀ x, G (A x)=f x) (B : W →ₗ[F] V) {k : V →ₗ[F] ker G}
      (hk : ∀ x, B (G x)+(k x).val=x) :
      Injective (k ∘ₗ A ∘ₗ (ker f).subtype) := by
    intro x y hxy
    have hxx (x : ker f) : ↑(k (A x.val)) = A x.val := by
      simpa only [hg, show f x.val = 0 from x.property, map_zero,zero_add] using hk (A x.val)
    apply Subtype.ext
    apply hA
    rw [←hxx x,←hxx y]
    exact congrArg Subtype.val hxy
  have hd : dim (ker G) = dim (ker G') := by
    have hr := G.finrank_range_add_finrank_ker
    have hr' := G'.finrank_range_add_finrank_ker
    rw [range_eq_top.mpr hG] at hr
    rw [range_eq_top.mpr hG'] at hr'
    exact Nat.add_left_cancel (hr.trans hr'.symm)
  obtain ⟨C,hC⟩ := equate (hh hA (fun _ => rfl) B hk)
    (hh hA' (fun x => (eqn x).symm) B' hk') hd
  let E := k' ∘ₗ A' - C.toLinearMap ∘ₗ k ∘ₗ A
  obtain ⟨D,hD⟩ := mem_range_comp (show ker f ≤ ker E by
    intro x hx
    change k' (A' x) - C (k (A x)) = 0
    have heq : C (k (A x)) = k' (A' x) := hC ⟨x,hx⟩
    rw [heq,sub_self])
  let L := B' ∘ₗ G + (ker G').subtype ∘ₗ (C.toLinearMap ∘ₗ k + D ∘ₗ G)
  have hl (x : V) : G x = G' (L x) := by
    change G x = G' (B' (G x) + ((C (k x)+D (G x)) : ker G').val)
    rw [map_add,hB', show G' ((C (k x)+D (G x)) : ker G').val = 0 from
      (C (k x)+D (G x)).property,add_zero]
  have hli : Injective L := by
    rw [← LinearMap.ker_eq_bot,eq_bot_iff]
    intro x hx
    have hy : G x=0 := by rw [hl,show L x=0 from hx,map_zero]
    change B' _ + ((C (k x)+ D (G x)) : ker G').val = 0 at hx
    simp only [hy,map_zero,zero_add,add_zero] at hx
    have h00 : C (k x) = 0 := Subtype.ext hx
    have h0 : k x = 0 := C.injective (by rw [map_zero, h00])
    have hw := hk x
    rw [h0,hy,map_zero,Submodule.coe_zero,zero_add] at hw
    rw [←hw]; exact Submodule.zero_mem _
  refine ⟨LinearEquiv.ofInjectiveEndo L hli, fun x => ?_, hl⟩
  change B' (G (A x)) + ((C (k (A x))+D (G (A x))) : ker G').val = _
  have heq : D (G (A x)) = k' (A' x) - C (k (A x)) := LinearMap.congr_fun hD x
  rw [heq,add_sub_cancel,eqn,hk']

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

theorem rk_add_le [FiniteDimensional F W] (f g : V →ₗ[F] W) :
    rk (f+g) ≤ rk f+rk g :=
  (Submodule.finrank_mono (show LinearMap.range (f+g) ≤ range f ⊔ range g by
    rintro x ⟨y,rfl⟩
    exact Submodule.add_mem_sup (show f y ∈ range f from ⟨y,rfl⟩)
      (show g y ∈ range g from ⟨y,rfl⟩))).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

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

theorem mrk_add_le (A B : Mat I J) : (A+B).rank ≤ A.rank + B.rank := by
  rw [rank_cast,rank_cast,rank_cast,mulVecLin_add]; exact rk_add_le _ _

omit [Fintype I] in
theorem colSp_mem {P : Mat I J} (j : J) : P.col j ∈ colSp P := by
  rw [colSp,range_mulVecLin]
  exact Submodule.subset_span ⟨j,rfl⟩

omit [Fintype I] in
/-- Matrix multiplication cancels when a left factor is injective. -/
theorem inj_comp_mat [Fintype K] (A : Mat I J) (B : Mat J K)
    (hA : Injective A.mulVec) (hB : Injective B.mulVec) :
    Injective (A*B).mulVec := by
  rw [← coe_mulVecLin,mulVecLin_mul]
  exact hA.comp hB

omit [Fintype I] in
theorem toMat_map [DecidableEq J] (f : Vec J →ₗ[F] Vec I) :
    (LinearMap.toMatrix' f).mulVecLin = f := by
  rw [← toLin'_apply']; exact LinearEquiv.symm_apply_apply _ _

/-- Paired-frame transitivity of §3 in matrix form. -/
theorem frame_move [Fintype K] [DecidableEq K] {A A' : Mat K I} {B B' : Mat K J}
    (ha : Injective A.mulVec) (ha' : Injective A'.mulVec) (hb : Injective B.mulVec)
    (hb' : Injective B'.mulVec) (h : Aᵀ * B = A'ᵀ * B') :
    ∃ L R : Mat K K, L*R = 1 ∧ R*L = 1 ∧ L*A=A' ∧ Rᵀ*B = B' := by
  classical
  have he : (Bᵀ*A) = (B'ᵀ*A') := by
    simpa only [transpose_mul,transpose_transpose] using congrArg Matrix.transpose h
  obtain ⟨C,hC,hD⟩ := equate_pair (A:=A.mulVecLin) (A':=A'.mulVecLin) (G:=Bᵀ.mulVecLin)
    (G':=B'ᵀ.mulVecLin) ha ha' (transpose_surj_iff.mpr hb)
    (transpose_surj_iff.mpr hb') (by rw [← mulVecLin_mul,← mulVecLin_mul,he])
  let L := LinearMap.toMatrix' C.toLinearMap
  let R := LinearMap.toMatrix' C.symm.toLinearMap
  have hl : L * R = 1 := by
    apply coe_mv_inj
    change (L*R).mulVecLin = Matrix.mulVecLin 1
    dsimp only [L,R]
    rw [mulVecLin_mul,toMat_map,toMat_map,mulVecLin_one]
    exact LinearMap.ext fun x => C.apply_symm_apply x
  have hr : R * L = 1 := by
    apply coe_mv_inj
    change (R*L).mulVecLin = Matrix.mulVecLin 1
    dsimp only [L,R]
    rw [mulVecLin_mul,toMat_map,toMat_map,mulVecLin_one]
    exact LinearMap.ext fun x => C.symm_apply_apply x
  refine ⟨L,R,hl,hr,?_,?_⟩
  · apply coe_mv_inj
    change (L*A).mulVecLin = _
    dsimp only [L]; rw [mulVecLin_mul,toMat_map]
    exact LinearMap.ext hC
  · have hB : Bᵀ = B'ᵀ * L := by
      apply coe_mv_inj
      change _ = (B'ᵀ*L).mulVecLin
      dsimp only [L]; rw [mulVecLin_mul,toMat_map]
      exact LinearMap.ext hD
    apply_fun Matrix.transpose
    · rw [transpose_mul,transpose_transpose,hB,Matrix.mul_assoc,hl,Matrix.mul_one]
    · exact Matrix.transpose_injective

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixFactorization
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators
variable {I J Q : Type} [Fintype I] [Fintype J] [Fintype Q]

/-- Projecting the columns onto their literal column space keeps the matrix. -/
theorem invariant_cols (M : Mat I J) (Z : Mat I Q) (R : Mat Q I) (e : colSp Z = colSp M)
    [DecidableEq Q] (hr : R*Z=(1:Mat Q Q)) :
    Z * (R*M) = M := by
  apply coe_mv_inj
  apply LinearMap.ext
  intro v
  change _ *ᵥ v = M *ᵥ v
  simp only [← Matrix.mulVec_mulVec]
  have h : M*ᵥv ∈ colSp Z := e.symm ▸ (show M*ᵥv ∈ colSp M from ⟨v,rfl⟩)
  obtain ⟨x,hx⟩ := h
  change Z*ᵥx=M*ᵥv at hx
  rw [← hx, Matrix.mulVec_mulVec x R Z,hr, Matrix.one_mulVec]

theorem rank_product (M : Mat I J) :
    ∃ (A : Mat I (Fin M.rank)) (B : Mat (Fin M.rank) J),
      Function.Injective A.mulVec ∧ Function.Surjective B.mulVec ∧ A*B=M := by
  let t := M.rank
  let A := pack (colSp M)
  have ha := pack_inj (colSp M)
  obtain ⟨L,hL⟩ := mat_left_inv ha
  have hh := invariant_cols M A L (colSp_pack _) hL
  refine ⟨A,L*M,ha, mrk_surj.mpr ?_, hh⟩
  refine le_antisymm (Matrix.rank_le_card_height _) ?_
  have hx := Matrix.rank_mul_le_right A (L*M)
  rw [hh] at hx
  rw [Fintype.card_fin]; exact hx

omit [Fintype Q] in
theorem matrix_cancel_left {A : Mat I J} (hA : Function.Injective A.mulVec)
    (C D : Mat J Q) (h : A*C=A*D) : C=D := by
  classical
  obtain ⟨R,hR⟩ := mat_left_inv hA
  have hh := congrArg ((R * ·) : Mat I Q → _) h
  simpa only [← Matrix.mul_assoc,hR,Matrix.one_mul] using hh

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateEmbeddings
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Embeddings -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {U V I J K T : Type} [Fintype U] [Fintype V] [Fintype I] [Fintype J]
    [Fintype K] [Fintype T]

omit [Fintype I] in
theorem embedMatT [DecidableEq U] (f : I → U) (x : Vec U) :
    (embedMat f)ᵀ *ᵥ x = fun i => x (f i) := by
  classical funext i
            simp [embedMat,Matrix.mulVec,dotProduct]

omit [Fintype V] [Fintype I] in
theorem mul_embedMat [DecidableEq U] (f : I → U) (M : Mat V U) :
    M*embedMat f = M.submatrix _root_.id f := by
  ext i j
  simp [Matrix.mul_apply,embedMat]

omit [Fintype V] [Fintype I] in
theorem embedMat_mul [DecidableEq U] (f : I → U) (M : Mat U V) :
    (embedMat f)ᵀ*M = M.submatrix f _root_.id := by
  ext i j
  simp [Matrix.mul_apply,embedMat]

omit [Fintype I] in
theorem embedMat_self [DecidableEq I] [DecidableEq U] {f : I → U} (h : Injective f) :
    (embedMat f)ᵀ * embedMat f = 1 := by
  ext i j
  rw [embedMat_mul]
  simp only [embedMat,Matrix.submatrix_apply,Matrix.of_apply,id_eq,
    Matrix.one_apply,h.eq_iff]

theorem embedMat_inj [DecidableEq U] {f : I → U} (h : Injective f) :
    Injective (embedMat f).mulVec := by
  classical
  intro x y g
  change embedMat f *ᵥ x = embedMat f *ᵥ y at g
  have he (x : Vec I) : (embedMat f)ᵀ *ᵥ (embedMat f *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec,embedMat_self h,Matrix.one_mulVec]
  rw [← he x,g,he]

omit [Fintype I] in
theorem rank_ge_mul (A : Mat I J) (B : Mat J K) :
    A.rank+B.rank ≤ (A*B).rank+Fintype.card J := by
  let f := A.mulVecLin
  let g := f ∘ₗ (colSp B).subtype
  have he : LinearMap.range g = colSp (A*B) := by
    change LinearMap.range g = LinearMap.range ((A*B).mulVecLin)
    rw [mulVecLin_mul]
    unfold g
    rw [LinearMap.range_comp,LinearMap.range_comp]
    simp [f,colSp]
  have hi : dim (LinearMap.ker g) ≤ dim (LinearMap.ker f) := by
    let q := ((colSp B).subtype ∘ₗ (LinearMap.ker g).subtype)
    have hq (x : LinearMap.ker g) : q x ∈ LinearMap.ker f := x.property
    let k := q.codRestrict (LinearMap.ker f) hq
    have hk : Injective k := by
      intro x y h
      have heq := congrArg (fun b : LinearMap.ker f => b.val) h
      exact Subtype.ext (Subtype.ext heq)
    exact LinearMap.finrank_le_finrank_of_injective hk
  have h1 := g.finrank_range_add_finrank_ker
  rw [he] at h1
  have h2 := f.finrank_range_add_finrank_ker
  change (A*B).rank + dim (LinearMap.ker g)=B.rank at h1
  change A.rank + dim (LinearMap.ker f)=dim (Vec J) at h2
  rw [dim_vec] at h2; omega

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticTesters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic Testers -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

theorem mpair_sum {I J : Type} [Fintype I] [Fintype J] (m : Mat I J)
    {α : Type*} (s : Finset α) (f : α → Mat I J) :
    mpair (∑ i ∈ s, f i) m = ∑ i ∈ s, mpair (f i) m := by
  rw [mpair_comm,map_sum]
  exact Finset.sum_congr rfl fun i _ => mpair_comm _ _

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
theorem bp_mul_nat (x : ℝ) (n : ℕ) : bp (x*n) = bp x ^ n := by
  unfold bp; rw [Real.rpow_mul (by norm_num)]; simp

theorem bp_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (a*x)) atTop atTop :=
  (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
    ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)

theorem bp_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (-a*x)) atTop (𝓝 0) := by
  simp_rw [neg_mul,bp_neg]
  exact (bp_tendsto ha).inv_tendsto_atTop

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

theorem map_unif_surjective [Fintype V] [Fintype W] (f : V →ₗ[F] W)
    (h : Function.Surjective f) : mapW unif f = unif := by
  rw [unif_lin,range_eq_top.mpr h]
  simp only [Submodule.mem_top,unifOn_true]

end General

theorem dim_mat (I J : Type) [Fintype I] [Fintype J] :
    dim (Mat I J) = Fintype.card I * Fintype.card J := by
  simp only [dim,Mat,finrank_matrix,finrank_self,mul_one]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramProbabilities
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameOrbitLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Move.finiteMove _root_.OAI.HadwigerCounterexample.Move.identity_move _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Orbit Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function

variable {U I J R S : Type} [Fintype U] [Fintype I] [Fintype J] [Fintype R] [Fintype S]
    [DecidableEq U]

namespace Move
variable (c : Move U)

omit [Fintype I] [Fintype J] in
theorem gram_invar (A : Mat U I) (B : Mat U J) :
    (c.L*A)ᵀ * (c.Rᵀ*B) = Aᵀ*B := by
  rw [transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc c.Lᵀ c.Rᵀ B,← transpose_mul,c.RL,
    Matrix.transpose_one, Matrix.one_mul]

theorem L_inj : Injective c.L.mulVec := by
  intro x y h
  have hi (x) : c.R *ᵥ (c.L *ᵥ x) = x := by rw [mulVec_mulVec,c.RL, Matrix.one_mulVec]
  change c.L *ᵥ x = c.L *ᵥ y at h
  rw [←hi x,h,hi y]

theorem perm_inj (A : Mat U I) : Injective A.mulVec ↔ Injective (c.L*A).mulVec := by
  refine ⟨inj_comp_mat _ _ c.L_inj, fun h => ?_⟩
  have hh := inj_comp_mat _ _ c.sym.L_inj h
  change Injective (c.R*(c.L*A)).mulVec at hh
  rwa [←Matrix.mul_assoc,c.RL,Matrix.one_mul] at hh

theorem invar (C : Mat I J → Prop) (x : Mat U I × Mat U J) :
    FramesAt C x ↔ FramesAt C (c.perm I J x) := by
  unfold FramesAt
  change _ ↔ C ((c.L*x.1)ᵀ * (c.Rᵀ*x.2)) ∧ _
  rw [gram_invar]
  exact and_congr Iff.rfl (and_congr (c.perm_inj x.1) (c.dual.perm_inj x.2))
end Move

/-- Nonempty matrix family if super-dimension slack. -/
theorem framesAt_exists [DecidableEq I] [DecidableEq J]
    {C : Mat I J → Prop} (h : ∃ G, C G) (hn : num I+num J < num U) :
    ∃ x : Mat U I × Mat U J, FramesAt C x := by
  obtain ⟨G,hG⟩ := h
  let v := (pairW unif unif : Wgt (Mat U I × Mat U J))
  have he (a : ℝ) (h : a < 0) : 0 < 1-bp a := sub_pos.mpr
    ((bp_lt h).trans_eq bp_zero)
  have hpos : 0 < pr v (gramGood G) := by
    refine lt_of_lt_of_le ?_ (gram_norm G hn.le).2
    have hi : num I - num U < 0 := by
      have hh : 0 ≤ num J := by unfold num; positivity
      linarith
    exact mul_pos (mul_pos (bp_pos _) (he _ hi)) (he _ (by linarith only [hn]))
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos (pairW_law unif_law unif_law).nz hpos
  exact ⟨x,hx.1.symm ▸ hG,hx.2⟩

theorem move_exists (G : Mat I J) (x y : Mat U I × Mat U J) (hx : gramGood G x)
    (hy : gramGood G y) : ∃ c : Move U, c.perm I J x = y := by
  obtain ⟨L,R,H,F,E,T⟩ := frame_move hx.2.1 hy.2.1 hx.2.2 hy.2.2 (hx.1.trans hy.1.symm)
  exact ⟨⟨L,R,H,F⟩,Prod.ext E T⟩

theorem move_exists_one {x y : Mat U I} (hx : Injective x.mulVec)
    (hy : Injective y.mulVec) : ∃ c : Move U, c.permMat I x = y := by
  let B := (0:Mat U Empty)
  let G := (0:Mat I Empty)
  have he {x : Mat U I} (hx : Injective x.mulVec) : gramGood G (x,B) :=
    ⟨Subsingleton.elim _ _, hx, fun a b _ => Subsingleton.elim a b⟩
  obtain ⟨c,hc⟩ := move_exists G _ _ (he hx) (he hy)
  exact ⟨c,congrArg Prod.fst hc⟩

variable [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S]

/-- Uniform law of plus-only observation; in particular plus frames are
uniform injective. -/
theorem framesAt_observe_plus {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x)
    {P : Mat I R} (hP : Injective P.mulVec) :
    mapW (unifOn (FramesAt (U:=U) C)) (fun x => x.1*P) =
      unifOn (fun x => Injective x.mulVec) := by
  refine uniform_orbit _ hc ?_ ?_
  · intro x hx; exact inj_comp_mat _ _ hx.2.1 hP
  intro y z hy hz
  obtain ⟨c,hc⟩ := move_exists_one hy hz
  refine ⟨c.perm I J,c.invar C, fun x => ?_⟩
  change x.1*P=y ↔ c.L*x.1*P=z
  rw [Matrix.mul_assoc,←hc]
  exact (c.permMat R).injective.eq_iff.symm

theorem framesAt_observe_minus {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x)
    {Q : Mat J S} (hQ : Injective Q.mulVec) :
    mapW (unifOn (FramesAt (U:=U) C)) (fun x => x.2*Q) =
      unifOn (fun x => Injective x.mulVec) := by
  refine uniform_orbit _ hc ?_ ?_
  · intro x hx; exact inj_comp_mat _ _ hx.2.2 hQ
  intro y z hy hz
  obtain ⟨c,hc⟩ := move_exists_one hy hz
  refine ⟨c.dual.perm I J,c.dual.invar C, fun x => ?_⟩
  change x.2*Q=y ↔ c.L*x.2*Q=z
  rw [Matrix.mul_assoc,←hc]
  exact (c.permMat S).injective.eq_iff.symm

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixedImageBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI

/-! # Mixed Image Bounds -/

noncomputable section

namespace HadwigerCounterexample
open Matrix Function LinearMap
open scoped BigOperators

variable {I J U S : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype S]
  [DecidableEq I] [DecidableEq J] [DecidableEq U] [DecidableEq S]

theorem plus_le_unif (hu : num I-num U ≤ -1) (P : Mat U I) :
    unifOn (fun P : Mat U I => Injective P.mulVec) P ≤ 2 * unif P := by
  have h : pr unif (fun P : Mat U I => ¬ Injective P.mulVec) ≤ (2:ℝ)⁻¹ := by
    apply le_trans unif_fail
    rw [show (2:ℝ)⁻¹=bp (-1) by rw [bp_neg,bp_one]]; exact bp_le hu
  rw [pr_not (unif:Wgt (Mat U I)) (p:=fun P => Injective P.mulVec),unif_law.total] at h
  have h1 := on_mon unif_law.nz (a:=(2:ℝ)⁻¹)
    (p:=fun P : Mat U I => Injective P.mulVec) (by norm_num) (by linarith only [h]) P
  rwa [on_unif,inv_inv] at h1

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice
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

theorem gramCond_exists (m : Mixer p n) : ∃ G, gramCond m G := by
  refine ⟨fromBlocks (selfM p n m.mixM) 0 0 0,?_,?_,?_⟩ <;> rfl

theorem raw_law (m : Mixer p n) (hN : 2*num (Full p n)<N) : IsLaw (raw m N) :=
  prodW_law (fun _ => unifOn_law (framesAt_exists (gramCond_exists m)
    (show num (Full p n) + num (Full p n) < num (Fin N) by
      rw [← two_mul]; simpa [num] using hN)))

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TensorIntersections
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensor Intersections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

section Rank
variable {U I J L : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype L]

omit [Fintype U] in
theorem colSp_join (A : Mat U I) (B : Mat U J) :
    colSp (fromCols A B) = colSp A ⊔ colSp B := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    rw [mulVecLin_apply,fromCols_mulVec]
    exact add_mem_sup (show A *ᵥ _ ∈ colSp A from ⟨_,rfl⟩)
      (show B *ᵥ _ ∈ colSp B from ⟨_,rfl⟩)
  refine sup_le ?_ ?_
  · rintro _ ⟨x,rfl⟩
    refine ⟨Sum.elim x 0,?_⟩
    simp only [mulVecLin_apply,fromCols_mulVec_sumElim,Matrix.mulVec_zero,add_zero]
  · rintro _ ⟨x,rfl⟩
    refine ⟨Sum.elim 0 x,?_⟩
    simp only [mulVecLin_apply,fromCols_mulVec_sumElim,Matrix.mulVec_zero,zero_add]

omit [Fintype U] in
theorem colSp_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    colSp (liftM P Q A) ≤ colSp P := by
  rw [liftM_def,Matrix.mul_assoc,colSp, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

omit [Fintype U] in
theorem rank_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    (liftM P Q A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Rank

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixQuotients
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

omit [Fintype K] [Fintype L] in
theorem liftM_transpose (A : Mat I J) (P : Mat K I) (Q : Mat L J) :
    (liftM P Q A)ᵀ = liftM Q P Aᵀ := by
  simp only [liftM_def,transpose_mul,transpose_transpose,Matrix.mul_assoc]

theorem box_mem (M : Mat I J) (S : Space (Vec I)) (T : Space (Vec J)) :
    M∈box S T ↔ colSp M ≤ S ∧ colSp Mᵀ ≤ T := by
  classical
  constructor
  · rintro ⟨A,rfl⟩
    rw [liftM_transpose]
    exact ⟨(colSp_lift_le ..).trans_eq (colSp_pack _),
      (colSp_lift_le ..).trans_eq (colSp_pack _)⟩
  · rintro ⟨h,g⟩
    obtain ⟨X,hX⟩ := mat_left_inv (pack_inj S)
    obtain ⟨Y,hY⟩ := mat_left_inv (pack_inj T)
    have h1 {I J : Type} [Fintype I] [Fintype J] {A : Mat I J} {S : Space (Vec I)}
        (h : colSp A ≤ S) {X : Mat (Fin (dim S)) I} (hx : X*pack S=1) : pack S*(X*A)=A := by
      apply coe_mv_inj
      refine LinearMap.ext fun x => ?_
      have he : A*ᵥx ∈ colSp (pack S) := (colSp_pack S).symm ▸
        h (show A*ᵥx∈colSp A from ⟨x,rfl⟩)
      obtain ⟨y,hy⟩ := he
      change pack S *ᵥ y=A *ᵥ x at hy
      change _ *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec y X, hx,
        Matrix.one_mulVec]
      exact hy
    refine ⟨liftM X Y M,?_⟩
    have h2 := congrArg Matrix.transpose (h1 g hY)
    rw [transpose_mul,transpose_mul,transpose_transpose] at h2
    change pack S * (X*M*Yᵀ)*(pack T)ᵀ=M
    rw [← Matrix.mul_assoc (pack S) (X*M),h1 h hX,h2]

theorem box_le {M M' : Space (Vec I)} {N N' : Space (Vec J)} (hm : M ≤ M') (hn : N ≤ N') :
    box M N ≤ box M' N' := fun _ h =>
  have he := (box_mem ..).mp h
  (box_mem ..).mpr ⟨he.1.trans hm,he.2.trans hn⟩

theorem lift_mem_box {M : Mat I J} {S : Space (Vec I)} {T : Space (Vec J)}
    (P : Mat K I) (Q : Mat L J) (h : M ∈ box S T) :
    liftM P Q M ∈ box (S.map P.mulVecLin) (T.map Q.mulVecLin) := by
  obtain ⟨A,rfl⟩ := h
  rw [liftM_comp,box_mem,liftM_transpose]
  constructor <;> apply le_trans (colSp_lift_le ..) <;>
    rw [colSp,mulVecLin_mul,LinearMap.range_comp]
  · rw [show LinearMap.range (pack S).mulVecLin=S from colSp_pack _]
  rw [show LinearMap.range (pack T).mulVecLin=T from colSp_pack _]

theorem evmat_transpose (M : Mat I J) (x : Vec I) (y : Vec J) :
    evmat Mᵀ y x=evmat M x y := dotProduct_transpose_mulVec _ _ _
theorem evmat_pull (P : Mat K I) (Q : Mat L J) (A : Mat K L) (x : Vec I) (y : Vec J) :
    evmat (pullM P Q A) x y=evmat A (P *ᵥ x) (Q *ᵥ y) := by
  rw [←mpair_outer,←mpair_outer,← liftM_outer,mpair_liftM]; rfl

theorem evmat_ext {M N : Mat I J} (h : ∀ x y, evmat M x y=evmat N x y) : M=N := by
  classical
  ext i j
  simpa [evmat] using h (Pi.single i 1) (Pi.single j 1)

theorem annih_dim (S : Space (Vec I)) :
    dim S + dim (annih S) = Fintype.card I := by
  have h := (pack S)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change ((pack S)ᵀ).rank + dim (annih S)=dim (Vec I) at h
  rwa [Matrix.rank_transpose,mrk_inj.mp (pack_inj _),dim_vec,Fintype.card_fin] at h

theorem dot_ext_zero {x : Vec I} (h : ∀ y, dotProduct y x=0) : x=0 := by
  classical funext i
            simpa using h (Pi.single i 1)

theorem annih_mem (x : Vec I) (S : Space (Vec I)) :
    x ∈ annih S ↔ ∀ y ∈ S,dotProduct x y = 0 := by
  change (pack S)ᵀ *ᵥ x=0 ↔ _
  constructor
  · intro h y hy
    obtain ⟨z,rfl⟩ := (pack_mem_iff ..).mp hy
    rw [← dotProduct_transpose_mulVec,h,dotProduct_zero]
  intro h
  refine dot_ext_zero fun y => ?_
  rw [dotProduct_transpose_mulVec]; exact h _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NominalSpaces
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nominal Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

theorem IH_self (b) : (IH p n b)ᵀ*IH p n b=1 := by
  apply embedMat_self
  intro i j; cases b <;> simp [putFull]
theorem IP_IH (a b : Bool) : (IP p n a)ᵀ * IH p n b=0 := by
  unfold IP IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> simp [embedMat,putFull]

theorem IH_cross {a b : Bool} (h : a ≠ b) : (IH p n a)ᵀ * IH p n b=0 := by
  unfold IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> first | contradiction | simp [embedMat,putFull]
theorem IH_IP (a b : Bool) : (IH p n a)ᵀ * IP p n b=0 := by
  simpa only [transpose_mul,Matrix.transpose_zero,transpose_transpose] using
    congrArg Matrix.transpose (IP_IH (p:=p) (n:=n) b a)

theorem ip_decomp (x : Dir p n) :
    (∑ b : Bool, ((IP p n b) *ᵥ ((IP p n b)ᵀ*ᵥx)+ (IH p n b)*ᵥ ((IH p n b)ᵀ*ᵥx)))=x := by
  rw [Fintype.sum_bool]
  unfold IP IH
  simp_rw [embedMatT]
  ext i
  rcases i with (i|i)|(i|i) <;>
    simp [embedMat,putFull,Matrix.mulVec,dotProduct,Pi.add_apply]

theorem images_ip (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IP p n b = primary (takeSign (onSide x b z.1) z.2) := by
  unfold IP; rw [mul_embedMat]
  cases b <;> ext <;> rfl
theorem images_ih (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IH p n b = channel (takeSign (onSide x b z.1) z.2) := by
  unfold IH; rw [mul_embedMat]
  cases b <;> ext <;> rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelDecomposition
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Channel Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Submodule
variable {I : Type} [Fintype I]

theorem evmat_addM {J : Type} [Fintype J] (A B : Mat I J) (x y) :
    evmat (A+B) x y = evmat A x y+evmat B x y := by rw [←mpair_outer,mpair_add,
      mpair_outer,mpair_outer]

variable {p : Shape} {n : ℕ}

theorem ip_le_primal (b : Bool) : colSp (IP p n b)≤primal p n := by
  cases b; exact le_sup_right; exact le_sup_left

theorem ih_le_channels (b : Bool) : colSp (IH p n b) ≤ channels p n := by
  cases b; exact le_sup_right; exact le_sup_left

theorem channels_proj (b : Bool) : channels p n ≤ LinearMap.ker (IP p n b)ᵀ.mulVecLin := by
  have hi (i : Bool) : colSp (IH p n i) ≤ LinearMap.ker (IP p n b)ᵀ.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change (IP p n b)ᵀ *ᵥ (IH p n i *ᵥ y) = _
    rw [mulVec_mulVec, IP_IH, Matrix.zero_mulVec]
  exact sup_le (hi _) (hi _)

theorem primal_proj (b : Bool) : primal p n ≤ LinearMap.ker (IH p n b)ᵀ.mulVecLin := by
  have hi (i : Bool) : colSp (IP p n i) ≤ LinearMap.ker (IH p n b)ᵀ.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change (IH p n b)ᵀ *ᵥ (IP p n i *ᵥ y) = _
    rw [mulVec_mulVec, IH_IP, Matrix.zero_mulVec]
  exact sup_le (hi _) (hi _)

theorem channels_disjoint : Disjoint (primal p n) (channels p n) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,hy⟩
  have he (b : Bool) : (IP p n b)ᵀ *ᵥ x = 0 := channels_proj b hy
  have hf (b : Bool) : (IH p n b)ᵀ *ᵥ x = 0 := primal_proj b hx
  have hh := ip_decomp (show Dir p n from x)
  simp_rw [he,hf,mulVec_zero,add_zero, Finset.sum_const_zero] at hh
  rw [← hh]
  exact Submodule.zero_mem _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AttackCutDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Attack Cut Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

theorem colSp_kill (S : Space (Vec I)) (M : Mat I J) :
    colSp M ≤ annih S ↔ ∀ x∈S,Mᵀ *ᵥ x=0 := by
  constructor
  · intro h x hx
    refine dot_ext_zero fun y => ?_
    rw [dotProduct_transpose_mulVec,dotProduct_comm]
    exact (annih_mem ..).mp (h ⟨y,rfl⟩) x hx
  rintro h z ⟨y,rfl⟩
  rw [annih_mem]; intro x hx
  rw [dotProduct_comm,mulVecLin_apply,←dotProduct_transpose_mulVec,h x hx,dotProduct_zero]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoverSpaces
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cover Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

theorem prj_data (S : Space (Vec I)) : ProjData S ⊥ (prj S) :=
  (proj_exists S ⊥ disjoint_bot_right).choose_spec

variable [DecidableEq I] [DecidableEq J]

theorem chop_ker (S : Space (Vec I)) (x : Vec I) :
    chop S *ᵥ x=0 ↔ x∈S := by
  rw [chop,Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero]
  constructor
  · intro h; exact h.symm ▸ (prj_data S).onto x
  exact fun h => ((prj_data S).fixes x h).symm

theorem chop_colT (S : Space (Vec I)) : colSp (chop S)ᵀ=annih S := by
  have hi : colSp (chop S)ᵀ ≤annih S := (colSp_kill ..).mpr (fun x hx => by
    rw [transpose_transpose]; exact (chop_ker S x).mpr hx)
  apply Submodule.eq_of_le_of_finrank_eq hi
  have h := (chop S).mulVecLin.finrank_range_add_finrank_ker
  rw [show ker (chop S).mulVecLin=S from (by ext x; exact chop_ker S x)] at h
  change (chop S).rank + dim S = dim (Vec I) at h
  have he := annih_dim S
  rw [dim_vec,← he, add_comm] at h
  exact (Matrix.rank_transpose _).trans (Nat.add_left_cancel h)

theorem vanish_chop {S : Space (Vec I)} {T : Space (Vec J)} (M : Mat I J) :
    vanish S T M ↔ liftM (chop S) (chop T) M=0 := by
  let A := (chop S)ᵀ
  let B := (chop T)ᵀ
  have h1 : liftM (chop S) (chop T) M=pullM A B M := by
    simp only [A,B,pullM,Matrix.transpose_transpose]
  have h2 : colSp A=annih S := chop_colT _
  have h3 : colSp B=annih T := chop_colT _
  rw [h1]
  unfold vanish
  rw [←h2,←h3]
  constructor
  · intro h
    refine evmat_ext fun x y => ?_
    rw [evmat_pull, h (A *ᵥ x) ⟨_,rfl⟩ (B *ᵥ y) ⟨_,rfl⟩]
    simp [evmat]
  rintro h x ⟨x,rfl⟩ y ⟨y,rfl⟩
  rw [mulVecLin_apply,mulVecLin_apply,←evmat_pull,h]
  simp [evmat]

theorem chopSpace_join (S T : Space (Vec I)) :
    S ⊔ chopSpace S T=S⊔ T := by
  classical
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rintro t ⟨x,h,rfl⟩
    rw [mulVecLin_apply,chop,Matrix.sub_mulVec,Matrix.one_mulVec]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right h)
      (Submodule.mem_sup_left ((prj_data S).onto x))
  intro x hx
  have he : x=prj S *ᵥ x+chop S *ᵥ x := by
    rw [chop,Matrix.sub_mulVec,Matrix.one_mulVec,add_sub_cancel]
  exact he.symm ▸ Submodule.add_mem_sup ((prj_data S).onto x)
    (show chop S *ᵥ x∈chopSpace S T from ⟨x,hx,rfl⟩)

theorem chopSpace_disjoint (S T : Space (Vec I)) : Disjoint S (chopSpace S T) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,y,hy,rfl⟩
  rw [mulVecLin_apply,chop,Matrix.sub_mulVec,Matrix.one_mulVec] at hx ⊢
  have hi := (prj_data S).fixes _ hx
  rw [Matrix.mulVec_sub,(prj_data S).fixes _ ((prj_data S).onto y),sub_self] at hi
  rw [←hi]; exact Submodule.zero_mem _

theorem chopSpace_rank (S T : Space (Vec I)) :
    dim S+dim (chopSpace S T) = dim (S⊔T : Submodule _ _) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (chopSpace S T)
  rw [chopSpace_join,(chopSpace_disjoint S T).eq_bot,finrank_bot,add_zero] at h
  exact h.symm

theorem cdim_sign (p : Shape) {N} (S : Cov p N) :
    cdim p S=cdSign p S true+cdSign p S false := by
  simp only [cdim,cdSign,Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib]

theorem matter_dim (x : Ambient p N) (b : Bool) : cdSign p (matter p x) b=epoch p x :=
  Finset.sum_congr rfl fun i _ => by cases b; exact Matrix.rank_transpose _; rfl

theorem covered_iff (S : Cov p N) (x) : covered p S x ↔
    ∀ e,vanish (S (e,true)) (S (e,false)) (x e) := by
  constructor
  · intro h e
    apply (vanish_chop _).mpr
    exact congr_fun h e
  intro h
  exact funext fun e => (vanish_chop _).mp (h e)

theorem covered_part {S : Cov p N} {x : Ambient p N} (h : matter p x ≤ S) :
    covered p S x := by
  refine (covered_iff ..).mpr (fun e a ha b _ => ?_)
  change dotProduct a (x e *ᵥ b)=0
  apply (annih_mem ..).mp ha
  exact h (e,true) ⟨b,rfl⟩

private theorem vanish_sum {S : Space (Vec I)} {T : Space (Vec J)}
    (M : Mat I J) :
    vanish S T M ↔ M∈box S ⊤ ⊔ box ⊤ T := by
  classical
  constructor
  · intro h
    let A := prj S
    let B := prj T
    let D := A*M
    let E := (1-A)*M*Bᵀ
    have hh : colSp D≤S := by
      rintro x ⟨y,rfl⟩
      rw [mulVecLin_apply,show D=_*_ from rfl,←mulVec_mulVec]
      exact (prj_data S).onto _
    have he : colSp Eᵀ ≤ T := by
      rintro x ⟨y,rfl⟩
      rw [mulVecLin_apply,show E=_*_ from rfl,transpose_mul,transpose_transpose,←mulVec_mulVec]
      exact (prj_data T).onto _
    have hx : M=D+E := by
      have hg := (vanish_chop _).mp h
      change (1-A)*M*(1-B)ᵀ = 0 at hg
      rw [transpose_sub,transpose_one,Matrix.mul_sub,Matrix.mul_one] at hg
      unfold D E
      rw [← sub_eq_zero.mp hg,Matrix.sub_mul,Matrix.one_mul,add_sub_cancel]
    rw [hx]; exact Submodule.add_mem_sup ((box_mem ..).mpr ⟨hh,le_top⟩)
      ((box_mem ..).mpr ⟨le_top,he⟩)
  · intro h
    obtain ⟨A,hA,B,hB,rfl⟩ := Submodule.mem_sup.mp h
    intro x hx y hy
    have hi : colSp A≤ S := ((box_mem ..).mp hA).1
    have hj : colSp Bᵀ≤ T := ((box_mem ..).mp hB).2
    rw [evmat_addM,show evmat A x y=0 from
      (annih_mem ..).mp hx _ (hi ⟨_,rfl⟩),zero_add,← evmat_transpose B]
    exact (annih_mem ..).mp hy _ (hj ⟨_,rfl⟩)

theorem cover_mem (S : Cov p N) (x : Ambient p N) :
    x∈coverX p S ↔ ∀ e,x e∈box (S (e,true)) ⊤ ⊔ box ⊤ (S (e,false)) :=
  (covered_iff ..).trans (forall_congr' fun e => vanish_sum (x e))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SpanDeficits
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Span Deficits -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- Loss of rank from overlapping mode spans. -/
private theorem colsum_bound (A B : Mat I J) :
    A.rank+B.rank ≤ (A+B).rank+dim (colSp A⊓colSp B : Submodule _ _)+
      dim (colSp Aᵀ ⊓ colSp Bᵀ : Submodule _ _) := by
  classical
  obtain ⟨X,Y,hX,hY,hA⟩ := rank_product A
  obtain ⟨S,T,hS,hT,hB⟩ := rank_product B
  have h := rank_ge_mul (fromCols X S) (fromRows Y T)
  have he {I J U : Type} [Fintype I] [Fintype U] [Fintype J] (A : Mat I U) {B : Mat U J}
      (h : Function.Surjective B.mulVec) :
      colSp (A*B) = colSp A := by
    rw [colSp,mulVecLin_mul,LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (show Function.Surjective B.mulVecLin from h),Submodule.map_top]
  have hc := colSp_join X S
  have hr := colSp_join Yᵀ Tᵀ
  rw [← he X hY,← he S hT,hA,hB] at hc
  rw [← he Yᵀ (transpose_surj_iff.mpr hX),←he Tᵀ (transpose_surj_iff.mpr hS),←transpose_mul,
    ←transpose_mul,hA,hB] at hr
  have h1 := finrank_sup_add_finrank_inf_eq (colSp A) (colSp B)
  rw [←hc] at h1
  have h2 := finrank_sup_add_finrank_inf_eq (colSp Aᵀ) (colSp Bᵀ)
  rw [←hr] at h2
  rw [fromCols_mul_fromRows,hA,hB,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin,
    ← Matrix.rank_transpose (fromRows _ _), transpose_fromRows] at h
  change (fromCols X S).rank+dim (_ : Submodule _ _) = A.rank+B.rank at h1
  change (fromCols Yᵀ Tᵀ).rank+dim (_ : Submodule _ _)=Aᵀ.rank+Bᵀ.rank at h2
  rw [Matrix.rank_transpose,Matrix.rank_transpose] at h2
  omega

theorem cdim_mono {a b : Cov p N} (h : a≤b) : cdim p a ≤ cdim p b :=
  Finset.sum_le_sum fun i _ => Submodule.finrank_mono (h i)

theorem cdim_sup_inf (a b : Cov p N) : cdim p (a⊔b)+cdim p (a⊓b)=cdim p a+cdim p b := by
  unfold cdim
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => finrank_sup_add_finrank_inf_eq (a i) (b i)

theorem tax_before (a b : Cov p N) : cdim p a+tax p a b=cdim p (a⊔b) :=
  Nat.add_sub_of_le (cdim_mono (p:=p) le_sup_left)

theorem tax_lost (a b : Cov p N) : tax p a b+cdim p (a⊓b)=cdim p b := by
  have h := cdim_sup_inf (p:=p) a b; rw [←tax_before (p:=p)] at h
  omega

theorem tax_antitone (p : Shape) {N} (a b c : Cov p N) (h : a≤b) :
    tax p b c≤ tax p a c := by
  have he := cdim_mono (p:=p) (inf_le_inf h (show c ≤ c from le_rfl))
  have hg := tax_lost (p:=p) a c
  have hh := tax_lost (p:=p) b c
  omega

theorem matter_pair {x y : Ambient p N} {a b : Cov p N}
    (hx : matter p x ≤ a) (hy : matter p y ≤ b) :
    matter p (x+y) ≤ a⊔b ∧
      epoch p x+ epoch p y+cdim p (a⊔b) ≤ epoch p (x+y)+cdim p a+cdim p b := by
  classical
  have h (i) : x i∈box (a (i,true)) (a (i,false)) :=
    (box_mem ..).mpr ⟨hx (i,true),hx (i,false)⟩
  have h' i : y i ∈box (b (i,true)) (b (i,false)) :=
    (box_mem ..).mpr ⟨hy (i,true),hy (i,false)⟩
  constructor
  · intro i
    let C := a⊔b
    have he : x i.1 + y i.1∈box (C (i.1,true)) (C (i.1,false)) :=
      Submodule.add_mem _ ((box_le le_sup_left le_sup_left) (h _))
        ((box_le le_sup_right le_sup_right) (h' _))
    have hg := (box_mem ..).mp he
    cases i with | mk i j => cases j; exact hg.2; exact hg.1
  · have hg (i) : (x i).rank+(y i).rank ≤ (x i+y i).rank+dim ((a⊓b) (i,true))+
        dim ((a⊓b) (i,false)) := by
      refine (colsum_bound (x i) (y i)).trans ?_
      have he c := Submodule.finrank_mono (inf_le_inf (hx (i,c)) (hy (i,c)))
      exact Nat.add_le_add (Nat.add_le_add_left (he true) _) (he false)
    have he := cdim_sup_inf (p:=p) a b
    have hh := (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hg i)
    simp only [Finset.sum_add_distrib] at hh
    change epoch _ x+epoch _ y≤ epoch p (x+y)+cdSign p _ true+cdSign p _ false at hh
    rw [Nat.add_assoc,← cdim_sign] at hh
    omega

theorem matter_erased {a : Cov p N} (x : Ambient p N) :
    matter p (erased p a x) ≤ chopped p a (matter p x) := by
  intro z
  let D := matter p x
  have h : x z.1∈box (D (z.1,true)) (D (z.1,false)) :=
    (box_mem ..).mpr ⟨le_rfl,le_rfl⟩
  have he := (box_mem ..).mp (lift_mem_box (chop (a (z.1,true))) (chop (a (z.1,false))) h)
  cases z with | mk e c => cases c; exact he.2; exact he.1

theorem cdim_chopped (p : Shape) {N} (a b : Cov p N) :
    cdim p (chopped p a b)=tax p a b := by
  have h := tax_before (p:=p) a b
  have he : cdim p a+cdim p (chopped p a b)=cdim p (a⊔b) := by
    unfold cdim
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => chopSpace_rank ..
  exact Nat.add_left_cancel (he.trans h.symm)

theorem epoch_charge {J} (f : J→Ambient p N) (s : Cov p N) (r : Finset J) :
    (matter p (∑ i∈r, erased p s (f i))) ≤ chopped p s (arrange p f r) ∧
      ((∑ i∈r,epoch p (erased p s (f i)))+tax p s (arrange p f r) ≤
        epoch p (∑ i∈r, erased p s (f i)) + ∑ i∈r,tax p s (matter p (f i))) := by
  classical
  induction r using Finset.induction with
  | empty =>
    have he : matter p (N:=N) (0:Ambient p N)=⊥ := by funext i; simp [matter,colSp,Pi.bot_apply]
    simp only [Finset.sum_empty,he,bot_le,true_and,zero_add,add_zero]
    have hi : arrange p f ∅ = ⊥ := Finset.sup_empty
    rw [hi,tax,sup_bot_eq,Nat.sub_self]; exact Nat.zero_le _
  | insert i r hr ih =>
    obtain ⟨hx,hh⟩ := matter_pair (matter_erased (a:=s) (f i)) ih.1
    simp only [Finset.sum_insert hr]
    have he : arrange p f (insert i r)= matter p (f i)⊔arrange p f r :=
      Finset.sup_insert
    have ht : chopped p s (arrange p f (insert i r)) =
        chopped p s (matter p (f i))⊔chopped p s (arrange p f r) := by
      rw [he]
      funext z; exact Submodule.map_sup _ _ _
    rw [ht]
    refine ⟨hx,?_⟩
    rw [← ht, cdim_chopped,cdim_chopped,cdim_chopped] at hh
    have hi := ih.2
    omega

theorem epoch_erased (s : Cov p N) (x : Ambient p N) : epoch p (erased p s x) ≤ epoch p x :=
  Finset.sum_le_sum fun i _ => rank_lift_le _ _ (x i)

theorem epoch_eq_zero (x : Ambient p N) : epoch p x=0 ↔ x=0 := by
  classical
  constructor
  · intro h
    funext i
    have he := Finset.single_le_sum (fun i _ => Nat.zero_le (x i).rank)
      (Finset.mem_univ i)
    have ht : (x i).rank=0 := Nat.eq_zero_of_le_zero (by simpa only [epoch] using h ▸ he)
    obtain ⟨A,B,hA,hB,hZ⟩ := rank_product (x i)
    have : IsEmpty (Fin (x i).rank) := ht ▸ Fin.isEmpty'
    apply hZ.symm.trans
    ext; simp [Matrix.mul_apply]
  intro h
  rw [h,epoch]; simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GreedyExposures
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Greedy Exposures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I : Type} [DecidableEq I]

private theorem tax_comp (a b c : Cov p N) :
    tax p a (b⊔c)=tax p a b + tax p (a⊔b) c := by
  have h1 := tax_before (p:=p) a (b⊔c)
  have h2 := tax_before (p:=p) a b
  have h3 := tax_before (p:=p) (a⊔b) c
  rw [sup_assoc] at h3
  omega

omit [DecidableEq I] in
private theorem price_drop (f : I → Ambient p N) (S T : Cov p N) (W R : Finset I)
    (h : S ≤ T) (g : R⊆ W) :
    price f T R ≤ price f S W := by
  refine Finset.sup_le fun i hi => (tax_antitone p S T (matter p (f i)) h).trans ?_
  exact (@Finset.le_sup _ _ _ _ W (fun i => tax p S (matter p (f i))) i (g hi))

private theorem union_arrange (f : I→Ambient p N) (W R : Finset I) :
    arrange p f (W∪R)= arrange p f W⊔arrange p f R := Finset.sup_union

private theorem grow (p : Shape) {N} (f : I→Ambient p N) (S : Cov p N) (W : Finset I)
    (r : ℕ) (h : r≤W.card) :
    ∃ E R : Finset I, W=E∪R ∧ Disjoint E R ∧ E.card=r ∧
      r*price f (S⊔ arrange p f E) R ≤ tax p S (arrange p f E) := by
  classical
  induction r generalizing W S with
  | zero => exact ⟨∅,W,by simp⟩
  | succ r ih =>
    obtain ⟨x,hx,hP⟩ := Finset.exists_mem_eq_sup W
      (Finset.card_pos.mp (show 0<W.card by omega)) (fun i => tax p S (matter p (f i)))
    let U := W.erase x
    let X := matter p (f x)
    have hU : U.card+1=W.card := Finset.card_erase_add_one hx
    obtain ⟨E,R,hE,hd,hT,hK⟩ := ih (S⊔X) U (by omega)
    have hx' : x∉E := fun H => Finset.notMem_erase _ _ (hE.symm ▸ Finset.mem_union_left R H)
    have hx'' : x∉R := fun H => Finset.notMem_erase _ _ (hE.symm ▸ Finset.mem_union_right E H)
    refine ⟨insert x E,R,?_,?_,?_,?_⟩
    · rw [Finset.insert_union,← hE,Finset.insert_erase hx]
    · rw [Finset.disjoint_insert_left]
      exact ⟨hx'',hd⟩
    · rw [Finset.card_insert_of_notMem hx',hT]
    · have hg : arrange p f (insert x E)=X⊔arrange p f E := Finset.sup_insert
      rw [hg,tax_comp (p:=p),←sup_assoc,Nat.add_mul,Nat.one_mul]
      have hi := price_drop f S (S⊔X⊔arrange p f E) W R
        (le_trans le_sup_left le_sup_left)
        (Finset.Subset.trans (show R⊆U from hE.symm ▸ Finset.subset_union_right)
          (Finset.erase_subset ..))
      have h1 : price f S W=tax p S X := hP
      rw [h1] at hi
      refine (Nat.add_le_add hK hi).trans_eq (Nat.add_comm ..)

/-- Dyadic selection if potential is strictly too low to sustain
all bad tail deficit ratios -/
private theorem greedy_expose (f : I→Ambient p N) (S : Cov p N) (W : Finset I)
    (b m : ℕ) (hW : W.card=2^m*b)
    (hg : 4*(W.card*price f S W+tax p S (arrange p f W)) < W.card*m) :
    ∃ E R : Finset I, W=E∪R ∧ Disjoint E R ∧ b≤R.card ∧
      let s' := S⊔arrange p f E
      4*(R.card*price f s' R) ≤ 4*tax p s' (arrange p f R)+R.card := by
  classical
  induction m generalizing W S with
  | zero => omega
  | succ m ih =>
    by_cases he : 4*(W.card*price f S W)≤ 4*tax p S (arrange p f W)+W.card
    · have h1 : b ≤ W.card := by rw [hW]; exact Nat.le_mul_of_pos_left b (by positivity)
      exact ⟨∅,W,by simpa [arrange,h1] using he⟩
    let k := 2^m*b
    have h1 : W.card=2*k := by rw [hW,pow_succ]; unfold k; ring
    obtain ⟨E,R,hE,hD,hT,hB⟩ := grow p f S W k (by omega)
    have hk : R.card=k := by rw [hE,Finset.card_union_of_disjoint hD] at h1; omega
    let X := S⊔arrange p f E
    have hX :
        tax p S (arrange p f W)=tax p S (arrange p f E)+tax p X (arrange p f R) := by
      rw [hE,union_arrange,tax_comp (p:=p)]
    have hh : 4*(R.card*price f X R+ tax p X (arrange p f R))<R.card*m := by
      have hcalc (a a' t b t' k m : ℕ)
          (hh : 4*(2*k*a+t)<2*k*(m+1)) (ht : t=b+t') (h : k*a'≤b)
          (ha : 4*t+2*k<4*(2*k*a)) :
          4*(k*a'+t')< k*m := by nlinarith
      rw [h1] at he hg
      rw [hk]
      exact hcalc _ _ _ _ _ _ _ hg hX hB (lt_of_not_ge he)
    obtain ⟨F,T,hF,hT,hb,h'⟩ := ih X R hk hh
    have hu : Disjoint E (F∪T) := by rwa [← hF]
    refine ⟨E∪F,T,by rw [hE,hF,Finset.union_assoc],
      by simp only [Finset.disjoint_union_left]; exact
        ⟨Disjoint.mono_right (show T⊆ F∪T from Finset.subset_union_right) hu,hT⟩,hb,?_⟩
    rw [union_arrange, ←sup_assoc]; exact h'

private theorem sum_charge_sign (f : I → Ambient p N) (W : Finset I) (i : Bool) :
    cdSign p (arrange p f W) i ≤ ∑ j∈W,epoch p (f j) := by
  classical
  induction W using Finset.induction with
  | empty =>
    have h : cdSign p (N:=N) ⊥ i=0 := Finset.sum_eq_zero fun e _ => finrank_bot ..
    rw [arrange,Finset.sup_empty,Finset.sum_empty,h]
  | insert x W hx hi =>
    rw [show arrange p f (insert x W)=matter p (f x)⊔arrange p f W from Finset.sup_insert,
      Finset.sum_insert hx]
    calc cdSign p _ i ≤ cdSign p (matter p (f x)) i+cdSign p (arrange p f W) i := by
                          unfold cdSign
                          rw [← Finset.sum_add_distrib]
                          exact Finset.sum_le_sum fun i _ =>
                            Submodule.finrank_add_le_finrank_add_finrank ..
         _ ≤ _ := by rw [matter_dim]; exact add_le_add (le_refl _) hi

theorem arrange_bound (f : I→Ambient p N) (W : Finset I) (k : ℕ) (h : ∀ i ∈ W,epoch p (f i) ≤ k)
    (i : Bool) :
    cdSign p (arrange p f W) i ≤ W.card*k :=
  (sum_charge_sign f W i).trans ((Finset.sum_le_sum fun j hj => h j hj).trans_eq (by simp))

theorem sparse_covered (f : I→ Ambient p N) (W : Finset I)
    (m b r : ℕ) (hW : W.card=2^m*(2*b))
    (hb : 1 ≤ b) (hm : 16*r < m) (hf : ∀ i∈W,epoch p (f i) ≤ r)
    (h : 2 * epoch p (∑ i∈W,f i) ≤ b) :
    ∃ E T : Finset I,E⊆ W ∧ T⊆ W ∧ Disjoint E T ∧ T.card=b ∧
      ∀ i∈T,covered p (arrange p f E) (f i) := by
  classical
  have htax (C : Cov p N) : tax p ⊥ C = cdim p C := by rw [tax,cdim_bot,bot_sup_eq,Nat.sub_zero]
  have hx : price f ⊥ W ≤ 2*r := by
    refine Finset.sup_le fun i hi => ?_
    rw [htax,cdim_sign,matter_dim,matter_dim,two_mul]
    exact add_le_add (hf i hi) (hf i hi)
  have hh :
      4*(W.card*price f ⊥ W + tax p ⊥ (arrange p f W))<W.card*m := by
    have hk : tax p ⊥ (arrange p f W)≤2*(W.card*r) := by
      rw [htax,cdim_sign,two_mul]
      exact add_le_add (arrange_bound f W r hf true) (arrange_bound f W r hf false)
    have hg : 0 < W.card := by rw [hW]; positivity
    nlinarith
  obtain ⟨E,R,hE,hD,hR,hL⟩ := greedy_expose f ⊥ W (2*b) m hW hh
  simp only [bot_sup_eq] at hL
  let S := arrange p f E
  let P (i : I) := ¬ covered p S (f i)
  let J := R.filter P
  have hZ :
      epoch p (∑ i∈R,erased p S (f i)) ≤ epoch p (∑ i∈W,f i) := by
    have hh : ∑ i∈E,erased p S (f i) = 0 := Finset.sum_eq_zero fun i hi =>
      covered_part (S:=S) (show matter p (f i) ≤
        E.sup (fun j => matter p (f j)) from (@Finset.le_sup _ _ _ _ _ (fun j => matter p (f j)) _ hi))
    have h1 : (∑ i∈R, erased p S (f i))=erased p S (∑ i∈W,f i) := by
      rw [hE,Finset.sum_union hD,map_add,map_sum,map_sum,hh,zero_add]
    rw [h1]; exact epoch_erased ..
  have hu : J.card≤ ∑ i∈R,epoch p (erased p S (f i)) := by
    calc J.card = ∑ i∈R, (if P i then (1:ℕ) else 0) := by rw [←Finset.sum_filter]; simp [J]
         _ ≤ _ := Finset.sum_le_sum fun j _ => by
                   split
                   · rename_i hh
                     exact Nat.one_le_iff_ne_zero.mpr (fun h => hh ((epoch_eq_zero _).mp h))
                   exact Nat.zero_le _
  have hp : (∑ i∈R,tax p S (matter p (f i))) ≤ R.card*price f S R := by
    refine (Finset.sum_le_sum (g:=fun i => price f S R) fun i hi => ?_).trans_eq (by simp)
    exact (@Finset.le_sup _ _ _ _ _ (fun i => tax p S (matter p (f i))) i hi)
  have ht := (epoch_charge f S R).2
  have hb' : b≤ (R\ J).card := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset P _)]
    change b ≤ R.card-J.card
    have heq : J.card≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
    change 4*(R.card*price f S R) ≤ 4*tax p S (arrange p f R)+R.card at hL
    omega
  obtain ⟨T,hT,hb'⟩ := Finset.exists_subset_card_eq hb'
  have hz : T ⊆ R := hT.trans Finset.sdiff_subset
  refine ⟨E,T,hE.symm ▸ Finset.subset_union_left,hE.symm ▸ hz.trans Finset.subset_union_right,
    Disjoint.mono_right hz hD,hb',fun i hi => ?_⟩
  exact Classical.byContradiction fun h =>
    (Finset.mem_sdiff.mp (hT hi)).2 (Finset.mem_filter.mpr ⟨hz hi,h⟩)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SumRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

private theorem draws_all (w : Wgt A) (hw : IsLaw w) (J : Finset I) (p : A → Prop) :
    pr (draws I w) (fun x => ∀ i∈J,p (x i)) = pr w p ^ J.card := by
  let v : Wgt (I→A) := prodW (fun _ => w)
  have hh : pr v (fun x => ∀ i∈J,p (x i)) =
      ∏ i:I, pr w (fun x => i∈J → p x) := prodW_pr (fun _ : I => w) (fun i x => i∈J → p x)
  have ht (i : I) :
      pr w (fun x => i∈J → p x)=if i∈J then pr w p else 1 := by
    by_cases hi : i∈J <;> simp [hi,hw.total]
  change pr v _=_
  rw [hh]
  simp_rw [ht]
  rw [← Finset.prod_filter]
  simp

variable {p : Shape} {N : ℕ}

omit [Fintype A] [Fintype I] in
private theorem arrange_fresh (f : A→Ambient p N) (E J : Finset I)
    (h : Disjoint E J) (x y : I → A) :
    arrange p (f ∘ refresh J x y) E=arrange p (f ∘ x) E := by
  classical
  unfold arrange
  apply Finset.sup_congr rfl
  intro i hi
  have he : i∉J := Finset.disjoint_left.mp h hi
  simp [Function.comp_def,refresh,he]

/-- With s=2^m*(2b), not requiring s itself to be a power
of two. -/
theorem no_cover_rank (p : Shape) {N} (f : A→ Ambient p N) (w : Wgt A)
    (hw : IsLaw w) (m b r : ℕ) (hb : 1 ≤ b) (hr : 16*r < m)
    (hf : ∀ i,epoch p (f i)≤ r)
    (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ S : Cov p N,(∀ i, cdSign p S i ≤ r*(2^m*(2*b))) →
      pr w (fun i => covered p S (f i)) ≤ c) :
    let s := 2^m*(2*b)
    pr (draws (Fin s) w) (fun x => 2*epoch p (∑ i,f (x i)) ≤ b) ≤
      ((2:ℝ)^s*(2:ℝ)^s)*c^b := by
  classical
  let s := 2^m*(2*b)
  let T := draws (Fin s) w
  have ht : IsLaw T := draws_law hw
  let Q (X : Finset (Fin s) × Finset (Fin s)) (x : Fin s→A) :=
    Disjoint X.1 X.2 ∧ X.2.card=b ∧ ∀ i∈X.2, covered p (arrange p (f ∘ x) X.1) (f (x i))
  have hg (x : Fin s → A) (h : 2*epoch p (∑ i,f (x i)) ≤ b) :
      ∃ X,Q X x := by
    obtain ⟨E,J,_,_,hi,hj,hX⟩ := sparse_covered (p:=p) (f ∘ x) Finset.univ m b r
      (by simp [s]) hb hr (fun i _ => hf _) h
    exact ⟨(E,J),hi,hj,hX⟩
  have hq (X : Finset (Fin s) × Finset (Fin s)) : pr T (Q X) ≤ c^b := by
    rcases X with ⟨E,J⟩
    by_cases h : Disjoint E J ∧ J.card=b
    · let P (x : Fin s→A) := fun i => covered p (arrange p (f ∘ x) E) (f i)
      have hp (x : Fin s→A) : pr w (P x) ≤ c := by
        apply he; intro i
        have hh := arrange_bound (p:=p) (f ∘ x) E r (fun _ _ => hf _) i
        have hi : E.card ≤ s := by simpa using card_le_card (Finset.subset_univ E)
        exact hh.trans ((Nat.mul_le_mul_right _ hi).trans_eq (Nat.mul_comm ..))
      unfold pr T
      rw [fresh_avg w hw J]
      refine ht.avg_le fun x => ?_
      have hx (y) :
          Q (E,J) (refresh J x y) ↔ ∀ i∈J,P x (y i) := by
        simp only [Q, h.1,h.2,true_and, arrange_fresh f E J h.1]
        constructor
        · intro hh i hi
          specialize hh i hi
          rwa [refresh,ite_eq_left hi] at hh
        intro hh i hi
        rw [refresh,ite_eq_left hi]; exact hh i hi
      simp_rw [hx]
      change pr T _ ≤ _
      rw [show pr T _ = pr w (P x)^J.card from draws_all w hw J _,h.2]
      gcongr
      · exact pr_nonneg hw.nz
      · exact hp x
    · have heq : Q (E,J) = fun _ => False := by
        funext x
        apply propext
        exact iff_false_intro (fun he => h ⟨he.1,he.2.1⟩)
      rw [heq,pr_false]; exact pow_nonneg hc _
  change pr T _ ≤ _
  refine ((pr_mono ht.nz hg).trans (pr_exists_le ht.nz Q)).trans ?_
  refine (Finset.sum_le_sum (g:=fun _ => c^b) fun i _ => hq i).trans_eq ?_
  simp [s]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.Move.finiteMove _root_.OAI.HadwigerCounterexample.Move.identity_move _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem map_pair_law {C D : Type} [Fintype C] [Fintype D]
    (w : Wgt A) (v : Wgt B) (f : A→C) (g : B→D) :
    mapW (pairW w v) (Prod.map f g)=pairW (mapW w f) (mapW v g) := by
  funext x
  unfold mapW pairW
  simp only [Prod.ext_iff]
  exact pairW_pr w v (fun y => f y=x.1) (fun y => g y=x.2)

theorem mapW_nested {C : Type} (w : Wgt A) (f : A→B) (g : B→C) :
    mapW (mapW w f) g=mapW w (g ∘ f) :=
  funext fun _ => mapW_pr _ _ _

omit [Fintype B] in
theorem mapW_repeat {I : Type} [Fintype I] [DecidableEq I]
    (w : I→ Wgt A) (f : I→ A→B) :
    mapW (prodW w) (fun x i => f i (x i))=prodW (fun i => mapW (w i) (f i)) := by
  funext x
  unfold mapW
  simp_rw [funext_iff]
  exact prodW_pr _ (fun i y => f i y=x i)

omit [Fintype B] in
theorem mapW_pr_eq (e : A≃A) (f : A→B) (u : B≃B) (h : ∀ x,f (e x)=u (f x))
    (w : Wgt A) (hw : ∀ x, w (e x)=w x) (x : B) : mapW w f (u x)=mapW w f x := by
  have he := avg_bij e w (fun y => ind (f y=u x))
  simp_rw [hw,h,u.injective.eq_iff] at he
  exact he.symm

private theorem pmax_test {x : A} (p : A → Prop) {w : Wgt A} (hw : SubLaw w)
    (h : ∀ y, p y → w y=w x) {m : ℝ} (hm : 0 < m)
    (hp : m ≤ pr unif p) [Nonempty A] :
    w x ≤ m⁻¹ * unif x := by
  have hh : pr w p=w x*nbr p := by
    simp only [pr,avg,nbr,tot,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases he : p i
    · rw [h i he]
    rw [ind_zero he,mul_zero,mul_zero]
  have h1 := (pr_le_tot (p:=p) hw.nz).trans hw.total
  rw [hh] at h1
  have hU : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [pr_unif (A:=A)] at hp
  have hi := (le_div_iff₀ hU).mp hp
  rw [unif_apply]
  field_simp
  nlinarith only [h1,hi,mul_le_mul_of_nonneg_left hi (hw.nz x)]

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

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

theorem gramObsCap {C : Mat (I⊕J) (I⊕J) → Prop}
    (hc : ∃ x : Mat U (I⊕J) × _, FramesAt C x)
    (T : Mat (I⊕J) J) (ht : Function.Injective T.mulVec)
    (hN : 2*num J-num U≤ -1) :
    let w := unifOn (FramesAt C)
    ∀ x : Mat U J × Mat U J,
      mapW w (observe T T) x ≤ (4*bp (num J*num J))*pairW unif unif x := by
  classical
  let w := unifOn (FramesAt (U:=U) C)
  have hw := unifOn_law hc
  let f := observe T T (U:=U)
  let v := mapW w f
  have hv : IsLaw v := mapW_law hw f
  have hg :
      carried v (fun x : Mat U J × _ => Injective x.1.mulVec ∧ Injective x.2.mulVec) := by
    refine mapW_carried (unifOn_carried _) (fun x hx => ?_)
    exact ⟨inj_comp_mat _ _ hx.2.1 ht,inj_comp_mat _ _ hx.2.2 ht⟩
  dsimp only
  intro x
  rw [← pair_unif]
  by_cases h : v x≠0
  · let G := (x.1ᵀ*x.2 : Mat J J)
    have hx : gramGood G x := ⟨rfl,Classical.byContradiction fun he => h (hg x he)⟩
    let m := bp (-num J*num J)/4
    have he (y : Mat U J × Mat U J) (hy : gramGood G y) : v y=v x := by
      obtain ⟨L,hL⟩ := move_exists G x y hx hy
      let e := L.perm (I⊕J) (I⊕J)
      have hl (y) : f (e y)=(L.perm J J) (f y) :=
        Prod.ext (Matrix.mul_assoc ..) (Matrix.mul_assoc ..)
      have hp y : w (e y)=w y := by
        unfold w; rw [unifOn_val, unifOn_val]
        congr 2
        exact propext (L.invar C y).symm
      exact hL ▸ mapW_pr_eq e f (L.perm J J) hl w hp x
    have hi := pmax_test (gramGood (U:=U) G) hv.sub he (m:=m)
      (div_pos (bp_pos _) (by norm_num)) (gram_norm_quarter G (by linarith only [hN]))
    apply hi.trans
    unfold m; rw [neg_mul,bp_neg]; field_simp
    exact le_rfl
  · change v x ≤ _
    rw [not_ne_iff.mp h]
    exact mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (unif_subLaw.nz _)

variable {p : Shape} {n N : ℕ}

theorem intoChan_inj : Injective (intoChan p n).mulVec :=
  embedMat_inj Sum.inr_injective
theorem intoChan_val (p : Shape) {n N} (x : Mat (Fin N) (Full p n)) :
    x * intoChan p n=channel x := by rw [intoChan,mul_embedMat]; rfl
theorem hchan_val (p : Shape) {n N} :
    hchan p (n:=n) (N:=N) = observe (intoChan p n) (intoChan p n) := by
  funext x
  exact Prod.ext (intoChan_val ..).symm (intoChan_val ..).symm

theorem hchan_cap (m : Mixer p n) (hN : 2*num (Full p n)-N≤ -1) :
    let w := unifOn (FramesAt (U:=Fin N) (gramCond m))
    ∀ x : HFrame p N,mapW w (hchan p) x≤(4*bp ((p.h:ℝ)*p.h))*pairW unif unif x := by
  classical
  have he : 2*num (Full p n)-num (Fin N)≤ -1 := by simpa [num] using hN
  have hh : ∃ x : Oframe p n N, FramesAt (gramCond m) x :=
    framesAt_exists (gramCond_exists m) (by linarith only [he])
  rw [hchan_val]
  have hr : num (Chan p) ≤ num (Full p n) := by
    have hf : Fintype.card (Row p n) + Fintype.card (Chan p)=Fintype.card (Full p n) :=
      (Fintype.card_sum ..).symm
    exact_mod_cast (show Fintype.card (Chan p)≤Fintype.card (Full p n) by omega)
  have hk := gramObsCap hh (intoChan p n) intoChan_inj (by linarith only [he,hr])
  rw [show num (Chan p)=(p.h:ℝ) from (by simp [num,Chan])] at hk
  exact hk

theorem hcube_cap (m : Mixer p n) (hN : 2*num (Full p n)-N≤ -1)
    (x : HCube p N) : mapW (raw m N) (hcube p) x ≤ chanPrice p*lawH p N x := by
  let w := unifOn (FramesAt (U:=Fin N) (gramCond m))
  have hh i := hchan_cap m hN (x i)
  change mapW (prodW (fun (_ : Comp p.g) => w)) _ x ≤ _
  unfold hcube
  rw [mapW_repeat (w:=fun (_:Comp p.g) => w) (f:=fun i => hchan p (n:=n) (N:=N))]
  refine le_trans (Finset.prod_le_prod ?_ fun i _ => hh i) ?_
  · intro i _
    exact pr_nonneg (unifOn_sub _).nz
  rw [Finset.prod_mul_distrib]
  simp [chanPrice,lawH,prodW]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Intersection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

/-- Standard embedding padded by zeros. -/
theorem pad_matrix_inj (a b : ℕ) (h : a ≤ b) :
    ∃ M : Mat (Fin b) (Fin a), Function.Injective M.mulVec := by
  let M : Mat (Fin b) (Fin a) := (1:Mat (Fin b) (Fin b)).submatrix _root_.id (Fin.castLE h)
  have hf : Function.Injective (1:Mat (Fin b) (Fin b)).mulVec := by intro i j he; simpa using he
  refine ⟨M,Matrix.mulVec_injective_iff.mpr ?_⟩
  exact (Matrix.mulVec_injective_iff.mp hf).comp (Fin.castLE h) (Fin.castLE_injective h)

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRankCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Rank Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

theorem cast_mat (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    num (Mat I J)=bp (num I*num J) := by
  unfold num
  rw [card_space,dim_mat]
  push_cast; rfl

theorem nbr_nonneg {A : Type} [Fintype A] (p : A → Prop) : 0 ≤ nbr p :=
  tot_nonneg fun _ => ind_nonneg _

theorem nbr_le_sum {A B : Type} [Fintype A] [Fintype B] (p : A → Prop)
    (q : B → A → Prop) (h : ∀ i, p i → ∃ j,q j i) :
    nbr p ≤ ∑ j, nbr (q j) := by
  have hp (p : A → Prop) : nbr p = pr (fun _ => 1) p := by simp [nbr,pr,avg,tot]
  rw [hp]
  simp_rw [hp]
  exact (pr_mono (fun _ => zero_le_one) h).trans (pr_exists_le (fun _ => zero_le_one) q)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] [DecidableEq J] in
theorem mul_factor (M : Mat I J) (r : ℕ) (h : M.rank ≤ r) :
    ∃ A : Mat I (Fin r),∃ B : Mat (Fin r) J,A*B=M := by
  obtain ⟨A,B,_,_,hg⟩ := rank_product M
  obtain ⟨a,ha⟩ := pad_matrix_inj M.rank r h
  obtain ⟨b,hb⟩ := mat_left_inv ha
  refine ⟨A*b,a*B,?_⟩
  rw [←Matrix.mul_assoc,Matrix.mul_assoc A b,hb,Matrix.mul_one,hg]

theorem nbr_matrix_rank (k : ℕ) :
    nbr (fun M : Mat I J => M.rank ≤ k) ≤ bp ((num I+num J)*k) := by
  classical
  let v := Mat I (Fin k) × Mat (Fin k) J
  let q (x : Mat I (Fin k) × Mat (Fin k) J) (M : Mat I J) := x.1*x.2=M
  refine (nbr_le_sum _ q fun M h => ?_).trans_eq ?_
  · obtain ⟨A,B,hB⟩ := mul_factor M k h
    exact ⟨(A,B),hB⟩
  have h (x : Mat I (Fin k) × Mat (Fin k) J) : nbr (q x) = 1 := by
    unfold nbr tot
    rw [Finset.sum_eq_single (x.1*x.2)]
    · simp [q,ind]
    · intro j _ h; simp [q,ind,h.symm]
    · simp
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,mul_one]
  change num (Mat I (Fin k) × Mat (Fin k) J)=_
  rw [num,Fintype.card_prod,Nat.cast_mul]
  change num (Mat I (Fin k))*num (Mat (Fin k) J)=_
  rw [cast_mat,cast_mat,← bp_add]
  simp [num]
  ring_nf

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem wsign_add (x y : F) : wsign (x+y) = wsign x * wsign y := by
  rcases bit_cases x with h|h <;> rcases bit_cases y with g|g <;>
    simp [h,g,char_two]

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

variable {A B V W : Type} [Fintype A] [Fintype B]

theorem avg_prod (w f g : Wgt A) :
    avg w f * avg w g = avg (pairW w w) (fun x => f x.1*g x.2) := (pairW_separate ..).symm

variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [Fintype V] [Fintype W]

/-- Walsh orthogonality via a translation of the uniform measure. -/
theorem wsign_lin (b : V →ₗ[F] F) : avg unif (fun x => wsign (b x)) = ind (b=0) := by
  classical
  by_cases h : b = 0
  · simp only [h,LinearMap.zero_apply,wsign_zero]
    simpa using unif_law.avg_const _
  obtain ⟨x,hx⟩ : ∃ x, b x=1 := by
    by_contra! hg
    exact h (LinearMap.ext fun x => (bit_cases _).resolve_right (hg x))
  let E : V ≃ V := ⟨(·+x),(·+x),add_polar x,add_polar x⟩
  have he := avg_bij E unif (fun x => wsign (b x))
  change avg unif (fun z => wsign (b (z+x))) = _ at he
  simp_rw [map_add,wsign_add,hx,wsign_one] at he
  rw [avg_mul] at he
  rw [ind_zero h]
  linarith only [he]

omit [Fintype V] in
theorem avg_ws (b : V →ₗ[F] W →ₗ[F] F) (x z : V) :
    avg unif (fun w => wsign (b x w)*wsign (b z w)) = ind (b x=b z) := by
  simp_rw [← wsign_add]
  change avg unif (fun w => wsign ((b x+b z) w)) = _
  rw [wsign_lin]
  apply congrArg ind
  exact propext (by rw [← ZModModule.sub_eq_add,sub_eq_zero])

/-- Unnormalized inner mean square identity. -/
theorem avg_wsq (b : V →ₗ[F] W →ₗ[F] F) (v f : Wgt V) :
    avg unif (fun w => (avg v (fun x => f x*wsign (b x w)))^2) =
      avg (pairW v v) (fun x => f x.1 * f x.2 * ind (b x.1=b x.2)) := by
  simp_rw [pow_two,avg_prod]
  rw [avg_avg]
  refine avg_congr fun ⟨x,z⟩ _ => ?_
  simp_rw [mul_mul_mul_comm (f x) _ (f z)]
  rw [avg_mul',avg_ws]

/-- Min-entropy form, squared. -/
theorem walsh_mass (b : V →ₗ[F] W →ₗ[F] F) (hb : Function.Injective b) (u : Wgt V) (v : Wgt W)
    (f : Wgt V) (g : Wgt W)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) (hu : SubLaw u) (hv : SubLaw v)
    {p q : ℝ} (hp : ∀ x, u x ≤ p) (hq : ∀ x, v x ≤ q) :
    (avg v (fun w => g w * avg u (fun x => f x*wsign (b x w))))^2 ≤
      (Fintype.card W : ℝ)*p*q := by
  classical
  let F w := avg u (fun x => f x*wsign (b x w))
  have hi {A : Type} [Fintype A] {p : ℝ} (h : 0 ≤ p) (v f : Wgt A) (hw : SubLaw v)
      (hh : ∀ x, v x ≤ p) (hg : ∀ x, |f x|≤1) : ∑ x, (v x*f x)^2 ≤ p := by
    have hr x : (v x*f x)^2 ≤ v x*p := calc
      _ = v x^2*f x^2 := mul_pow _ _ _
      _ ≤ v x^2*1 := by
        have he := abs_le.mp (hg x)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [he.1,he.2]
      _ ≤ _ := by rw [mul_one,pow_two]; exact mul_le_mul_of_nonneg_left (hh x) (hw.nz x)
    exact (Finset.sum_le_sum (fun x _ => hr x)).trans (hw.avg_le h (f:=fun _ => p) (fun _ => le_rfl))
  have hh1 := hi ((hv.nz 0).trans (hq 0)) v g hv hq hg
  have hh2 := hi ((hu.nz 0).trans (hp 0)) u f hu hp hf
  have heq : avg (pairW u u) (fun x : V×V => f x.1*f x.2*ind (b x.1=b x.2)) =
      ∑ x, (u x*f x)^2 := by
    rw [pairW_avg]; unfold avg
    refine Finset.sum_congr rfl fun x _ => ?_
    have h z : (b x=b z) ↔ x=z := hb.eq_iff
    simp [h,ind]
    ring
  have hW : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh3 : ∑ w, F w^2 ≤ (Fintype.card W : ℝ)*p := by
    rw [mul_comm]
    apply (div_le_iff₀ hW).mp
    calc _ = avg unif (fun w => F w^2) := by simp only [avg,unif_apply,← Finset.mul_sum];
                                              rw [div_eq_mul_inv,mul_comm]
         _ ≤ _ := (avg_wsq b u f).le.trans (heq.le.trans hh2)
  calc
    _ = (∑ w, (v w*g w)*F w)^2 := by simp only [mul_assoc]; rfl
    _ ≤ (∑ w, (v w*g w)^2) * ∑ w, (F w)^2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := by rw [mul_comm _ q]; exact mul_le_mul hh1 hh3
                  (Finset.sum_nonneg fun _ _ => sq_nonneg _) ((hv.nz 0).trans (hq 0))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImageCharacterBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image Character Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

variable {r : Place p→ℕ}

theorem tuple_dim :
    dim (DTuple (p:=p) r N)=N*∑ z : Place p,r z := by
  unfold DTuple dim
  rw [finrank_pi_fintype,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (dim_mat _ _).trans (by simp)

variable {I J : Type} [Fintype I] [Fintype J]
theorem mpair_nondeg (M : Mat I J) (h : mpair M=0) : M=0 := by
  classical
  apply evmat_ext; intro x y
  rw [←mpair_outer,h]; simp [evmat]

theorem tupleB_val (x y : DTuple (p:=p) r N) :
    tupleB p r N x y=∑ z,mpair (x z) (y z) := by
  simp only [tupleB,LinearMap.sum_apply,LinearMap.coe_mk,AddHom.coe_mk]; rfl

theorem tupleB_inj (p : Shape) (r : Place p→ℕ) (N : ℕ) :
    Function.Injective (tupleB p r N) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  refine le_bot_iff.mp (fun x hx => ?_)
  change tupleB p r N x = 0 at hx
  have hh (z : Place p) : mpair (x z)=0 := by
    refine LinearMap.ext (fun M => ?_)
    have he := LinearMap.congr_fun hx (Pi.single z M)
    rw [tupleB_val,Finset.sum_eq_single z] at he
    · rwa [Pi.single_eq_same] at he
    · intro i _ hi; simp [hi]
    simp
  have h' : x=0 := funext fun z => mpair_nondeg _ (hh z)
  rw [h']; exact Submodule.zero_mem _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentPhaseBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Phase Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {J K : Type} [Fintype J] [Fintype K]

private theorem perm_pair (A B : Mat J K) (M : Mat J J) :
    mpair (A*Bᵀ) M=mpair (M*B) A := by

  change (A*Bᵀ*Mᵀ).trace=(M*B*Aᵀ).trace

  rw [← Matrix.trace_transpose (M*B*Aᵀ),Matrix.transpose_mul,Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.mul_assoc]

variable [DecidableEq J] [DecidableEq K]

private theorem iid_prodM (M : Mat J J) :
    avg (pairW (unif : Wgt (Mat J K)) unif) (fun x => wsign (mpair (x.2*x.1ᵀ) M)) =
      bp (- (M.rank:ℝ) * num K) := by
  classical
  rw [pairW_avg]
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product M
  have he (y : Mat J K) :
      avg unif (fun a : Mat J K => wsign (mpair (a*yᵀ) M)) = ind (B*y=0) := by
    have ht : mpair (M*y)=0 ↔ B*y=0 := by
      rw [ show M*y=A*B*y from congrArg (·*y) hM.symm,Matrix.mul_assoc]
      constructor
      · intro h
        have he := mpair_nondeg _ h
        exact matrix_cancel_left hA (B*y) 0 (he.trans (Matrix.mul_zero A).symm)
      intro h
      rw [h,Matrix.mul_zero]
      exact LinearMap.ext fun x => by rw [mpair_comm,map_zero,LinearMap.zero_apply]
    simp_rw [perm_pair,wsign_lin]
    rw [ht]
  change avg unif (fun y => avg unif _) = _
  refine Eq.trans (congrArg (avg unif) (funext he)) ?_
  change pr unif _ = _
  have hf : pr unif (fun y : Mat J K => B*y=0)=bp (-num (Fin M.rank)*num K) := by
    have hx : Function.Injective Bᵀ.mulVec :=
      transpose_surj_iff.mp (by rw [transpose_transpose]; exact hB)
    simpa only [Matrix.transpose_transpose] using
      pr_gram_fixed hx (0:Mat (Fin M.rank) K)
  rw [hf,num,Fintype.card_fin]

omit [Fintype J] in
theorem wsign_sum (s : Finset J) (f : J → F) :
    wsign (∑ i∈s,f i)=∏ i∈s,wsign (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih => rw [Finset.sum_insert h,Finset.prod_insert h,wsign_add,ih]

theorem lawH_law (p : Shape) (N : ℕ) : IsLaw (lawH p N) :=
  prodW_law (fun _ => pairW_law unif_law unif_law)

theorem lawH_phased (x : Ambient p N) :
    avg (lawH p N) (fun y => wsign (uPhase p y x)) = bp (- (p.h:ℝ) * epoch p x) := by
  classical
  let w (i : Comp p.g) := (pairW unif unif : Wgt (HFrame p N))
  let f (i : Comp p.g) (x' : HFrame p N) := wsign (mpair (x'.2*x'.1ᵀ) (x i))
  have hh y : wsign (uPhase p y x)= prodW f y := by
    rw [uPhase,LinearMap.sum_apply, wsign_sum]; rfl
  change avg (prodW w) _ = _
  simp_rw [hh]
  rw [prodW_avg]
  have hg i : avg (w i) (f i)=bp (- (p.h:ℝ)*(x i).rank) := by
    change avg (pairW unif unif) _ = _
    refine (iid_prodM (x i) (K:=Chan p)).trans ?_
    congr 1
    simp only [Chan,num,Fintype.card_fin]
    ring
  simp_rw [hg]
  rw [←bp_sum,←Finset.mul_sum,←Nat.cast_sum,epoch]

theorem freeH_law (p : Shape) (N : ℕ) : IsLaw (freeH p N) :=
  pairW_law (lawH_law p N) (lawH_law p N)

set_option maxHeartbeats 800000 in
theorem free_phase {S : Party} (x : Ambient p N) (h : S≠0) :
    let Q := avg (freeH p N) (fun y => wsign (joinPhase p y S x));
    0 ≤ Q ∧ Q ≤ bp (- (p.h:ℝ)* epoch p x) := by
  classical
  let T (b : F) := avg (lawH p N) (fun y => wsign (b*uPhase p y x))
  have he :
      avg (freeH p N) (fun y => wsign (joinPhase p y S x))=T (S true)*T (S false) := by
    have hh y :
        wsign (joinPhase p y S x)=
          wsign (S true*uPhase p y.1 x)*wsign (S false*uPhase p y.2 x) := by
      rw [joinPhase, Fintype.sum_bool,LinearMap.add_apply,wsign_add]
      rfl
    simp_rw [hh]
    exact pairW_separate (lawH p N) (fun y => wsign (S true*uPhase p y x))
      (lawH p N) (fun y => wsign (S false*uPhase p y x))
  rw [he]
  let B := bp (- (p.h:ℝ) * epoch p x)
  have h0 : T 0=1 := by
    unfold T; simp only [zero_mul,wsign_zero, (lawH_law p N).avg_const]
  have h1 : T 1=B := by unfold T; simp only [one_mul,lawH_phased,B]
  have hz : 0≤ B := (bp_pos _).le
  have hl : B ≤1 := by
    unfold B
    rw [←bp_zero]
    exact bp_le (mul_nonpos_of_nonpos_of_nonneg (by simp) (Nat.cast_nonneg _))
  rcases bit_cases (S true) with hT|hT <;>
    rcases bit_cases (S false) with hF|hF <;> rw [hT,hF]
  · exact (h (by funext i; cases i <;> assumption)).elim
  · rw [h0,h1,one_mul]; exact ⟨hz,le_rfl⟩
  · rw [h1,h0,mul_one]; exact ⟨hz,le_rfl⟩
  rw [h1]; exact ⟨mul_nonneg hz hz,(mul_le_mul_of_nonneg_left hl hz).trans_eq (mul_one B)⟩

/-- cap for channel cube pair from joint raw -/
theorem phase_cap {w : Wgt (UnitType p n N)} {c : ℝ} (hc : 0 ≤ c)
    (m : Mixer p n)
    (h : ∀ x,w x ≤ c*pairW (raw m N) (raw m N) x)
    (hN : 2*num (Full p n)-N≤ -1) (y : PhasePair p N) :
    mapW w (listens p) y ≤ c*chanPrice p^2 * freeH p N y := by
  refine (mapW_cap h (listens p) _).trans ?_
  unfold listens
  simp only [map_pair_law]
  have hz (x) : 0 ≤ mapW (raw m N) (hcube p) x := pr_nonneg (raw_nonneg m)
  calc c*pairW _ _ y
    _ ≤ c*((chanPrice p*lawH p N y.1)*(chanPrice p*lawH p N y.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (hcube_cap m hN y.1) (hcube_cap m hN y.2)
        (hz _) ((hz _).trans (hcube_cap m hN y.1))) hc
    _ = _ := by unfold freeH pairW; ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetLifting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Lifting -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Submodule Module Finset Function
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

omit [Fintype I] in
theorem col_follow (A : Mat I J) (B : Mat J K) :
    colSp (A*B) ≤ colSp A := by
  rw [colSp,Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range ..

omit [Fintype I] in
theorem col_retain {A : Mat I J} {B : Mat J K} (h : Surjective B.mulVec) :
    colSp (A*B)=colSp A := by
  rw [colSp,Matrix.mulVecLin_mul,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (show Surjective B.mulVecLin from h),Submodule.map_top,colSp]

private theorem trans_surj {A : Mat I J} (hA : Surjective A.mulVec) : Injective Aᵀ.mulVec :=
  transpose_surj_iff.mp (by rwa [Matrix.transpose_transpose])

omit [Fintype I] in
theorem pull_cols (A : Mat I J) (B : Mat I K) (h : colSp B ≤ colSp A) :
    ∃ Q : Mat J K,A*Q=B := by
  classical
  have hf (i : K) : B.col i ∈ colSp A := h (colSp_mem i)
  choose v hv using show ∀ (i:K),∃ v : Vec J,A *ᵥ v = B.col i from hf
  refine ⟨Matrix.of (fun i j => v j i),?_⟩
  ext i j
  exact congr_fun (hv j) i

variable [DecidableEq I]

theorem chop_inj_pack {S : Space (Vec I)} {T : Mat I J} (h : Injective T.mulVec)
    (he : Disjoint S (colSp T)) :
    Injective (chop S*T).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  rw [← Matrix.mulVec_mulVec] at hx
  have hh : T *ᵥ x∈S⊓colSp T := ⟨(chop_ker ..).mp hx,⟨_,rfl⟩⟩
  rw [he.eq_bot,Submodule.mem_bot] at hh
  exact h (hh.trans (Matrix.mulVec_zero T).symm)

private theorem frame_image_lift {S T : Space (Vec I)} {A : Mat I J}
    (h : colSp A ≤ chopSpace S T) :
    ∃ A' : Mat I J,colSp A'≤T ∧ chop S * A'=A := by
  classical
  have hf : chopSpace S T=colSp (chop S*pack T) := by
    rw [chopSpace,colSp,Matrix.mulVecLin_mul,LinearMap.range_comp,
      show LinearMap.range (pack T).mulVecLin=_ from colSp_pack T]
  obtain ⟨V,hV⟩ := pull_cols (chop S*pack T) A (hf ▸ h)
  refine ⟨pack T*V,(col_follow ..).trans_eq (colSp_pack T),?_⟩
  rw [←Matrix.mul_assoc,hV]

private theorem projected_unique {M V : Space (Vec I)} {M' V' : Space (Vec I)}
    (h : Disjoint M M') (h' : Disjoint V V') (A B : Mat I I)
    (hA : A∈ box M' V') (hB : B∈box M' V')
    (hf : liftM (chop M) (chop V) A=liftM (chop M) (chop V) B) :
    A=B := by
  classical
  obtain ⟨A,rfl⟩ := hA
  obtain ⟨B,rfl⟩ := hB
  have he := chop_inj_pack (S:=M) (pack_inj M') (by rw [colSp_pack]; exact h)
  have he' := chop_inj_pack (S:=V) (pack_inj V') (by rw [colSp_pack]; exact h')
  rw [liftM_comp,liftM_comp] at hf
  rw [liftM_inj he he' hf]

private theorem frame_extend (M : Mat I I) (S T V W : Space (Vec I)) (A B : Mat I K)
    (hV : M ∈ box V W)
    (hx : Disjoint S V) (hy : Disjoint T W)
    (hA : Injective A.mulVec) (hB : Injective B.mulVec)
    (he : liftM (chop S) (chop T) M=A*Bᵀ) :
    ∃ X Y : Mat I K,
      FrameProduct M V W X Y ∧ chop S*X=A ∧ chop T*Y=B := by
  classical
  have heq : A*Bᵀ ∈box (chopSpace S V) (chopSpace T W) := he ▸ lift_mem_box _ _ hV
  obtain ⟨hL,hH⟩ := (box_mem ..).mp heq
  rw [col_retain (transpose_surj_iff.mpr hB)] at hL
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,col_retain (transpose_surj_iff.mpr hA)] at hH
  obtain ⟨X,hX,hZ⟩ := frame_image_lift hL
  obtain ⟨Y,hY,hU⟩ := frame_image_lift hH
  have hi {A B : Mat I K} (f : Mat I I)
      (h : f*A=B) (hB : Injective B.mulVec) : Injective A.mulVec := by
    rw [←h] at hB
    intro x y he
    apply hB
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,he]
  refine ⟨X,Y,⟨hi _ hZ hA,hi _ hU hB,hX,hY,?_⟩,hZ,hU⟩
  refine projected_unique hx hy _ _ ((box_mem ..).mpr ⟨(col_follow ..).trans hX,?_⟩) hV ?_
  · rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    exact (col_follow ..).trans hY
  rw [he,liftM_def,←hU,←hZ,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem frame_products (M : Bool → Mat I I) (S T : Space (Vec I))
    (a b : Bool → Space (Vec I))
    (h : ∀ i,M i∈box (a i) (b i)) (hg : vanish S T (M true+M false))
    (ha : ∀ i,Disjoint S (a i)) (hb : ∀ i,Disjoint T (b i)) :
    ∃ X Y : Bool → Mat I (Fin (M true).rank), (∀ i,FrameProduct (M i) (a i) (b i) (X i) (Y i)) ∧
      chop S*X true=chop S*X false ∧ chop T*Y true=chop T*Y false := by
  classical
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product (M true)
  let C := Bᵀ
  have hC : Injective C.mulVec := trans_surj hB
  obtain ⟨hL,hR⟩ := (box_mem ..).mp (h true)
  rw [← hM,col_retain hB] at hL
  rw [←hM,Matrix.transpose_mul,col_retain (transpose_surj_iff.mpr hA)] at hR
  have hf : liftM (chop S) (chop T) (M true)= (chop S*A)*(chop T*C)ᵀ := by
    rw [liftM_def,Matrix.transpose_mul, show Cᵀ=B from rfl,Matrix.mul_assoc,Matrix.mul_assoc (chop S),← Matrix.mul_assoc A,
      hM]
  obtain ⟨P,Q,hP,hQ,hF⟩ := frame_extend (M false) S T (a false) (b false)
    (chop S*A) (chop T*C) (h false) (ha false) (hb false)
    (chop_inj_pack hA (Disjoint.mono_right hL (ha true)))
    (chop_inj_pack hC (Disjoint.mono_right hR (hb true))) (by
      have he := (vanish_chop _).mp hg
      rw [map_add] at he
      rw [←hf]
      exact add_left_cancel (he.trans (char_two _).symm))
  refine ⟨onSide (A,P), onSide (C,Q),fun i => ?_,hQ.symm,hF.symm⟩
  cases i
  · exact hP
  exact ⟨hA,hC,hL,hR,hM⟩

private theorem diff_into (a : Bool → Mat I J) (S : Space (Vec I))
    (h : chop S*a true=chop S*a false) :
    ∃ (k : ℕ) (P : Mat (Fin (dim S)) (Fin k)) (B : Mat (Fin k) J),
      k≤Fintype.card J ∧ Injective (pack S * P).mulVec ∧ Surjective B.mulVec ∧
      a true+a false=(pack S*P)*B := by
  classical
  let X := a true+a false
  obtain ⟨A,B,hA,hB,hX⟩ := rank_product X
  have hi : colSp X≤S := by
    rintro x ⟨y,rfl⟩
    apply (chop_ker ..).mp
    rw [mulVecLin_apply,Matrix.mulVec_mulVec,show X=_+_ from rfl,Matrix.mul_add,h,char_two,
      Matrix.zero_mulVec]
  obtain ⟨P,hP⟩ := pull_cols (pack S) A (by rw [← col_retain hB,hX,colSp_pack]; exact hi)
  refine ⟨X.rank,P,B,X.rank_le_card_width,?_,hB,?_⟩
  · rw [hP]; exact hA
  rw [hP,hX]

/-- δ expansion at one component: S*T offsets bases plus paired
companions Z for either reference endpoint. Cost recorded in actual
offset widths kp/km and kernel matrices. -/
theorem one_offsets (M : Bool → Mat I I) (S T : Space (Vec I))
    (a b : Bool → Space (Vec I))
    (h : ∀ i,M i∈box (a i) (b i)) (hg : vanish S T (M true+M false))
    (ha : ∀ i,Disjoint S (a i)) (hb : ∀ i,Disjoint T (b i)) :
    ∃ (kp km : ℕ) (A : Mat (Fin (dim S)) (Fin kp)) (B : Mat (Fin (dim T)) (Fin km))
      (H : Mat (Fin kp) (Fin km)),
      let X := pack S * A
      let Y := pack T * B
      kp≤(M true).rank ∧ km≤ (M true).rank ∧ Injective X.mulVec ∧ Injective Y.mulVec ∧
      ∀ i,∃ (Z : Mat I (Fin kp)) (W : Mat I (Fin km)), Injective Z.mulVec ∧ Injective W.mulVec ∧
        colSp Z≤ b i ∧ colSp W≤ a i ∧ M true+M false=X*Zᵀ+W*Yᵀ+X*H*Yᵀ := by
  classical
  obtain ⟨P,Q,hP,hQ,hF⟩ := frame_products M S T a b h hg ha hb
  obtain ⟨k,A,E,hk,hA,hE,hX⟩ := diff_into P S hQ
  obtain ⟨k',B,D,hk',hB,hD,hY⟩ := diff_into Q T hF
  rw [Fintype.card_fin] at hk hk'
  let X := pack S * A
  let Y := pack T * B
  refine ⟨k,k',A,B,E*Dᵀ,hk,hk',hA,hB,fun i => ?_⟩
  let V := P i
  let U := Q i
  have ht : M true+M false=M i+M (!i) := by cases i; exact add_comm _ _; rfl
  have hx : P (!i) = V+X*E := by
    rw [show X*E=P true+P false from hX.symm]
    cases i
    · change P true=P false+(P true+P false); rw [add_left_comm,char_two,add_zero]
    · change P false=P true+(P true+P false); rw [←add_assoc,char_two,zero_add]
  have hy : Q (!i)=U+Y*D := by
    rw [show Y*D=Q true+Q false from hY.symm]
    cases i
    · change Q true=Q false+(Q true+Q false); rw [add_left_comm,char_two,add_zero]
    · change Q false=Q true+(Q true+Q false); rw [←add_assoc,char_two,zero_add]
  refine ⟨U*Eᵀ,V*Dᵀ,inj_comp_mat _ _ (hP i).yin (trans_surj hE),
    inj_comp_mat _ _ (hP i).xin (trans_surj hD), (col_follow ..).trans (hP i).ycol,
    (col_follow ..).trans (hP i).xcol,?_⟩

  have hm :
      M true+M false=V*Uᵀ+(V+X*E)*(U+Y*D)ᵀ := ht.trans (congrArg₂ (· + ·)
    (hP i).prod.symm ((hP (!i)).prod.symm.trans (congrArg₂ (· * ·) hx
      (congrArg Matrix.transpose hy))))
  apply hm.trans
  change _=X * _ + _ * Yᵀ+ X * _ * Yᵀ
  simp only [transpose_add,transpose_mul,transpose_transpose,Matrix.add_mul,Matrix.mul_add,
    Matrix.mul_assoc,add_assoc]
  calc _ = (V*Uᵀ + V*Uᵀ) + (X * (E * Uᵀ) + (V * (Dᵀ*Yᵀ) + X * (E * (Dᵀ*Yᵀ)))) := by abel
       _ = _ := by rw [char_two,zero_add]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetRecords
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Records -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}

theorem mr_box (m : BMark p n N) (x) (i) (e : Comp p.g) :
    mrAmbient m x i e∈box (imageP p x i (e,true)) (imageP p x i (e,false)) := by
  let P := fpAt p (onSide x i) (e,true)
  let Q := fpAt p (onSide x i) (e,false)
  change liftM P Q _∈box (colSp P) (colSp Q)
  rw [box_mem,liftM_transpose]
  exact ⟨colSp_lift_le .., colSp_lift_le ..⟩

variable {S : Cov p N}

private theorem join_order (p : Shape) {N r} (g : Ambient p N)
    (q p' : Comp p.g → ℕ) (hyp : ∀ e, q e≤ (g e).rank) (hyp' : ∀ e,p' e ≤ (g e).rank)
    (h : epoch p g ≤ r) :
    ∃ ω : Wide p r, (∀ e,(ω (e,true)).val=q e) ∧ (∀ e,(ω (e,false)).val=p' e) ∧
      (∑ z,(ω z).val) ≤2*r := by
  classical
  have ht (e) : (g e).rank ≤ r :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le ((g i).rank)) (Finset.mem_univ e)).trans h
  let Q := fun e => (⟨q e,Nat.lt_succ_of_le ((hyp e).trans (ht e))⟩ : Fin (r+1))
  let P := fun e => (⟨p' e,Nat.lt_succ_of_le ((hyp' e).trans (ht e))⟩ : Fin (r+1))
  let ω : Wide p r := fun x => if x.2 then Q x.1 else P x.1
  refine ⟨ω,fun _ => rfl, fun _ => rfl,?_⟩
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Finset.sum_add_distrib]
  rw [two_mul]
  exact Nat.add_le_add ((Finset.sum_le_sum fun i _ => hyp i).trans h)
    ((Finset.sum_le_sum fun i _ => hyp' i).trans h)

set_option maxHeartbeats 800000 in
theorem delta_offset (m : BMark p n N) (x)
    (h : covered p S (delta m x))
    (hz : delta m x ≠0)
    (hs : ∀ i z,Disjoint (S z) (imageP p x i z))
    (hr : epoch p (mrAmbient m x true) ≤ r) :
    ∃ X : Atlas p r S,standard X ∧ ∀ i,∃ A,compFor X A (imageP p x i) (delta m x) := by
  classical
  choose q p' A B H hT using fun e : Comp p.g =>
    one_offsets (fun i => mrAmbient m x i e) (S (e,true)) (S (e,false))
      (fun i => imageP p x i (e,true)) (fun i => imageP p x i (e,false))
      (fun i => mr_box m x i e)
      ((covered_iff ..).mp h e)
      (fun i => hs i _) (fun i => hs i _)
  obtain ⟨g,hg,hG,hS⟩ := join_order p (mrAmbient m x true) q p'
    (fun i => (hT i).1) (fun i => (hT i).2.1) hr

  have ht (e : Comp p.g) :
      ∃ (A' : Mat (Fin (dim (S (e,true)))) (Fin (g (e,true)).val))
        (B' : Mat (Fin (dim (S (e,false)))) (Fin (g (e,false)).val))
        (H' : Mat (Fin (g (e,true)).val) (Fin (g (e,false)).val)),
        let X := pack (S (e,true)) * A'
        let Y := pack (S (e,false))* B'
        Injective X.mulVec ∧ Injective Y.mulVec ∧
        ∀ i : Bool,∃ (Z : Mat (Fin N) (Fin (g (e,true)).val)) (W : Mat (Fin N) (Fin (g (e,false)).val)),
          Injective Z.mulVec ∧ Injective W.mulVec ∧
          colSp Z≤ imageP p x i (e,false) ∧ colSp W≤ imageP p x i (e,true) ∧
          delta m x e=X*Zᵀ+W*Yᵀ+X*H'*Yᵀ := by
    rw [hg,hG]
    exact ⟨A e,B e,H e,(hT e).2.2⟩
  choose A' B' H' hL hR hyp using fun e => by simpa only using ht e
  let X : Atlas p r S := ⟨g, (fun z => match z with
    | ⟨e,true⟩ => A' e
    | ⟨e,false⟩ => B' e),H'⟩
  have he (i) : ∃ Z,compFor X Z (imageP p x i) (delta m x) := by
    choose Z W hZ hW hC hD hJ using fun e => hyp e i
    refine ⟨(fun z => match z with | ⟨e,true⟩ => Z e | ⟨e,false⟩ => W e),?_,funext fun e => ?_⟩
    · rintro ⟨e,c|c⟩
      · exact ⟨hW e,hD e⟩
      exact ⟨hZ e,hC e⟩
    exact hJ e
  refine ⟨X,⟨?_,hS,?_⟩,he⟩
  · intro hc
    have h1 (z) : breadth X z = 0 := Nat.eq_zero_of_le_zero
      (show _≤0 from le_trans
        (Finset.single_le_sum (fun z _ => Nat.zero_le (breadth X z)) (Finset.mem_univ z))
        hc.le)
    obtain ⟨A,_,hA⟩ := he true
    apply hz
    rw [hA]
    funext e
    let (z : Place p) : IsEmpty (Fin (breadth X z)) := by rw [h1]; infer_instance
    unfold spelled edgeCost
    ext
    simp only [liftM_def,Matrix.add_apply,Matrix.mul_apply]
    change _ = 0

    simp
  · rintro ⟨e,c|c⟩
    · exact hR e
    exact hL e

/-- Capturing offsets suffices to cover the tensor. -/
theorem covered_spelled (X : Atlas p r S) (A) (T : Cov p N) (he : offsetCov X ≤ T) :
    covered p T (spelled X A) := by
  apply (cover_mem ..).mpr
  intro e
  let P := src X (e,true)
  let Q := src X (e,false)
  have h : ∀ V : Mat (Fin (breadth X (e,true))) (Fin N), P*V∈box (T (e,true)) ⊤ :=
    fun V => (box_mem ..).mpr ⟨(col_follow ..).trans (he _),le_top⟩
  have h' (V : Mat (Fin N) (Fin (breadth X (e,false)))) :
      V*Qᵀ ∈box ⊤ (T (e,false)) := by
    rw [box_mem,transpose_mul,transpose_transpose]
    exact ⟨le_top,(col_follow ..).trans (he _)⟩
  unfold spelled
  refine Submodule.add_mem _ (add_mem_sup (h _) (h' _)) (Submodule.mem_sup_left ?_)
  unfold edgeCost
  rw [liftM_def,Matrix.mul_assoc]
  exact h _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetEnergy
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Energy -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}
variable {q t : Place p→ℕ} {S : Cov p N}

theorem heat_flip (p : Shape) {n N} (x : UnitType p n N) (v : Party) (z : Place p) :
    (heat p x v (flipZ p z))ᵀ=heat p x v z := by
  simp only [heat,Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,flipZ_flip]

theorem heat_unary (x : UnitType p n N) (i) (z : Place p) :
    heat p x (unary i) z=fyAt p (onSide x i) z * (fyAt p (onSide x i) (flipZ p z))ᵀ := by
  rw [heat,Finset.sum_eq_single i]
  · simp [unary]
  · intro j _ hj; simp [unary,hj]
  simp

theorem fuse_val (x : UnitType p n N) (v : Party) (A : DTuple (p:=p) q N) (z : Place p) :
    images x z * hfused p n q (sparks p x v A) z=thermal p x v A z := by
  classical
  unfold hfused thermal heat sparks
  rw [Fintype.sum_bool,Fintype.sum_bool]
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add]
  have he (i : Bool) :
      images x z * (IH p n i * ((fyAt p (onSide x i) (flipZ p z))ᵀ * A z))=
        fyAt p (onSide x i) z*(fyAt p (onSide x i) (flipZ p z))ᵀ * A z := by
    rw [← Matrix.mul_assoc (images x z),images_ih]
    change _ * (_ * _) = _ * _ * _
    exact (Matrix.mul_assoc ..).symm
  rw [he,he]

theorem fused_support (B : Bool→DTuple (p:=p) q p.h) (z : Place p) :
    colSp (hfused p n q B z) ≤ channels p n := by
  unfold hfused
  rw [Fintype.sum_bool]
  rintro x ⟨y,rfl⟩
  rw [mulVecLin_apply,Matrix.add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  exact Submodule.add_mem _ (ih_le_channels true ⟨_,rfl⟩) (ih_le_channels false ⟨_,rfl⟩)

theorem fused_inj (A : Bool→DTuple (p:=p) q p.h) (z : Place p) (i : Bool)
    (h : Injective (A i z).mulVec) :
    Injective (hfused p n q A z).mulVec := by
  have hh : (IH p n i)ᵀ*hfused p n q A z=A i z := by
    unfold hfused
    rw [Fintype.sum_bool,Matrix.mul_add]
    simp only [← Matrix.mul_assoc]
    cases i <;>
      simp only [IH_self,IH_cross (show false≠true by decide),IH_cross (show true≠false by decide),
        Matrix.zero_mul,Matrix.one_mul,add_zero,zero_add]
  intro x y hx
  apply h
  rw [←hh, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,hx]

theorem hotfused (x : UnitType p n N) (v : Party) (A : DTuple (p:=p) q N)
    (i : Bool) (h : v i=1) (hh : glimpse p x i A) (z) :
    Injective (hfused p n q (sparks p x v A) z).mulVec := by
  refine fused_inj _ _ i ?_
  unfold sparks; rw [h,one_smul]
  exact hh z

theorem tone_heat (x : UnitType p n N) (v : Party) (T : Ambient p N) :
    tone p x v T = ∑ e : Comp p.g, mpair (heat p x v (e,false)) (T e) := by
  classical
  simp only [tone,joinPhase,uPhase,heat,mpair_sum,mpair_smul,LinearMap.sum_apply,
    LinearMap.comp_apply,LinearMap.smul_apply,smul_eq_mul,mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  cases i <;> rfl

variable {I J : Type} [Fintype I] [Fintype J]

private theorem trace_shift_l (M : Mat I I) (A V : Mat I J) :
    mpair M (A*Vᵀ)=mpair V (Mᵀ*A) := by
  rw [mpair_comm V]
  change (M*(A*Vᵀ)ᵀ).trace=((Mᵀ*A)* Vᵀ).trace
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,
    ←Matrix.trace_transpose ((Mᵀ*A) * Vᵀ),Matrix.transpose_mul,Matrix.transpose_mul,
      Matrix.transpose_transpose,Matrix.transpose_transpose,←Matrix.mul_assoc V,
      Matrix.trace_mul_comm _ M]

private theorem trace_shift_r (M : Mat I I) (A V : Mat I J) :
    mpair M (V*Aᵀ)=mpair V (M*A) := by
  rw [mpair_comm V]
  change (M*(V*Aᵀ)ᵀ).trace=((M*A)* Vᵀ).trace
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem tone_offset (x : UnitType p n N) (v : Party) (M : Atlas p r S) (A : Batch M N) :
    tone p x v (spelled M A)=tupleB p (breadth M) N A (thermal p x v (src M))+
      tone p x v (edgeCost M) := by
  rw [tone_heat,tone_heat,tupleB_val,Fintype.sum_prod_type]
  simp only [spelled,map_add,Finset.sum_add_distrib,Fintype.sum_bool]
  refine congrArg (fun z => z+_) (congrArg₂ (·+·) ?_ ?_)
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [trace_shift_l,show (heat p x v (e,false))ᵀ=heat p x v (e,true) from
      heat_flip p x v (e,true)]
    rfl
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [trace_shift_r]; rfl
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProbePointMasses
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probe Point Masses -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Submodule LinearMap Finset Function
variable {p : Shape} {n N : ℕ} {q t : Place p→ℕ}

theorem side_same {A : Type} [Fintype A] (i : Bool) (w : Wgt A) (hw : IsLaw w)
    (v : Wgt (A × A)) {H : ℝ}
    (h : ∀ x,mapW v (fun x => onSide x i) x≤H * w x)
    (P : A×A→Prop) (he : ∀ x y,onSide x i=onSide y i → (P x↔P y)) :
    pr v P ≤ H * pr (pairW w w) P := by
  classical
  let Q := fun x => P (x,x)
  have hq : P=fun x => Q (onSide x i) := by
    funext x; exact propext (he x _ (by cases i <;> rfl))
  rw [hq,←mapW_pr v (fun x => onSide x i) Q]
  refine (pr_cap h Q).trans_eq ?_
  have hh : pr (pairW w w) (fun x => Q (onSide x i)) = pr w Q := by
    cases i
    · change pr (pairW w w) (fun x => Q x.2)=pr w Q
      simpa only [true_and, pr_true,hw.total,one_mul] using pairW_pr w w (fun _ => True) Q
    change pr (pairW w w) (fun x => Q x.1)=pr w Q
    simpa only [and_true,pr_true,hw.total,mul_one] using pairW_pr w w Q (fun _ => True)
  rw [hh]

set_option maxHeartbeats 600000 in
theorem poke_cap (B : WTuple (p:=p) q n) (C : WTuple (p:=p) t n)
    (Z : DTuple (p:=p) q N) (A : DTuple (p:=p) t N)
    (m : Mixer p n) {ε : ℝ} (he : initCap p N m ε)
    (hB : ∀ z, Injective (B z).mulVec)
    (hC : ∀ z, Injective (C z).mulVec)
    (hD : ∀ z, Disjoint (colSp (B z)) (colSp (C (flipZ p z)))) :
    pr (pairW (raw m N) (raw m N)) (poke p B C Z A) ≤
      fee N ε (ctot p q+ctot p t) := by
  classical
  let μ := raw m N
  let w := pairW μ μ
  have hw (x) : 0 ≤ w x := mul_nonneg (raw_nonneg m _) (raw_nonneg m _)
  by_cases h : 0 < pr w (poke p B C Z A)
  · obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw h
    let U : Plan p n := fun z => colSp (B (flipZ p z)) ⊔ colSp (C z)
    let V := Pin.make U x
    refine (pr_mono hw (q:=V.agree) fun y hy => ?_).trans ((he V).trans ?_)
    · intro z v hv
      change images y z *ᵥ v=images x z *ᵥ v
      obtain ⟨l,⟨t,rfl⟩,r,⟨u,rfl⟩,rfl⟩ := Submodule.mem_sup.mp
        (show v∈colSp (B (flipZ p z))⊔colSp (C z) from hv)
      have h1 := (hx (flipZ p z)).1.trans (hy (flipZ p z)).1.symm
      simp only [flipZ_flip] at h1
      simp only [mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec,h1,
        (hx z).2,(hy z).2]
    · have hF (z) : dim (U z)=q (flipZ p z)+t z := by
        have hi := Submodule.finrank_sup_add_finrank_inf_eq (colSp (B (flipZ p z))) (colSp (C z))
        have hy := hD (flipZ p z)
        rw [flipZ_flip] at hy
        rw [hy.eq_bot,finrank_bot,add_zero] at hi
        exact hi.trans (congrArg₂ (·+·) ((mrk_inj.mp (hB (flipZ p z))).trans (Fintype.card_fin _))
          ((mrk_inj.mp (hC z)).trans (Fintype.card_fin _)))
      have ht : planRank V.sp=ctot p q+ctot p t := by
        unfold planRank ctot
        change ∑ z,dim (U z)= _
        simp_rw [hF,Finset.sum_add_distrib]
        exact congrArg (fun x => x + ∑ z,t z) (Equiv.sum_comp (flipEquiv p) q)
      rw [ht]
  exact (not_lt.mp h).trans (bp_pos _).le

private theorem format_size :
    num (Among p n q × (Bool → DTuple (p:=p) t p.h)) =
      bp (num (Row p n)*ctot p q+2*p.h*ctot p t) := by
  classical
  unfold num
  rw [card_space,dim,Module.finrank_prod, Nat.cast_add]
  have he : finrank F (Among p n q)=Fintype.card (Row p n)*ctot p q := by
    unfold Among
    rw [finrank_pi_fintype]
    unfold ctot; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => (dim_mat ..).trans (by rw [Fintype.card_fin])
  have hf :
      finrank F (Bool → DTuple (p:=p) t p.h)=2*p.h*ctot p t := by
    rw [finrank_pi_fintype,Fintype.sum_bool]
    change dim (DTuple ..)+dim (DTuple ..)=_
    rw [tuple_dim]
    unfold ctot; ring
  rw [he,hf]
  push_cast; rfl

set_option maxHeartbeats 800000 in
theorem heat_rate (i : Bool) (S : Party) (hi : S i=1)
    (A : DTuple (p:=p) t N)
    (B : DTuple (p:=p) t N) (Z : DTuple (p:=p) q N)
    (m : Mixer p n) {ε : ℝ} (he : initCap p N m ε) :
    pr (pairW (raw m N) (raw m N)) (fun x =>
      basisFrom p x i Z ∧ glimpse p x i A ∧ thermal p x S A=B)
      ≤ heatRate p n N ε (ctot p q) (ctot p t) := by
  classical
  let M := Among p n q × (Bool → DTuple (p:=p) t p.h)
  let P (v : M) (x : UnitType p n N) :=
    let X := csignal p i v.1
    let Y := hfused p n _ v.2
    (∀ z, Injective (X z).mulVec ∧ Injective (Y z).mulVec) ∧ poke p X Y Z B x
  let w := pairW (raw m N) (raw m N)
  have hw x : 0 ≤ w x := mul_nonneg (raw_nonneg m _) (raw_nonneg m _)
  have h : ∀ x : UnitType p n N,basisFrom p x i Z ∧ glimpse p x i A ∧ thermal p x S A=B →
      ∃ v, P v x := by
    rintro x ⟨hF,hT,hU⟩
    choose A' hA using fun z => pull_cols (fpAt p (onSide x i) (flipZ p z)) (Z z) (hF z).2
    let C := sparks p x S A
    let Y := hfused p n _ C
    let X := csignal p i A'
    have hh z : images x (flipZ p z)*X z=Z z := by
      unfold X csignal
      rw [← Matrix.mul_assoc, images_ip]
      exact hA z
    refine ⟨(A',C),fun z => ⟨?_,hotfused x S A i hi hT z⟩, fun z => ?_⟩
    · have hg := (hF z).1
      rw [← hh z] at hg
      intro p' q he
      apply hg
      change X z *ᵥ p' = X z*ᵥ q at he
      rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,he]
    exact ⟨hh z,(fuse_val x S A z).trans (congr_fun hU z)⟩
  have hg (v : M) :
      pr w (P v) ≤ fee N ε (ctot p q+ctot p t) := by
    let X := csignal p i v.1
    let Y := hfused p n _ v.2
    by_cases hh : ∀ z, Injective (X z).mulVec ∧ Injective (Y z).mulVec
    · refine (pr_mono hw (p:=P v) (q:=poke p X Y Z B) fun x h => h.2).trans
        (poke_cap X Y _ _ m he (fun z => (hh z).1) (fun z => (hh z).2) ?_)
      intro z
      exact (channels_disjoint (p:=p) (n:=n)).mono
        ((col_follow ..).trans (ip_le_primal i)) (fused_support v.2 _)
    have heq : P v=(fun _ => False) := funext fun x => propext (iff_false_intro (fun h => hh h.1))
    rw [heq,pr_false]; exact (bp_pos _).le
  refine ((pr_mono hw h).trans (pr_exists_le hw P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hg i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change num (Among p n q × _) *_= _
  rw [format_size]; rfl

theorem heat_one (i : Bool)
    (A : DTuple (p:=p) t N) (B : DTuple (p:=p) t N)
    (Z : DTuple (p:=p) q N)
    {w : Wgt (UnitType p n N)} {H : ℝ} (hH : 0 ≤ H)
    (m : Mixer p n) {ε : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hw : bySide p w m H) :
    pr w (fun x => basisFrom p x i Z ∧ glimpse p x i A ∧ thermal p x (unary i) A=B) ≤
      H*heatRate p n N ε (ctot p q) (ctot p t) := by
  refine (side_same i _ hm w (hw i) _ ?_).trans
    (mul_le_mul_of_nonneg_left (heat_rate i (unary i) (by simp [unary]) A B Z m he) hH)
  intro x y h
  unfold basisFrom glimpse thermal imageP
  simp_rw [heat_unary,h]

theorem heat_none (i : Bool) (Z : DTuple (p:=p) q N)
    {w : Wgt (UnitType p n N)} {H : ℝ} (hH : 0 ≤ H)
    (m : Mixer p n) {ε : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hw : bySide p w m H) :
    pr w (fun x => basisFrom p x i Z) ≤ H*heatRate p n N ε (ctot p q) 0 := by
  classical
  let t : Place p→ℕ := fun _ => 0
  let B : DTuple (p:=p) t N := 0
  have hh := heat_one i B B Z hH m hm he hw
  have h1 (x : UnitType p n N) : glimpse p x i B := fun z v v' h => Subsingleton.elim v v'
  have h2 (x : UnitType p n N) : thermal p x (unary i) B=B := Subsingleton.elim _ _
  simp_rw [h1,h2,and_true] at hh
  simpa only [ctot,t,Finset.sum_const_zero] using hh

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionCosts
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Intersection Costs -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

private theorem prod_one {A I : Type} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → Wgt A) (hf : ∀ i,IsLaw (f i)) (i : I) :
    mapW (prodW f) (fun g => g i)=f i := by
  classical
  funext x
  let q (j : I) (y : A) := if j=i then y=x else True
  have hh : (fun f : I→A => f i=x)=fun f : I→A => ∀ j,q j (f j) := by
    funext g
    apply propext; constructor
    · intro h j; unfold q; split_ifs with he
      · rwa [he]
    intro h; simpa only [q,ite_eq_left rfl] using h i
  unfold mapW
  rw [hh,prodW_pr f q,Finset.prod_eq_single i]
  · simp [q]
  · intro j _ hj
    simp [q,hj,(hf j).total]
  simp

/-- Raw law of a single-sign observation of primary/channel columns. -/
theorem raw_part (m : Mixer p n) (z : Place p) [DecidableEq I]
    (hN : 2*num (Full p n)-N≤ -1)
    {A : Mat (Full p n) I} (hA : Injective A.mulVec) :
    mapW (raw m N) (fun x => takeSign (p:=p) (x z.1) z.2 * A)=
      unifOn (fun x => Injective x.mulVec) := by
  classical
  let w := unifOn (FramesAt (U:=Fin N) (gramCond m))
  have he : 2*num (Full p n)-num (Fin N) ≤ -1 := by simpa only [num,Fintype.card_fin] using hN
  have h : ∃ x : Oframe p n N, FramesAt (gramCond m) x := framesAt_exists
    (gramCond_exists m) (by linarith only [he])
  have hF := prod_one (fun (_ : Comp p.g) => w) (fun _ => unifOn_law h) z.1
  let g := fun o : Oframe p n N => takeSign o z.2 * A
  change mapW (raw m N) (g ∘ (fun x => x z.1))=_
  rw [← mapW_nested]
  rw [show mapW (raw m N) (fun x => x z.1)=w from hF]
  cases z with
  | mk e c =>
    cases c; exact framesAt_observe_minus h hA; exact framesAt_observe_plus h hA

theorem frameP_cap {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1) :
    ∀ y,mapW w (fun x => fpAt p (onSide x i) z) y≤H*(2 * unif y) := by
  classical
  intro y
  let g := fun x : UnitType p n N => onSide x i
  let f := fun x : Orient p n N => fpAt p x z
  have hg : num (Row p n)-num (Fin N)≤ -1 := by
    have hi : num (Row p n) ≤ num (Full p n) := by
      have h := Fintype.card_le_of_injective _ (Sum.inl_injective (β:=Fin p.h)
        (α:=Row p n))
      exact_mod_cast h
    have hh : 0≤num (Full p n) := Nat.cast_nonneg _
    simp only [num,Fintype.card_fin] at hN hi hh ⊢ <;> linarith
  change mapW w (f ∘ g) _ ≤ _
  rw [← mapW_nested]
  apply (mapW_cap (h i) f y).trans
  have hf (x : Orient p n N) :
      f x=takeSign (p:=p) (x z.1) z.2 * ipPart p n := by
    rw [ipPart,mul_embedMat]; rfl
  rw [show f=(fun x : Orient p n N => takeSign (p:=p) (x z.1) z.2 * ipPart p n) from funext hf]
  rw [raw_part m z hN (A:=ipPart p n) (embedMat_inj Sum.inl_injective)]
  exact mul_le_mul_of_nonneg_left (plus_le_unif hg y) hH

theorem frameY_cap {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1) :
    ∀ y,mapW w (fun x => fyAt p (onSide x i) z) y≤H*(2 * unif y) := by
  classical
  intro y
  let g := fun x : UnitType p n N => onSide x i
  let f := fun x : Orient p n N => fyAt p x z
  have hg : num (Fin p.h)-num (Fin N)≤ -1 := by
    have hi : num (Fin p.h) ≤ num (Full p n) := by
      have h := Fintype.card_le_of_injective _ (Sum.inr_injective (β:=Fin p.h)
        (α:=Row p n)); exact_mod_cast h
    have hh : 0≤num (Full p n) := Nat.cast_nonneg _
    simp only [num,Fintype.card_fin] at hN hi hh ⊢ <;> linarith
  change mapW w (f ∘ g) _ ≤ _
  rw [← mapW_nested]
  apply (mapW_cap (h i) f y).trans
  have hf (x : Orient p n N) :
      f x=takeSign (p:=p) (x z.1) z.2 * intoChan p n := (intoChan_val ..).symm
  rw [show f=(fun x : Orient p n N => takeSign (p:=p) (x z.1) z.2 * intoChan p n) from funext hf]
  rw [raw_part m z hN (A:=intoChan p n) intoChan_inj]
  exact mul_le_mul_of_nonneg_left (plus_le_unif hg y) hH

variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem any_span_hit (S : Space (Vec I)) :
    pr unif (fun M : Mat I J => ¬ Disjoint (colSp M) S) ≤ bp (num J+dim S-num I) := by
  classical
  let P := fun (z : Vec J × S) (M : Mat I J) => z.1≠0 ∧ M *ᵥ z.1=z.2.val
  have h (M : Mat I J) : ¬ Disjoint (colSp M) S → ∃ z,P z M := by
    intro h
    rw [Submodule.disjoint_def] at h
    push Not at h
    obtain ⟨x,⟨y,rfl⟩,hy,hx⟩ := h
    have hh : y≠0 := fun h => hx (by rw [h,map_zero])
    exact ⟨(y,⟨_,hy⟩),hh,rfl⟩
  have he (z : Vec J × S) : pr unif (P z) ≤ bp (-num I) := by
    by_cases hh : z.1=0
    · simp only [P,hh,ne_eq,not_true_eq_false,false_and,pr_false]
      exact (bp_pos _).le
    have h' := shift_pmax (@unif_subLaw (Mat I J) _) ⊤ (fun _ _ _ => rfl) hh z.2.val
    rw [show dim (⊤ : Space (Vec I))=_ from (finrank_top ..).trans (dim_vec _)] at h'
    simpa only [P,hh,ne_eq,not_false_eq_true,true_and] using h'
  refine ((pr_mono unif_subLaw.nz h).trans (pr_exists_le unif_subLaw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => he i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,
    Nat.cast_mul,card_space,dim_vec,bp_sub,bp_add,bp_neg,num,div_eq_mul_inv]

theorem transposed_uniform {P : Mat I J} (hp : Injective P.mulVec) :
    mapW (unif : Wgt (Mat I K)) (fun x => xᵀ*P)=unif := by
  obtain ⟨L,hL⟩ := mat_left_inv hp
  apply map_unif_surjective (expand P K)
  intro v
  exact ⟨(v*L)ᵀ,by change ((v*L)ᵀ)ᵀ*P=v; rw [transpose_transpose,Matrix.mul_assoc,hL,Matrix.mul_one]⟩

/-- per fixed nominal offsets in one component/side -/
theorem test_transpose {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1)
    (M : Mat (Fin N) I) (hM : Injective M.mulVec) :
    ∀ x,mapW w (fun y => (fyAt p (onSide y i) z)ᵀ * M) x≤H*2 * unif x := by
  intro x
  let f (y : HMat p N) := yᵀ * M
  let g (x : UnitType p n N) := fyAt p (onSide x i) z
  change mapW w (f ∘ g) _ ≤ _
  rw [←mapW_nested]
  have he := frameY_cap m hH h i z hN
  simp_rw [← mul_assoc] at he
  refine (mapW_cap he f x).trans_eq ?_
  rw [show mapW unif f=unif from transposed_uniform hM]

theorem glimpse_failure {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (hw : SubLaw w) (i : Bool) (hN : 2*num (Full p n)-N≤ -1)
    {q : Place p→ℕ} (M : DTuple (p:=p) q N) (k : ℕ) (hm : ∀ z,Injective (M z).mulVec)
    (hk : ∀ z,q z≤k) :
    pr w (fun x => ¬ glimpse p x i M) ≤ glimpsesBill p k H := by
  classical
  let P (A : Place p) :=
    fun x => ¬Injective ((fyAt p (onSide (x : UnitType p n N) i) (flipZ p A))ᵀ * M A).mulVec
  have he x : ¬ glimpse p x i M → ∃ z,P z x := by
    intro h
    unfold glimpse at h
    push Not at h
    exact h
  have hi z : pr w (P z) ≤ H*2*bp ((k:ℝ)-p.h) := by
    let f (x : UnitType p n N) := (fyAt p (onSide x i) (flipZ p z))ᵀ*M z
    let Q := fun x : Mat (Chan p) (Fin (q z)) => ¬ Injective x.mulVec
    change pr w (Q ∘ f) ≤ _
    rw [show pr w (Q ∘ f)=pr (mapW w f) Q from (mapW_pr w f Q).symm]
    refine (pr_cap (test_transpose m hH h i (flipZ p z) hN _ (hm z)) Q).trans
      (mul_le_mul_of_nonneg_left (unif_fail.trans ?_) (by positivity))
    apply bp_le
    have hh : (q z:ℝ)≤k := by exact_mod_cast hk z
    simpa [Chan,num] using sub_le_sub_right hh (p.h:ℝ)
  refine ((pr_mono hw.nz he).trans (pr_exists_le hw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hi i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,glimpsesBill,num]

/-- span of entire individual primary image in a fixed cover mode. -/
theorem any_frame_hit {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1)
    (S : Space (Vec (Fin N))) :
    pr w (fun x => ¬ Disjoint (imageP p x i z) S) ≤
      H*2*bp (num (Row p n)+dim S-N) := by
  let P (M : Mat (Fin N) (Row p n)) := ¬ Disjoint (colSp M) S
  let f (x : UnitType p n N) := fpAt p (onSide x i) z
  change pr w (fun x => P (f x)) ≤ _
  rw [← mapW_pr w f P]
  have he := frameP_cap m hH h i z hN
  simp_rw [← mul_assoc] at he
  refine (pr_cap he P).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simpa only [num,Fintype.card_fin] using any_span_hit (J:=Row p n) S

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SupportedPhaseLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported Phase Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

namespace Bazaar

variable (s : Bazaar p n r T)

theorem active {Δ : UnitType p n N→Ambient p N} {w} {M}
    (h : s.opened Δ w) (x) (hx : s.chart w M x≠0) :
    s.ix x=M ∧ standard M ∧ ∀ i,compFor M (s.bag M i x) (imageP p x i) (Δ x) := by
  have h' : s.ix x=M := Classical.byContradiction fun he => hx (subW_carried w _ _ he)
  refine ⟨h',?_⟩
  subst M; exact h x (left_ne_zero_of_mul hx)

end Bazaar

namespace Bazaar
variable {s : Bazaar p n r T}

theorem bag_rate (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    {w : Wgt (UnitType p n N)} {Δ} {ε : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hv : SubLaw w) (hw : bySide p w m H)
    (hl : s.opened Δ w) (hp : selPrice p r n N H ε)
    (M : Atlas p r T) (i : Bool) :
    ∀ x, mapW (s.chart w M) (s.bag M i) x ≤ loseA p N (cells M) 0 := by
  classical
  intro x
  let v := s.chart w M
  have hV : SubLaw v := subLaw_sub hv _
  by_cases hx : standard M
  · refine le_trans (pr_on_mono hV.nz (P:=fun y => s.bag M i y=x)
      (Q:=fun y => basisFrom p y i x) (fun z hz hg => ?_)) ?_
    · subst x
      exact ((active s hl z hz).2.2 i).1
    refine (pr_mono_left (subW_le hv.nz _) _).trans ?_
    exact (heat_none i x hH m hm he hw).trans (hp (cells M) 0 hx.2.1 (Nat.zero_le _))
  have h : v=(fun _ => 0) :=
    funext fun x => Classical.byContradiction fun h => hx (active s hl x h).2.1
  change mapW v _ _≤_
  rw [h]
  simp only [mapW,pr,avg,zero_mul,Finset.sum_const_zero]
  exact (bp_pos _).le

theorem glimpse_prize (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    {w : Wgt (UnitType p n N)} {Δ} {ε : ℝ}
    (hm : IsLaw (raw m N)) (he : initCap p N m ε) (hv : SubLaw w)
    (hw : bySide p w m H) (h : s.opened Δ w) (hp : selPrice p r n N H ε)
    (M G : Atlas p r T) (i : Bool) (hh : standard M) (hh' : standard G)
    (P : UnitType p n N → Prop)
    (hf : ∀ x, s.chart w G x≠0 → P x → glimpse p x i (src M)) :
    ∀ x, mapW (subW (s.chart w G) P) (s.pay M G i (unary i)) x≤ prize p N (cells G) := by
  classical
  rintro ⟨x,y⟩
  let v := s.chart w G
  have hv' : SubLaw v := subLaw_sub hv _
  change pr (subW v P) _ ≤ _
  rw [pr_sub]
  refine (pr_on_mono hv'.nz (Q:=fun z =>
    basisFrom p z i y ∧ glimpse p z i (src M) ∧ thermal p z (unary i) (src M)=x) ?_).trans ?_
  · rintro z hz ⟨he,hx⟩
    have h1 : s.bag G i z=y := congrArg Prod.snd hx
    exact ⟨h1 ▸ ((active s h z hz).2.2 i).1,hf z hz he,congrArg Prod.fst hx⟩
  refine (pr_mono_left (subW_le hv.nz _) _).trans ?_
  apply (heat_one i (src M) x y hH m hm he hw).trans
  refine (hp (cells G) (cells M) hh'.2.1 hh.2.1).trans ?_
  unfold prize loseA
  apply bp_le
  have ht : (1:ℝ) ≤ cells M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hh.1
  rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

end Bazaar

variable {A B V : Type} [Fintype A] [Fintype B] [Fintype V]

private theorem write_weight (g : Wgt A) (w : Wgt A) (hw : SubLaw w) (f : A→B)
    (h : ∀ x, |g x|≤1) :
    ∃ t : Wgt B, (∀ x,|t x|≤1) ∧
    ∀ s : Wgt B, avg w (fun x => g x*s (f x))=avg (mapW w f) (fun y => t y*s y) := by
  classical
  let V (y : B) := onW w (fun x => f x=y)
  have hv (y) : SubLaw (V y) := normW_subLaw (subW_nonneg hw.nz _)
  let T (y) := avg (V y) g
  refine ⟨T,fun y => (abs_avg_le (hv y).nz).trans ((hv y).avg_le zero_le_one h),fun s => ?_⟩
  calc avg w (fun x => g x*s (f x))
    _ = avg (mixW (mapW w f) V) (fun x => g x*s (f x)) :=
      congrArg (avg · (fun x => g x*s (f x))) (disintegrate hw.nz f)
    _ = _ := by
      rw [mixW_avg]; refine avg_congr (fun x _ => ?_)
      calc _ = avg (V x) (fun y => g y*s x) := avg_congr (fun y hy => by
                 have h : f y=x := Classical.byContradiction fun h => hy
                   (normW_carried (subW_carried w (fun v => f v=x)) y h)
                 rw [h])
           _ = _ := avg_mul ..

theorem mapW_sub (f : A→B) {w : Wgt A} (hw : SubLaw w) : SubLaw (mapW w f) := by
  refine ⟨fun _ => pr_nonneg hw.nz,?_⟩
  have he := mapW_avg w f (fun _ => 1)
  rw [avg_const,avg_const,mul_one,mul_one] at he
  rw [he]; exact hw.total

variable [AddCommGroup V] [Module F V]

/-- Walsh bound on pushforward tuples with arbitrary separate
query weights. -/
theorem walsh_weighted (b : V →ₗ[F] V →ₗ[F] F) (hb : Function.Injective b)
    (w : Wgt A) (v : Wgt B) (hw : SubLaw w) (hv : SubLaw v)
    (f : A→V) (g : B→V) (S : Wgt A) (T : Wgt B) {p q : ℝ}
    (hs : ∀ x,|S x|≤1) (ht : ∀ x, |T x| ≤1)
    (hp : ∀ x, mapW w f x ≤ p) (hq : ∀ x,mapW v g x ≤ q) :
    (avg (pairW w v) (fun x => S x.1*T x.2 * wsign (b (f x.1) (g x.2))))^2 ≤ num V*p*q := by
  obtain ⟨Y,hY,hA⟩ := write_weight S w hw f hs
  obtain ⟨X,hX,hB⟩ := write_weight T v hv g ht
  have he :
      avg (pairW w v) (fun x => S x.1*T x.2*wsign (b (f x.1) (g x.2)))=
        avg (mapW v g) (fun y => X y* avg (mapW w f) (fun x =>
          Y x*wsign (b x y))) := by
    rw [pairW_avg,avg_avg]
    have he y :
        avg w (fun x => S x*T y* wsign (b (f x) (g y))) =
        T y * avg (mapW w f) (fun x => Y x*wsign (b x (g y))) := by
      have hh := hA (fun v => wsign (b v (g y)))
      simp_rw [mul_comm (S _) (T y),mul_assoc,avg_mul']
      rw [hh]
    simp_rw [he]
    exact hB (fun y => avg _ (fun x => Y x*wsign (b x y)))
  rw [he]
  exact walsh_mass b hb (mapW w f) (mapW v g) Y X hY hX (mapW_sub f hw) (mapW_sub g hv) hp hq

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetFourierBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Fourier Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

variable {U V : Type} [AddCommGroup U] [AddCommGroup V] [Module F U] [Module F V]

theorem coupledB_inj {A : U →ₗ[F] U →ₗ[F] F} {B : V →ₗ[F] V →ₗ[F] F}
    (ha : Injective A) (hb : Injective B) :
    Injective (coupledB A B) := by
  intro x y h
  apply Prod.ext
  · apply ha
    refine LinearMap.ext fun z => ?_
    have he : A x.1 z+B x.2 0=A y.1 z+B y.2 0 := LinearMap.congr_fun h (z,0)
    simpa only [map_zero,add_zero] using he
  apply hb
  refine LinearMap.ext fun z => ?_
  have he : A x.1 0+B x.2 z=A y.1 0+B y.2 z := LinearMap.congr_fun h (0,z)
  simpa only [map_zero,zero_add] using he

theorem tupleB_comm (p : Shape) (r : Place p→ℕ) (N : ℕ) (x y) :
    tupleB p r N x y=tupleB p r N y x := by
  rw [tupleB_val,tupleB_val]
  exact Finset.sum_congr rfl fun i _ => mpair_comm ..

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 800000 in
private theorem beat_one {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : SubLaw w) (M G : Atlas p r T)
    (S R : Party) (i : Bool) (C : UnitType p n N → Prop)
    (hA : ∀ x,mapW (s.chart w M) (s.bag M i) x ≤ loseA p N (cells M) 0)
    (hB : standard M → standard G → ∀ y,mapW (subW (s.chart w G) C)
      (s.pay M G i S) y ≤ prize p N (cells G)) :
    |avg (pairW (s.chart w M) (subW (s.chart w G) C)) (chant p Δ S R)| ≤ beat N := by
  classical
  let u := s.chart w M
  let v := subW (s.chart w G) C
  have hw : SubLaw u := subLaw_sub hv _
  have ht : SubLaw v := subLaw_sub (subLaw_sub hv _) _
  let y := avg (pairW u v) (chant p Δ S R)
  by_cases hy : y=0
  · change |y|≤_
    rw [hy, abs_zero]; exact (bp_pos _).le
  have h : ∃ x,pairW u v x ≠ 0 := by
    by_contra! he
    apply hy; unfold y avg; simp_rw [he] <;> simp
  obtain ⟨⟨x0,y0⟩,hx⟩ := h
  have hV x (hh : v x≠0) : s.chart w G x≠0 := left_ne_zero_of_mul hh
  have H (x : UnitType p n N) (hh : u x≠0) := s.active hl x hh
  have H' (x : UnitType p n N) (hh : v x≠0) := s.active hl x (hV x hh)
  let a (x) := (s.bag M i x,thermal p x R (src G))
  let b := s.pay M G i S
  let f (x : UnitType p n N) := wsign (tone p x R (edgeCost G))
  let g (x : UnitType p n N) := wsign (tone p x S (edgeCost M))
  let B := coupledB (tupleB p (breadth M) N) (tupleB p (breadth G) N)
  have hc :
      y=avg (pairW u v) (fun x => f x.1*g x.2*wsign (B (a x.1) (b x.2))) := by
    refine avg_congr fun ⟨x,y⟩ hh => ?_
    have h1 := ((H x (left_ne_zero_of_mul hh)).2.2 i).2
    have h2 := ((H' y (right_ne_zero_of_mul hh)).2.2 i).2
    unfold chant; dsimp only
    rw [h1,h2,tone_offset,tone_offset]
    unfold f g
    rw [←wsign_add,←wsign_add]
    apply congrArg wsign
    change _=_+(tupleB p (breadth M) N _ _+tupleB p (breadth G) N _ _)
    rw [tupleB_comm p (breadth G) N (s.bag G i y)]
    dsimp only [coupledB,b,pay,a]
    simp only [LinearMap.fst_apply,LinearMap.snd_apply]
    abel
  let D := Batch M N × Batch G N
  have ha (x : D) : mapW u a x ≤ loseA p N (cells M) 0 := by
    refine (pr_mono hw.nz (p:=fun y => a y=x) (q:=fun y => s.bag M i y=x.1)
      (fun y h => ?_)).trans (hA x.1)
    exact congrArg Prod.fst h
  have hb (x : D) : mapW v b x ≤ prize p N (cells G) :=
    hB ((H x0 (left_ne_zero_of_mul hx)).2.1) ((H' y0 (right_ne_zero_of_mul hx)).2.1) x
  have he := walsh_weighted B
    (coupledB_inj (tupleB_inj ..) (tupleB_inj ..)) u v hw ht a b f g (fun x => by simp [f])
    (fun x => by simp [g]) ha hb
  have hi : y^2 ≤ beat N^2 := by
    rw [hc]
    refine he.trans ?_
    let F := Batch M N
    let G' := Batch G N
    unfold num
    rw [card_space,dim,finrank_prod]
    have hf : finrank HadwigerCounterexample.F F=N*cells M := tuple_dim
    have hg : finrank HadwigerCounterexample.F G'=N*cells G := tuple_dim
    rw [hf,hg,loseA,prize,beat,←bp_add,←bp_add,pow_two,←bp_add]
    apply le_of_eq; push_cast <;> ring_nf
  change |y|≤_
  exact le_of_pow_le_pow_left₀ (show 2 ≠ (0:ℕ) by decide) (bp_pos _).le
    (sq_abs y ▸ hi)

set_option maxHeartbeats 800000 in
theorem beat_mix {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (S R : Party) (i : Bool) (C : Sales p n r T)
    (hA : ∀ M x,mapW (s.chart w M) (s.bag M i) x ≤ loseA p N (cells M) 0)
    (hB : ∀ M G,standard M → standard G → ∀ y,mapW (subW (s.chart w G) (C M G))
      (s.pay M G i S) y ≤ prize p N (cells G))
    (ht : num (Atlas p r T) ≤ bp (0.002*N)) :
    |pitch p Δ w S R| ≤ discard (s:=s) w C + bp (-0.24*N) := by
  classical
  let V := pairW w w
  let F := chant p Δ S R
  let P := fun x : (UnitType p n N)×_ => C (s.ix x.1) (s.ix x.2) x.2
  let g := fun x => ind (P x)*F x
  let f := fun x => ind (¬P x)*F x
  let μ := s.chart w
  let W := fun M G => subW (μ G) (C M G)
  have hn x : 0≤ V x := (pairW_law hv hv).nz x
  have he x : F x=f x+ g x := by
    unfold f g
    by_cases h : P x <;> simp [h]
  have hf : |avg V f| ≤ discard (s:=s) w C := by
    refine (abs_avg_le hn).trans_eq ?_
    unfold discard pr
    refine avg_congr (fun x _ => ?_)
    rw [show f x= _*_ from rfl, abs_mul, abs_of_nonneg (ind_nonneg (¬P x))]
    simp [F,P,chant]
  have hg :
      avg V g=∑ M : Atlas p r T,∑ G : Atlas p r T, avg (pairW (μ M) (W M G)) F := by
    let U (M G : Atlas p r T) (x : UnitType p n N × UnitType p n N) :=
      ind (s.ix x.1=M)*ind (s.ix x.2=G)*ind (C M G x.2)*F x
    have hu (M G : Atlas p r T) :
        avg (pairW (μ M) (W M G)) F=avg V (U M G) := by
      unfold avg
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold U W μ V pairW chart subW; ring
    simp_rw [hu,← avg_sum]
    refine avg_congr fun x _ => ?_
    rw [Finset.sum_eq_single (s.ix x.1)]
    · rw [Finset.sum_eq_single (s.ix x.2)]
      · simp only [U,ind_true,one_mul]; rfl
      · intro j _ hj; simp [U,ind_zero hj.symm]
      simp
    · intro j _ hj; simp [U,ind_zero hj.symm]
    simp
  have hh : |avg V g| ≤ bp (-0.24*N) := by
    rw [hg]; apply le_trans (Finset.abs_sum_le_sum_abs ..)
    let J := num (Atlas p r T)
    have hz (M : Atlas p r T) :
        |∑ G : Atlas p r T, avg (pairW (μ M) (W M G)) F|≤ J*beat N := by
      refine (Finset.abs_sum_le_sum_abs ..).trans
        ((Finset.sum_le_sum (fun i' _ =>
          beat_one s hl hv.sub M i' S R i (C M i') (hA M) (hB M i'))).trans_eq ?_)
      simp only [J,Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]
    calc ∑ M : Atlas p r T,|∑ G : Atlas p r T,avg (pairW (μ M) (W M G)) F|
      _ ≤ ∑ _ : Atlas p r T,J*beat N := Finset.sum_le_sum fun M _ => hz M
      _ = J*J*beat N := by simp [J,mul_assoc,num]
      _ ≤ bp (0.002*N)*bp (0.002*N)*beat N := mul_le_mul_of_nonneg_right
        (mul_self_le_mul_self (Nat.cast_nonneg _ : 0≤J) ht) (bp_pos _).le
      _ ≤ bp (-0.24*N) := by
        unfold beat; rw [← bp_add,← bp_add]; apply bp_le; linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]
  change |avg V F|≤ _
  rw [show F=(fun x => f x+g x) from funext he,avg_add]
  exact (abs_add_le ..).trans (add_le_add hf hh)

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SingletonPhaseTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Singleton Phase Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N} {A : Type} [Fintype A]

theorem avg_on_support {w f g : Wgt A} (h : ∀ x,0≤w x)
    (he : ∀ x,w x≠0 → f x≤g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum (fun x _ => by
    by_cases hh : w x=0
    · rw [hh,zero_mul,zero_mul]
    exact mul_le_mul_of_nonneg_left (he x hh) (h x))

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 600000 in
theorem single_pitch {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (i : Bool) (R : Party)
    (m : Mixer p n) {ε H : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hH : 0 ≤ H) (hw : bySide p w m H)
    (hp : selPrice p r n N H ε) (ht : num (Atlas p r T) ≤ bp (0.002*N))
    (hN : 2*num (Full p n)-N≤ -1) :
    |pitch p Δ w (unary i) R|≤ glimpsesBill p r H+bp (-0.24*N) ∧
    ((∀ x,w x≠0 → ∀ y,w y≠0 → glimpse p y i (src (s.ix x))) →
      |pitch p Δ w (unary i) R|≤bp (-0.24*N)) := by
  classical
  let C : Sales p n r T := fun M _ y => glimpse p y i (src M)
  have hb M G (hh : standard M) (hh' : standard G) :=
    glimpse_prize m hH hm he hv.sub hw hl hp M G i hh hh' (C M G) (fun _ _ h => h)
  have hf := beat_mix s hl hv (unary i) R i C (fun M => bag_rate m hH hm he hv.sub hw hl hp M i)
    hb ht
  have he : discard (s:=s) w C = avg w (fun x =>
      pr w (fun y => ¬ glimpse p y i (src (s.ix x)))) := pairW_avg ..
  rw [he] at hf
  constructor
  · refine hf.trans (add_le_add_left ?_ _)
    rw [← hv.avg_const (glimpsesBill p r H)]
    apply avg_on_support hv.nz
    intro x hx
    have hX := (hl x hx).1
    exact glimpse_failure m hH hw hv.sub i hN _ r hX.2.2 (fun z =>
      Nat.lt_add_one_iff.mp ((s.ix x).1 z).isLt)
  intro hh
  have hW : avg w (fun x => pr w (fun y => ¬glimpse p y i (src (s.ix x))))=0 := by
    rw [← hv.avg_const 0]
    refine avg_congr (fun x hx => ?_)
    rw [← hv.avg_const 0]
    exact avg_congr fun y hy => ind_zero (by simp [hh x hx y hy])
  rwa [hW,zero_add] at hf

theorem calm_pitch {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (i : Bool) (R S : Party)
    (m : Mixer p n) {ε H : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hH : 0 ≤ H) (hw : bySide p w m H)
    (hp : selPrice p r n N H ε) (ht : num (Atlas p r T) ≤ bp (0.002*N)) :
    |pitch p Δ w S R| ≤ pr (pairW w w)
      (fun x => s.frequent w S i (s.ix x.1) (s.ix x.2) x.2) + bp (-0.24*N) := by
  classical
  let C : Sales p n r T := fun M G y => ¬ s.frequent w S i M G y
  have hb (M G : Atlas p r T) (hh : standard M) (hh' : standard G) :
      ∀ y,mapW (subW (s.chart w G) (C M G)) (s.pay M G i S) y ≤ prize p N (cells G) := by
    let v := s.chart w G
    let J := s.pay M G i S
    have hw' : SubLaw v := subLaw_sub hv.sub _
    intro y
    by_cases he : mapW v J y≤prize p N (cells G)
    · exact (pr_mono_left (subW_le hw'.nz _) _).trans he
    change pr (subW v (C M G)) (fun x => J x=y) ≤ _
    rw [pr_sub]
    have hx : (fun x => C M G x ∧ J x=y)=(fun _ => False) := by
      funext x
      refine propext (iff_false_intro (fun ⟨h,h'⟩ => he ?_))
      rw [← h']
      exact le_of_not_gt h
    rw [hx,pr_false]; exact (bp_pos _).le
  have hf := beat_mix s hl hv S R i C (fun M => bag_rate m hH hm he hv.sub hw hl hp M i) hb ht
  unfold discard C at hf; simpa only [not_not] using hf

theorem bids_mem (w : Wgt (UnitType p n N)) (S : Party) (i : Bool)
    (M G : Atlas p r T) (x : UnitType p n N) :
    s.frequent w S i M G x ↔
      thermal p x S (src M) ∈ s.bids w S i M G (s.bag G i x) := by
  classical
  simp only [bids,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

theorem bids_bound {w : Wgt (UnitType p n N)} (S : Party) (i : Bool)
    (M G : Atlas p r T) (Z : Batch G N) (hw : SubLaw w)
    (h : ∀ x,mapW (s.chart w G) (s.bag G i) x ≤ loseA p N (cells G) 0) :
    (↑(s.bids w S i M G Z).card:ℝ) ≤ bp (0.51*N) := by
  classical
  let f := s.pay M G i S
  let v := s.chart w G
  have hv : SubLaw v := subLaw_sub hw _
  let B := s.bids w S i M G Z
  let P := prize p N (cells G)
  have he (x) (hx : x∈B) : P ≤ mapW v f (x,Z) := (Finset.mem_filter.mp hx).2.le
  have hg : ↑B.card * P ≤ loseA p N (cells G) 0 := by
    have hZ : ∑ x : Batch M N,mapW v f (x,Z)=mapW v (s.bag G i) Z := by
      let T := fun x => (f x).1
      have hh (x : Batch M N) : (fun y => f y=(x,Z))=
          fun y => s.bag G i y=Z ∧ T y=x := by ext y; simp [Prod.mk.injEq,f,T,pay,and_comm]
      simp only [mapW,hh,sum_pr_tag]
    calc ↑B.card * P = ∑ x ∈ B,P := (by simp)
         _ ≤ ∑ x∈B,mapW v f (x,Z) := Finset.sum_le_sum he
         _ ≤ ∑ x : Batch M N,mapW v f (x,Z) := Finset.sum_le_sum_of_subset_of_nonneg
           (Finset.subset_univ B) (fun i _ _ => pr_nonneg hv.nz)
         _ ≤ loseA p N (cells G) 0 := hZ.trans_le (h Z)
  refine (le_of_mul_le_mul_right (hg.trans_eq ?_) (bp_pos _ : 0<P))
  unfold P prize loseA
  rw [← bp_add]; congr 1; push_cast <;> ring

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AdditionalProbeBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additional Probe Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

omit [Fintype I] in
private theorem moreMatrix_act_p0 {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (x : Vec (Fin (r+1))) :
    moreMatrix_p0 A v *ᵥ x=x 0 • v + A *ᵥ (fun i => x i.succ) := by
  funext i; simp only [Matrix.mulVec,dotProduct,moreMatrix_p0,Matrix.of_apply,
    Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fin.cons_zero,Fin.cons_succ]
  congr 1; exact mul_comm _ _

omit [Fintype I] in
private theorem moreMatrix_inj_p0 {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (ha : Injective A.mulVec) (h : v∉colSp A) :
    Injective (moreMatrix_p0 A v).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  rw [moreMatrix_act_p0] at hx
  let b (i : Fin r) := x i.succ
  rcases bit_cases (x 0) with he|he
  · have hh : b=0 := by
      apply ha
      rw [he,zero_smul,zero_add] at hx
      exact hx.trans (Matrix.mulVec_zero _).symm
    funext i
    refine Fin.cases he (fun k => ?_) i
    exact congr_fun hh k
  · rw [he,one_smul] at hx
    have heq : v=A *ᵥ b := add_right_cancel (hx.trans (char_two _).symm)
    exact (h ⟨b,heq.symm⟩).elim

omit [Fintype J] in
private theorem moreMatrix_mul {r} (B : Mat J I) (A : Mat I (Fin r)) (v) :
    B*moreMatrix_p0 A v=moreMatrix_p0 (B*A) (B *ᵥ v) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  simp only [moreMatrix_p0,Matrix.mul_apply,Matrix.of_apply,Fin.cons_succ]

variable {p : Shape} {n N r : ℕ} {T : Cov p N}
variable {q : Place p → ℕ}

private theorem grow_sum (q : Place p→ℕ) (z : Place p) :
    ctot p (growFmt (p:=p) q z)=ctot p q+1 := by simp [growFmt,ctot,Finset.sum_add_distrib]

private theorem castMat_inj {r n m : ℕ} (e : r=n)
    (A : Mat (Fin m) (Fin r)) (h : Injective A.mulVec) :
    Injective (cast (show Mat (Fin m) (Fin r)=Mat (Fin m) (Fin n) from congrArg (fun t => Mat (Fin m) (Fin t)) e) A).mulVec := by
  subst n
  exact h
private theorem castMat_prod {r n m : ℕ} (e : r=n)
    (A : Mat (Fin m) (Fin r)) (B : Mat (Fin m) (Fin m)) :
    B*(cast (show Mat (Fin m) (Fin r)=Mat (Fin m) (Fin n) from congrArg (fun t => Mat (Fin m) (Fin t)) e) A) =
    cast (show Mat (Fin m) (Fin r)=Mat (Fin m) (Fin n) from congrArg (fun t => Mat (Fin m) (Fin t)) e) (B*A) := by
  subst n; rfl

private theorem growth_inj (A : DTuple (p:=p) q N) (z : Place p) (v : Vec (Fin N))
    (hv : v∉colSp (A z)) (h : ∀ i, Injective (A i).mulVec) :
    ∀ i,Injective (growing A z v i).mulVec := by
  intro i
  by_cases he : i=z
  · subst i
    simp [growing,growFmt]
    apply castMat_inj _ (moreMatrix_p0 (A z) v) (moreMatrix_inj_p0 (A z) v (h z) hv)
    simp
  simp [growing,growFmt,he]
  apply castMat_inj _ (A i) (h i)
  simp [he]

private theorem growth_value (A : DTuple (p:=p) q N) (z : Place p) (v : Vec (Fin N))
    (x : UnitType p n N) (S : Party) :
    thermal p x S (growing A z v)=growing (thermal p x S A) z (heat p x S z *ᵥ v) := by
  funext i
  by_cases he : i=z
  · subst i
    simp [thermal,growing,growFmt]
    rw [←moreMatrix_mul]
    apply castMat_prod
    simp
  simp [thermal,growing,growFmt,he]
  apply castMat_prod
  simp [he]

theorem column_observe (A : DTuple (p:=p) q N) (z : Place p) (j : Fin (q z))
    (x : UnitType p n N) (S : Party) :
    heat p x S z *ᵥ (A z).col j=(thermal p x S A z).col j := rfl

namespace Bazaar
variable (s : Bazaar p n r T)

theorem extend_probe (w : Wgt (UnitType p n N)) (S : Party) (j : Bool) {k : ℕ}
    (A : DTuple (p:=p) q N) (hq : ctot p q=k)
    (h : ∀ i, Injective (A i).mulVec)
    (F : Catalog p T r q) (hF : ∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N))
    (G : Atlas p r T) (hg : ¬ offsetCov G ≤ probed p A)
    (hb : ∀ M Z,(↑(s.bids w S j G M Z).card:ℝ) ≤ bp (0.51*N)) :
    ∃ (q : Place p→ℕ) (A' : DTuple (p:=p) q N)
      (F' : Catalog p T r q), ctot p q=k+1 ∧
      (∀ i, Injective (A' i).mulVec) ∧
      (∀ M Z,(↑(F' M Z).card:ℝ) ≤ bp (0.51*(k+1)*N)) ∧
      ∀ x,s.atList S j A F x → s.frequent w S j G (s.ix x) x →
        s.atList S j A' F' x := by
  classical
  obtain ⟨z,i,hg⟩ :
      ∃ (z : Place p) (i : Fin (breadth G z)),(src G z).col i∉colSp (A z) := by
    by_contra! hh
    apply hg
    intro z
    change colSp (src G z) ≤ _
    rw [colSp,range_mulVecLin]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr (hh z))
  let q' := growFmt (p:=p) q z
  let v := (src G z).col i
  let f (M Z) : Finset (DTuple (p:=p) q' N) :=
    ((F M Z) ×ˢ (s.bids w S j G M Z)).image
      (fun a => growing a.1 z ((a.2 z).col i))
  refine ⟨q',growing A z v, f,(grow_sum q z).trans (by rw [hq]),
    growth_inj A z v hg h,fun M Z => ?_,fun x hx hi => ?_⟩
  · have he := bp_pos (0.51*(k:ℝ)*N)
    have h1 :
        (↑(f M Z).card:ℝ) ≤ (↑(F M Z).card:ℝ)*(↑(s.bids w S j G M Z).card:ℝ) := by
      exact_mod_cast (show (f M Z).card ≤ _*_ from
        Finset.card_image_le.trans_eq (Finset.card_product ..))
    apply (h1.trans (mul_le_mul (hF M Z) (hb M Z) (Nat.cast_nonneg _) he.le)).trans_eq
    rw [←bp_add]; congr 1; ring
  · rw [atList,growth_value]

    refine Finset.mem_image.mpr ⟨(thermal p x S A,thermal p x S (src G)),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨hx,(s.bids_mem ..).mp hi⟩
    · change growing _ _ _ = _
      rw [show heat p x S z *ᵥ v=_ from column_observe (src G) z i x S]

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentTestWitnesses
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Test Witnesses -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 800000 in
theorem shooting {w : Wgt (UnitType p n N)} (hw : IsLaw w)
    (S : Party) (j : Bool) (k d : ℕ) (hh : k ≤ d) (l : ℝ) (hl : 0 < l)
    (h : 5*l ≤ pr (pairW w w) (fun x => s.frequent w S j (s.ix x.1) (s.ix x.2) x.2))
    (hC : ∀ C : Cov p N,cdim p C≤d → pr w (fun x => offsetCov (s.ix x) ≤ C) ≤ l)
    (hb : ∀ A M Z,(↑(s.bids w S j A M Z).card:ℝ) ≤ bp (0.51*N)) :
    ∃ (q : Place p→ℕ) (R : DTuple (p:=p) q N)
      (F : Catalog p T r q), ctot p q=k ∧
      (∀ i, Injective (R i).mulVec) ∧
      (∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N)) ∧ l^(k+1)≤pr w (s.atList S j R F) := by
  classical
  let A := UnitType p n N
  let u (x y : A) := s.frequent w S j (s.ix x) (s.ix y) y
  let B (y : A) := 3*l≤pr w (fun x => u x y)
  suffices he : ∃ (q : Place p→ℕ) (R : DTuple (p:=p) q N)
      (F : Catalog p T r q), ctot p q=k ∧
      (∀ i, Injective (R i).mulVec) ∧ (∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N)) ∧
      l^(k+1)≤pr w (fun x => B x ∧ s.atList S j R F x) by
    obtain ⟨a,b,c,h1,h2,h3,h4⟩ := he
    exact ⟨a,b,c,h1,h2,h3,h4.trans (pr_mono hw.nz fun x h => h.2)⟩
  induction k with
  | zero =>
    let q := fun _ : Place p => 0
    let R : DTuple (p:=p) q N := 0
    let F : Catalog p T r q := fun _ _ => {R}
    have heq x : s.atList S j R F x := mem_singleton.mpr (Subsingleton.elim _ _)
    refine ⟨q,R,F,by simp [ctot,q],fun i x y h => Subsingleton.elim _ _,by simp [F],?_⟩
    simp only [heq,and_true,Nat.zero_add,pow_one]
    have hf : 5*l ≤ avg w (fun y => pr w (fun x => u x y)) := by
      change 5*l≤avg (pairW w w) _ at h
      rw [pairW_avg,avg_avg] at h
      exact h
    have hg (y) : pr w (fun x => u x y) ≤ 3*l+ind (B y) := by
      by_cases hh : B y
      · rw [ind_one hh]; exact ((pr_le_tot hw.nz).trans hw.total.le).trans (by linarith)
      rw [ind_zero hh,add_zero]; exact le_of_not_ge hh
    have ha := hf.trans (avg_mono hw.nz hg)
    rw [avg_add,hw.avg_const] at ha
    unfold pr; linarith only [hl,ha]
  | succ k ih =>
    obtain ⟨q,R,F,h1,h2,h3,h4⟩ := ih (Nat.le_of_succ_le hh)
    let P := fun x => B x ∧ s.atList S j R F x
    let C := Bazaar.probed p R
    let Z := fun x => offsetCov (s.ix x) ≤ C
    have hD : pr w Z ≤ l := by
      apply hC C
      refine le_trans ?_ (Nat.le_of_succ_le hh)
      rw [←h1]
      exact Finset.sum_le_sum fun i _ => (R i).rank_le_card_width.trans_eq (Fintype.card_fin _)
    obtain ⟨x,hx,hg⟩ :
        ∃ x,¬ Z x ∧ l^(k+2)≤ pr w (fun y => P y ∧ u x y) := by
      have he :
          avg w (fun x => ind (¬Z x)*pr w (fun y => P y ∧ u x y)) =
          avg w (fun y => ind (P y)*pr w (fun x => u x y ∧ ¬Z x)) := by
        unfold pr; simp_rw [← avg_mul',ind_and]
        rw [avg_avg]; apply congrArg
        funext y; apply congrArg; ext; ring
      let f := fun x => ind (¬Z x)*pr w (fun y => P y ∧ u x y)
      have hu (y : A) (hy : P y) : 2*l ≤ pr w (fun x => u x y ∧ ¬Z x) := by
        have hi (x : A) (h : u x y) : Z x ∨ (u x y ∧ ¬ Z x) :=
          or_iff_not_imp_left.mpr fun hx => ⟨h,hx⟩
        have hf := (show 3*l ≤ pr w _ from hy.1).trans
          ((pr_mono hw.nz hi).trans (pr_or_le hw.nz))
        linarith
      have hp := pow_pos hl (k+2)
      have hi : l^(k+2)<avg w f := by
        unfold f; rw [he]
        calc l^(k+2) < (2*l)*l^(k+1) := by rw [pow_succ l (k+1)] at *; linarith
             _ ≤ (2*l)*pr w P := mul_le_mul_of_nonneg_left h4 (by linarith)
             _ ≤ _ := by
               unfold pr
               rw [← avg_mul']
               refine avg_mono hw.nz (fun y => ?_)
               by_cases hv : P y
               · rw [ind_one hv,mul_one,one_mul]
                 exact hu y hv
               simp only [ind_zero hv,mul_zero,zero_mul,le_refl]
      obtain ⟨x,hx⟩ : ∃ x,l^(k+2)<f x := by
        by_contra! hn; exact not_lt_of_ge (hw.avg_le hn) hi
      by_cases hz : Z x
      · have hg : f x=0 := by simp [f,hz]
        exact (not_lt_of_ge hp.le (hg ▸ hx)).elim
      exact ⟨x,hz, (show f x=pr w (fun y => P y ∧ u x y) from (by simp [f,hz])) ▸ hx.le⟩
    obtain ⟨q',R',F',hQ,hR,hF,hH⟩ :=
      s.extend_probe w S j R h1 h2 F h3 (s.ix x) hx (hb _)
    refine ⟨q',R',F',hQ,hR, ?_,hg.trans (pr_mono hw.nz (fun y h => ⟨h.1.1,hH y h.1.2 h.2⟩))⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hF

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AdaptiveRecordBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive Record Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 800000 in
private theorem probe_event {w : Wgt (UnitType p n N)} {Δ}
    (hw : IsLaw w) (h : s.opened Δ w)
    (S : Party) (j : Bool) (hi : S j=1) {k : ℕ}
    {q : Place p→ℕ} (R : DTuple (p:=p) q N) (F : Catalog p T r q)
    (hq : ctot p q=k) (hr : ∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N))
    (m : Mixer p n) {ε H : ℝ} (he₀ : initCap p N m ε) (hH : 0≤H) (hZ : quest p r k n N H ε)
    (hg : ∀ x,w x≤H*pairW (raw m N) (raw m N) x)
    (hT : num (Atlas p r T) ≤ bp (0.002*N)) :
    pr w (fun x => s.atList S j R F x ∧ glimpse p x j R) ≤ bp (-0.1*N) := by
  classical
  let P (M : Atlas p r T) (z : Batch M N) (v : DTuple (p:=p) q N) :=
    fun x => basisFrom p (x : UnitType p n N) j z ∧ glimpse p x j R ∧ thermal p x S R=v
  let L (M : Atlas p r T) (x) := standard M ∧ ∃ z,∃ v∈ F M z,P M z v x
  have he x : w x≠0 → s.atList S j R F x ∧ glimpse p x j R →
      ∃ M,L M x := by
    rintro hx ⟨hx',hy⟩
    exact ⟨s.ix x,(h x hx).1,s.bag (s.ix x) j x, thermal p x S R,hx',
      ((h x hx).2 j).1,hy,rfl⟩
  have ht (M : Atlas p r T) : pr w (L M) ≤ bp (-0.2*N) := by
    by_cases hu : standard M
    · let x := cells M
      have hb (z : Batch M N) :
          pr w (fun y => ∃ v∈F M z,P M z v y) ≤ bp (0.51*k*N)*(H*heatRate p n N ε x k) := by
        have ha v : pr w (P M z v) ≤ H*heatRate p n N ε x k := by
          rw [← hq]; exact (pr_cap hg _).trans
            (mul_le_mul_of_nonneg_left (heat_rate _ S hi R v z m he₀) hH)
        refine (pr_union_le hw.nz (F M z) (P M z)).trans ((Finset.sum_le_sum fun v _ => ha v).trans ?_)
        rw [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right (hr M z)
        unfold heatRate
        exact mul_nonneg hH (mul_nonneg (bp_pos _).le (bp_pos _).le)
      simp only [L,hu,true_and]
      refine (pr_exists_le hw.nz (fun z y => ∃ v∈F M z,P M z v y)).trans
        ((Finset.sum_le_sum (fun z _ => hb z)).trans ?_)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space]
      rw [show dim (Batch M N)=x*N from tuple_dim.trans (Nat.mul_comm ..),
        Nat.cast_mul, ← mul_assoc]
      exact hZ x hu.2.1
    simp only [L,hu,false_and,pr_false]
    exact (bp_pos _).le
  refine ((pr_on_mono hw.nz he).trans (pr_exists_le hw.nz L)).trans
    ((Finset.sum_le_sum fun i _ => ht i).trans ?_)
  rw [Finset.sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right hT (bp_pos _).le).trans
  rw [←bp_add]
  apply bp_le; linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]

set_option maxHeartbeats 600000 in
theorem frequent_sparse {w : Wgt (UnitType p n N)} {Δ}
    (hw : IsLaw w) (h : s.opened Δ w)
    (S : Party) (j : Bool) (hi : S j=1)
    (k d : ℕ) (hh : k ≤ d) (l : ℝ) (hl : 0< l)
    (hC : ∀ C : Cov p N,cdim p C≤d → pr w (fun x => offsetCov (s.ix x) ≤ C) ≤ l)
    (hb : ∀ A M Z,(↑(s.bids w S j A M Z).card:ℝ) ≤ bp (0.51*N))
    (m : Mixer p n) {ε H L : ℝ} (hN : 2*num (Full p n)-N≤ -1)
    (he : initCap p N m ε)
    (hH : 0≤H) (hZ : quest p r k n N H ε)
    (hg : ∀ x,w x≤H*pairW (raw m N) (raw m N) x)
    (hL : 0 ≤ L) (hv : bySide p w m L)
    (hT : num (Atlas p r T) ≤ bp (0.002*N))
    (hk : glimpsesBill p k L+bp (-0.1*N)<l^(k+1)) :
    pr (pairW w w) (fun x => s.frequent w S j (s.ix x.1) (s.ix x.2) x.2) ≤5*l := by
  classical
  by_contra! hr
  obtain ⟨q,R,F,hq,hR,hF,hx⟩ := s.shooting hw S j k d hh l hl hr.le hC hb
  have hp := s.probe_event hw h S j hi R F hq hF m he hH hZ hg hT
  have hq' z : q z≤ k := hq ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
    (Finset.mem_univ z)
  have hu := glimpse_failure m hL hv hw.sub j hN R k hR hq'
  let T := fun (x : UnitType p n N) => glimpse p x j R
  let V := s.atList S j R F
  have hh' x : V x → ¬T x ∨ (V x ∧ T x) := fun h => by by_cases ht:T x <;> simp [ht,h]
  exact not_lt_of_ge
    (hx.trans ((pr_mono hw.nz hh').trans ((pr_or_le hw.nz).trans (add_le_add hu hp)))) hk

end Bazaar

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseMomentBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Moment Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A : Type} [Fintype A]

theorem poweravg (w f : Wgt A) (s : ℕ) :
    avg w f ^ s=avg (draws (Fin s) w) (fun x => ∏ i : Fin s,f (x i)) := by
  classical
  change _=avg (prodW _) (prodW (fun _ : Fin s => f))
  rw [prodW_avg]; simp

theorem phase_power (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party) (s : ℕ)
    (hw : IsLaw w) (hg : ∀ x,|g x|≤1) (hs : S≠0) :
    avg (freeH p N) (fun q => (sweep p f w g S q)^s) ≤
      avg (draws (Fin s) w) (fun x => bp (- (p.h:ℝ)*epoch p (∑ i,f (x i)))) := by
  classical
  simp_rw [sweep,poweravg]
  rw [avg_avg]
  refine avg_mono (draws_law hw).nz fun x => ?_
  let y := ∑ i : Fin s,f (x i)
  have hh := free_phase y hs
  simp_rw [Finset.prod_mul_distrib,← wsign_sum,←map_sum,avg_mul']
  let T := ∏ i : Fin s,g (x i)
  have hi : T≤1 := by
    have he : |T| ≤ ∏ (_ : Fin s), (1:ℝ) := by
      unfold T; rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hg _)
    exact (le_abs_self _).trans (by simpa using he)
  exact ((mul_le_mul_of_nonneg_right hi hh.1).trans_eq (one_mul _)).trans hh.2

theorem abs_sweep (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party)
    (hw : IsLaw w) (hg : ∀ x,|g x|≤1) :
    ∀ q,|sweep p f w g S q| ≤1 := by
  intro q
  apply (abs_avg_le hw.nz).trans (hw.avg_le (fun x => ?_))
  rw [abs_mul, wsign_abs,mul_one]; exact hg x

theorem rare_sweep (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party)
    (hw : IsLaw w) (hg : ∀ x,|g x| ≤1) (hs : S≠0) (r m b : ℕ) (hr : ∀ x,epoch p (f x) ≤ r)
    (hm : 16*r < m) (hb : 1≤b)
    (c ψ : ℝ) (hc : 0 ≤ c) (hh : ∀ t : Cov p N,
      (∀ i, cdSign p t i ≤ r*(2^m*(2*b))) → pr w (fun i => covered p t (f i)) ≤ c)
    (hψ : 0<ψ) :
    pr (freeH p N) (fun y => ψ ≤ |sweep p f w g S y|) ≤
      exponentErr p m b c / ψ^(2^m*(2*b)) := by
  classical
  let s := 2^m*(2*b)
  let v := draws (Fin s) w
  let y := sweep p f w g S
  have he := phase_power p f w g S s hw hg hs
  have ht : avg (freeH p N) (fun q => (y q)^s) ≤ exponentErr p m b c := by
    apply le_trans he
    let k (x : Fin s→A) := epoch p (∑ i,f (x i))
    let t := bp (-(p.h:ℝ)*b / 2)
    have hg (x : Fin s→A) :
        bp (-(p.h:ℝ)*k x) ≤ ind (2*k x ≤ b)+t := by
      by_cases hl : 2*k x ≤ b
      · rw [ind_one hl]
        refine (bp_le (show -(p.h:ℝ)*k x ≤0 by
          exact mul_nonpos_of_nonpos_of_nonneg (by simp) (by positivity))).trans ?_
        rw [bp_zero]
        exact le_add_of_nonneg_right (bp_pos _).le
      rw [ind_zero hl,zero_add]
      apply bp_le
      have hh : (b:ℝ) ≤ 2*(k x:ℝ) := by exact_mod_cast (le_of_not_ge hl)
      have he := mul_le_mul_of_nonneg_left hh (show 0≤(p.h:ℝ) from Nat.cast_nonneg _)
      linarith only [he]
    have hv : IsLaw v := draws_law hw
    refine le_trans (avg_mono hv.nz hg) ?_
    rw [avg_add,hv.avg_const]
    exact add_le_add_left (no_cover_rank p f w hw m b r hb hm hr c hc hh) _
  have hEv : Even s := ⟨2^m*b, by unfold s; ring⟩
  have hi : avg (freeH p N) (fun q => |y q|^s) ≤ exponentErr p m b c := by
    have hs (q) : |y q|^s=y q^s := hEv.pow_abs _
    simp_rw [hs]; exact ht
  change pr (freeH p N) _ ≤ _/ψ^s
  apply (le_div_iff₀ (pow_pos hψ s)).mpr
  rw [mul_comm]
  let u := freeH p N
  have hu : IsLaw u := freeH_law p N
  refine (mul_le_mul_of_nonneg_left (pr_mono (q:=fun q => ψ^s ≤ |y q|^s) hu.nz
    (fun q h => pow_le_pow_left₀ hψ.le h s)) (pow_pos hψ s).le).trans ?_
  exact (le_avg_markov hu.nz (fun q => pow_nonneg (abs_nonneg (y q)) s) _).trans hi

theorem epoch_count (p : Shape) (N r : ℕ) :
    nbr (fun x : Ambient p N => epoch p x ≤ r) ≤ bp (2*(r:ℝ)*num (Comp p.g)*N) := by
  classical
  let P := fun (M : Mat (Fin N) (Fin N)) => M.rank ≤r
  have hi : ∀ x : Ambient p N,epoch p x ≤ r → ∀ i,P (x i) := fun x hx i =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le ((x i).rank)) (Finset.mem_univ i)).trans hx
  have hg : nbr (fun x : Ambient p N => ∀ i,P (x i)) =
      ∏ _ : Comp p.g,nbr P := by
    unfold nbr; simp_rw [ind_all]
    change tot (prodW (β:=fun _ : Comp p.g => Mat (Fin N) (Fin N)) (fun i a => ind (P a))) = _
    exact prodW_tot _
  refine (tot_mono (fun x => ind_mono (hi x))).trans ?_
  change nbr _ ≤ _
  rw [hg]
  let t := bp ((num (Fin N)+num (Fin N))*r)
  refine (Finset.prod_le_prod (g:=fun _ => t) (fun _ _ => nbr_nonneg P) (fun _ _ =>
    nbr_matrix_rank r)).trans_eq ?_
  simp only [t,Finset.prod_const,Finset.card_univ,← bp_mul_nat,num,Fintype.card_fin]
  congr 1; ring

set_option maxHeartbeats 800000 in
theorem pitch_no_cover (p : Shape) {N n} (Δ : UnitType p n N→ Ambient p N) {w}
    (hw : IsLaw w) (S R : Party) (hs : S ≠ 0)
    (r m b : ℕ) (hr : ∀ x,epoch p (Δ x) ≤ r)
    (hm : 16*r < m) (hb : 1≤b)
    (c ψ H : ℝ) (hc : 0 ≤ c) (hh : ∀ t : Cov p N,
      (∀ i, cdSign p t i ≤ r*(2^m*(2*b))) → pr w (fun i => covered p t (Δ i)) ≤ c)
    (hψ : 0<ψ) (hH : 0≤H) (mix : Mixer p n)
    (hN : 2*num (Full p n)-N≤ -1)
    (hc' : ∀ x,w x ≤ H * pairW (raw mix N) (raw mix N) x) :
    |pitch p Δ w S R| ≤ ψ+noSweepBudget p N m b r c ψ H := by
  classical
  let g (v : Ambient p N) (x : UnitType p n N) := wsign (tone p x R v)
  have hg v x : |g v x|≤1 := by simp [g]
  let y (v : Ambient p N) := sweep p Δ w (g v) S
  let Q := exponentErr p m b c / ψ^(2^m*(2*b))
  have h v := rare_sweep p Δ w (g v) S hw (hg v) hs r m b hr hm hb c ψ hc hh hψ
  let F' (v : Ambient p N) (x : UnitType p n N) := y v (listens p x)
  let A := {v : Ambient p N//epoch p v ≤ r}
  let B (x : UnitType p n N) := ∃ v : A, ψ ≤ |F' v.val x|
  have ha (x) : |F' (Δ x) x| ≤ ψ+ind (B x) := by
    by_cases h : ψ ≤ |F' (Δ x) x|
    · rw [ind_one (show B x from ⟨⟨Δ x,hr x⟩,h⟩)]
      exact (abs_sweep p Δ w _ S hw (hg _) _).trans (by linarith)
    exact le_trans (le_of_not_ge h) (le_add_of_nonneg_right (ind_nonneg _))
  have hZ : pitch p Δ w S R = avg w (fun x => F' (Δ x) x) := by
    rw [pitch,pairW_avg,avg_avg]
    simp_rw [wsign_add]
    rfl
  rw [hZ]
  refine ((abs_avg_le hw.nz).trans (avg_mono hw.nz ha)).trans ?_
  rw [avg_add,hw.avg_const]
  apply add_le_add_right
  have hz (v : A) :
      pr w (fun x => ψ ≤ |F' v.val x|) ≤ H*chanPrice p^2 * Q := by
    let P (y' : PhasePair p N) := ψ ≤ |y v.val y'|
    calc pr w (fun x => ψ ≤ |F' v.val x|)
      _ = pr (mapW w (listens p)) P := (mapW_pr w (listens p) P).symm
      _ ≤ _ := (pr_cap (phase_cap hH mix hc' hN) P).trans
         (mul_le_mul_of_nonneg_left (h _) (mul_nonneg hH (sq_nonneg _)))
  refine (pr_exists_le hw.nz (fun v : A => fun x => ψ ≤ |F' v.val x|)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hz i).trans ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  unfold noSweepBudget
  apply mul_le_mul_of_nonneg_right
  · exact (nbr_eq_card (fun v : Ambient p N => epoch p v ≤ r)).symm.trans_le (epoch_count p N r)
  · exact mul_nonneg (mul_nonneg hH (sq_nonneg _)) ((pr_nonneg (freeH_law p N).nz).trans
      (h (0:Ambient p N)))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseAlternativeSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem onW_ne {w : Wgt A} {P : A→Prop} {x : A} (h : onW w P x≠0) : P x ∧ w x≠0 := by
  have hh : subW w P x≠0 := fun hx => h (by unfold onW normW; rw [hx,zero_div])
  exact ⟨Classical.byContradiction (fun hx => hh (subW_carried _ _ _ hx)),
    left_ne_zero_of_mul hh⟩

theorem on_law {w : Wgt A} (hw : ∀ x,0 ≤ w x) {P : A→Prop} (hp : 0<pr w P) :
    IsLaw (onW w P) := normW_law (subW_nonneg hw _) hp
theorem onW_true (w : Wgt A) (h : IsLaw w) : onW w (fun _ => True)=w := by
  funext x
  simp only [onW_val,ind_true,mul_one,pr_true,h.total,div_one]
theorem on_both (w : Wgt A) (p q : A→Prop) (h : ∀ x,0≤ w x) (hp : 0<pr w p)
    (hq : 0< pr (onW w p) q) :
    onW (onW w p) q=onW w (fun x => p x∧q x) := by
  funext x
  rw [onW_val,onW_val,onW_val,pr_of_on h p q,ind_and]
  field_simp

theorem pr_shield {w : Wgt A} (h : ∀ x,0≤w x) (P Q : A→Prop) :
    pr w P-pr w (fun x => ¬Q x) ≤ pr w (fun x => P x ∧ Q x) := by
  have ht x : P x → (P x∧Q x) ∨ ¬Q x := fun h => by by_cases he:Q x <;> simp [h,he]
  exact sub_le_iff_le_add.mpr ((pr_mono h ht).trans (pr_or_le h))

theorem bySide_on {w : Wgt (UnitType p n N)} (m : Mixer p n)
    {H : ℝ} (hw : ∀ x,0≤w x) (hh : bySide p w m H)
    (P : UnitType p n N → Prop) {c : ℝ} (hc : 0 < c)
    (hp : c/2 ≤ pr w P) :
    bySide p (onW w P) m (rhUp H c) := by
  intro i x
  refine (mapW_cap (on_mon hw (show 0 < c/2 by linarith) hp) _ x).trans ?_
  unfold rhUp
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hh i x) (by positivity)

theorem pitch_turn (Δ : UnitType p n N → Ambient p N) (w S R) :
    pitch p Δ w S R=pitch p Δ w R S := by
  unfold pitch
  rw [pairW_avg,pairW_avg,avg_avg]
  refine avg_congr (fun x hx => avg_congr (fun y hy => ?_))
  exact congrArg wsign (add_comm _ _)

theorem tonal_left (Δ : UnitType p n N → Ambient p N) (w)
    (h : ∀ S R,S≠0 → |pitch p Δ w S R|<0.005) : tonalMix p Δ w := by
  rintro S R (he|he)
  · exact h _ _ he
  rw [pitch_turn]; exact h _ _ he

theorem glimpse_sub (x : UnitType p n N) (i : Bool) (C : Cov p N) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) (h : ∀ z,colSp (A z) ≤ C z) (hA : ∀ z,Injective (A z).mulVec)
    (hg : glimpse p x i (q:=fun z => dim (C z)) (fun z => pack (C z))) :
    glimpse p x i A := by
  classical
  intro z
  obtain ⟨X,hX⟩ := pull_cols (pack (C z)) (A z) (by rw [colSp_pack]; exact h z)
  have hI : Injective X.mulVec := by
    have ht := hA z
    rw [←hX] at ht
    intro a b h
    apply ht
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,h]
  rw [←hX,← Matrix.mul_assoc]; exact inj_comp_mat _ _ (hg z) hI

theorem glimpse_cover_failure {w : Wgt (UnitType p n N)} (hv : SubLaw w) (m : Mixer p n)
    {L : ℝ} (h : bySide p w m L) (hL : 0 ≤ L)
    (C : Cov p N) (d : ℕ) (hd : cdim p C≤d)
    (hN : 2*num (Full p n)-N ≤ -1) :
    pr w (fun x => ¬preGlimpse x C) ≤ 2*glimpsesBill p d L := by
  classical
  let M : DTuple (p:=p) (fun z => dim (C z)) N := fun z => pack (C z)
  let P (i : Bool) := fun x : UnitType p n N => ¬glimpse p x i M
  have hp x : ¬preGlimpse x C → ∃ i,P i x := by
    intro h
    unfold preGlimpse at h; push Not at h; exact h
  have hh z : dim (C z) ≤ d :=
    (Finset.single_le_sum (fun z _ => Nat.zero_le (dim (C z))) (Finset.mem_univ z)).trans hd
  refine ((pr_mono hv.nz hp).trans (pr_exists_le hv.nz P)).trans ?_
  rw [Fintype.sum_bool,two_mul]
  exact add_le_add (glimpse_failure m hL h hv true hN M d (fun z => pack_inj _) hh)
    (glimpse_failure m hL h hv false hN M d (fun z => pack_inj _) hh)

namespace Bazaar

variable {T : Cov p N}
variable (s : Bazaar p n r T)

set_option maxHeartbeats 600000 in
theorem cover_options (Δ : UnitType p n N →Ambient p N) (w : Wgt (UnitType p n N))
    (m : Mixer p n) {ε L H l : ℝ} (hw : IsLaw w) (h : s.opened Δ w)
    (hem : IsLaw (raw m N)) (hi : initCap p N m ε)
    (hl : 0 ≤ L) (he₀ : 0< l) (he' : l≤1) (hL : bySide p w m L)
    (hH : 0 ≤ H) (hF : ∀ x,w x≤H*pairW (raw m N) (raw m N) x)
    (hN : 2*num (Full p n)-N≤ -1)
    (ht : num (Atlas p r T) ≤ bp (0.002*N))
    (hd : selPrice p r n N L ε) (hd' : selPrice p r n N (rhUp L l) ε)
    (k d : ℕ) (hK : k≤d) (hQ : quest p r k n N H ε)
    (hk : glimpsesBill p k L+bp (-0.1*N)<l^(k+1))
    (hg : 2*glimpsesBill p d L≤l/2)
    (hψ : 5*l+bp (-0.24*N)<0.005) :
    ∃ P : UnitType p n N→Prop,
      l/2≤pr w P ∧ (tonalMix p Δ (onW w P) ∨ tonalTiny p Δ (onW w P) d) := by
  classical
  let bite (C : Cov p N) := fun x => offsetCov (s.ix x) ≤ C
  by_cases hh : ∀ C,cdim p C≤d → pr w (bite C) ≤ l
  · refine ⟨fun _ => True,by rw [pr_true,hw.total]; linarith, Or.inl ?_⟩
    rw [onW_true w hw]; apply tonal_left Δ w
    intro S R hS
    obtain ⟨j,hj⟩ : ∃ i,S i=1 := by
      by_contra! he
      exact hS (funext fun i => (bit_cases (S i)).resolve_right (he i))
    have heq := s.calm_pitch h hw j R S m hem hi hl hL hd ht
    have hφ := s.frequent_sparse hw h S j hj k d hK l he₀ hh
      (fun A G Z => s.bids_bound S j A G Z hw.sub (bag_rate m hl hem hi hw.sub hL h hd G j))
      m hN hi hH hQ hF hl hL ht hk
    exact ((heq.trans (add_le_add_left hφ _))).trans_lt hψ
  push Not at hh
  obtain ⟨C,hC,hX⟩ := hh
  let P := fun x : UnitType p n N => bite C x ∧ preGlimpse x C
  have hp : l/2≤pr w P := by
    have ht := glimpse_cover_failure hw.sub m hL hl C d hC hN
    have hh := pr_shield hw.nz (bite C) (fun x => preGlimpse x C)
    change _ ≤ pr w P at hh
    linarith only [hh,hg,ht,hX]
  let v := onW w P
  have hv : IsLaw v := on_law hw.nz (lt_of_lt_of_le (half_pos he₀) hp)
  have he x (h' : v x≠0) : standard (s.ix x) ∧ ∀ i, compFor (s.ix x)
      (s.bag (s.ix x) i x) (imageP p x i) (Δ x) := h x (onW_ne h').2
  have ht' (x y : UnitType p n N) (hx : v x≠0) (hy : v y≠0) (i) :
      glimpse p y i (src (s.ix x)) := by
    have hh := he x hx
    exact glimpse_sub y i C _ (onW_ne hx).1.1 hh.1.2.2 ((onW_ne hy).1.2 i)
  have hUp := bySide_on m hw.nz hL P he₀ hp
  refine ⟨P,hp,Or.inr ⟨C,hC,fun x hx => ?_,fun i R => ?_⟩⟩
  · obtain h := ((he x hx).2 true).2
    rw [h]; exact covered_spelled (s.ix x) _ C (onW_ne hx).1.1
  exact (s.single_pitch he hv i R m hem hi (by unfold rhUp; positivity) hUp hd' ht hN).2
    (fun x hx y hy => ht' x y hx hy i)

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FinitePhaseAlternative
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Phase Alternative -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}

theorem framesCost {w : Wgt (UnitType p n N)} (hw : SubLaw w) (m : Mixer p n)
    {H : ℝ} (hl : 0≤ H) (hh : bySide p w m H) (hN : 2*num (Full p n)-N≤ -1)
    (T : Cov p N) (r : ℕ) (hT : ∀ i,cdSign p T i ≤r) :
    pr w (fun x => ¬voidFrame p x T) ≤ scaleBill p n N r H := by
  classical
  let P := fun i : Place p × Bool => fun x => ¬ Disjoint (imageP p (x : UnitType p n N) i.2 i.1)
      (T i.1)
  have h x : ¬voidFrame p (n:=n) x T → ∃ i,P i x := by
    intro h
    unfold voidFrame at h; push Not at h
    obtain ⟨i,z,h⟩ := h
    exact ⟨(z,i),fun he => h he.symm⟩
  let Y := H*2 * bp (num (Row p n)+r-N)
  have hr i : pr w (P i) ≤ Y := by
    rcases i with ⟨⟨z,b⟩,i⟩
    have hh' : dim (T (z,b)) ≤ r :=
      (Finset.single_le_sum (fun j _ => Nat.zero_le (dim (T (j,b)))) (Finset.mem_univ z)).trans
        (hT b)
    exact (any_frame_hit m hl hh i _ hN _).trans (mul_le_mul_of_nonneg_left (bp_le (by
      have hf : (dim (T (z,b)):ℝ) ≤ r := by exact_mod_cast hh'
      linarith only [hf])) (by positivity))
  refine ((pr_mono hw.nz h).trans (pr_exists_le hw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hr i).trans_eq ?_
  simp only [Y,scaleBill,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num,Fintype.card_prod,
    Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]

private theorem mark_bazaar (m : BMark p n N) {v : Wgt (UnitType p n N)}
    {T : Cov p N} (h : ∀ x,v x≠0 → covered p T (delta m x) ∧ voidFrame p x T ∧
       delta m x≠0 ∧ epoch p (mrAmbient m x true) ≤ r) :
    ∃ s : Bazaar p n r T,s.opened (delta m) v := by
  classical
  have he x : ∃ s : Atlas p r T,
      v x≠0 →
        standard s ∧ ∀ i,∃ A,compFor s A (imageP p x i) (delta m x) := by
    by_cases he : v x≠0
    · obtain ⟨hC,hV,hD,hR⟩ := h x he
      obtain ⟨X,hX,hY⟩ := delta_offset m x hC hD hV hR
      exact ⟨X,fun _ => ⟨hX,hY⟩⟩
    exact ⟨default,fun hs => (he hs).elim⟩
  choose f hf using he
  choose A hA using
    show ∀ (M : Atlas p r T) (i : Bool) (x), ∃ A,
        M=f x → v x≠0 → compFor M A (imageP p x i) (delta m x) from by
      intro M i x
      by_cases hs : v x=0
      · exact ⟨0,fun _ hh => (hh hs).elim⟩
      by_cases he : M=f x
      · subst M
        obtain ⟨A,hA⟩ := (hf x hs).2 i
        exact ⟨A,fun _ _ => hA⟩
      exact ⟨0,fun H => (he H).elim⟩
  exact ⟨⟨f,A⟩,fun x h => ⟨(hf x h).1,fun i => hA _ i x rfl h⟩⟩

set_option maxHeartbeats 800000 in
theorem phase_alternative {w : Wgt (UnitType p n N)}
    (mark : BMark p n N)
    {c l ψ ε L H : ℝ} {m b k d : ℕ}
    (mix : Mixer p n) (hr : PhaseReady p n N m b r k d mix c l ψ ε L H)
    (hw : IsLaw w)
    (hk : bySide p w mix L)
    (hv : ∀ x,w x≤H * pairW (raw mix N) (raw mix N) x)
    (hh : ∀ x,w x≠0 → delta mark x≠0 ∧ epoch p (mrAmbient mark x true) ≤ r)
    (hK : ∀ x,epoch p (delta mark x) ≤r) :
    ∃ P : UnitType p n N→Prop,(c/2)*(l/2)≤pr w P ∧
      (tonalMix p (delta mark) (onW w P) ∨ tonalTiny p (delta mark) (onW w P) d) := by
  classical
  have hc := hr.hc
  have hl := hr.hl
  by_cases he : ∀ T : Cov p N, (∀ i,cdSign p T i ≤ maxSpan m b r) →
      pr w (fun i => covered p T (delta mark i)) ≤ c
  · refine ⟨fun _ => True,?_,Or.inl ?_⟩
    · rw [pr_true,hw.total]
      nlinarith [hr.hc',hr.hl']
    rw [onW_true w hw]
    apply tonal_left _ _
    intro S R hS
    exact (pitch_no_cover p _ hw S R hS _ _ _ hK hr.hm hr.hb c ψ H hc.le he
      hr.hψ hr.hH mix hr.hN hv).trans_lt hr.noBranch
  push Not at he
  obtain ⟨T,hT,hW⟩ := he
  let P := fun x : UnitType p n N => covered p T (delta mark x) ∧ voidFrame p x T
  let v := onW w P
  have hp : c/2≤pr w P := by
    have he := framesCost hw.sub mix hr.hL hk hr.hN T (maxSpan m b r) hT
    have hs := pr_shield hw.nz (fun x => covered p T (delta mark x)) (fun x => voidFrame p x T)
    change _ ≤ pr w P at hs
    linarith only [hr.frames,hW,he,hs]
  have hpp : 0<pr w P := lt_of_lt_of_le (half_pos hc) hp
  have hf : IsLaw v := on_law hw.nz hpp
  obtain ⟨s,h⟩ := mark_bazaar (r:=r) mark
    (show ∀ x,v x≠0 → covered p T (delta mark x) ∧ voidFrame p x T ∧ delta mark x≠0 ∧
       epoch p (mrAmbient mark x true) ≤ r from fun x h => by
      obtain ⟨⟨ha,hb⟩,ht⟩ := onW_ne h; exact ⟨ha,hb,hh x ht⟩)
  have hH := hr.hH; have hL := hr.hL
  have hm : IsLaw (raw mix N) := raw_law mix (by linarith only [hr.hN])
  have he x : v x ≤ rhUp H c * pairW (raw mix N) (raw mix N) x := by
    apply (on_mon hw.nz (half_pos hc) hp x).trans
    unfold rhUp; rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hv x) (by positivity)
  obtain ⟨Q,hQ,hV⟩ := s.cover_options _ v mix hf h hm hr.cap
    (by unfold rhUp; positivity) hl hr.hl' (bySide_on mix hw.nz hk P hc hp)
    (by unfold rhUp; positivity) he hr.hN (hr.atlas T hT) hr.price hr.price'
    k d hr.hk hr.localQ hr.testFailure hr.testFailure' hr.beatSlack
  refine ⟨fun x => P x ∧ Q x,?_,?_⟩
  · rw [pr_of_on hw.nz]
    exact mul_le_mul hp hQ (by positivity) hpp.le
  rw [← on_both w P Q hw.nz hpp (lt_of_lt_of_le (half_pos hl) hQ)]
  exact hV

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

theorem const (hz : Tendsto z l atTop) {a : ℝ} (ha : 0<a) : warm l z (fun _=>a) := by
  intro ε he
  exact (((bp_tendsto_zero he).comp hz).eventually (gt_mem_nhds ha)).mono (fun _ h=> h.le)
theorem mono (h : warm l z x) (hg : ∀ᶠ i in l,x i≤ y i) : warm l z y := fun ε he=>
  (h ε he).mp (hg.mono fun _ hi h=>h.trans hi)
theorem positive (h : warm l z x) : ∀ᶠ i in l,0<x i :=
  (h 1 zero_lt_one).mono (fun _ hi => (bp_pos _).trans_le hi)

theorem mul (h : warm l z x) (hg : warm l z y) : warm l z (fun i=> x i*y i) := by
  intro ε he
  filter_upwards [h (ε/2) (half_pos he),hg (ε/2) (half_pos he)] with i hi hj
  rw [show -ε*z i= -(ε/2)*z i + -(ε/2)*z i from by ring,bp_add]
  exact mul_le_mul hi hj (bp_pos _).le ((bp_pos _).le.trans hi)
end warm

theorem taking {X : A→ Type*} [∀ n,Nonempty (X n)]
    {P : ∀ n,X n→Prop} (h : ∀ᶠ n in l,∃ w:X n,P n w) :
    ∃ w:∀ n,X n,∀ᶠ n in l,P n (w n) := by
  classical
  let f n:= if h:∃ w,P n w then h.choose else Classical.choice (inferInstance:Nonempty (X n))
  refine ⟨f,h.mono (fun n hn=>?_)⟩
  unfold f; rw [dite_eq_left hn]; exact hn.choose_spec

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

theorem tinyPhase_pos (g r : ℕ) (D : ℝ) : 0< tinyPhase g r D := bp_pos _

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

theorem strength.slide (h : strength s w μ D ζ K) (hD : D≤E) (hζ : ζ≤η)
    (hk : K≤L) (hμ : ∀ x,0≤μ x) : strength s w μ E η L := by
  classical
  refine ⟨h.part,fun i hi=>?_⟩
  have hh:=h.leaf _ hi
  refine ⟨hh.pos,hh.fixpin,hh.bound.trans hk,fun b=>?_,fun x=>?_⟩
  · refine (hh.clear b).trans (bp_le ?_)
    gcongr
  exact (hh.density x).trans (mul_le_mul_of_nonneg_right (bp_le (by gcongr)) (hμ _))

theorem sapLaw (h : 0 < s.amount w) (hw : IsLaw w) : IsLaw (s.sap w) := on_law hw.nz h

theorem in_parent {P : X p n N → Prop} (h : s.within P) {x} (he : inTiles s.T x) : P x :=
  h he.choose he.choose_spec.1 _ he.choose_spec.2
theorem present {x} (h : s.sap w x≠0) : inTiles s.T x ∧ w x≠0 := onW_ne h

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreparedPopulationTrimming
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prepared Population Trimming -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M} {b : Sketch p M}

theorem retainInitial (hl : l≤atTop) (hq : q.planted p M)
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n)) :
    durable q l p M m w s := by
  refine ⟨((warm.const (trend_sizes l hl hq.hM).2 (by norm_num : 0<(1/2:ℝ))).mono
    (hx.mono fun i hi=> hi.weight)),?_⟩
  filter_upwards [hx] with n hn
  have hh := hq.early
  refine ⟨hn.strength.slide ?_ ?_ ?_ (fun x=> mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)),
    fun i hi x hx => (hn.onTile i hi x hx).2.2.2⟩
  · unfold leafNew; linarith [(Nat.cast_nonneg q.u : 0≤(q.u:ℝ)),(Nat.cast_nonneg q.s :
      0≤(q.s:ℝ))]
  · linarith only [hh.pos]
  unfold pins; omega

variable {P : Campaign p M}

theorem citable.on_law (h : citable q l p M m w s b P)
    (hl : l ≤ atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n)) :
    ∀ᶠ n in l, IsLaw (potion s w P n) := by
  filter_upwards [h.mass.positive,hw,(retainInitial hl hq hx).mass.positive] with n hn ht hv
  exact HadwigerCounterexample.on_law (LeafMixture.sapLaw hv ht.law).nz hn

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhasePreparedOutcomes
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Prepared Outcomes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P Q : Campaign p M}

theorem citable_interpose (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (h : warm l (fun i=>((M*i:ℕ):ℝ)) (fun i=> pr (potion s w P i) (Q i))) :
    let Y:= fun i x=> P i x∧Q i x
    q.citable l p M m w s b Y ∧
    ∀ᶠ n in l,potion s w Y n=onW (potion s w P n) (Q n) := by
  classical
  let Y : Campaign p M := fun i x=>P i x∧Q i x
  have hz : ∀ᶠ n in l, IsLaw ((s n).sap (w n)) := by
    filter_upwards [hw,hx] with n hn h
    exact LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) h.weight) hn.law
  have hm : citable q l p M m w s b Y := by
    refine ⟨(hb.mass.mul h).mono ?_,hb.forecast, hb.mark.mono fun i hi j hj x hx h =>hi j hj x hx h.1⟩
    filter_upwards [hz] with n hn
    exact (pr_of_on hn.nz (P n) (Q n)).symm.le
  refine ⟨hm,?_⟩
  filter_upwards [hz,hb.mass.positive,h.positive] with n hn ht he
  exact (on_both ((s n).sap (w n)) (P n) (Q n) hn.nz ht he).symm

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreliminaryRestrictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preliminary Restrictions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass
namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P : Campaign p M}

theorem pollen_pos : 0<pollen := by unfold pollen; positivity

theorem pollen_price :
    (pollen⁻¹:ℝ)*2≤bp 100 := by
  rw [show (100:ℝ)=(↑(100:ℕ):ℝ) from by norm_num,bp_nat]
  unfold pollen; norm_num

theorem potency {w : Wgt (UnitType p n N)} {s : LeafMixture p n N} (hw : IsLaw w)
    (hs : (1/2:ℝ) ≤ s.amount w) (P : UnitType p n N→Prop) (hP : pollen ≤ pr (s.sap w) P) (x) :
    onW (s.sap w) P x ≤ bp (100)*w x := by
  have hm:=LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) hs) hw
  have he (x) : s.sap w x ≤ 2*w x := (on_mon hw.nz (by norm_num) hs x).trans_eq (by norm_num)
  calc
    onW (s.sap w) P x ≤ (pollen)⁻¹* s.sap w x := on_mon hm.nz pollen_pos hP x
    _ ≤ _ := by
       refine (mul_le_mul_of_nonneg_left (he x) (inv_nonneg.mpr pollen_pos.le)).trans ?_
       rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right pollen_price (hw.nz _)

theorem dosed.stake (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P) :
    ∀ᶠ n in l, let N:=M*n; let v := potion s w P n
      IsLaw v ∧ bySide p v (m n) q.spear ∧ ∀ x,v x ≤ bp (q.spJoint*N)*usual p (m n) N x := by
  classical
  filter_upwards [hx,hw,hb.lower,hb.cite.on_law hl hq hw hx,
    (trend_sizes l hl hq.hM).2.eventually (eventually_ge_atTop 100)]
    with n hx hw h ht hN
  let N:=M*n; let v:=potion s w P n
  have hh (x) : v x ≤ bp (100)*w n x := potency hw.law hx.weight (P n) h x
  refine ⟨ht,LeafMixture.upperSide hw.border hh (bp_pos _).le le_rfl,fun x=>?_⟩
  apply (hh x).trans
  apply (mul_le_mul_of_nonneg_left (hw.total x) (bp_pos _).le).trans
  rw [←mul_assoc, ←bp_add]
  refine mul_le_mul_of_nonneg_right (bp_le ?_) (show 0≤usual p (m n) (M*n) x from
    mul_nonneg (raw_nonneg ..) (raw_nonneg ..))
  unfold spJoint; linarith only [hN]

private theorem epic_bounds (p : Shape) (z : BMark p n N) (x : UnitType p n N)
    (h : ∀ i,totalRank (z x i)≤q.e) :
    epoch p (delta z x) ≤ q.rank ∧ ∀ i,epoch p (mrAmbient z x i)≤ q.rank := by
  classical
  have hm i : epoch p (mrAmbient z x i) ≤ q.e :=
    (Finset.sum_le_sum (s:=Finset.univ) (g:=fun j:Comp p.g=>(z x i j).rank)
      (fun j _=> rank_lift_le _ _ _)).trans (h i)
  have hh : epoch p (delta z x) ≤
      epoch p (mrAmbient z x true)+epoch p (mrAmbient z x false) := by
    unfold epoch; rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => mrk_add_le ..
  have hi : q.e+q.e≤q.rank := by unfold rank; omega
  exact ⟨hh.trans ((add_le_add (hm _) (hm _)).trans hi),fun i=>(hm i).trans (by unfold rank; omega)⟩

set_option maxHeartbeats 900000 in
theorem phaseSplit_oai (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P)
    (he : ∀ᶠ n in l, (s n).within
      (fun x=> P n x → delta (b.m n) x ≠ 0)) :
    ∃ R : Campaign p M, q.citable l p M m w s b R ∧ ∀ᶠ n in l,
      let v:=potion s w R n
      tonalMix p (delta (b.m n)) v ∨ tonalTiny p (delta (b.m n)) v q.d := by
  classical
  let c:=(tinyPhase p.g q.rank q.spJoint / 2)*(coin/2)
  have hc : 0 < c := mul_pos (half_pos (tinyPhase_pos ..)) (by norm_num [coin])
  let v:=potion s w P
  let R n (A : UnitType p n (M*n) → Prop) :=
      c ≤ pr (v n) A ∧
        (tonalMix p (delta (b.m n)) (onW (v n) A) ∨ tonalTiny p (delta (b.m n)) (onW (v n) A) q.d)
  obtain ⟨A,hA⟩ : ∃ A : Campaign p M,∀ᶠ n in l, R n (A n) := by
    refine taking ?_
    filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hb.capped]
      with n hn ht hv he
    have hh (x) := epic_bounds p (b.m n) x (he x)
    change ∃ _,c≤_∧_
    refine phase_alternative (b.m n) (m n) (ht.2.2.2.1 _) hn.1 hn.2.1 hn.2.2 (fun x hx => ?_)
      (fun x=>(hh x).1)
    obtain ⟨hp,hx⟩:= onW_ne hx
    exact ⟨LeafMixture.in_parent hv (LeafMixture.present hx).1 hp,(hh x).2 _⟩
  have hx' : warm l (fun i=> ((M*i:ℕ):ℝ)) (fun i=>pr (v i) (A i)) :=
    (warm.const (trend_sizes l hl hq.hM).2 hc).mono (hA.mono fun i hi=>hi.1)
  obtain ⟨h1,h2⟩:= citable_interpose hw hx hb.cite hx'
  refine ⟨_,h1,?_⟩
  filter_upwards [h2,hA] with n hn ht
  dsimp only; rw [hn]
  exact ht.2

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.PreparationParameters.phaseSplit_oai := @OAI.HadwigerCounterexample.PreparationParameters.phaseSplit_oai
