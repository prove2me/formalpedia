-- Prove2me | solution 1 for OAI.HadwigerCounterexample.exists_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:56.188673+00:00
-- url     : https://prove2.me/submissions/fde67784-1da7-46ee-bec3-1fc4ec55f51d

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

theorem IsLaw.avg_le (hw : IsLaw w) {b : ℝ} (h : ∀ x, f x ≤ b) : avg w f ≤ b :=
  (avg_mono hw.nz h).trans (hw.avg_const _).le

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

end Basic

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}

omit [Fintype α] in
theorem subW_nonneg (hw : ∀ x, 0 ≤ w x) (p : α → Prop) : ∀ x, 0 ≤ subW w p x :=
  fun x => mul_nonneg (hw x) (ind_nonneg _)

omit [Fintype α] in
theorem subW_le (hw : ∀ x, 0 ≤ w x) (p : α → Prop) (x : α) : subW w p x ≤ w x :=
  (mul_le_mul_of_nonneg_left (ind_le_one _) (hw x)).trans_eq (mul_one _)

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

theorem subLaw_pair {w : Wgt A} {v : Wgt B} (hw : SubLaw w) (hv : SubLaw v) :
    SubLaw (pairW w v) := by
  refine ⟨fun x => mul_nonneg (hw.nz _) (hv.nz _),?_⟩
  rw [pairW_tot]
  exact (mul_le_mul hw.total hv.total (tot_nonneg hv.nz) (by norm_num)).trans_eq (one_mul _)

theorem unifOn_slice (p : A × B → Prop) (x : A) (y : B) :
    unifOn p (x,y) =
      mapW (unifOn p) Prod.fst x * unifOn (fun y => p (x,y)) y := by
  classical
  have hm : mapW (unifOn p) Prod.fst x =
      nbr (fun y => p (x,y)) / nbr p := by
    simp only [mapW,pr,avg,Fintype.sum_prod_type,unifOn_val, nbr,tot]
    rw [Finset.sum_eq_single x]
    · simp [ind_true,div_eq_mul_inv,Finset.sum_mul]
    · intro b _ hb
      simp [ind,hb]
    · simp
  rw [hm,unifOn_val,unifOn_val]
  by_cases h : p (x,y)
  · have hh {A : Type} [Fintype A] (p : A → Prop) (x : A) (hx : p x) : 0 < nbr p := by
      have hp := weight_le_tot (fun y => ind_nonneg (p y)) x
      exact lt_of_lt_of_le (ind_one hx ▸ zero_lt_one) hp
    rw [ind_one h]
    have hv := hh _ _ h
    have hw := hh (fun y => p (x,y)) _ h
    field_simp
  · rw [ind_zero h]
    ring

theorem unifOn_and (p q : A → Prop) :
    onW (unifOn p) q = unifOn (fun x => p x ∧ q x) := by
  classical
  have hp : pr (unifOn p) q = nbr (fun x => p x ∧ q x) / nbr p := by
    simp only [pr,avg,unifOn_val,div_eq_mul_inv,ind_and,nbr,tot,Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  funext x
  rw [onW_val,hp,unifOn_val,unifOn_val,ind_and]
  by_cases h : p x
  · by_cases g : q x
    · have hl (p : A → Prop) (h : p x) : 0 < nbr p :=
        lt_of_lt_of_le (ind_one h ▸ zero_lt_one) (weight_le_tot (fun y => ind_nonneg (p y)) x)
      have hh := hl p h
      have hg := hl (fun x => p x ∧ q x) ⟨h,g⟩
      field_simp
    · rw [ind_zero g]
      ring
  · rw [ind_zero h]
    ring

theorem pr_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c*v x) (p : A → Prop) :
    pr w p ≤ c*pr v p := calc
  _ ≤ pr (fun x => c*v x) p := pr_mono_left (w:=w) (v:=fun x => c*v x) h _
  _ = _ := by simp only [pr,avg,Finset.mul_sum,mul_assoc]

theorem semi_avg (w : Wgt A) (k : A → Wgt B) (f : A × B → ℝ) :
    avg (semi w k) f = avg w (fun x => avg (k x) (fun y => f (x,y))) := by
  simp only [avg,semi,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem pair_semi_avg (w w' : Wgt A) (k k' : A → Wgt B) (f : (A × B) × (A × B) → ℝ) :
    avg (pairW (semi w k) (semi w' k')) f =
      avg (pairW w w') (fun x =>
        avg (pairW (k x.1) (k' x.2)) (fun y => f ((x.1,y.1), (x.2,y.2)))) := by
  simp only [pairW_avg, semi_avg]
  refine avg_congr fun x _ => ?_
  exact avg_avg _ _ _

theorem pair_semi_pr (w w' : Wgt A) (k k' : A → Wgt B) (p : A × A → Prop) (q : B × B → Prop) :
    pr (pairW (semi w k) (semi w' k')) (fun x => p (x.1.1,x.2.1) ∧ q (x.1.2,x.2.2)) =
      avg (pairW w w') (fun x => ind (p x) * pr (pairW (k x.1) (k' x.2)) q) := by
  unfold pr
  rw [pair_semi_avg]
  simp_rw [ind_and]
  refine avg_congr fun x _ => ?_
  exact avg_mul' _ _ _

variable [Fintype I] [DecidableEq I]

/-- Reassociate two arrays of independent columns into componentwise independent pairs. -/
theorem prodW_pair_pr (w v : I → Wgt A) (p : I → A × A → Prop) :
    pr (pairW (prodW w) (prodW v)) (fun x => ∀ i, p i (x.1 i,x.2 i)) =
      ∏ i, pr (pairW (w i) (v i)) (p i) := by
  simp_rw [pr,ind_all,pairW_avg]
  have hx (x : I → A) :
      avg (prodW v) (fun y => ∏ i, ind (p i (x i,y i))) =
        ∏ i, avg (v i) (fun y => ind (p i (x i,y))) :=
    prodW_avg _ (fun i y => ind (p i (x i,y)))
  simp_rw [hx]
  exact prodW_avg w (fun i x => avg (v i) (fun y => ind (p i (x,y))))

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

omit [Fintype I] in
theorem colSp_dim (P : Mat I J) : dim (colSp P) = P.rank := rfl

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentCoordinates
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moment Coordinates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

theorem card_row (p : Shape) (n : ℕ) :
    Fintype.card (Row p n) = psize p * (1 + (p.g*p.g+3)*n) := by
  simp [Row,AIdx,psize,add_comm]

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

theorem bp_poly_dom {a : ℝ} (ha : 0 < a) (c d : ℝ) :
    ∀ᶠ x : ℝ in atTop, c*x^d < bp (a*x) := by
  have hla : 0 < Real.log 2 * a := mul_pos (Real.log_pos (by norm_num)) ha
  have h := tendsto_exp_mul_div_rpow_atTop d _ hla
  filter_upwards [h.eventually (eventually_gt_atTop c), eventually_gt_atTop (0:ℝ)] with x hx hx'
  change c < Real.exp ((Real.log 2*a)*x)/x^d at hx
  rw [lt_div_iff₀ (by positivity)] at hx
  rwa [bp, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← mul_assoc]

theorem bp_poly_dom_nat {a : ℝ} (ha : 0 < a) (c : ℝ) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, c*(n:ℝ)^d < bp (a*n) := by
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (bp_poly_dom ha c d)
  simpa using h

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
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem plus_marginal {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x) :
    mapW (unifOn (FramesAt (U:=U) C)) Prod.fst =
      unifOn (fun x => Injective x.mulVec) := by
  have he : Injective (1:Mat I I).mulVec := fun x y h => by simpa using h
  simpa using framesAt_observe_plus hc he

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixedImageBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

/-- Exact image tests under a translate-stable minus (or plus) pair law cost
dim T bits per vector. Directions mix both endpoints in one direct sum. -/
theorem mixed_cap {w w' : Wgt (Mat U I)} (hw : SubLaw w) (hw' : SubLaw w')
    (T : Space (Vec U)) (hT : columnInv (w:=w) T) (hT' : columnInv (w:=w') T)
    (D : Mat (I ⊕ I) J) (hD : Injective D.mulVec) (M : Mat U J) :
    pr (pairW w w') (fun x => mixImage D x = M) ≤ bp (- (dim T:ℝ)*num J) := by
  let n := dim T
  obtain ⟨F,hF⟩ := mat_left_inv hD
  obtain ⟨R,hR⟩ := mat_left_inv (pack_inj T)
  have hi : Injective (fun A : Mat (Fin n) J => pack T * A) := by
    intro A B h
    have he := congrArg (R * ·) h
    simpa only [← Matrix.mul_assoc,hR,Matrix.one_mul] using he
  let e : Mat (Fin n) J ↪ Mat U J := ⟨(pack T * ·),hi⟩
  let f : (Mat U I × Mat U I) →ₗ[HadwigerCounterexample.F] Mat U J := mixImageLin D
  have he (t : Mat (Fin n) J) :
      ∃ x, f x = e t ∧ ∀ y, pairW w w' (y+x) = pairW w w' y := by
    let A := t*F
    let B := pack T * A.toCols₁
    let C := pack T * A.toCols₂
    have hu (G : Mat (Fin n) I) : colSp (pack T * G) ≤ T := by
      rintro x ⟨y,rfl⟩
      change (pack T * G) *ᵥ y ∈ T
      rw [← Matrix.mulVec_mulVec]
      have hg : pack T *ᵥ (G *ᵥ y) ∈ colSp (pack T) := ⟨G *ᵥ y,rfl⟩
      rwa [colSp_pack] at hg
    refine ⟨(B,C),?_,fun y => ?_⟩
    · have hx : fromCols A.toCols₁ A.toCols₂ = A := by ext i j; cases j <;> rfl
      change fromCols (pack T * A.toCols₁) _ * D = _
      rw [show C = pack T * A.toCols₂ from rfl,← Matrix.mul_fromCols,hx]
      change _ * _ = pack T * t
      unfold A
      rw [Matrix.mul_assoc,Matrix.mul_assoc,hF,Matrix.mul_one]
    · change w (y.1+B) * w' (y.2+C) = _
      rw [hT _ _ (hu _),hT' _ _ (hu _)]
      rfl
  have h := translate_cap (subLaw_pair hw hw') f e he M
  rw [card_space,dim_mat] at h
  refine le_trans h (le_of_eq ?_)
  have ht : (↑(Fintype.card (Fin n) * Fintype.card J) : ℝ) = (dim T:ℝ) * num J := by
    simp [num,n]
  rw [ht,neg_mul,bp_neg]

omit [DecidableEq I] [DecidableEq U] in
theorem kerTr_dim {P : Mat U I} (h : Injective P.mulVec) :
    (dim (ker Pᵀ.mulVecLin) : ℝ) = num U - num I := by
  have hx := Pᵀ.mulVecLin.finrank_range_add_finrank_ker
  change rk Pᵀ.mulVecLin + dim (ker Pᵀ.mulVecLin) = dim (Vec U) at hx
  rw [rk_surj.mp (show Surjective Pᵀ.mulVecLin from transpose_surj_iff.mpr h), dim_vec,
    dim_vec] at hx
  have hj : num I + dim (ker Pᵀ.mulVecLin) = num U := by exact_mod_cast hx
  linarith only [hj]

omit [DecidableEq I] [DecidableEq U] in
theorem two_kerTr {P Q : Mat U I} (h : Injective P.mulVec) (g : Injective Q.mulVec) :
    num U - 2*num I ≤ (dim (ker Pᵀ.mulVecLin ⊓ ker Qᵀ.mulVecLin : Submodule _ _) : ℝ) := by
  let A := ker Pᵀ.mulVecLin
  let B := ker Qᵀ.mulVecLin
  have he : (dim (A⊔B : Submodule _ _) : ℝ)+dim (A⊓B : Submodule _ _) = dim A + (dim B:ℝ) := by
    exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq A B
  have hf : (dim (A⊔B : Submodule _ _) : ℝ) ≤ num U := by
    have hh := Submodule.finrank_le (A ⊔ B)
    change dim _ ≤ dim _ at hh
    rw [dim_vec] at hh; exact_mod_cast hh
  change _ ≤ (dim (A⊓B : Submodule _ _) : ℝ)
  rw [show (dim A:ℝ) = _ from kerTr_dim h,show (dim B:ℝ) = _ from kerTr_dim g] at he
  linarith only [he,hf]

theorem weak_shift {C : Mat I I → Prop} (P : Mat U I) :
    columnInv (w:=weakMinus C P) (ker Pᵀ.mulVecLin) := by
  intro M A hA
  have h : Pᵀ * A = 0 := by
    apply coe_mv_inj
    change (Pᵀ * A).mulVecLin = _
    rw [mulVecLin_mul]
    exact LinearMap.ext fun x => by
      have hh : Pᵀ.mulVecLin (A.mulVecLin x)=0 := hA (show A.mulVecLin x ∈ colSp A from ⟨x,rfl⟩)
      simp only [LinearMap.comp_apply,hh,Matrix.mulVecLin_zero,LinearMap.zero_apply]
  simp only [weakMinus,unifOn_val,Matrix.mul_add,h,add_zero]

theorem minus_le_weak {C : Mat I I → Prop} (hc : ∃ M, C M) (P : Mat U I)
    (hP : Injective P.mulVec) (hu : 2*num I - num U ≤ -1) (x : Mat U I) :
    unifOn (fun Q => FramesAt C (P,Q)) x ≤ 2 * weakMinus C P x := by
  let w := weakMinus C P
  have hh : IsLaw w := by
    refine unifOn_law ?_
    obtain ⟨M,hM⟩ := hc
    obtain ⟨B,hB⟩ := gramL_surj I hP M
    change Pᵀ*B=M at hB
    exact ⟨B,hB.symm ▸ hM⟩
  have hg : pr w (fun M => ¬Injective M.mulVec) ≤ (2:ℝ)⁻¹ := by
    apply le_trans (shift_fail hh.sub _ (weak_shift P))
    rw [kerTr_dim hP,show (2:ℝ)⁻¹=bp (-1) by rw [bp_neg,bp_one]]
    exact bp_le (by linarith only [hu])
  rw [pr_not w (p:=fun M => Injective M.mulVec),hh.total] at hg
  have h1 := on_mon hh.nz (p:=fun M => Injective M.mulVec) (a:= (2:ℝ)⁻¹)
    (by norm_num) (by linarith only [hg]) x
  simp only [w,weakMinus,unifOn_and,inv_inv] at h1
  simpa only [FramesAt,hP,true_and,weakMinus] using h1

theorem plus_le_unif (hu : num I-num U ≤ -1) (P : Mat U I) :
    unifOn (fun P : Mat U I => Injective P.mulVec) P ≤ 2 * unif P := by
  have h : pr unif (fun P : Mat U I => ¬ Injective P.mulVec) ≤ (2:ℝ)⁻¹ := by
    apply le_trans unif_fail
    rw [show (2:ℝ)⁻¹=bp (-1) by rw [bp_neg,bp_one]]; exact bp_le hu
  rw [pr_not (unif:Wgt (Mat U I)) (p:=fun P => Injective P.mulVec),unif_law.total] at h
  have h1 := on_mon unif_law.nz (a:=(2:ℝ)⁻¹)
    (p:=fun P : Mat U I => Injective P.mulVec) (by norm_num) (by linarith only [h]) P
  rwa [on_unif,inv_inv] at h1

private theorem pair_cap_aux {A : Type} {w v w' v' : Wgt A}
    (hu : ∀ x, 0 ≤ w' x) (hg : ∀ x, 0 ≤ v x) (hc : ∀ x, w x ≤ 2*v x)
    (hd : ∀ x, w' x ≤ 2*v' x) (p) : pairW w w' p ≤ 4 * pairW v v' p := by
  refine (mul_le_mul (hc p.1) (hd p.2) (hu _) (mul_nonneg (by norm_num) (hg _))).trans_eq ?_
  rw [pairW]; ring

theorem comp_image_cap {C : Mat I I → Prop} (hc : ∃ M, C M)
    (hu : 2*num I-num U ≤ -1)
    (D : Mat (I⊕I) J) (D' : Mat (I⊕I) S)
    (hD : Injective D.mulVec) (hD' : Injective D'.mulVec)
    (M : Mat U J) (M' : Mat U S) :
    let w := unifOn (FramesAt (U:=U) C)
    pr (pairW w w) (fun x =>
      mixImage D (x.1.1,x.2.1) = M ∧ mixImage D' (x.1.2,x.2.2)=M') ≤
        16*bp (-num U * num J - (num U-2*num I)*num S) := by
  let Y (x : Mat U I) := Injective x.mulVec
  let w := unifOn (FramesAt (U:=U) C)
  let v := unifOn Y
  let k (x : Mat U I) := unifOn (fun Q => FramesAt C (x,Q))
  have h₀ : num I - num U ≤ -1 := by
    have hi : 0 ≤ num I := Nat.cast_nonneg _
    linarith
  have hh := framesAt_exists (U:=U) hc (show num I+num I<num U by linarith only [hu])
  have hw : w = semi v k := by
    funext x
    rcases x with ⟨x,y⟩
    rw [show w (x,y) = _ from unifOn_slice _ x y,plus_marginal hh]; rfl
  let p := fun x => mixImage D x=M
  let q := fun x => mixImage D' x=M'
  let b1 := bp (-num U * num J)
  let b2 := bp (- (num U-2*num I)*num S)
  change pr (pairW w w) _ ≤ _
  rw [hw,pair_semi_pr v v k k p q]
  have he1 : pr (pairW v v) p ≤ 4*b1 := by
    have hi := pr_cap (w:=pairW v v)
      (pair_cap_aux (unifOn_sub Y).nz unif_subLaw.nz (plus_le_unif h₀) (plus_le_unif h₀)) p
    refine hi.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    refine (mixed_cap unif_subLaw unif_subLaw ⊤ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      _ hD _).trans ?_
    dsimp only [b1]
    rw [dim,finrank_top,show Module.finrank F (Vec U)=_ from dim_vec _]
  have he2 (P P' : Mat U I) :
      pr (pairW (k P) (k P')) q ≤ 4*b2 := by
    by_cases h : Y P
    · by_cases g : Y P'
      · let T := ker Pᵀ.mulVecLin ⊓ ker P'ᵀ.mulVecLin
        have hh : columnInv (w:=weakMinus C P) T :=
          fun M A hA => weak_shift P _ _ (hA.trans inf_le_left)
        have hh' : columnInv (w:=weakMinus C P') T :=
          fun M A hA => weak_shift P' _ _ (hA.trans inf_le_right)
        have hi := pr_cap (w:=pairW (k P) (k P'))
          (pair_cap_aux (unifOn_sub _).nz (v:=weakMinus C P) (unifOn_sub _).nz
            (minus_le_weak hc P h hu) (minus_le_weak hc P' g hu)) q
        refine hi.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        refine (mixed_cap (unifOn_sub _) (unifOn_sub _) T hh hh' _ hD' M').trans (bp_le ?_)
        apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact neg_le_neg (two_kerTr h g)
      · have hi := bp_pos (- (num U-2*num I)*num S)
        change ¬ Injective _ at g
        simp [pr,avg,pairW,k,FramesAt,g,unifOn_val,b2]; exact (bp_pos _).le
    · have hi := bp_pos (- (num U-2*num I)*num S)
      change ¬ Injective _ at h
      simp [pr,avg,pairW,k,FramesAt,h,unifOn_val,b2]; exact (bp_pos _).le
  let r := pairW v v
  calc avg r (fun x => ind (p x)*pr (pairW (k x.1) (k x.2)) q)
    _ ≤ avg r (fun x => ind (p x)*(4*b2)) :=
        avg_mono (subLaw_pair (unifOn_sub _) (unifOn_sub Y)).nz
          (fun x => mul_le_mul_of_nonneg_left (he2 _ _) (ind_nonneg _))
    _ = pr r p * (4*b2) := avg_mul _ _ _
    _ ≤ (4*b1)*(4*b2) := mul_le_mul_of_nonneg_right he1 (mul_nonneg (by norm_num) (bp_pos _).le)
    _ = _ := by simp only [sub_eq_add_neg,← neg_mul, bp_add,b1,b2] <;> ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem valid_iff (m : Mixer p n) (X : Oframe p n N) :
    valid (selfM p n m.mixM) X ↔ FramesAt (gramCond m) X := by
  have he : (X.1ᵀ*X.2).toBlocks₁₁ = (primary X.1)ᵀ * primary X.2 := by ext; rfl
  have hf : (X.1ᵀ*X.2).toBlocks₂₁ = (channel X.1)ᵀ * primary X.2 := by ext; rfl
  have hg : (X.1ᵀ*X.2).toBlocks₁₂ = (primary X.1)ᵀ * channel X.2 := by ext; rfl
  unfold valid FramesAt gramCond
  rw [he,hf,hg]; tauto

theorem raw_law (m : Mixer p n) (hN : 2*num (Full p n)<N) : IsLaw (raw m N) :=
  prodW_law (fun _ => unifOn_law (framesAt_exists (gramCond_exists m)
    (show num (Full p n) + num (Full p n) < num (Fin N) by
      rw [← two_mul]; simpa [num] using hN)))

theorem raw_nonneg (m : Mixer p n) (X : Orient p n N) : 0 ≤ raw m N X :=
  prodW_nonneg (fun _ _ => (unifOn_sub _).nz _) _

theorem raw_carried (m : Mixer p n) (N : ℕ) : carried (raw m N) (frameLaw m) := by
  intro X h
  unfold frameLaw at h
  push Not at h
  obtain ⟨e,he⟩ := h
  unfold raw prodW
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  exact unifOn_carried _ _ ((valid_iff _ _).not.mp he)

theorem Pin.agree_pack {a : Pin p n N} {x : UnitType p n N} :
    a.agree x ↔ ∀ i : Place p, images x i * pack (a.sp i) = a.target i * pack (a.sp i) := by
  have heq {I J L : Type} [Fintype I] [Fintype J] [Fintype L] (P Q : Mat I J) (M : Mat J L) :
      (∀ v ∈ colSp M, P *ᵥ v = Q *ᵥ v) ↔ P*M=Q*M := by
    constructor
    · intro h
      apply coe_mv_inj
      exact LinearMap.ext fun v => by
        change (P*M) *ᵥ v=(Q*M) *ᵥ v
        rw [← mulVec_mulVec,← mulVec_mulVec]
        exact h _ ⟨v,rfl⟩
    · rintro h x ⟨v,rfl⟩
      change P *ᵥ (M *ᵥ v) = Q *ᵥ (M *ᵥ v)
      rw [mulVec_mulVec,mulVec_mulVec,h]
  unfold Pin.agree
  apply forall_congr'; intro i
  have hh := heq (images x i) (a.target i) (pack (a.sp i))
  rw [colSp_pack] at hh
  exact hh

theorem bp_sum {A : Type*} (s : Finset A) (f : A → ℝ) :
    bp (∑ i ∈ s, f i) = ∏ i ∈ s, bp (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi => rw [Finset.sum_insert ha, Finset.prod_insert ha,bp_add,hi]

/-- Image cap under two independent raw orientations. Uniform over all
simultaneous exact-image specifications. -/
theorem reference_cap (m : Mixer p n) (a : Pin p n N) {δ : ℝ} (hd : 0 < δ)
    (hu : 2*num (Full p n) - N ≤ -1)
    (hδ : 2*num (Full p n) ≤ δ/2 * N)
    (hA : 4*num (Comp p.g) ≤ δ/2 * N) :
    pr (pairW (raw m N) (raw m N)) a.agree ≤ bp (-(1-δ)*(planRank a.sp)*N) := by
  let s := a.sp
  let μ := raw m N
  have hn : 2*num (Full p n)<N := by linarith only [hu]
  have hh := raw_law m hn
  by_cases he : planRank s = 0
  · change _ ≤ bp (_ * (planRank s) * _)
    rw [he]
    simp only [Nat.cast_zero,mul_zero,zero_mul,bp_zero]
    exact le_trans (pr_le_tot (pairW_law hh hh).nz) (pairW_law hh hh).total.le
  let g (e : Comp p.g) := unifOn (FramesAt (U:=Fin N) (gramCond m))
  let D (e : Place p) := pack (s e)
  let rankval (e : Place p) := (dim (s e) : ℝ)
  let f (e : Comp p.g) (w : Oframe p n N × Oframe p n N) :=
    mixImage (D (e,true)) (w.1.1,w.2.1) = a.target (e,true) * D (e,true) ∧
    mixImage (D (e,false)) (w.1.2,w.2.2) = a.target (e,false) * D (e,false)
  have hf : pr (pairW μ μ) a.agree = ∏ e, pr (pairW (g e) (g e)) (f e) := by
    have hfun : a.agree = (fun x => ∀ e, f e (x.1 e,x.2 e)) := by
      funext x; apply propext
      rw [Pin.agree_pack]
      constructor
      · intro hi e
        exact ⟨hi (e,true),hi (e,false)⟩
      · rintro h ⟨e,b⟩; cases b
        · exact (h e).2
        · exact (h e).1
    rw [hfun]
    exact prodW_pair_pr g g f
  let y := fun e : Comp p.g => 4 - (1-δ/2) * (rankval (e,true)+rankval (e,false))*N
  have hb (e) : pr (pairW (g e) (g e)) (f e) ≤ bp (y e) := by
    have h1 := comp_image_cap (gramCond_exists m)
      (show 2*num (Full p n)-num (Fin N) ≤ -1 by simpa [num] using hu)
      _ _ (pack_inj (s (e,true))) (pack_inj (s (e,false))) (a.target (e,true)*D (e,true))
      (a.target (e,false)*D (e,false))
    have hnum (n : ℕ) : num (Fin n)=(n:ℝ) := by simp [num]
    change pr _ _ ≤ _
    apply le_trans h1
    rw [show (16:ℝ)=bp 4 by
      have hh := bp_nat 4; norm_num at hh ⊢; linarith,← bp_add,hnum,hnum,hnum]
    apply bp_le
    let rp := rankval (e,true)
    let rm := rankval (e,false)
    change 4+(-((N:ℝ))*rp-(_-2*num (Full p n))*rm) ≤ 4 - _ * (rp+rm)*_
    have hp := mul_nonneg (show 0 ≤ rp from Nat.cast_nonneg _) (mul_nonneg hd.le
      (show (0:ℝ) ≤ N from Nat.cast_nonneg _))
    have hg := mul_le_mul_of_nonneg_right hδ (show 0 ≤ rm from Nat.cast_nonneg _)
    linarith only [hp,hg]
  have hg : pr (pairW μ μ) a.agree ≤ bp (∑ i, y i) := by
    rw [hf,bp_sum]
    apply Finset.prod_le_prod _ fun i _ => hb i
    exact fun i _ => pr_nonneg
      (subLaw_pair (unifOn_sub _) (unifOn_sub _)).nz
  apply hg.trans
  apply bp_le
  have ht : (planRank s : ℝ) = ∑ i : Comp p.g, (rankval (i,true) + rankval (i,false)) := by
    rw [planRank,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Nat.cast_sum,Nat.cast_add,rankval]
  have h1 : ∑ i, y i = 4*num (Comp p.g) - (1-δ/2)*(planRank s)*N := by
    dsimp only [y]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul, ← Finset.mul_sum, ← ht]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]
    ring
  have hk : 1 ≤ (planRank s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
  rw [h1]
  change _ ≤ -(1-δ)*(planRank s)*N
  have he := mul_le_mul_of_nonneg_right hk
    (mul_nonneg hd.le (show (0:ℝ) ≤ N from Nat.cast_nonneg _))
  linarith only [hA,he]

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

theorem IP_self (b) : (IP p n b)ᵀ*IP p n b=1 := by
  apply embedMat_self
  intro i j; cases b <;> simp [putFull]

theorem images_ip (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IP p n b = primary (takeSign (onSide x b z.1) z.2) := by
  unfold IP; rw [mul_embedMat]
  cases b <;> ext <;> rfl
theorem images_ih (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IH p n b = channel (takeSign (onSide x b z.1) z.2) := by
  unfold IH; rw [mul_embedMat]
  cases b <;> ext <;> rfl

theorem sPin_dim (s : Plan p n) (z : Place p) (i) : dim (sPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _
theorem hPin_dim (s : Plan p n) (z : Place p) (i) : dim (hPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _

theorem dim_le_plan (s : Plan p n) (e : Place p) :
    dim (s e) ≤ planRank s := Finset.single_le_sum (fun j _ => Nat.zero_le (dim (s j)))
      (Finset.mem_univ _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImagePartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image Partitions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem plan_mono {a b : Plan p n} (h : a ≤ b) : planRank a ≤ planRank b :=
  Finset.sum_le_sum fun i _ => Submodule.finrank_mono (h i)

theorem plan_add_rank (a b : Plan p n) :
    planRank a + planNew a b = planRank (a⊔b) :=
  Nat.add_sub_of_le (plan_mono le_sup_left)

theorem planNew_mono_add {a b c : Plan p n} (h : a ≤ b) :
    planNew a b + planNew b c = planNew a (b⊔c) := by
  have he := plan_add_rank a b
  have hf := plan_add_rank b c
  have hg := plan_add_rank a (b⊔c)
  rw [sup_eq_right.mpr h] at he
  rw [sup_eq_right.mpr (le_trans h le_sup_left)] at hg
  omega

theorem Pin.combine {a b : Pin p n N} {x y} (ha : a.agree x) (hb : b.agree x) :
    (Pin.make (a.sp ⊔ b.sp) x).agree y ↔ a.agree y ∧ b.agree y := by
  change (∀ i, ∀ v ∈ a.sp i ⊔ b.sp i, images y i *ᵥ v = images x i *ᵥ v) ↔ _
  constructor
  · intro h
    exact ⟨fun i v hv => (h i v (Submodule.mem_sup_left hv)).trans (ha _ v hv),
      fun i v hv => (h i v (Submodule.mem_sup_right hv)).trans (hb _ v hv)⟩
  · rintro ⟨u,w⟩ i v hv
    obtain ⟨l,hl,r,hr,rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add,Matrix.mulVec_add,ha _ _ hl,hb _ _ hr,u _ _ hl,w _ _ hr]

theorem heavy_leaf {r w : Wgt (UnitType p n N)}
    {D ζ : ℝ} (hz : 0 < ζ) (hz' : ζ < 1) (hn : 0 < N)
    (hR : ∀ a : Pin p n N, pr r a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N)*r x) (hw : ∀ x, 0 ≤ w x)
    (R : Finset (UnitType p n N)) (a : Pin p n N) (hf : ∀ x ∈ R, a.agree x)
    {K : ℕ} (hK : D + ζ ≤ (ζ-ζ/4)*K)
    (hpos : bp (-ζ*N) < pr w (fun x => x ∈ R)) :
    ∃ S : Finset (UnitType p n N), S ⊆ R ∧ ∃ b : Pin p n N,
      PeelCell w r D ζ K S a b := by
  classical
  have hn' : 0 < (N:ℝ) := by exact_mod_cast hn
  have hr : ∀ x, 0 ≤ r x := by
    intro x
    by_contra! h
    exact not_lt_of_ge ((hw x).trans (hc x)) (mul_neg_of_pos_of_neg (bp_pos _) h)
  let cut := bp (-ζ*N)
  let q (b : Pin p n N) := planNew a.sp b.sp
  let s (b : Pin p n N) : Finset (UnitType p n N) := R.filter b.agree
  let c (b : Pin p n N) := pr w (fun x => x ∈ s b)
  let heavy (b : Pin p n N) := a.sp ≤ b.sp ∧ cut * fee N ζ (q b) < c b
  let T := {t : ℕ | ∃ b, heavy b ∧ q b = t}
  have e1 : heavy a := by
    have ha : s a = R := by ext x; simp [s]; tauto
    refine ⟨le_rfl,?_⟩
    simpa only [q,planNew,sup_idem,Nat.sub_self,cut,c,ha,fee,Nat.cast_zero,
      mul_zero,zero_mul,bp_zero,mul_one] using hpos
  have bound (b : Pin p n N) (hh : heavy b) : q b ≤ K := by
    have hmo : (planRank b.sp : ℝ) ≥ q b := by
      have hg := plan_add_rank a.sp b.sp
      rw [sup_eq_right.mpr hh.1] at hg
      have hh' : q b ≤ planRank b.sp := by unfold q; omega
      exact_mod_cast hh'
    have he : cut * fee N ζ (q b) < bp (D*N) * fee N (ζ/4) (q b) := by
      refine hh.2.trans_le ?_
      calc
        c b ≤ pr w b.agree :=
          pr_mono hw (fun x h => (Finset.mem_filter.mp h).2)
        _ ≤ bp (D*N)* pr r b.agree := pr_cap hc _
        _ ≤ _ := mul_le_mul_of_nonneg_left ((hR b).trans (by
          unfold fee
          apply bp_le
          apply mul_le_mul_of_nonneg_right _ hn'.le
          exact mul_le_mul_of_nonpos_left hmo (by linarith))) (bp_pos _).le
    unfold cut fee at he
    rw [← bp_add,← bp_add] at he
    have hg (x y : ℝ) (h : bp x<bp y) : x<y := lt_of_not_ge (fun e =>
      not_lt_of_ge (bp_le e) h)
    have h' := hg _ _ he
    have hi : (ζ-ζ/4)*(q b:ℝ) < D+ζ := by
      apply (mul_lt_mul_iff_left₀ hn').mp
      linarith only [h']
    have hj := (mul_lt_mul_iff_right₀ (show 0 < ζ-ζ/4 by linarith)).mp (hi.trans_le hK)
    exact_mod_cast hj.le
  obtain ⟨b,hb,hT⟩ : ∃ b, heavy b ∧ q b = sSup T :=
    Nat.sSup_mem (show T.Nonempty from ⟨_,a,e1,rfl⟩)
      (show BddAbove T from ⟨K,fun t ⟨b,h,r⟩ => r ▸ bound b h⟩)
  have hcut := bp_pos (-ζ*N)
  have hmass : 0 < c b := (mul_pos hcut (bp_pos _)).trans hb.2
  let v := onW w (fun x => x ∈ s b)
  have hv : IsLaw v := normW_law (subW_nonneg hw _) hmass
  have hg := plan_add_rank a.sp b.sp
  rw [sup_eq_right.mpr hb.1] at hg
  have hp := bound b hb
  refine ⟨s b,Finset.filter_subset _ _,b,hmass,fun x h => (Finset.mem_filter.mp h).2,
    hb.1, ?_, fun B => ?_, fun x => ?_⟩
  · change planNew _ _ ≤ _ at hp
    omega
  · by_contra! he
    have hB := bp_pos (-(1-ζ)*(planNew b.sp B.sp)*N)
    change fee N ζ _ < pr v B.agree at he
    have he' := pr_of_on hw (fun x => x ∈ s b) B.agree
    change _ = c b * pr v B.agree at he'
    have hhpos : 0 < pr w (fun x => x ∈ s b ∧ B.agree x) :=
      he'.symm ▸ mul_pos hmass (lt_trans hB he)
    obtain ⟨x,⟨hx,hx'⟩,_⟩ := exists_of_pr_pos hw hhpos
    let J := Pin.make (b.sp⊔B.sp) x
    have hjoin : c J = c b * pr v B.agree := by
      have hxy (y) : y ∈ s J ↔ y ∈ s b ∧ B.agree y := by
        have hy := Pin.combine (Finset.mem_filter.mp hx).2 hx' (y:=y)
        change J.agree y ↔ b.agree y ∧ B.agree y at hy
        simp only [s,Finset.mem_filter,hy,and_assoc]
      simp_rw [← he',c,hxy]
    have hu : q b + planNew b.sp B.sp = q J := planNew_mono_add hb.1
    have hj : heavy J := by
      refine ⟨le_trans hb.1 le_sup_left, ?_⟩
      have hi :
          fee N ζ (q J) = fee N ζ (q b)* fee N ζ (planNew b.sp B.sp) := by
        unfold fee; rw [← bp_add,← hu]
        push_cast <;> ring_nf
      rw [hjoin,hi,← mul_assoc]
      apply lt_trans (mul_lt_mul_of_pos_right hb.2 hB)
      exact mul_lt_mul_of_pos_left he hmass
    have hd : 0 < planNew b.sp B.sp := by
      by_contra! hi
      rw [show planNew b.sp B.sp=0 from Nat.eq_zero_of_le_zero hi] at he
      have hh := pr_le_tot (p:=B.agree) hv.nz
      rw [hv.total] at hh
      simp only [fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero] at he
      linarith
    have ha : q J ≤ sSup T := le_csSup
      (show BddAbove T from ⟨K,fun t ⟨b,h,r⟩ => r ▸ bound b h⟩)
      ⟨J,hj,rfl⟩
    omega
  · apply (on_mon hw (mul_pos hcut (bp_pos (-(1-ζ)*(q b)*N))) hb.2.le x).trans
    apply (mul_le_mul_of_nonneg_left (hc x) (inv_nonneg_of_nonneg (mul_pos hcut (bp_pos _)).le)).trans
    rw [← mul_assoc,← bp_add,← bp_neg,← bp_add]
    apply mul_le_mul_of_nonneg_right _ (hr x)
    apply bp_le
    have hk1 : 0 ≤ (q b:ℝ) := Nat.cast_nonneg _
    have hh : (q b:ℝ) ≤ K := by exact_mod_cast hp
    nlinarith only [mul_le_mul_of_nonneg_right hh hn'.le, mul_lt_mul_of_pos_right hz' hn',
      mul_nonneg hk1 (mul_pos hz hn').le]

theorem peel_family {r w : Wgt (UnitType p n N)}
    {D ζ : ℝ} (hz : 0 < ζ) (hz' : ζ < 1) (hn : 0 < N)
    (hR : ∀ a : Pin p n N, pr r a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N)*r x) (hw : ∀ x, 0 ≤ w x)
    (R : Finset (UnitType p n N)) (a : Pin p n N) (hf : ∀ x ∈ R, a.agree x)
    {K : ℕ} (hK : D + ζ ≤ (ζ-ζ/4)*K) :
    ∃ G : Finset (Finset (UnitType p n N)),
      (∀ S ∈ G, S⊆R ∧ ∃ b, PeelCell w r D ζ K S a b) ∧
      (∀ x, ∀ S ∈ G, ∀ J ∈ G, x∈S → x∈J → S=J) ∧
      pr w (fun x => x ∈ R ∧ ¬∃ S∈G,x∈S) ≤ bp (-ζ*N) := by
  classical
  induction R using Finset.strongInductionOn with | _ R ih
  by_cases hr : pr w (fun x => x∈R) ≤ bp (-ζ*N)
  · exact ⟨∅,by simpa using hr⟩
  obtain ⟨S,hS,b,hb⟩ := heavy_leaf hz hz' hn hR hc hw R a hf hK (lt_of_not_ge hr)
  have he := exists_of_pr_pos hw hb.pos
  obtain ⟨G,hG,hU,hW⟩ := ih (R\ S) (Finset.sdiff_ssubset hS
    (show S.Nonempty from ⟨he.choose,he.choose_spec.1⟩))
    (fun x h => hf x (Finset.mem_sdiff.mp h).1)
  refine ⟨insert S G, fun J h => ?_, fun x J h J' h' g g' => ?_,?_⟩
  · rcases Finset.mem_insert.mp h with rfl|h
    · exact ⟨hS,b,hb⟩
    · exact ⟨(hG J h).1.trans (Finset.sdiff_subset), (hG J h).2⟩
  · have hi (J) (h : J∈G) (g : x∈J) : x∉S := (Finset.mem_sdiff.mp ((hG J h).1 g)).2
    rcases Finset.mem_insert.mp h with h|h <;> rcases Finset.mem_insert.mp h' with h'|h'
    · rw [h,h']
    · exact ((hi _ h' g') (h ▸ g)).elim
    · exact ((hi _ h g) (h' ▸ g')).elim
    · exact hU _ _ h _ h' g g'
  · refine le_trans (pr_mono hw ?_) hW
    intro x h
    simp only [Finset.exists_mem_insert,not_or] at h
    exact ⟨Finset.mem_sdiff.mpr ⟨h.1,h.2.1⟩,h.2.2⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoverSpaces
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.momFintype
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

variable [DecidableEq I] [DecidableEq J]
theorem cdim_sign (p : Shape) {N} (S : Cov p N) :
    cdim p S=cdSign p S true+cdSign p S false := by
  simp only [cdim,cdSign,Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem mapW_nested {C : Type} (w : Wgt A) (f : A→B) (g : B→C) :
    mapW (mapW w f) g=mapW w (g ∘ f) :=
  funext fun _ => mapW_pr _ _ _

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

variable {p : Shape} {n N : ℕ}

theorem intoChan_inj : Injective (intoChan p n).mulVec :=
  embedMat_inj Sum.inr_injective
theorem intoChan_val (p : Shape) {n N} (x : Mat (Fin N) (Full p n)) :
    x * intoChan p n=channel x := by rw [intoChan,mul_embedMat]; rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConstructionScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Construction Scales -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Filter

theorem card_full (p : Shape) (n : ℕ) :
    Fintype.card (Full p n) = psize p * (1+(p.g*p.g+3)*n) + p.h := by
  calc
    _ = Fintype.card (Row p n) + Fintype.card (Fin p.h) :=
      Fintype.card_sum ..
    _ = _ := by rw [card_row, Fintype.card_fin]

theorem full_linear (p : Shape) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 0 < n →
    num (Full p n) ≤ B*n := by
  let b := psize p*(1+(p.g*p.g+3)) + p.h
  refine ⟨↑b,Nat.cast_nonneg b, fun n hn => ?_⟩
  have h1 : 1 ≤ n := hn
  have h2 : Fintype.card (Full p n) ≤ b*n := by
    rw [card_full]
    unfold b
    calc _ ≤ psize p * (n+(p.g*p.g+3)*n) + p.h*n :=
           add_le_add (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
         _ = _ := by ring
  exact_mod_cast h2

theorem unit_size (p : Shape) (n N : ℕ) :
    num (UnitType p n N) = bp (num (Comp p.g) * 4 * N * num (Full p n)) := by
  have hc :
      (Fintype.card (UnitType p n N)) =
        ((Fintype.card (Mat (Fin N) (Full p n)))^2)^(Fintype.card (Comp p.g)) *
        ((Fintype.card (Mat (Fin N) (Full p n)))^2)^(Fintype.card (Comp p.g)) := by
    simp [UnitType, Orient, Oframe, RawFrame, pow_two]
  unfold num
  rw [hc]
  push_cast
  rw [card_space,dim_mat,Fintype.card_fin]
  push_cast
  simp only [← bp_mul_nat,← bp_add]
  push_cast <;> ring_nf

/-- Fixed linear and constant expenses become any fixed small fraction of N. -/
theorem have_budget {δ : ℝ} (hd : 0 < δ) (a b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → a*n+b ≤ δ*(M*n : ℕ) := by
  have h : Tendsto (fun M : ℕ => δ*M) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hd).mpr tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (eventually_ge_atTop (a+b))] with M hM n hn
  change a+b ≤ δ*M at hM
  push_cast
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  nlinarith only [mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n : (0:ℝ)≤n),
    mul_le_mul_of_nonneg_right hn' hb]

theorem columns_budget (p : Shape) {δ : ℝ} (hd : 0 < δ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, 1 ≤ n →
      a*num (Full p n) + b ≤ δ*(M*n:ℕ) := by
  obtain ⟨B,hB,h⟩ := full_linear p
  filter_upwards [have_budget hd (a*B) b hb] with M hM n hn
  refine le_trans ?_ (hM n hn)
  rw [mul_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (h _ hn) ha) _

theorem raw_ready (p : Shape) {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ n : ℕ in atTop, let N := M*n;
      num (UnitType p n N) ≤ bp ((4*num (Comp p.g))*N^ (2 : ℕ)) ∧
      ∀ m : Mixer p n, IsLaw (raw m N) ∧ ∀ a : Pin p n N,
        pr (pairW (raw m N) (raw m N)) a.agree ≤ bp (-(1-δ)*(planRank a.sp)*N) := by
  have hd' : 0 < δ/2 := by positivity
  filter_upwards [columns_budget p hd' 2 (4*num (Comp p.g)) (by norm_num)
    (by unfold num; positivity),
    columns_budget p (δ:=1) (by norm_num) 2 1 (by norm_num) (by norm_num)] with M ha hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  specialize ha n hn
  specialize hb n hn
  let N := M*n
  have hi : 0 ≤ num (Comp p.g) := Nat.cast_nonneg _
  have hj : 0 ≤ num (Full p n) := Nat.cast_nonneg _
  rw [one_mul] at hb
  have hh : 2*num (Full p n)<N := by unfold N; linarith only [hb]
  dsimp only
  constructor
  · rw [unit_size]
    apply bp_le
    have hf : num (Full p n) ≤ N := by linarith

    exact le_trans (mul_le_mul_of_nonneg_left hf (by positivity))
      (le_of_eq (by unfold N; push_cast <;> ring))
  · intro m
    refine ⟨raw_law m hh, fun a => reference_cap _ a hd ?_ ?_ ?_⟩ <;> linarith
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Channel Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem checkgram_dim :
    dim (CheckGram p n)=16*ncComp p*p.h*Fintype.card (Row p n) := by
  classical
  let r := p.h*Fintype.card (Row p n)
  let T := Mat (Chan p) (Row p n)
  have hf : finrank F T=r := (dim_mat _ _).trans (by simp [r,Chan])
  have hg {I V : Type} [Fintype I] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
      finrank F (I→V) = Fintype.card I * finrank F V := by
    rw [finrank_pi_fintype]; simp
  have h : finrank F (CheckOne p n)=8*ncComp p*r := by
    unfold CheckOne
    rw [hg,hg,hg,hf]
    simp [ncComp,Place]
    ring
  unfold CheckGram dim
  rw [Module.finrank_prod,h]
  unfold r; ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CollisionInequality
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision Inequality -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]

theorem collision_scales (p : Shape) (K : ℕ) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop, let N := M*n;
    100≤N ∧ (dim (CheckGram p n):ℝ) ≤ 0.01*N ∧
      (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N := by
  filter_upwards [columns_budget p (δ:=0.01) (by norm_num)
    (16*(ncComp p:ℝ)*p.h) 0 (by positivity) (by norm_num),
    columns_budget p (δ:=0.005) (by norm_num)
    (2*(K+(kmax p:ℝ))) 0 (by positivity) (by norm_num),eventually_ge_atTop 1] with M hM hB hg
  filter_upwards [eventually_ge_atTop 100] with n hn
  specialize hM n (by omega)
  specialize hB n (by omega)
  have hN : 100 ≤ M*n := by nlinarith
  refine ⟨hN,?_,?_⟩
  · rw [checkgram_dim]
    simp only [Nat.cast_mul,Nat.cast_ofNat]; unfold num at hM
    have hi : (↑(Fintype.card (Row p n)):ℝ)≤Fintype.card (Full p n) := by
      have he : Fintype.card (Full p n)=_+_ := Fintype.card_sum ..
      exact_mod_cast (show Fintype.card (Row p n)≤Fintype.card (Full p n) from he.symm ▸
        Nat.le_add_right ..)
    rw [add_zero] at hM
    rw [Nat.cast_mul] at hM
    exact le_trans (mul_le_mul_of_nonneg_left hi (by positivity)) hM
  rw [show num (JointIdx p n) = 2*num (Full p n) from (by
    unfold num JointIdx; rw [Fintype.card_sum]; push_cast <;> ring)]
  linarith only [hB]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem bounded_pack {I : Type} [Fintype I] (S : Space (Vec I)) (k : ℕ) :
    ∃ M : Mat I (Fin k), colSp M ≤ S ∧ dim (colSp M) = min (dim S) k := by
  have h (M : Mat (Fin (dim S)) (Fin k)) : colSp (pack S*M) ≤ S := by
    rw [colSp,mulVecLin_mul,LinearMap.range_comp]
    apply le_trans (Submodule.map_mono (show _ ≤ ⊤ from le_top))
    rw [←LinearMap.range_eq_map]
    exact (colSp_pack S).le
  by_cases hs : dim S ≤ k
  · obtain ⟨M,hM⟩ := pad_matrix_inj _ _ hs
    refine ⟨pack S * Mᵀ,h _,?_⟩
    have hg : Function.Surjective Mᵀ.mulVecLin := transpose_surj_iff.mpr hM
    have hh : colSp (pack S * Mᵀ) = S := by
      rw [colSp,mulVecLin_mul,LinearMap.range_comp,
        LinearMap.range_eq_top.mpr hg,← LinearMap.range_eq_map]; exact colSp_pack S
    rw [hh,min_eq_left hs]
  · obtain ⟨M,hM⟩ := pad_matrix_inj _ _ (by omega : k ≤ dim S)
    refine ⟨pack S * M,h _,?_⟩
    have hh := mrk_inj.mp (inj_comp_mat _ _ (pack_inj S) hM)
    rw [colSp_dim,hh,Fintype.card_fin,min_eq_right (by omega)]

variable {p : Shape} {n N : ℕ}

theorem largeJoin_pin {t : ℕ} {x : UnitType p n N} (h : t ≤ joins x) :
    ∃ g : KCand p n t,
      (t ≤ planRank (zeroPin (N:=N) g).sp) ∧ (zeroPin g).agree x := by
  classical
  choose M hM hg using (fun i : Comp p.g =>
    bounded_pack (ker (images x (i,true)).mulVecLin) t)
  let d (i : Comp p.g) := dim (ker (images x (i,true)).mulVecLin)
  refine ⟨M, ?_, ?_⟩
  · unfold planRank
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    change t ≤ ∑ i : Comp p.g, (dim (colSp (M i))+dim (⊥ : Submodule F (Dir p n)))
    have hb : dim (⊥ : Submodule F (Dir p n)) = 0 := finrank_bot _ _
    simp_rw [hb,add_zero,hg]
    change t ≤ ∑ i, min (d i) t
    by_cases hh : ∃ i, t ≤ d i
    · obtain ⟨i,h⟩ := hh
      exact (min_eq_right h).symm.le.trans
        (Finset.single_le_sum (fun i _ => Nat.zero_le (min (d i) t)) (Finset.mem_univ _))
    · push Not at hh
      simp_rw [min_eq_left (hh _).le]; exact h
  · rintro ⟨i,_|_⟩ a ha
    · change a ∈ (⊥ : Submodule _ _) at ha
      have he : a = 0 := by simpa using ha
      rw [he,Matrix.mulVec_zero,Matrix.mulVec_zero]
    · have he := hM i (show a ∈ colSp (M i) from (by simpa only [zeroPin,↓reduceIte] using ha))
      change _ = (0:Mat _ _)*ᵥ_
      rw [Matrix.zero_mulVec]
      exact he

theorem num_kcand (p : Shape) (n t : ℕ) :
    num (KCand p n t) = bp (num (Comp p.g) * (2*num (Full p n)) * t) := by
  have heq : Fintype.card (KCand p n t) =
      Fintype.card (Mat (JointIdx p n) (Fin t)) ^ Fintype.card (Comp p.g) :=
    Fintype.card_fun
  unfold num; rw [heq]
  push_cast
  rw [card_space, dim_mat, ← bp_mul_nat]
  have h : Fintype.card (JointIdx p n) = 2*Fintype.card (Full p n) :=
    (Fintype.card_sum ..).trans (two_mul _).symm
  rw [h,Fintype.card_fin]
  push_cast <;> ring_nf

theorem raw_join_cap (m : Mixer p n) (H : ∀ a : Pin p n N,
    pr (pairW (raw m N) (raw m N)) a.agree ≤ bp (-(1-1/8)*(planRank a.sp)*N)) (t : ℕ) :
    pr (pairW (raw m N) (raw m N)) (fun x => t ≤ joins x) ≤
      bp (num (Comp p.g)*(2*num (Full p n))*t - (1-1/8)*t*N) := by
  classical
  let w := pairW (raw m N) (raw m N)
  have hw (x) : 0 ≤ w x := mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)
  have hh (c : KCand p n t) :
      pr w (fun x => t ≤ planRank (zeroPin (N:=N) c).sp ∧ (zeroPin c).agree x) ≤
        bp (-(1-1/8)*(t:ℝ)*N) := by
    by_cases h : t ≤ planRank (zeroPin (N:=N) c).sp
    · simp only [h,true_and]
      apply le_trans (H _)
      apply bp_le
      have ht : (t:ℝ) ≤ planRank (zeroPin (N:=N) c).sp := by exact_mod_cast h
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith only [ht]
    · simp only [h,false_and,pr_false]
      exact (bp_pos _).le
  refine (le_trans (pr_mono (w:=w) hw (fun _ => largeJoin_pin)) (pr_exists_le hw _)).trans
    ((Finset.sum_le_sum (fun i _ => hh i)).trans_eq ?_)
  rw [sub_eq_add_neg (num (Comp p.g)*(2*num (Full p n))*t),bp_add,← num_kcand]
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]
  rw [neg_mul,neg_mul]

open Filter
/-- The stronger join restriction is exponentially likely under the stated joint cap. -/
theorem sparse_usual (p : Shape) (D : ℕ) (hd : 0 < D) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ n : ℕ in atTop, let N := M*n;
      ∀ (m : Mixer p n) (w : Wgt (UnitType p n N)),
        (∀ x, w x ≤ bp ((D:ℝ)*N) * pairW (raw m N) (raw m N) x) →
        pr w (fun x => 2*D < joins x) ≤ bp (-(D:ℝ)/2*N) := by
  have H := raw_ready p (δ:=1/8) (by norm_num)
  let a := num (Comp p.g)*4*D
  have hd' : 0 < (D:ℝ)/4 := by positivity
  have hA := columns_budget p hd' a 0 (by dsimp [a,num] <;> positivity) (by norm_num)
  filter_upwards [H,hA] with M hM ha
  filter_upwards [hM,eventually_ge_atTop 1] with n hn hn'
  specialize ha n hn'
  rw [add_zero] at ha
  intro N m w h
  let v := (pairW (raw m N) (raw m N))
  have hi := pr_cap (v:=v) h (fun x => 2*D < joins x)
  refine hi.trans ?_
  have hv (x) : 0 ≤ v x := mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)
  apply le_trans (mul_le_mul_of_nonneg_left (le_trans
    (pr_mono hv (p:=fun x => 2*D<joins x) (q:=fun x => 2*D≤joins x) (fun _ => le_of_lt))
    (raw_join_cap m (hn.2 m).2 (2*D))) (bp_pos _).le)
  rw [←bp_add]
  apply bp_le
  unfold a at ha
  unfold N; push_cast at ha ⊢
  linarith only [ha]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRankCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

open Filter

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

variable {S : Cov p N}

theorem atlas_size (S : Cov p N) (r : ℕ) :
    num (Atlas p r S) ≤ num (Wide p r) * bp (cdim p S*r+(num (Comp p.g))*r*r) := by
  classical
  change (↑(Fintype.card (Atlas p r S)) : ℝ) ≤ _
  unfold Atlas
  rw [Fintype.card_sigma,Nat.cast_sum]
  have hg (q : Wide p r) :
      (↑(Fintype.card (OffBasis p r S q×OffAux p r q)):ℝ) ≤ bp (cdim p S*r+(num (Comp p.g))*r*r) := by
    rw [card_space]
    apply bp_le
    have ht : dim (OffBasis p r S q)≤ cdim p S*r := by
      unfold dim OffBasis
      rw [finrank_pi_fintype]
      unfold cdim; rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have h := dim_mat (Fin (dim (S i))) (Fin (q i).val)
      rw [Fintype.card_fin,Fintype.card_fin] at h
      exact h.trans_le (Nat.mul_le_mul_left _ (Nat.lt_add_one_iff.mp (q i).isLt))
    have hu : dim (OffAux p r q) ≤ Fintype.card (Comp p.g)*r*r := by
      unfold dim OffAux
      rw [finrank_pi_fintype]
      refine (Finset.sum_le_sum (g:=fun _ => r*r) fun i _ => ?_).trans_eq ?_
      · refine (dim_mat _ _).trans_le ?_
        rw [Fintype.card_fin,Fintype.card_fin]
        exact Nat.mul_le_mul (Nat.lt_add_one_iff.mp (q _).isLt) (Nat.lt_add_one_iff.mp (q _).isLt)
      simp [mul_assoc]
    unfold dim
    rw [Module.finrank_prod,Nat.cast_add]
    have hsum := add_le_add ht hu
    unfold num
    exact_mod_cast hsum
  exact (Finset.sum_le_sum fun i _ => hg i).trans_eq (by simp [num])

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionCosts
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseAlternativeSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseParameters
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem denom_pos (r) : 0<denomStep r := by unfold denomStep Bstep; positivity

theorem row_le (p : Shape) (n : ℕ) : num (Row p n) ≤ num (Full p n) := by
  have h' : Fintype.card (Full p n)=Fintype.card (Row p n)+Fintype.card (Fin p.h) := by
    simp only [Full,Fintype.card_sum]
  unfold num; rw [h']; push_cast
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem tinyPhase_pos (g r : ℕ) (D : ℝ) : 0< tinyPhase g r D := bp_pos _

theorem tinyPhase_le (g r : ℕ) {D : ℝ} (hD : 0 ≤ D) : tinyPhase g r D ≤1 := by
  have ht : 0 ≤ num (Comp g) := Nat.cast_nonneg _
  rw [tinyPhase,←bp_zero]
  apply bp_le; unfold pcoef stage; linarith [Nat.cast_nonneg (α:=ℝ) r,
    show 0≤ (denomStep r:ℝ)*(2*r*num (Comp g)+D+1) from mul_nonneg (Nat.cast_nonneg _) (by positivity)]

theorem heatloss_pos (r k : ℕ) : 0 < heatloss r k := by unfold heatloss; positivity

theorem bp_nat_vanish {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => bp (-c*n)) atTop (𝓝 0) :=
  (bp_tendsto_zero hc).comp tendsto_natCast_atTop_atTop

theorem eventually_grid {P : ℕ → Prop} (h : ∀ᶠ N : ℕ in atTop,P N) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ n : ℕ in atTop, P (M*n) := by
  obtain ⟨k,hk⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop 1] with M hM
  filter_upwards [eventually_ge_atTop k] with n hn
  exact hk _ (by nlinarith)

private theorem absorb_pow (p : Shape) {D : ℝ} (hD : 0≤D) (r b N : ℕ)
    (hN : N ≤2*denomStep r*b)
    (hp : 2*pcoef p.g r D ≤ p.h) :
    exponentErr p (mstep r) b (tinyPhase p.g r D)/warn^(2^(mstep r)*(2*b))
      ≤ 2*bp (-(stage p.g r D)*N) := by
  let Z := pcoef p.g r D
  let L := stage p.g r D
  let s := 2^(mstep r)*(2*b)
  have hl : 0 ≤ L := by unfold L stage num; positivity
  have hx : 12*(s:ℝ)+L*N ≤ Z*b := by
    have h : (N:ℝ) ≤ 2*(denomStep r:ℝ)*b := by exact_mod_cast hN
    have hs : (s:ℝ)=(Bstep r:ℝ)*b := by unfold s Bstep; push_cast <;> ring
    unfold Z pcoef; rw [hs]; change _ ≤ (12*_+2*_ * L)*_
    nlinarith only [mul_le_mul_of_nonneg_left h hl]
  have hz : L*N+10*(s:ℝ) ≤ (p.h:ℝ)*b/2 := by
    have hb : 2*Z*(b:ℝ) ≤ (p.h:ℝ)*b :=
      mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
    linarith [(Nat.cast_nonneg s : 0≤(s:ℝ))]
  unfold exponentErr tinyPhase warn
  change (((2:ℝ)^s*2^s)*bp (-Z)^b+bp _)/bp (-10)^s≤_
  rw [←bp_nat s,←bp_mul_nat,←bp_mul_nat, ← bp_add,←bp_add,add_div,← bp_sub,← bp_sub,
    two_mul]
  refine add_le_add (bp_le ?_) (bp_le ?_)
  · change _ ≤ -L*N; linarith only [hx]
  change _ ≤ -L*N; linarith only [hz]

private theorem limit_pow (p : Shape) (r : ℕ) {D : ℝ} (hD : 0≤D)
    (hp : 2*pcoef p.g r D ≤ p.h) :
    ∀ᶠ N : ℕ in atTop,warn + noSweepBudget p N (mstep r) (N/denomStep r) r
      (tinyPhase p.g r D) warn (bp (D*N))<0.005 := by
  let C := chanPrice p
  have hw : warn < 0.005 := by
    unfold warn; rw [bp_neg, show (10:ℝ)=↑(10:ℕ) from by norm_num, bp_nat]; norm_num
  have hi : Tendsto (fun N : ℕ => warn+(2*C^2)*bp (-1*N)) atTop (𝓝 warn) := by
    have h := (bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul (2*C^2)
    simpa only [neg_mul,mul_zero,add_zero] using h.const_add warn
  filter_upwards [hi.eventually (gt_mem_nhds hw),eventually_ge_atTop (denomStep r)]
    with N h hN
  let b := N / denomStep r
  have he : N≤2*denomStep r*b := by
    have h' : 1≤b := (Nat.le_div_iff_mul_le (denom_pos r)).mpr (by simpa using hN)
    have h2 : b*denomStep r + N%denomStep r=N := Nat.div_add_mod' ..
    have h3 : N%denomStep r < denomStep r := Nat.mod_lt _ (denom_pos r)
    nlinarith
  have hh : noSweepBudget p N (mstep r) b r (tinyPhase p.g r D) warn (bp (D*N))≤
      2*C^2*bp (-1*N) := by
    let A := bp (2*(r:ℝ)*num (Comp p.g)*N)
    unfold noSweepBudget
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (absorb_pow p hD r b N he hp)
      (mul_nonneg (bp_pos _).le (sq_nonneg _)
      )) (bp_pos _).le).trans_eq ?_
    change A * (bp _ * C^2 * _) = _
    have he : A * bp (D*N) * bp (-(stage p.g r D)*N)= bp (-1*N) := by
      unfold A stage; rw [←bp_add,←bp_add]; congr 1; ring
    rw [← he]; ring
  exact (add_le_add_right hh _).trans_lt h

theorem span_stage (b r N : ℕ) (hN : denomStep r*b ≤ N) :
    (↑(maxSpan (mstep r) b r):ℝ) ≤ 0.001*N ∧
    2*(↑(maxSpan (mstep r) b r):ℝ)*r ≤ 0.001*N := by
  have he : maxSpan (mstep r) b r = r*Bstep r*b := by unfold maxSpan Bstep; ring
  rw [he]
  have hb : (Bstep r:ℝ)≥0 := Nat.cast_nonneg _
  have hL : (denomStep r:ℝ)*(b:ℝ) ≤ N := by exact_mod_cast hN
  unfold denomStep at hL
  push_cast at hL ⊢
  have h0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have h1 : 0 ≤ (Bstep r:ℝ)*(b:ℝ) := mul_nonneg hb (Nat.cast_nonneg _)
  constructor <;> nlinarith only [hL,h1,h0,mul_nonneg h0 h1, mul_nonneg (sq_nonneg (r:ℝ)) h1]

private theorem atlas_stage (p : Shape) (r : ℕ) :
    ∀ᶠ N : ℕ in atTop,∀ T : Cov p N,(∀ i,cdSign p T i ≤ maxSpan (mstep r) (N/denomStep r) r) →
      num (Atlas p r T)≤bp (0.002*N) := by
  let K := num (Wide p r)
  let L := bp (num (Comp p.g)*r*r)
  have he := bp_poly_dom_nat (by norm_num : 0<(0.001:ℝ)) (K*L) 0
  filter_upwards [he] with N h T hT
  apply (atlas_size T _).trans
  let W := maxSpan (mstep r) (N/denomStep r) r
  have hf : (cdim p T:ℝ) ≤2*W := by
    exact_mod_cast (show cdim p T≤ 2*W from (cdim_sign p T).trans_le
      ((add_le_add (hT _) (hT _)).trans_eq (two_mul W).symm))
  have h1 := mul_le_mul_of_nonneg_right hf (show 0≤(r:ℝ) from Nat.cast_nonneg _)
  have hL : (cdim p T:ℝ)*r≤0.001*N := h1.trans
    (span_stage _ r N (Nat.mul_div_le _ _)).2
  have h2 : K*L≤bp (0.001*N) := by simpa using h.le
  have h3 : 0≤K := Nat.cast_nonneg _
  rw [bp_add]
  change K * (_ * L) ≤ _
  rw [mul_comm _ L, ←mul_assoc]
  exact (mul_le_mul h2 (bp_le hL) (bp_pos _).le (bp_pos _).le).trans_eq (by
    rw [←bp_add]; congr 1; ring)

private theorem price_bound {p : Shape} {r n N k : ℕ} {L : ℝ}
    (x y : ℕ) (hx : x≤ 2*r) (hy : y≤ 2*r+k)
    (hf : (2*(r:ℝ))*num (Full p n)+2*p.h*(2*(r:ℝ)+k) ≤ 0.004*N)
    (hl : L ≤ bp (0.004*N)) :
    L*heatRate p n N (heatloss r k) x y≤loseA p N x y := by
  apply (mul_le_mul_of_nonneg_right hl
    (mul_nonneg (bp_pos _).le (bp_pos _).le)
    ).trans
  unfold loseA
  rw [←bp_add,←bp_add]
  refine bp_le ?_
  let ε := heatloss r k
  have he : ε*(4*r+k + (1:ℝ))=0.001 := by
    unfold ε heatloss; field_simp
  have hg : (x:ℝ)≤ 2*r := by exact_mod_cast hx
  have hh : (y:ℝ)≤ 2*r+k := by exact_mod_cast hy
  have ht : ε*(x+y:ℝ) ≤ 0.001 := he ▸ mul_le_mul_of_nonneg_left
    (show _≤_ by linarith) (heatloss_pos r k).le
  have hN := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N : 0≤(N:ℝ))
  have hi :
      num (Row p n)*x+2*p.h*(y:ℝ) ≤ 0.004*N := by
    have hu := mul_le_mul (row_le p n) hg
      (Nat.cast_nonneg x : 0≤(x:ℝ)) (Nat.cast_nonneg _ : 0≤num (Full p n))
    have hv := mul_le_mul_of_nonneg_left hh (show 0≤ 2*(p.h:ℝ) by positivity)
    linarith only [hf,hu,hv]
  push_cast
  unfold ε at hN
  linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]

private theorem early_spend (W : ℝ) :
    ∀ᶠ N : ℕ in atTop,W≤bp (0.004*N) := by
  filter_upwards [bp_poly_dom_nat (by norm_num : 0<(0.004:ℝ)) W 0] with N h
  simpa using h.le

private theorem glimpses_stage (g k r d : ℕ) (D L : ℝ) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
      glimpsesBill p k (rhUp L (tinyPhase g r D)) < coin^(k+1) ∧
      2*glimpsesBill p d (rhUp L (tinyPhase g r D)) ≤ coin/2 := by
  let L' := rhUp L (tinyPhase g r D)
  let f (k h : ℕ) := (num (Comp g×Bool))*(L'*2*bp ((k:ℝ)-h))
  have ht k : Tendsto (f k) atTop (𝓝 0) := by
    let c : ℝ := num (Comp g×Bool)*L'*2*bp k
    have h : f k=fun h : ℕ => c*bp (-1*h) := by
      unfold f c; ext; simp [neg_mul,bp_sub,bp_neg] <;> ring
    rw [h]
    simpa using (bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul c
  have hh : 0 < coin := by norm_num [coin]
  filter_upwards [(ht k).eventually (gt_mem_nhds (pow_pos hh (k+1))),
    (ht d).eventually (gt_mem_nhds (show 0 < coin/4 by linarith))] with h hA hB p hg hp
  subst g h
  change f k p.h < coin^(k+1) ∧ 2*f d p.h ≤ coin/2
  exact ⟨hA,by linarith only [show f d p.h < coin/4 from hB]⟩

set_option maxHeartbeats 1800000 in
theorem phase_calendar (g r k d : ℕ) (D L : ℝ) (hl : 0≤L) (hd : 0≤D)
    (hk : k ≤ d) (hK : D+1 ≤ 0.49*k) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ mix : Mixer p n, PhaseReady p n N (mstep r) (N/denomStep r) r k d mix
        (tinyPhase g r D) coin warn (heatloss r k) L (bp (D*N)) := by
  filter_upwards [glimpses_stage g k r d D L,tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2*pcoef g r D))] with h hstage hH p hg hp
  subst g h
  let ε := heatloss r k
  let t := tinyPhase p.g r D
  let A := rhUp L t
  let B := rhUp A coin
  obtain ⟨hG,hY⟩ := hstage p rfl rfl
  have he :
      ∀ᶠ N : ℕ in atTop,glimpsesBill p k A+bp (-0.1*N) < coin^(k+1) ∧
        5*coin+bp (-0.24*N)<0.005 ∧
        (num (Place p)*2)*(L*2*bp (-0.4*N))≤t/2 := by
    have ht := tinyPhase_pos p.g r D
    let P (N : ℕ) := bp (-0.1*N); let Q (N : ℕ) := bp (-0.24*N)
    let z : ℝ := num (Place p)*2*(L*2)
    have hf1 : ∀ᶠ N in atTop,P N< coin^(k+1)-glimpsesBill p k A :=
      (bp_nat_vanish (by norm_num)).eventually (gt_mem_nhds (sub_pos.mpr hG))
    have hf2 : ∀ᶠ N in atTop,Q N<0.005-5*coin :=
      (bp_nat_vanish (by norm_num)).eventually (gt_mem_nhds (by norm_num [coin]))
    have hf3 : ∀ᶠ N : ℕ in atTop,z*bp (-0.4*N)<t/2 := by
      have hh : Tendsto (fun N : ℕ => z*bp (-0.4*N)) atTop (𝓝 0) := by
        simpa using (bp_nat_vanish (by norm_num : 0<(0.4:ℝ))).const_mul z
      exact hh.eventually (gt_mem_nhds (half_pos ht))
    filter_upwards [hf1,hf2,hf3] with i hi hj hk
    refine ⟨?_,?_,?_⟩
    · unfold P at hi; linarith
    · unfold Q at hj; linarith
    rw [←mul_assoc]
    exact hk.le
  have hε : 0 < ε := heatloss_pos r k
  filter_upwards [columns_budget p (δ:=0.004) (by norm_num)
    (2*(r:ℝ)) (2*p.h*(2*(r:ℝ)+k)) (by positivity) (by positivity),
    columns_budget p (δ:=1) zero_lt_one 2 1 (by norm_num) zero_le_one, raw_ready p hε,
    eventually_grid he,eventually_grid (limit_pow p r hd hH), eventually_grid (atlas_stage p r),
    eventually_grid (early_spend A),eventually_grid (early_spend B),
    eventually_grid (early_spend (t/2)⁻¹),eventually_grid (eventually_ge_atTop (denomStep r))
    ] with M hcols hfull hraw hδ hF hQ ha hb hu hN
  filter_upwards [eventually_ge_atTop 1,hraw,hδ,hF,hQ,ha,hb,hu,hN] with n hn hz hz' hA hZ
    hα hβ hr ht
  dsimp only
  intro mix
  let N := M*n
  have h1 := hcols n hn
  have h2 := hfull n hn
  change 2*num (Full p n)+1≤1*N at h2
  let b := N/denomStep r
  refine ⟨(Nat.le_div_iff_mul_le (denom_pos r)).mpr (by simpa using ht),by unfold mstep; omega,
    hk,tinyPhase_pos ..,tinyPhase_le _ _ hd,by norm_num [coin],by norm_num [coin],
    bp_pos _,hε,hl,(bp_pos _).le,by linarith only [h2],?_,hA,?_,hZ,?_,?_,?_,
      hz'.1,hY,hz'.2.1⟩
  · exact (hz.2 mix).2
  · refine le_trans ?_ hz'.2.2
    unfold scaleBill
    change (num (Place p)*2)*(L*2 * bp (_+(maxSpan (mstep r) b r : ℝ)-N))≤_
    have hi := bp_le (show num (Row p n)+(maxSpan (mstep r) b r:ℝ) - N ≤ -0.4*N by
      have he := (span_stage b r N (Nat.mul_div_le _ _)).1
      linarith only [row_le p n,h2,he,(Nat.cast_nonneg N : 0≤(N:ℝ))])
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (by positivity))
      (by unfold num; positivity)
  · intro x y hx hy; exact price_bound x y hx (by omega) h1 hα
  · intro x y hx hy; exact price_bound x y hx (by omega) h1 hβ
  intro x hx
  let H := bp (D*N)
  have hh : rhUp H t * heatRate p n N ε x k≤ H * loseA p N x k := by
    unfold rhUp; rw [mul_comm _ H,mul_assoc]
    exact mul_le_mul_of_nonneg_left (price_bound x _ hx (by omega) h1 hr) (bp_pos _).le
  change bp _ * bp _ * _ ≤ _
  refine (mul_le_mul_of_nonneg_left hh
    (mul_nonneg (bp_pos _).le (bp_pos _).le)
    ).trans ?_
  unfold H loseA
  rw [← bp_add,← bp_add,← bp_add]
  apply bp_le
  change _ ≤ -0.2*(N:ℝ)
  have h3 := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg N : 0≤(N:ℝ))
  linarith only [h3,(Nat.cast_nonneg N : 0≤(N:ℝ))]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PinInjectionTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pin Injection Tests -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem rootSet_dim (b : Fpins p n N) (x : UnitType p n N) (i : Bool) (z : Place p) :
    dim (rootSet b x i z)≤planRank (b x) :=
  (Submodule.finrank_map_le ..).trans ((sPin_dim ..).trans (dim_le_plan ..))

theorem rootSet_subset (b : Fpins p n N) (x : UnitType p n N) (i : Bool) (z : Place p) :
    rootSet b x i z ≤ imageP p x i z := by
  rintro y ⟨v,hv,rfl⟩
  exact ⟨v,rfl⟩

theorem fans_of_not_inj (b : Fpins p n N) (x y : UnitType p n N) (m : Mixer p n)
    (hh : ∀ i,frameLaw m (onSide x i))
    (h : ¬tableInj (b x) (b y) (actual p x y)) :
    ∃ z i j, fans b z i j x y := by
  unfold tableInj at h
  push Not at h
  obtain ⟨z,i,j,v,hv,he,hg⟩ := h
  let B := fpAt p (onSide x i) z
  have hf : v∈sPin (b x) z i := ⟨_,hv,(by
    change (IP p n i)ᵀ *ᵥ (IP p n i *ᵥ v) = v
    rw [Matrix.mulVec_mulVec,IP_self,Matrix.one_mulVec])⟩
  have ht : Injective B.mulVec := by
    cases z with
    | mk e c =>
      cases c; exact primary_inj (hh i e).2.1; exact primary_inj (hh i e).1
  refine ⟨z,i,j,B *ᵥ v,⟨v,hf,rfl⟩, fun hx => hg (ht (hx.trans (Matrix.mulVec_zero _).symm)),?_⟩
  have hZ :
      channelOut p (actual p x y) j z * IP p n i=(fyAt p (onSide y j) (flipZ p z))ᵀ*B := by
    unfold channelOut actual
    rw [Matrix.mul_assoc (images x z)ᵀ,images_ih,Matrix.transpose_mul,Matrix.transpose_transpose,
      Matrix.mul_assoc,images_ip]; rfl
  rw [Matrix.mulVec_mulVec,hZ,← Matrix.mulVec_mulVec] at he
  exact he

set_option maxHeartbeats 600000 in
theorem strikers (b : Fpins p n N) (K : ℕ) (hb : ∀ x,planRank (b x)≤K)
    {k : ℕ} (P : Mat (Fin N) (Fin k)) (h : Injective P.mulVec)
    {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0 ≤ H)
    (hh : bySide p w m H) (hw : SubLaw w) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1) :
    pr w (fun y => ∀ j,strikeH b z i (P.col j) y) ≤ fireBill p k K H := by
  classical
  let f (y : UnitType p n N) := (fyAt p (onSide y i) (flipZ p z))ᵀ*P
  have hh' y (hh : ∀ j,strikeH b z i (P.col j) y) :
      colSp (f y)≤ hPin (b y) z i := by
    rw [colSp, range_mulVecLin]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hh j)
  let A := Mat (Chan p) (Fin K)
  let D := Mat (Fin K) (Fin k)
  have he y (hh : ∀ j,strikeH b z i (P.col j) y) :
      ∃ v : A×D, f y=v.1 * v.2 := by
    have hr : (f y).rank ≤ K :=
      (Submodule.finrank_mono (hh' y hh)).trans
        (((hPin_dim ..).trans (dim_le_plan ..)).trans (hb y))
    obtain ⟨Q,X,hQ⟩ := mul_factor (f y) K hr
    exact ⟨(Q,X),hQ.symm⟩
  let C (v : A×D) (x) := f x=v.1*v.2
  refine ((pr_mono hw.nz he).trans (pr_exists_le hw.nz C)).trans ?_
  have ht v :
      pr w (C v)≤H*2* (bp (-(p.h:ℝ)*k)) := by
    have he := test_transpose m hH hh i (flipZ p z) hN P h (v.1*v.2)
    rw [unif_apply,card_space,dim_mat] at he
    exact he.trans_eq (by rw [neg_mul,bp_neg]; simp)
  refine (Finset.sum_le_sum fun i _ => ht i).trans_eq ?_
  rw [Finset.sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Nat.cast_mul]
  have hA : num A=bp ((p.h:ℝ)*K) := by simp only [A,cast_mat,Chan,num,Fintype.card_fin]
  have hD : num D=bp ((K:ℝ)*k) := by simp only [D,cast_mat,num,Fintype.card_fin]
  unfold fireBill
  change num A*num D*_ = _
  rw [hA,hD,←bp_add, mul_left_comm,←bp_add]; congr 2; ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InjectionWitnesses
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injection Witnesses -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

omit [Fintype I] in
private theorem moreMatrix_act_p1 {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (x : Vec (Fin (r+1))) :
    moreMatrix_p1 A v *ᵥ x=x 0 • v + A *ᵥ (fun i => x i.succ) := by
  funext i; simp only [Matrix.mulVec,dotProduct,moreMatrix_p1,Matrix.of_apply,
    Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Fin.cons_zero,Fin.cons_succ]
  congr 1; exact mul_comm _ _

omit [Fintype I] in
private theorem moreMatrix_inj_p1 {r : ℕ} (A : Mat I (Fin r)) (v : Vec I)
    (ha : Injective A.mulVec) (h : v∉colSp A) :
    Injective (moreMatrix_p1 A v).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  rw [moreMatrix_act_p1] at hx
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

variable {p : Shape} {n N : ℕ}

set_option maxHeartbeats 800000 in
private theorem booming (b : Fpins p n N) (K k t : ℕ) (hk : k≤t)
    (hK : ∀ x,planRank (b x) ≤ K) (z : Place p) (i j : Bool)
    (w v : Wgt (UnitType p n N)) (hw : IsLaw w) (hv : IsLaw v) {l : ℝ} (hl : 0 < l)
    (hf : ∀ T : Space (Vec (Fin N)),dim T ≤ t →
      pr w (fun x => ¬Disjoint (imageP p x i z) T) ≤ l)
    (Q : UnitType p n N→Prop) (hp : 0 < pr v Q)
    (hQ : ∀ y,Q y→3*l≤ pr w (fun x => fans b z i j x y)) :
    ∃ Y : Mat (Fin N) (Fin k), Injective Y.mulVec ∧
      (pushCost l K)^k * pr v Q ≤ pr v (fun y => Q y ∧ ∀ m,strikeH b z j (Y.col m) y) := by
  classical
  have hx : 0<pushCost l K := div_pos hl (bp_pos _)
  induction k with
  | zero =>
    refine ⟨0,fun a b _ => Subsingleton.elim a b,?_⟩
    simp
  | succ k ih =>
    obtain ⟨Y,hY,hA⟩ := ih (Nat.le_of_succ_le hk)
    let S (y) := Q y∧∀ m,strikeH b z j (Y.col m) y
    have hq : 0 < pr v S := lt_of_lt_of_le (mul_pos (pow_pos hx _) hp) hA
    let P (x : UnitType p n N) := Disjoint (imageP p x i z) (colSp Y)
    obtain ⟨x,hx,hP⟩ :
        ∃ x,P x ∧ l*pr v S<pr v (fun y => S y ∧ fans b z i j x y) := by
      have hg :
          avg w (fun x => ind (P x)*pr v (fun y => S y∧fans b z i j x y))=
          avg v (fun y => ind (S y)*pr w (fun x => fans b z i j x y∧P x)) := by
        unfold pr; simp_rw [← avg_mul',ind_and]
        rw [avg_avg]; apply congrArg; funext y
        apply congrArg; ext; ring
      have he : pr w (fun x => ¬ P x) ≤ l := hf _ ((Y.rank_le_card_width.trans_eq
        (Fintype.card_fin _)).trans (Nat.le_of_succ_le hk))
      let g (x) := ind (P x)*pr v (fun y => S y∧fans b z i j x y)
      have hh : 2*l*pr v S≤avg w g := by
        unfold g; rw [hg]
        unfold pr; rw [← avg_mul']; refine avg_mono hv.nz fun y => ?_
        by_cases ht : S y
        · rw [ind_one ht,mul_one,one_mul]
          refine le_trans ?_ (pr_shield hw.nz (fun x => fans b z i j x y) P)
          have hh := hQ y ht.1; linarith
        rw [ind_zero ht,zero_mul,mul_zero]
      obtain ⟨x,hx⟩ : ∃ x,l*pr v S<g x := by
        by_contra! hn
        have hw := hh.trans (hw.avg_le hn)
        nlinarith
      by_cases hi : P x
      · exact ⟨x,hi,by simpa only [g,ind_one hi,one_mul] using hx⟩
      have he : g x=0 := by simp [g,ind_zero hi]
      rw [he] at hx
      exact (not_lt_of_ge (mul_pos hl hq).le hx).elim
    let R := rootSet b x i z
    let C (v : R) (y : UnitType p n N) := v.val≠0 ∧ S y ∧ strikeH b z j v.val y
    obtain ⟨a,ha⟩ :
        ∃ a : R,pushCost l K*pr v S<pr v (C a) := by
      have h (y) : (S y∧fans b z i j x y) → ∃ a : R,C a y := by
        rintro ⟨h,a,ha,hk,hb⟩; exact ⟨⟨a,ha⟩,hk,h,hb⟩
      have hh := (hP.trans_le (pr_mono hv.nz h)).trans_le (pr_exists_le hv.nz C)
      by_contra! he
      have ht := hh.trans_le (Finset.sum_le_sum fun i _ => he i)
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space] at ht
      have hlg : bp (dim R) ≤ bp K := bp_le (by exact_mod_cast ((rootSet_dim ..).trans (hK x)))
      have he' := mul_le_mul_of_nonneg_right hlg (show 0≤pushCost l K*pr v S by
        unfold pushCost; exact mul_nonneg (div_nonneg hl.le (bp_pos _).le) hq.le)
      have hr : bp (K:ℝ)*(pushCost l K*pr v S)=l*pr v S := by
        have hz := bp_pos (K:ℝ)
        unfold pushCost
        field_simp
      exact (lt_irrefl _ (ht.trans_le (he'.trans_eq hr)))
    have hc : a.val≠0 := by
      by_contra hc
      rw [show C a=(fun _ => False) by unfold C; rw [hc]; simp,pr_false] at ha
      have h := div_pos hl (bp_pos (K:ℝ))
      exact (not_lt_of_ge (mul_pos h hq).le ha).elim
    refine ⟨moreMatrix_p1 Y a.val,moreMatrix_inj_p1 Y _ hY ?_,?_⟩
    · intro h
      exact hc (Submodule.disjoint_def.mp hx a.val ((rootSet_subset ..) a.property) h)
    · have hC y (h : C a y) : Q y ∧ ∀ m,strikeH b z j ((moreMatrix_p1 Y a.val).col m) y := by
        refine ⟨h.2.1.1,fun k => Fin.cases h.2.2 (fun m => ?_) k⟩
        have hh : (moreMatrix_p1 Y a.val).col m.succ=Y.col m := by
          ext; simp [Matrix.col_apply,moreMatrix_p1]
        rw [hh]; exact h.2.1.2 m
      rw [pow_succ,mul_comm _ (pushCost l K),mul_assoc]
      exact ((mul_le_mul_of_nonneg_left hA (div_pos hl (bp_pos _)).le).trans ha.le).trans
        (pr_mono hv.nz hC)

set_option maxHeartbeats 600000 in
theorem cannon {b : Fpins p n N} (K k : ℕ)
    (hK : ∀ x,planRank (b x) ≤ K) (z : Place p) (i j : Bool)
    (w v : Wgt (UnitType p n N)) (hw : IsLaw w) (hv : IsLaw v)
    {l : ℝ} (hl : 0 < l)
    (m : Mixer p n) {A B : ℝ} (hL : 0≤ A) (hB : 0 ≤ B)
    (he : bySide p w m A) (hf : bySide p v m B)
    (hN : 2*num (Full p n)-N≤ -1)
    (hg : A*2*bp (num (Row p n)+k-N) ≤ l) :
    pr v (fun y => 3*l≤ pr w (fun x => fans b z i j x y)) ≤
      fireBill p k K B / (pushCost l K)^k := by
  classical
  let Q := fun y => 3*l≤pr w (fun x => fans b z i j x y)
  have hx : 0<pushCost l K:= div_pos hl (bp_pos _)
  apply (le_div_iff₀ (pow_pos hx _)).mpr
  rw [mul_comm]
  by_cases h : 0<pr v Q
  · have het (T : Space (Vec (Fin N))) (h : dim T≤k) :
        pr w (fun x => ¬Disjoint (imageP p x i z) T)≤ l := by
      apply le_trans (any_frame_hit m hL he i z hN T) (le_trans ?_ hg)
      have hr : (dim T:ℝ) ≤ k := by exact_mod_cast h
      gcongr
    obtain ⟨Y,hY,hP⟩ := booming b K k k le_rfl hK z i j w v hw hv hl het Q h (fun _ h => h)
    exact (hP.trans (pr_mono hv.nz fun _ => And.right)).trans
      (strikers b K hK Y hY m hB hf hv.sub j z hN)
  exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.le _) (not_lt.mp h)).trans (by
    unfold fireBill; exact mul_nonneg (by positivity) (bp_pos _).le)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TableInjectionTransfer
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Table Injection Transfer -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {A B : Type}

theorem pair_each [Fintype A] (w : Wgt A) (P : A×A→Prop) :
    pr (pairW w w) P = avg w (fun y => pr w (fun x => P (x,y))) := by
  unfold pr
  rw [pairW_avg]; exact avg_avg w w _

set_option maxHeartbeats 600000 in
private theorem named_fans {P : UnitType p n N × UnitType p n N → Prop}
    {C U L l : ℝ} (hP : named P C) (hu : 0<U) (hl : 0≤L) (hℓ : 0<l)
    (w : Wgt (UnitType p n N)) (b : Fpins p n N) (K k : ℕ)
    (hb : ∀ x,planRank (b x)≤K)
    (hw : IsLaw w) (m : Mixer p n) (hm : bySide p w m L) (i j : Bool) (z : Place p)
    (hN : 2*num (Full p n)-N≤ -1)
    (hf : rhUp L (2*U)*2 * bp (num (Row p n)+k-N) ≤ l) :
    pr (pairW w w) (fun x => P x ∧ fans b z i j x.1 x.2) ≤
      3*l* pr (pairW w w) P + U+ C*(fireBill p k K L/(pushCost l K)^k) := by
  classical
  obtain ⟨t,hC,S,hS⟩ := hP
  let v := onW w
  let f := fans b z i j
  let event (y : UnitType p n N) :=
    ∃ a : Fin t,U≤pr w (S a) ∧ 3*l≤pr (v (S a)) (fun x => f x y)
  let R := fireBill p k K L/(pushCost l K)^k
  have hR : 0 ≤ R := by
    refine div_nonneg ?_ (pow_nonneg (div_pos hℓ (bp_pos _)).le _)
    exact mul_nonneg (by positivity) (bp_pos _).le
  have he : pr w event ≤ C * R := by
    let Q (a : Fin t) := fun y => U ≤ pr w (S a) ∧ 3*l≤pr (v (S a)) (fun x => f x y)
    have h a : pr w (Q a) ≤ R := by
      by_cases ht : U≤pr w (S a)
      · have hv := on_law hw.nz (lt_of_lt_of_le hu ht)
        have hk := bySide_on m hw.nz hm (S a) (show 0<2*U by positivity) (by linarith)
        simp only [Q,ht,true_and]
        exact cannon K k hb z i j (v (S a)) w hv hw hℓ m (by unfold rhUp; positivity)
          hl hk hm hN hf
      simp only [Q,ht,false_and,pr_false]; exact hR
    refine (pr_exists_le hw.nz Q).trans ?_
    refine (Finset.sum_le_sum fun i _ => h i).trans ?_
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hC hR
  have hU (y : UnitType p n N) :
      pr w (fun x => P (x,y) ∧ f x y) ≤ 3*l*pr w (fun x => P (x,y)) + U + ind (event y) := by
    obtain ⟨a,ha⟩ := hS y
    simp_rw [ha]
    have h1 := pr_nonneg (p:=S a) hw.nz
    have hr := mul_nonneg (show 0≤3*l by linarith) h1
    by_cases h : U≤pr w (S a)
    · by_cases ht : 3*l ≤ pr (v (S a)) (fun x => f x y)
      · rw [ind_one (show event y from ⟨a,h,ht⟩)]
        exact ((pr_le_tot hw.nz).trans hw.total.le).trans (by linarith only [hr,hu])
      rw [pr_of_on hw.nz]
      have hj := mul_le_mul_of_nonneg_left (le_of_not_ge ht) h1
      have hi := ind_nonneg (event y)
      refine hj.trans ?_
      linarith only [hi,hu]
    have hh := (pr_mono hw.nz (p:=fun x => S a x∧ f x y) (q:=S a) fun x h => h.1).trans
      (le_of_not_ge h)
    refine hh.trans ?_
    linarith only [hr,ind_nonneg (event y)]
  rw [pair_each,pair_each]
  apply (avg_mono hw.nz hU).trans
  rw [avg_add,avg_add,avg_mul',hw.avg_const]
  exact add_le_add_right he _

set_option maxHeartbeats 800000 in
theorem secure_one {P : UnitType p n N × UnitType p n N → Prop}
    {C U L l : ℝ} (hP : named P C) (hu : 0<U) (hl : 0≤L) (hℓ : 0<l)
    (w : Wgt (UnitType p n N)) (b : Fpins p n N) (K k : ℕ)
    (hb : ∀ x,planRank (b x)≤K)
    (hw : IsLaw w) (m : Mixer p n) (hm : bySide p w m L)
    (hx : ∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i))
    (hN : 2*num (Full p n)-N≤ -1)
    (hf : rhUp L (2*U)*2 * bp (num (Row p n)+k-N) ≤ l) :
    pr (pairW w w) (fun x => P x ∧ ¬ acceptsInj p b x) ≤
      (4*num (Place p))*(3*l* pr (pairW w w) P + U+ C*(fireBill p k K L/(pushCost l K)^k)) := by
  classical
  let J := Place p × Bool × Bool
  let Q := fun (u : Place p × Bool × Bool) (x : UnitType p n N × _) =>
    P x ∧ fans b u.1 u.2.1 u.2.2 x.1 x.2
  let v := pairW w w
  have hh x (h : v x≠0) (hf : P x ∧ ¬ acceptsInj p b x) : ∃ i,Q i x := by
    obtain ⟨z,i,j,hf₀⟩ := fans_of_not_inj b _ _ m (hx x.1 (left_ne_zero_of_mul h)) hf.2
    exact ⟨(z,i,j),⟨hf.1,hf₀⟩⟩
  have hv := (pairW_law hw hw).nz
  refine ((pr_on_mono hv hh).trans (pr_exists_le hv Q)).trans ?_
  refine (Finset.sum_le_sum fun i _ => named_fans hP hu hl hℓ w b K k hb hw m hm i.2.1 i.2.2 i.1
    hN hf).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,num,Fintype.card_bool]
  push_cast
  ring

theorem perm_pair_prob [Fintype A] (w : Wgt A) (P : A × A→ Prop) :
    pr (pairW w w) (P ∘ Prod.swap)=pr (pairW w w) P := by
  rw [pair_each]
  unfold pr; rw [pairW_avg]; rfl

theorem secure_bound {P : UnitType p n N × UnitType p n N → Prop}
    {C U L l : ℝ} (hP : named P C) (hq : named (P ∘ Prod.swap) C)
    (hu : 0<U) (hl : 0≤L) (hℓ : 0<l)
    (w : Wgt (UnitType p n N)) (b : Fpins p n N) (K k : ℕ)
    (hb : ∀ x,planRank (b x)≤K)
    (hw : IsLaw w) (m : Mixer p n) (hm : bySide p w m L)
    (hx : ∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i))
    (hN : 2*num (Full p n)-N≤ -1)
    (hf : rhUp L (2*U)*2 * bp (num (Row p n)+k-N) ≤ l) :
    pr (pairW w w) (fun x => P x ∧ ¬ secureAt p b x) ≤
      8*num (Place p)*(3*l*pr (pairW w w) P+U+C*(fireBill p k K L/(pushCost l K)^k)) := by
  classical
  let Q := acceptsInj p b
  let v := pairW w w
  have he := secure_one hP hu hl hℓ w b K k hb hw m hm hx hN hf
  have ht :
      pr v (fun x => P x∧¬ Q x.swap)≤
      4*num (Place p)*(3*l*pr v P+U+C*(fireBill p k K L/(pushCost l K)^k)) := by
    rw [←perm_pair_prob w (fun x => P x∧¬Q x.swap),←perm_pair_prob w P]
    have h : (fun x => P x∧¬Q x.swap) ∘ Prod.swap = fun x => P x.swap∧¬ Q x := by
      funext x; rw [Function.comp_apply,Prod.swap_swap]
    rw [h]; exact secure_one hq hu hl hℓ w b K k hb hw m hm hx hN hf
  have hx x : P x ∧ ¬secureAt p b x → (P x∧¬Q x)∨ (P x ∧¬Q x.swap) := by
    intro h
    have hh : P x∧¬ (Q x∧Q x.swap) := h
    tauto
  have hv := (pairW_law hw hw).nz
  refine ((pr_mono hv hx).trans ((pr_or_le hv).trans (add_le_add he ht))).trans_eq ?_
  unfold v
  ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RelativeInjectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative Injection Bounds -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Submodule Function Finset Filter
open scoped BigOperators Topology
variable {p : Shape} {n N : ℕ}

private theorem fire_budget (K : ℕ) (p : Shape) {l D : ℝ}
    (hd : 0 ≤D) (hh : 2*K+l+200*(D+2 : ℝ) ≤ p.h) :
    ∀ᶠ N : ℕ in atTop,
      bp (D*N)*(fireBill p (N/100) K (shine N)/(pushCost (bp (-l)) K)^(N/100)) ≤ fringe N := by
  have he := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (1+p.h*(K:ℝ)))
  filter_upwards [he,eventually_ge_atTop 100] with N hN hk
  change (1+p.h*(K:ℝ))≤(N:ℝ) at hN
  let k := N/100
  have ht : N ≤ 200*k := by
    have h1 : 1 ≤ N/100 := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hk)
    have h := Nat.div_add_mod' N 100
    unfold k; omega
  have ht' : (N:ℝ)≤200*k := by exact_mod_cast ht
  have h1 : (D+2)*N≤ (p.h-(2*K+(l:ℝ)))*k := by
    have h := mul_le_mul_of_nonneg_left ht' (show 0≤D+2 by linarith)
    have h' := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg k : 0≤(k:ℝ))
    linarith only [h,h']
  change bp _*(fireBill p k K (shine N)/_ ^ k)≤_
  unfold fireBill pushCost shine fringe
  rw [←bp_sub, ← bp_mul_nat, ← bp_one,←bp_add,←bp_add,←bp_sub,←bp_add]
  apply bp_le
  linarith only [h1,hN,(Nat.cast_nonneg N : 0≤(N:ℝ))]

set_option maxHeartbeats 1000000 in
theorem guard_grid (g K : ℕ) (D ε : ℝ) (hd : 0≤D) (he : 0<ε) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
    ∀ (P : UnitType p n N×UnitType p n N→Prop),
    named P (bp (D*N)) → named (P ∘ Prod.swap) (bp (D*N)) →
    ∀ w (b : Fpins p n N) (m : Mixer p n), (∀ x,planRank (b x)≤ K) →
    IsLaw w → bySide p w m (shine N) → (∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i)) →
    pr (pairW w w) (fun x => P x ∧ ¬ secureAt p b x) ≤
      ε*pr (pairW w w) P+edgeError N := by
  let W := 8*num (Comp g×Bool)
  obtain ⟨k,hk⟩ : ∃ k : ℕ,W*(3*bp (-(k:ℝ)))≤ ε := by
    have hh : Tendsto (fun n : ℕ => W*(3*bp (-(n:ℝ)))) atTop (𝓝 0) := by
      have hi := ((bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul 3).const_mul W
      simpa using hi
    obtain ⟨n,hn⟩ := (hh.eventually (gt_mem_nhds he)).exists
    exact ⟨n,hn.le⟩
  let l := bp (-(k:ℝ))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2*K+(k:ℝ)+200*(D+2)))] with h hH p hg hp

  have heq : (8*num (Place p):ℝ)*(3*l) ≤ ε := by
    change (8*num (Comp p.g×Bool):ℝ)*(3*l) ≤ _
    rwa [hg]
  have hFire : ∀ᶠ N : ℕ in atTop,
      bp (D*N)*(fireBill p (N/100) K (shine N)/(pushCost l K)^(N/100)) ≤ fringe N :=
    fire_budget K p hd (hp.symm ▸ hH)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      8*num (Place p)*(fringe N +fringe N)≤edgeError N := by
    filter_upwards [bp_poly_dom_nat (by norm_num : 0<(0.005:ℝ)) (8*num (Place p)*2) 0] with N hN
    unfold fringe edgeError
    rw [←two_mul,←mul_assoc]
    refine (mul_le_mul_of_nonneg_right (show _≤bp (0.005*N) from by simpa using hN.le)
      (bp_pos _).le).trans_eq ?_
    rw [←bp_add]; congr 1; ring
  filter_upwards [eventually_grid hFire,eventually_grid hsmall,
    columns_budget p (δ:=1) zero_lt_one 2 1 (by norm_num) zero_le_one,
    eventually_grid (tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (10*((k:ℝ)+1))))] with M hM hT hS hY
  filter_upwards [hM,hT,eventually_ge_atTop 1,hY] with n hM hT hn hY
  dsimp only
  intro P hP hQ w b m hb hw hW hx
  let N := M*n
  have hN : 2*num (Full p n)+1≤N := (hS n hn).trans_eq (one_mul _)
  have hρ : rhUp (shine N) (2*fringe N)*2 * bp (num (Row p n)+(N/100:ℕ)-N)≤l := by
    change 10*((k:ℝ)+1) ≤ N at hY
    have hh : 100*((N/100:ℕ):ℝ)≤N := by exact_mod_cast (show 100*(N/100) ≤ N from Nat.mul_div_le _ _)
    unfold rhUp shine fringe
    rw [show 2*bp (-0.01*N)/2=bp (-0.01*N) from (by ring), ← bp_neg, ←bp_one,
      ←bp_add,←bp_add,←bp_add]
    apply bp_le
    linarith only [hY,hN,hh,row_le p n]
  have hl : 0<l:=bp_pos _
  have hX := secure_bound hP hQ (bp_pos _ : 0<fringe N) (bp_pos _).le hl w b K (N/100) hb
    hw m hW hx (by linarith only [hN]) hρ
  let V := pr (pairW w w) P
  have hv : 0≤V := pr_nonneg (pairW_law hw hw).nz
  have hi := mul_le_mul_of_nonneg_right heq hv
  refine hX.trans ?_
  change (8*num (Place p))*(3*l*V+_ + bp (D*N)* _)≤ε*V+_
  calc _ ≤ (8*num (Place p))*(3*l*V+fringe N + fringe N) :=
      mul_le_mul_of_nonneg_left (add_le_add (show 3*l*V+fringe N ≤ _ from le_rfl) (show _ ≤ fringe N from hM)) (by unfold num; positivity)
       _ ≤ _ := by linarith only [hi,hT]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PartitionSelection
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partition Selection -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

variable {w μ : Wgt (UnitType p n N)}

theorem first_ripe {ζ D : ℝ} {K : ℕ} (hz : 0 < ζ) (hz' : ζ < 1) (hn : 0<N)
    (hR : ∀ a : Pin p n N, pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N) * μ x) (hw : ∀ x, 0 ≤ w x)
    (R : CTile p n N) (hK : D + ζ ≤ (ζ-ζ/4)*K) :
    ∃ T : Canopy p n N,apart T ∧ (∀ S∈T,S⊆R ∧ ∃ b,Ripe p w μ S b (D+K+1) ζ K) ∧
      pr w (fun x => x∈R ∧ ¬ inTiles T x) ≤ bp (-ζ*N) := by
  let a := dustPin p n N
  have h x : a.agree x := by
    intro i v hv
    have hl : v = 0 := show v∈(⊥:Space _) from hv
    rw [hl,Matrix.mulVec_zero,Matrix.mulVec_zero]
  obtain ⟨T,hT,hU,hW⟩ := peel_family hz hz' hn hR hc hw R a (fun i _ => h i) hK
  have he : planRank a.sp=0 := Finset.sum_eq_zero (fun i _ => finrank_bot ..)
  refine ⟨T,hU,fun S h => ?_,hW⟩
  obtain ⟨hh,b,hb⟩ := hT S h
  exact ⟨hh,b,hb.pos,hb.fixpin,by simpa only [he,zero_add] using hb.bound,hb.clear,hb.density⟩

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

theorem strength.slide (h : strength s w μ D ζ K) (hD : D≤E) (hζ : ζ≤η)
    (hk : K≤L) (hμ : ∀ x,0≤μ x) : strength s w μ E η L := by
  classical
  refine ⟨h.part,fun i hi=>?_⟩
  have hh:=h.leaf _ hi
  refine ⟨hh.pos,hh.fixpin,hh.bound.trans hk,fun b=>?_,fun x=>?_⟩
  · refine (hh.clear b).trans (bp_le ?_)
    gcongr
  exact (hh.density x).trans (mul_le_mul_of_nonneg_right (bp_le (by gcongr)) (hμ _))

/-- first rural pack. -/
theorem grove_first (ζ D : ℝ) (K : ℕ) (hz : 0<ζ) (hz' : ζ < 1)
    (hn : 0<N)
    (hR : ∀ a : Pin p n N, pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x,w x ≤ bp (D*N)*μ x)
    (hw : ∀ x,0≤w x) (P : X p n N→Prop)
    (hK : D+ζ ≤ (ζ-ζ/4)*K) :
    ∃ s : LeafMixture p n N,s.strength w μ (D+K+1) ζ K ∧ s.within P ∧
      pr w P-bp (-ζ*N) ≤ s.amount w := by
  classical
  let R := Finset.univ.filter P
  have hr (x : X p n N) : x∈R↔ P x := by simp [R]
  obtain ⟨T,ht,hg,h⟩:= first_ripe hz hz' hn hR hc hw R hK
  choose a ha using (show ∀ S:CTile p n N,∃ a,S∈T→Ripe p w μ S a (D+K+1) ζ K from
    fun S=>by
      by_cases hs : S∈T
      · obtain ⟨x,h⟩:=(hg S hs).2; exact ⟨x,fun _=>h⟩
      exact ⟨dustPin ..,fun hh=>(hs hh).elim⟩)
  let s : LeafMixture p n N := ⟨T,a⟩
  refine ⟨s, ⟨ht,fun x hx=>ha x hx⟩,fun i hi x hx=>(hr x).mp ((hg _ hi).1 hx),?_⟩
  simp_rw [hr] at h
  let Q (x : X p n N) := P x ∧ ¬inTiles T x
  have hv (x : X p n N) : P x → inTiles T x ∨ Q x := by unfold Q; tauto
  have hh : pr w P ≤ s.amount w+bp (-ζ*N) :=
    ((pr_mono hw hv).trans (pr_or_le hw)).trans (add_le_add_right h _)
  linarith

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InitialPartitionExistence
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial Partition Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
namespace PreparationParameters

variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}

/-- combines early h & M choices assuming row/selector bounds supplied. -/
theorem stamp (g : ℕ) (q : PreparationParameters)
    (hq : q.allows) (hd : 0 < q.D) (hf : (q.D:ℝ)+q.ζ ≤ (q.ζ-q.ζ/4)*q.e)
    (hk : q.k≤ q.d) (hg : q.spJoint+1 ≤0.49*q.k)
    (hu : 3*q.d+2*q.e+2 ≤ q.u) :
    ∀ᶠ h : ℕ in atTop,∀ p:Shape,p.g=g→p.h=h →
    Odd p.g → 3≤p.g → 1≤p.j → 1≤p.r → (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j) →
    8*q.D <p.g*p.g → (∃ d_:ℕ,4*q.D≤p.g*d_∧2*screenRank p q.e+1 ≤ ((p.g-1)/2)*(p.g-d_)*p.r) →
    ∀ᶠ M : ℕ in atTop, q.entry p M := by
  classical
  have hl : 0≤q.spear := mul_nonneg (bp_pos _).le hq.hL
  have hq' : 0<q.ζ/4:=by have hh:=hq.pos; positivity
  have h1 : 0 ≤ q.spJoint := add_nonneg (Nat.cast_nonneg _) zero_le_one
  filter_upwards [phase_calendar g q.rank q.k q.d q.spJoint q.spear hl h1 hk hg,
    guard_grid g q.pins (3*q.d) 0.0005 (by positivity) (by norm_num)]
    with h hP hG p hp hH hg hg' hj hr hb hf' he
  have hs : 0<(q.D:ℝ)/2 := by positivity
  filter_upwards [hP p hp hH,hG p hp hH,sparse_usual p q.D hd,
    columns_budget p (δ:=1) zero_lt_one 2 1 (by norm_num) zero_le_one,
    raw_ready p hq',eventually_ge_atTop 1]
    with M hm hM hF hS hr' hqM
  have hz := trend_sizes atTop (le_refl _) hqM
  have hh : planted q p M := by
    refine ⟨hq,hqM,hg,hg',hj,hr,hb,hf',he,?_⟩
    filter_upwards [hm,hM,eventually_ge_atTop 1,hr',
      hz.2.eventually (eventually_ge_atTop (2*(q.e:ℝ)^2))] with n hn ht hi hr hN
    obtain ⟨_,hr⟩:=hr
    dsimp only
    have he := hS n hi
    rw [one_mul] at he
    refine ⟨by linarith only [he],?_, (fun m a=> (hr m).2 a),?_,ht⟩
    · have hg : (3*q.d+2*q.e+2:ℝ) ≤ q.u := by exact_mod_cast hu
      have hk := mul_le_mul_of_nonneg_right hg (show (0:ℝ) ≤ (M*n:ℕ) by positivity)
      change _≤((M*n:ℕ):ℝ) at hN
      linarith only [hN,hk]
    intro m
    specialize hn m
    rw [hp]; exact hn
  refine ⟨hh,?_⟩
  filter_upwards [hF,hh.wrap,hz.1.eventually (eventually_gt_atTop 0),
    (((bp_tendsto_zero hq.pos).comp hz.2).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))),
    (((bp_tendsto_zero hs).comp hz.2).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)))]
    with n hn ht hN hA hB N m w hw hx
  let P (x:UnitType p n N) := w x≠0 ∧ (rawHoles m).unit x ∧ joins x≤2*q.D ∧ frameSide p m x
  obtain ⟨s,h1,h2,h3⟩:= LeafMixture.grove_first q.ζ q.D q.e hq.pos hq.small hN
    (ht.2.2.1 m) hw.total hw.law.nz P hf
  refine ⟨s,?_,h1.slide (by unfold leafOld; linarith) le_rfl le_rfl
    (fun x=> mul_nonneg (raw_nonneg ..) (raw_nonneg ..)),h2⟩
  have heq x (h : w x≠0) : (rawHoles m).unit x ∧ frameSide p m x := by
    have he := lt_of_lt_of_le (lt_of_le_of_ne (hw.law.nz _) h.symm) (hw.total x)
    have he : usual p m N x≠0 := by intro hg; rw [hg,mul_zero] at he; exact he.false
    refine ⟨by_contra fun e=>h (hx x e),fun i=>?_⟩
    have hz := raw_carried m N
    cases i
    · exact by_contra fun e => right_ne_zero_of_mul he (hz _ e)
    exact by_contra fun e=> left_ne_zero_of_mul he (hz _ e)
  let Q (x:UnitType p n N):=2*q.D<joins x
  have hi : pr w P=pr w (fun x=>¬Q x) := by
    apply avg_congr
    intro x hx
    simp only [P,Q,(heq x hx).1,(heq x hx).2,and_true,true_and,not_lt]
    exact congrArg ind (propext (and_iff_right hx))
  rw [hi,pr_not,hw.law.total] at h3
  have he : pr w Q≤bp (-((q.D:ℝ)/2)*N) := by
    specialize hn _ _ hw.total
    rwa [neg_div] at hn
  change bp (-q.ζ*N)<1/4 at hA
  change bp _ < 1/4 at hB
  linarith only [he,h3,hB,hA]
end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ParameterExistence
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parameter Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

theorem floor_supply (x : ℝ) (y : ℝ) (hy : 0<y) : ∃ k : ℕ,x≤ y*k := by
  obtain ⟨i,hi⟩ := ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (x/y))).exists
  refine ⟨i,?_⟩
  rw [mul_comm]; exact (div_le_iff₀ hy).mp hi

set_option maxHeartbeats 1400000 in
theorem seed_ribbon : ∃ b : PreparationParameters, Ribbon b := by
  classical
  let x : ℝ := 56*((birthG-1:ℕ):ℝ)
  let ζ := 1/(1000*x)
  have hx : 1≤x := by norm_num [x,birthG]
  have hq : 0<ζ ∧ ζ≤1/1000 := by
    unfold ζ
    exact ⟨by positivity,(div_le_iff₀ (by positivity)).mpr (by linarith)⟩
  have hz : 0<ζ-ζ/4:=by linarith only [hq.1]
  let D:=4000*birthG
  obtain ⟨e,he⟩:=floor_supply ((D:ℝ)+ζ) _ hz
  obtain ⟨k,hk⟩:=floor_supply ((D:ℝ)+1+1) 0.49 (by norm_num)
  let d:= (2*e+2)*4*k
  let u:=10*(e+d+1)
  obtain ⟨r,hr⟩:=floor_supply ((D:ℝ)+e+2+u+ζ) _ hz
  let b : PreparationParameters:=⟨D,bp 1000,d,e,r,u,k,ζ,
      10*(frameBills birthG (3*e+r)+10000*birthG+1)⟩
  refine ⟨b,⟨⟨hq.1, hq.2.trans_lt (by norm_num), (bp_pos _).le, hr⟩, rfl,rfl,he,?_,hk,?_,?_,?_⟩⟩
  · change k ≤ d; unfold d; nlinarith
  · change 3*d+2*e+2 ≤ u; unfold u; omega
  · change frameBills birthG (3*e+r)+1000 ≤ 10*(_+10000*birthG+1)
    have hh : 3≤ birthG := by norm_num [birthG]
    omega
  change 2*ζ≤_ ∧ 2*ζ*x≤_
  refine ⟨by linarith only [hq.2],?_⟩
  have hg : ζ*x=1/1000 := by unfold ζ; field_simp
  linarith only [hg]

private theorem lanesNeed (q b j J : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      let p:= layout birthG b j J r
      rankAll p q+2*(q+2*(3*blin q))≤p.h := by
  let p:=layout birthG b j J 0
  let x:= rankAll p q +2*(q+2*(3*blin q))
  filter_upwards [eventually_ge_atTop x] with r hr
  let p':=layout birthG b j J r
  dsimp only
  change rankAll p' q + _≤ 1000*r
  have hh : rankAll p' q=rankAll p q+30*r := by
    unfold rankAll rankInit
    change 2*(15*r+14*J*ncComp p)+dqBound p (q+14) q (rankRes q)=_
    change _= 2*(15*0+14*J*ncComp p)+dqBound p (q+14) q (rankRes q)+30*r
    ring
  rw [hh]; unfold x at hr
  omega

private theorem altitude_need (q b j J : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      let p:= layout birthG b j J r
      2*screenRank p q+1 ≤ ((p.g-1)/2)*(p.g-16000)*p.r := by
  filter_upwards [eventually_ge_atTop (J*q+1)] with r hr
  unfold screenRank layout
  dsimp only
  norm_num only [birthG]
  norm_num [birthG] at *
  rw [Nat.mul_assoc 2 J]
  omega

private theorem labels_large (j B g : ℕ) (hg : 3≤g) :
    ∃ b:ℕ,(B:ℝ)<bp ((b:ℝ)-2*j) ∧ 3*B < Fintype.card (Label b) := by
  classical
  obtain ⟨b,hb⟩ := ((bp_poly_dom_nat (a:=1) zero_lt_one
    (100*g*(B+1:ℝ)*bp (2*j)) 0)).exists
  have he : 100*g*(B+1:ℝ)*bp (2*j)< bp (b:ℝ) := by simpa using hb
  have hb' : (B:ℝ)<bp ((b:ℝ)-2*j) := by
    rw [bp_sub,lt_div_iff₀ (bp_pos _)]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by
      have hh : 3≤(g:ℝ) := by exact_mod_cast hg
      nlinarith [(Nat.cast_nonneg B : 0≤(B:ℝ))]) (bp_pos _).le) he
  have hb'' : 3*B < Fintype.card (Label b) := by
    have hs : 1 ≤ bp (2*j) := by rw [←bp_zero]; exact bp_le (by positivity)
    have hh : Fintype.card (Label b)=2^b := by simp [Label,F]
    have heq : 3*(B:ℝ) < bp b := by
      have hh : 3≤(g:ℝ):=by exact_mod_cast hg
      refine lt_of_le_of_lt ?_ he
      have hz : 100*g*(B+1:ℝ) ≤ 100*g*(B+1:ℝ)*bp (2*j) := by
        exact le_mul_of_one_le_right (by positivity) hs
      nlinarith [(Nat.cast_nonneg B :0≤(B:ℝ))]
    rw [hh]; rw [bp_nat] at heq; exact_mod_cast heq
  exact ⟨b,hb',hb''⟩

set_option maxHeartbeats 240000 in
theorem exists_parameters_oai : ∃ (p : Shape) (b : PreparationParameters) (M r : ℕ),AnalyticParameters p M b r ∧
    p.g=birthG ∧ b.D=4000*p.g ∧ b.L=bp 1000 := by
  classical
  obtain ⟨t,ht⟩:=seed_ribbon
  let K:=t.pins; let g:=birthG
  have hg : 3 ≤ g := by norm_num [g,birthG]
  have hx : Odd g := by
    unfold g birthG; use 500000000; norm_num
  let j:= 10*(K+1)*(Rorth K+20)
  have hj : (K+1)*qorth K≤j+1 := by unfold j qorth; nlinarith
  have hj' : 6*Rorth K+4≤j := by unfold j; nlinarith
  obtain ⟨b,hb',hb''⟩:=labels_large j t.B g hg
  let C:=profileA (layout g b j 0 0) K
  let r:=4*C+1
  let J:=100*(r+K^2+1)+1
  have hyJ : 1≤J ∧ r≤J := by unfold J; omega
  have hJ : bp (-((J-r:ℕ):ℝ))*bp r < glintRate K := by
    rw [←bp_add]; apply bp_lt
    have hh : K^2+4+r≤J-r := by unfold J; omega
    have hi : ((K^2:ℕ):ℝ)+4+(r:ℝ) ≤ ((J-r:ℕ):ℝ) := by exact_mod_cast hh
    linarith only [hi]
  have hU : 8*t.D<g*g:=by rw [ht.hd]; norm_num [g,birthG]
  have hD : 0<t.D:=by rw [ht.hd]; norm_num [birthG]
  obtain ⟨h0,hA⟩:= Filter.eventually_atTop.mp (PreparationParameters.stamp g t ht.life hD ht.rain ht.hk
    ht.beam ht.dul)
  obtain ⟨y,hc,he,hy,_hx⟩:= ((lanesNeed K b j J).and ((altitude_need t.e b j J).and
    ((eventually_ge_atTop (1:ℕ)).and (eventually_ge_atTop h0)))).exists
  let p:=layout g b j J y
  have hp : realizeAssum p K:= ⟨hx,hj',hc⟩
  have hY : 1≤p.j := show 1≤j by omega
  have he' := hA p.h (show h0≤1000*y by omega) p rfl rfl hx hg hY hy hb' hU
    ⟨16000,(by change 4*t.D ≤ g*16000; rw [ht.hd]; norm_num [g,birthG]),he⟩
  obtain ⟨M,hM,hM',hK⟩:= (he'.and ((eventually_ge_atTop (4:ℕ)).and
    (collision_scales p K))).exists
  have hF : 2*C < r := by unfold r; omega
  refine ⟨p,t,M,r, ⟨hM,hM',show 2*C < r from hF,hyJ.1,hyJ.2,hJ,hj,ht.size,hb'',?_⟩,rfl,
    ht.hd,ht.mercury⟩
  filter_upwards [hK,eventually_ge_atTop (2*y)] with n hn he
  refine ⟨hy,he,hp,by linarith only [ht.life.pos],ht.dust.1, ?_,hn.1,hn.2.1,hn.2.2⟩
  unfold kmax; push_cast
  exact ht.dust.2
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.exists_parameters_oai := @OAI.HadwigerCounterexample.exists_parameters_oai
