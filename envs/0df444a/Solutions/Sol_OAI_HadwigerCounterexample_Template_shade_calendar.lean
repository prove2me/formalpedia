-- Prove2me | solution 1 for OAI.HadwigerCounterexample.Template.shade_calendar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:54.984631+00:00
-- url     : https://prove2.me/submissions/d0118fd7-b65a-4dfa-be9b-137f4c721d43

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ430Hc000
import Theorems.Thm_OAI_HadwigerCounterexample_Template_crane_mean
import Theorems.Thm_OAI_HadwigerCounterexample_law_peekR
import Theorems.Thm_OAI_HadwigerCounterexample_poUse
import Theorems.Thm_OAI_HadwigerCounterexample_pooled_batch

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

omit [Fintype I] in
/-- Matrix multiplication cancels when a left factor is injective. -/
theorem inj_comp_mat [Fintype K] (A : Mat I J) (B : Mat J K)
    (hA : Injective A.mulVec) (hB : Injective B.mulVec) :
    Injective (A*B).mulVec := by
  rw [← coe_mulVecLin,mulVecLin_mul]
  exact hA.comp hB

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentCoordinates
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

variable (p : Shape)
variable {n : ℕ}

theorem point_base_eval (s : Label p.b) (z : Base p.g n) (r : AIdx p.g n) :
    point p s z (emptySel,r) = baseV z r := by simp [point,putLab,selV,emptySel]

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.momFintype
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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
attribute [-instance] _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch
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

namespace Flavor

theorem keepZ (f : Flavor g) (x : Tag g) : keeps f x Block.Z := by
  rcases f with (_|_|_) <;> simp [keeps]

end Flavor

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

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

variable {A B V W : Type} [Fintype A] [Fintype B]

theorem avg_prod (w f g : Wgt A) :
    avg w f * avg w g = avg (pairW w w) (fun x => f x.1*g x.2) := (pairW_separate ..).symm

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseMomentBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem pr_shield {w : Wgt A} (h : ∀ x,0≤w x) (P Q : A→Prop) :
    pr w P-pr w (fun x => ¬Q x) ≤ pr w (fun x => P x ∧ Q x) := by
  have ht x : P x → (P x∧Q x) ∨ ¬Q x := fun h => by by_cases he:Q x <;> simp [h,he]
  exact sub_le_iff_le_add.mpr ((pr_mono h ht).trans (pr_or_le h))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterSummaryMass
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BatchCharacters
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Batch Characters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function Finset
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
variable {n N t : ℕ}

theorem led_uniform (F : Wgt (I→Rack J N)) :
    avg (unif : Wgt (Rack (I×J) N)) (fun x => F (fun i => led i x))=
    avg (draws I unif) F := by
  change avg unif (fun x => F (relay I J N x))=_
  rw [← mapW_avg,unif_equiv,← draws_unif]

theorem led_piece (T : Finset I) (p : I→Rack J N→Prop) :
    avg unif (fun x => ∏ i∈T,ind (p i (led i x))) =
      ∏ i∈T,pr unif (p i) := by
  classical
  let F (i : I) (z) := if i∈T then ind (p i z) else 1
  let H : Wgt (I→ Rack J N) := prodW F
  have he x : (∏ i∈T,ind (p i (led i x))) = H (fun i => led i x) := by
    unfold H F prodW
    rw [← Finset.prod_filter]; simp
  have hf i : avg unif (F i) = if i∈T then pr unif (p i) else 1 := by
    by_cases hh : i∈T <;> simp [F,pr,hh,unif_law.avg_const]
  simp_rw [he]; rw [led_uniform]
  unfold H draws
  rw [prodW_avg]; simp_rw [hf]; rw [← Finset.prod_filter]; simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionedBatchLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioned Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

private theorem cut_inj {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (A : PlusRack I N) (h : Injective A.mulVec) {g : J→I} (hg : Injective g) :
    Injective (A.submatrix _root_.id g).mulVec := by
  rw [← mul_embedMat]
  exact inj_comp_mat _ _ h (embedMat_inj hg)

variable {g : Route (I×J) G}

omit [Fintype G] in
set_option maxHeartbeats 600000 in
theorem laneGram (Z : GeoM g) (x : Rack (I × J) N) (h : bothPart Z x) (i : I) :
    bothPart (laneM Z i) (led i x) := by
  classical
  obtain ⟨hh,hj⟩ := (both_test ..).mp h
  apply (both_test ..).mpr
  constructor
  · refine (part_scores ..).mpr fun q a b => ?_
    exact (part_scores ..).mp hh q (condLane g i q a) (condLane g i q b)
  intro j
  let f := condLane g i j
  have he : Injective f := by intro a b h; exact Subtype.ext (congrArg
    (fun x : Port g j => x.val.2) h)
  exact ⟨cut_inj (rackEquiv g N x j).1 (hj j).1 he,
    cut_inj (rackEquiv g N x j).2 (hj j).2 he⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RepeatedBatchLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq I]
variable [DecidableEq J] [DecidableEq G] {p : Shape} {n N : ℕ}

variable {f : Route I G}

omit [Fintype I] [Fintype J] [Fintype G] [DecidableEq I] [DecidableEq J] [DecidableEq G] in
theorem peek_pooled (A B : J→NomQuery p n f) (x : Forum p n N G) (i : J) :
    led i (peekR p (tied f J) (pooled A) (pooled B) x)=peekR p f (A i) (B i) x := by
  apply Prod.ext <;> ext <;> rfl

omit [Fintype I] [Fintype J] [Fintype G] [DecidableEq I] [DecidableEq J] [DecidableEq G] in
theorem lane_pooled (A B : J→NomQuery p n f) (m : Mixer p n) (i : J) :
    laneM (database m (pooled A) (pooled B)) i=database m (A i) (B i) := by
  funext z; ext x y; rfl

omit [Fintype G] in
theorem pool_injective {A : J → NomQuery p n f} (h : ∀ i, Injective (pooled A i).mulVec) :
    ∀ z i,Injective (A z i).mulVec := by
  classical
  intro z i
  let e := condLane (tied f J) z i
  have he : Injective e := by
    intro a b h; exact Subtype.ext (congrArg (fun x : Port (tied f J) i => x.val.2) h)
  have ho : A z i=pooled A i*embedMat e := by rw [mul_embedMat]; rfl
  rw [ho]; exact inj_comp_mat _ _ (h i) (embedMat_inj he)

set_option maxHeartbeats 600000 in
theorem pool_upper (A B : J → NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (ha : ∀ i, Injective (pooled A i).mulVec)
    (hb : ∀ i, Injective (pooled B i).mulVec)
    (hL : ∀ i,2*num (Port (tied f J) i)-N ≤ -1) (P : J→Rack I N → Prop) :
    let w := forumLaw (G:=G) m N
    pr w (fun x => ∀ i,P i (peekR p f (A i) (B i) x))≤
      netFact (tied f J)* ∏ i, pr w (fun x => P i (peekR p f (A i) (B i) x)) := by
  classical
  let w := forumLaw (G:=G) m N
  let S := database m (pooled A) (pooled B)
  let q (x : Rack (J×I) N) := ∀ i,P i (led i x)
  have h1 i :
      pr w (fun x => P i (peekR p f (A i) (B i) x)) =
        pr (rackStation (database m (A i) (B i)) N) (P i) := by
    unfold w; rw [←mapW_pr,law_peekR m hN (pool_injective ha i) (pool_injective hb i)]
  have ht :
      pr w (fun x => ∀ i,P i (peekR p f (A i) (B i) x)) =
        pr (rackStation S N) q := by
    rw [show pr (rackStation S N) q= _ from
      (poUse A B m hN ha hb (fun x => ind (q x))).symm]
    refine avg_congr fun x _ => ?_
    simp_rw [q,peek_pooled]
  let M := netFact (tied f J)
  let g (i : J) := bothPart (laneM S i) (N:=N)
  have hg x (hh : bothPart S x ∧ q x) :
      ∀ i,g i (led i x)∧ P i (led i x) := fun i => ⟨laneGram S _ hh.1 _,hh.2 i⟩
  change pr w _ ≤ _
  rw [ht, rackStation,← on_unif,pr_on]
  have hx : pr unif (fun x : Rack (J×I) N => ∀ i,g i (led i x)∧ P i (led i x)) =
      ∏ i,pr unif (fun x => g i x∧P i x) := by
    change avg unif _=_
    simp_rw [ind_all]
    exact led_piece Finset.univ (fun i x => g i x∧P i x)
  have hh0 := net_norm S N hL
  refine (div_le_div₀ (pr_nonneg unif_law.nz)
    (pr_mono unif_law.nz hg) (inv_pos_of_pos netFact_pos) hh0.1).trans ?_
  rw [hx,div_eq_mul_inv,inv_inv,mul_comm]
  apply mul_le_mul_of_nonneg_left _ netFact_pos.le
  refine Finset.prod_le_prod (fun i _ => pr_nonneg unif_law.nz) (fun i _ => ?_)
  rw [pr_of_on unif_law.nz (g _),on_unif,h1]
  have h0 (i) : pr unif (g i)≤1 := (pr_le_tot unif_law.nz).trans unif_law.total.le
  apply le_trans (mul_le_mul_of_nonneg_right (h0 _) (pr_nonneg (unifOn_sub _).nz))
  unfold g S; rw [lane_pooled,one_mul]; exact le_rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GroupedQueryIndependence
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem law_probes (p : Shape) (n)
    (w : I→ Wgt (Knobs p.g n)) (hw : ∀ i,mapW (w i) (freePart p)=unif) :
    mapW (draws J (prodW w)) (freeNet p (n:=n) (I:=I))=unif := by
  classical
  let X (x : Inputs p n I) : I → Vec (Fin n) := fun i => freePart p (x i)
  have he := mapW_repeat w (f:=fun i => freePart p (n:=n))
  simp_rw [hw] at he
  have hh : mapW (prodW w) X=unif := he.trans (Eq.symm draws_unif)
  let E : (J→I→Vec (Fin n))≃PlusRack (J×I) n :=
    { toFun := fun x => Matrix.of (fun i j => x j.1 j.2 i)
      invFun := fun x j i k => x k (j,i)
      left_inv _ := rfl
      right_inv _ := rfl }
  let Y (x : J→ Inputs p n I) := fun i => X (x i)
  have h : mapW (draws J (prodW w)) Y=unif := by
    have hY := mapW_repeat (fun (_ : J) => prodW w) (fun _ => X)
    simp_rw [hh] at hY
    exact hY.trans (Eq.symm draws_unif)
  change mapW _ (E ∘ Y) = _
  rw [←mapW_nested,h,unif_equiv]

theorem buds (p : Shape) (n)
    (w : I→ Wgt (Knobs p.g n)) (hw : ∀ i,mapW (w i) (freePart p)=unif) :
    pr (draws J (prodW w)) (fun x => ¬bloom p x) ≤ bp (num J*num I-n) := by
  classical
  unfold bloom
  rw [show pr _ _ = pr (mapW (draws J (prodW w)) (freeNet p)) (fun x : PlusRack (J×I) n =>
    ¬Injective x.mulVec) from (mapW_pr ..).symm,law_probes _ _ _ hw]
  simpa only [num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    using (@unif_fail (J×I) (Fin n) _ _ _ _)

omit [DecidableEq I] in
theorem inject_column_slice {f : I→J} (M : PlusRack J n)
    (h : Injective M.mulVec) (hf : Injective f) :
    Injective (M.submatrix _root_.id f).mulVec := by
  rw [← mul_embedMat]
  exact inj_comp_mat _ _ h (embedMat_inj hf)

variable {g : Route I G}

omit [Fintype G] [DecidableEq J] in
theorem ray_bloom {f : Route J G} {b : J → I}
    {A : NomQuery p n f} (e : G) (V : PlusRack I n)
    (h : Injective V.mulVec) (he : Injective (fun i : Port f e => b i.val))
    (hm : ∀ i : Port f e, ∀ j : Fin n,A e (emptySel,some (Block.Z,j)) i=V j (b i.val)) :
    Injective (A e).mulVec := by
  intro x y hx
  apply inject_column_slice V h he
  funext j
  have hh := congr_fun hx (emptySel,some (Block.Z,j))
  change ∑ i:Port f e,_=∑ i:Port f e,_ at *
  simp_rw [hm] at hh; exact hh

namespace Template

variable (v : Template p I)

omit [Fintype G] in
/-- covers endpoint variants whenever a position only visits each port once -/
theorem queries_bloom (x : J→ Inputs p n I) (g : Route (KeySlots p v.t) G)
    (h : bloom p x) (he : ∀ e : G,Injective (fun i : Port g e => i.val.1))
    (i : G) :
    Injective (pooled (fun i => queryLaw v (x i) (g:=g)) i).mulVec := by
  classical
  let r : J × KeySlots p v.t → J×I := fun y => (y.1,y.2.1)
  have hr : Injective (fun a : Port (tied g J) i => r a.val) := by
    rintro ⟨⟨j,a⟩,ha⟩ ⟨⟨j',b⟩,hb⟩ heq
    have hA : j=j' := congrArg Prod.fst heq
    have hK : a=b := congrArg Subtype.val (he i (show (⟨a,ha⟩:Port g i).val.1=
      (⟨b,hb⟩:Port g i).val.1 from congrArg Prod.snd heq))
    exact Subtype.ext (Prod.ext hA hK)
  refine ray_bloom (b:=r) _ _ h hr ?_
  rintro a j
  let t := a.val.1
  let i := a.val.2.1
  change point p _ _ (emptySel,some (Block.Z,j))=freeNet p x j (t,i)
  rw [point_base_eval]; exact ite_eq_left (Flavor.keepZ _ _)
end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QueryConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Query Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Module Matrix Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I G A K D : Type} [Fintype I] [Fintype G] [Fintype A]
variable [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq G] [DecidableEq K]

variable {g : Route I G}

theorem forum_law (m : Mixer p n) {N : ℕ} (hN : 2*num (Full p n)<N) :
    IsLaw (forumLaw m N (G:=G)) :=
  prodW_law (fun _ => unifOn_law (framesAt_exists (gramCond_exists m)
    (by rw [←two_mul]; simpa only [num,Fintype.card_fin] using hN)))

theorem avg_bound1 {w : Wgt A} (hw : IsLaw w) (f : Wgt A) (hf : ∀ x,|f x|≤1) :
    |avg w f|≤1 := (abs_avg_le hw.nz).trans (hw.avg_le hf)
theorem avg_cross_sq (w : Wgt A) (f : Wgt A) :
    avg w f ^ 2=avg (draws Bool w) (fun q => f (q true)* f (q false)) := by
  let g (i : Bool) := f
  have hh := prodW_avg (fun _ : Bool => w) g
  have he : prodW g=(fun q => f (q true)* f (q false)) := by ext; unfold prodW; rw [Fintype.prod_bool]
  rw [he,Fintype.prod_bool] at hh; rw [pow_two]; exact hh.symm

theorem avg_var (w : Wgt A) (f : Wgt A) (hw : IsLaw w) :
    avg w (fun x => (f x-avg w f)^2) = avg w (fun x => f x^2) - (avg w f)^2 := by
  let g := avg w f
  have hh (x) : (f x-g)^2=f x^2-2*g*f x+g^2 := by ring
  change avg w (fun x => (f x-g)^2)=_
  simp_rw [hh,avg_add,avg_sub,avg_mul',hw.avg_const]
  unfold g; ring

namespace Program
variable {s : Program p n g A}

set_option maxHeartbeats 800000 in
theorem oVar (m : Mixer p n) (hN : 2*num (Full p n) < N)
    (T : A→Wgt (Rack I N))
    (w : Wgt A) (hw : IsLaw w) (hT : ∀ i x,|T i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port (tied g Bool) i)≤k)
    (hK : 2*k-N≤-1)
    (r : ℝ) (hr : pr (draws Bool w) (fun x => ¬ s.free x) ≤ r) :
    let v := forumLaw (G:=G) m N
    let f := s.oexpect w T
    avg v (fun o => (f o-avg v f)^2) ≤
      2*r + 2*netFact (tied g Bool)*twinkle (tied g Bool) k N := by
  classical
  let v := forumLaw (G:=G) m N
  let f := s.oexpect w T
  let F (x : A) := fun o => T x (s.showKey x o)
  let D := draws Bool w
  let B := 2*netFact (tied g Bool)*twinkle (tied g Bool) k N
  have hD : IsLaw D := draws_law hw
  have hv : IsLaw v := forum_law _ hN
  let V (x : Bool→A) := avg v (fun o => F (x true) o * F (x false) o)
  let W (x : Bool→A) := avg v (F (x true))*avg v (F (x false))
  have hW :
      (avg v f)^2 = avg D W := by
    unfold f oexpect
    rw [avg_avg,avg_cross_sq]
  have hV :
      avg v (fun x => f x^2) = avg D V := by
    unfold f oexpect; simp_rw [avg_cross_sq]; rw [avg_avg]
  have hi x :
      V x-W x ≤ 2*ind (¬s.free x)+B := by
    by_cases he : s.free x
    · have hh := pooled_batch (s.left ∘ x) (s.right ∘ x) m hN k hk hK he.1 he.2
        (T ∘ x) (fun i y => hT _ _)
      simp_rw [Fintype.prod_bool] at hh
      rw [ind_zero (fun h => h he),mul_zero,zero_add]
      exact (le_abs_self _).trans hh
    have h1 (a b : ℝ) (h : |a|≤1) (g : |b|≤1) : |a*b|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul h g (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have hh : |W x|≤1 := h1 _ _ (avg_bound1 hv _ (fun y => hT _ _)) (avg_bound1 hv _
      (fun y => hT _ _))
    have hg : |V x|≤1 := avg_bound1 hv _ (fun i => h1 _ _ (hT _ _) (hT _ _))
    have ht : 0 ≤ twinkle (tied g Bool) k N := add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (bp_pos _).le)) (bp_pos _).le
    have h2 : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) netFact_pos.le) ht
    rw [ind_one he,mul_one]
    exact sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hh).1,(abs_le.mp hg).2])
  change avg v _ ≤ _
  rw [avg_var v f hv,hW,hV,← avg_sub]
  apply (avg_mono hD.nz hi).trans
  rw [avg_add,avg_mul',hD.avg_const]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hr (by norm_num)) _

set_option maxHeartbeats 800000 in
theorem oTail (m : Mixer p n) (hN : 2*num (Full p n) < N)
    (T : A→Rack I N →Prop)
    (w : Wgt A) (hw : IsLaw w)
    {k : ℝ} {l : ℕ} (hk : ∀ i,num (Port (tied g (Fin l)) i)≤k)
    (hK : 2*k-N≤-1)
    (r : ℝ) (hr : pr (draws (Fin l) w) (fun x => ¬ s.free x) ≤ r)
    {ε : ℝ} (hε : 0 ≤ ε) :
    let v := forumLaw (G:=G) m N
    let f := (fun o => oFreq w T o s)
    (ε^l - r)*pr v (fun x => ε ≤ f x) ≤ netFact (tied g (Fin l))* (avg v f)^l := by
  classical
  let v := forumLaw (G:=G) m N
  let f := (fun o : Forum p n N G => oFreq w T o s)
  have hv : IsLaw v := forum_law _ hN
  let F := draws (Fin l) w
  have hF : IsLaw F := draws_law hw
  let P (x) (y : Fin l→A) := ∀ i,T (y i) (s.showKey (y i) x)
  have hh (x) : pr F (fun y => P x y)= f x ^ l := by
    unfold P F draws
    rw [prodW_pr (fun (_ : Fin l) => w) (fun _ i => T i (s.showKey i x))]
    simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
    rfl
  let Q (x : Fin l → A) := s.free x
  let S (o) (x : Fin l→A) := P o x ∧ Q x
  have hi (o) :
      (ε^l-r)*ind (ε≤f o)≤ pr F (S o) := by
    by_cases ht : ε≤f o
    · rw [ind_one ht,mul_one]
      refine (sub_le_sub (pow_le_pow_left₀ hε ht l) hr).trans ?_
      rw [←hh]; exact pr_shield hF.nz _ _
    rw [ind_zero ht,mul_zero]; exact pr_nonneg hF.nz
  let W (x) := pr v (fun i => T x (s.showKey x i))
  let C := netFact (tied g (Fin l))
  have hq (x : Fin l → A) :
      pr v (fun i => S i x) ≤ C*∏ i:Fin l,W (x i) := by
    by_cases he : Q x
    · have hg := pool_upper (s.left ∘ x) (s.right ∘ x) m hN he.1 he.2
        (fun i => by linarith only [hk i,hK]) (T ∘ x)
      simp only [S,he,and_true]
      exact hg
    simp only [S,he,and_false,pr_false]; exact mul_nonneg netFact_pos.le
      (Finset.prod_nonneg fun i _ => pr_nonneg hv.nz)
  have hg : avg v f=avg w W := avg_avg _ _ _
  have he := avg_mono hv.nz hi
  rw [avg_mul'] at he
  change _ ≤ _
  apply le_trans he
  calc avg v (fun x => pr F (S x)) = avg F (fun y => pr v (fun x => S x y)) := avg_avg _ _ _
       _ ≤ avg F (fun x => C*∏ i,W (x i)) := avg_mono hF.nz hq
       _ = netFact _ * (avg v f)^l := by rw [avg_mul',hg, poweravg]
end Program
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_DependentPairConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependent Pair Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem outlier {w : Wgt A} (hw : ∀ x, 0 ≤ w x)
    {f : Wgt A} (m : ℝ) (c : ℝ) (hc : 0 < c) {d : ℝ}
    (h : avg w (fun x => (f x-m)^2)≤d) :
    pr w (fun x => c≤|f x-m|) ≤ d/c^2 := by
  refine (le_div_iff₀ (pow_pos hc 2)).mpr ?_
  rw [mul_comm]
  let g (x : A) := (f x-m)^2
  have hg x (h : c≤ |f x-m|) : c^2 ≤ g x := by
    unfold g; exact (pow_le_pow_left₀ hc.le h 2).trans_eq (sq_abs _)
  exact ((mul_le_mul_of_nonneg_left (pr_mono hw hg) (sq_nonneg c)).trans
    (le_avg_markov hw (fun x => sq_nonneg (f x-m)) _)).trans h

omit [Fintype A] [Fintype B] in
theorem mix_data (f : X → Wgt A) (g : Y → Wgt B) (u : Wgt X) (v : Wgt Y) :
    mixW (pairW u v) (fun x => pairW (f x.1) (g x.2))=pairW (mixW u f) (mixW v g) := by
  classical
  funext i
  unfold mixW
  exact pairW_separate u (fun j => f j i.1) v (fun j => g j i.2)

set_option maxHeartbeats 800000 in
theorem paired_spread {μ : Wgt X} {ν : Wgt Y} {w : Wgt (X×Y)}
    (F : Wgt (A×B)) (f : X→ Wgt A) (g : Y→Wgt B)
    (hμ : IsLaw μ) (hν : IsLaw ν) (hw : IsLaw w)
    (hf : ∀ x, IsLaw (f x)) (hg : ∀ x,IsLaw (g x))
    (hF : ∀ x, |F x|≤1)
    (η d e τ : ℝ) (hη : 0<η) (hτ : 0<τ) (he : 0 ≤ e)
    (hA : approxData μ f η d) (hB : approxData ν g η d) (hQ : thinData ν g τ η e)
    (L H : ℝ) (hL : 0≤L) (hH : 0≤H)
    (hwA : ∀ x,mapW w Prod.fst x≤ L*μ x) (hwB : ∀ x,mapW w Prod.snd x≤ L*ν x)
    (h : ∀ x,w x≤H *pairW μ ν x) :
    let M x := avg (pairW (f x.1) (g x.2)) F
    pr w (fun x : X×Y => 5*η ≤|M x-avg (pairW μ ν) M|) ≤ L*(d+d/τ)+H*e := by
  classical
  let M (x : X × Y) := avg (pairW (f x.1) (g x.2)) F
  let pA := mixW μ f; let pB := mixW ν g
  have hpB := mixW_law hν hg
  let hfun (y : B) (x : A) := F (x,y)
  have hf1 y x : |hfun y x|≤1 := hF (x,y)
  let Lfun (y : B) := avg pA (hfun y)
  let Lx (x : X) (y : B) := avg (f x) (hfun y)
  have h1 {w : Wgt A} (hw : IsLaw w) y :
      |avg w (hfun y)| ≤1 := avg_bound1 hw _ (hf1 _)
  have hLa (x y) : |Lx x y|≤1 := h1 (hf x) y
  have hLb (y) : |Lfun y|≤1 := h1 (mixW_law hμ hf) y
  let bad (x : X) (y : B) := η ≤ |Lx x y-Lfun y|
  let Q (x : X) := τ ≤ pr pB (bad x)
  have h2 : pr μ Q≤d/τ := by
    have he' : avg μ (fun x => pr pB (bad x)) ≤ d := by
      unfold pr
      rw [avg_avg]
      exact hpB.avg_le (fun i => hA _ (hf1 i))
    apply (le_div_iff₀ hτ).mpr
    rw [mul_comm]
    exact le_trans (le_avg_markov hμ.nz (fun x => pr_nonneg
      (p:=bad x) hpB.nz) _) he'
  let R (y : Y) := η≤|avg (g y) Lfun-avg pB Lfun|
  have hR : pr ν R ≤ d := hB _ hLb
  let S := fun x : X×Y => ¬Q x.1 ∧ η ≤ pr (g x.2) (bad x.1)
  have hS : pr (pairW μ ν) S≤ e := by
    rw [pr,pairW_avg]
    refine hμ.avg_le (fun x => ?_)
    by_cases h : Q x
    · unfold S; simp only [h,not_true_eq_false,false_and,ind_false,avg_zero]
      exact he
    unfold S
    simp only [h,not_false_eq_true,true_and]
    exact hQ (bad x) (le_of_not_ge h)
  have ha (x : X × Y) (hh : ¬ (Q x.1 ∨ R x.2 ∨ S x)) :
      ¬ (5*η ≤|M x-avg (pairW μ ν) M|) := by
    have hy := not_or.mp hh
    have ht : pr (g x.2) (bad x.1) < η := lt_of_not_ge fun h =>
      (not_or.mp hy.2).2 ⟨hy.1,h⟩
    have hW y : |Lx x.1 y-Lfun y| ≤ η+2*ind (bad x.1 y) := by
      by_cases he' : bad x.1 y
      · rw [ind_one he',mul_one]
        exact (abs_sub ..).trans ((add_le_add (hLa ..) (hLb y)).trans (by linarith only [hη]))
      · rw [ind_zero he',mul_zero,add_zero]; exact le_of_not_ge he'
    have hW' :
        |avg (g x.2) (Lx x.1)-avg (g x.2) Lfun|<3*η := by
      rw [←avg_sub]
      apply lt_of_le_of_lt ((abs_avg_le (hg _).nz).trans (avg_mono (hg _).nz hW))
      rw [avg_add,(hg _).avg_const,avg_mul']
      unfold pr at ht; linarith only [ht]
    have hr : |avg (g x.2) Lfun -avg pB Lfun|<η := lt_of_not_ge ((not_or.mp hy.2).1)
    have eq1 (x : X×Y) : M x=avg (g x.2) (Lx x.1) := by
      unfold M; rw [pairW_avg,avg_avg]
    have eq2 :
        avg (pairW μ ν) M=avg pB Lfun := by
      rw [show avg (pairW μ ν) M= _ from (mixW_avg _ (fun x : X × Y => pairW (f x.1) (g x.2)) F).symm]
      rw [mix_data,pairW_avg,avg_avg]
    rw [eq1,eq2]
    apply not_le_of_gt
    exact ((abs_sub_le ..).trans_lt ((add_lt_add hW' hr).trans (by linarith)))
  have hh x :
      5*η ≤ |M x-avg (pairW μ ν) M| → Q x.1 ∨ R x.2 ∨ S x :=
    fun hz => Classical.byContradiction (fun h => ha x h hz)
  have hW : pr w (Q ∘ Prod.fst) ≤ L*(d/τ) := by
    simp only [comp_def]
    rw [show pr w _=pr (mapW w Prod.fst) Q from (mapW_pr w Prod.fst Q).symm]
    exact (pr_cap hwA _).trans (mul_le_mul_of_nonneg_left h2 hL)
  have hT : pr w (R ∘ Prod.snd) ≤ L*d := by
    simp only [comp_def]
    rw [show pr w _=pr (mapW w Prod.snd) R from (mapW_pr w Prod.snd R).symm]
    exact (pr_cap hwB _).trans (mul_le_mul_of_nonneg_left hR hL)
  have hG : pr w S ≤ H*e := (pr_cap h _).trans (mul_le_mul_of_nonneg_left hS hH)
  change pr w _ ≤ _
  apply le_trans (pr_mono hw.nz hh)
  apply le_trans (pr_or_le (p:=Q ∘ Prod.fst) (q:=fun x => R x.2 ∨ S x) hw.nz)
  apply (add_le_add hW ((pr_or_le (p:=R ∘ Prod.snd) (q:=S) hw.nz).trans (add_le_add hT hG))).trans
  linarith

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConcentrationScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
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

/-- pay slack for any fixed multiple of exponentially smaller term. -/
theorem pay_nat {a b : ℝ} (c : ℝ) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,c * bp (-a*n) ≤ bp (-b*n) := by
  have h := (bp_tendsto (sub_pos.mpr hab)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually (eventually_ge_atTop c)] with n hn
  change c ≤ bp ((a-b)*n) at hn
  refine (mul_le_mul_of_nonneg_right hn (bp_pos _).le).trans_eq ?_
  rw [← bp_add, show (a-b)*n + -a*n= -b*n by ring]

theorem pay_div_nat {a b : ℝ} (c u : ℝ) (hu : 0 < u) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,c * bp (-a*n) ≤ u*bp (-b*n) := by
  filter_upwards [pay_nat (c/u) hab] with n hn
  calc _ = u*(c/u*bp (-a*n)) := by field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_left hn hu.le

theorem cast_tops (M : ℕ) (hM : 1≤M) :
    Tendsto (fun n : ℕ => (↑(M*n):ℝ)) atTop atTop := by
  simp_rw [Nat.cast_mul]; exact
    (tendsto_const_mul_atTop_of_pos (show 0<(M:ℝ) from by
      exact_mod_cast (show 0 < M from hM))).mpr tendsto_natCast_atTop_atTop

variable {p : Shape} {M n N : ℕ}
variable {I J K G A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
variable [Fintype A] [Fintype B]
variable {g : Route J G}

omit [Fintype G] [DecidableEq J] in
theorem port_limit (g : Route J G) (i : G) :
    num (Port g i) ≤ num J := by
  exact_mod_cast Fintype.card_subtype_le _

namespace Program
variable {s : Program p n g A}

omit [Fintype G] [DecidableEq G] in
theorem data_law (s : Program p n g A) (w : Wgt A) (o : Forum p n N G)
    (hw : IsLaw w) : IsLaw (s.makeData w o) := mapW_law hw _
omit [Fintype G] [DecidableEq G] in
theorem view_data (s : Program p n g A) (w : Wgt A) (o : Forum p n N G)
    (f : Wgt (A×Rack J N)) :
    avg (s.makeData w o) f=s.oexpect w (fun a b => f (a,b)) o := mapW_avg ..
omit [Fintype G] [DecidableEq G] in
theorem freq_data (s : Program p n g A) (w : Wgt A) (o : Forum p n N G)
    (P : A×Rack J N→Prop) :
    pr (s.makeData w o) P = oFreq w (fun a b => P (a,b)) o s := mapW_pr ..

set_option maxHeartbeats 600000 in
theorem variance_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (r u : ℝ) (hu : 0 < u) (hM : 1≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (T : A→ Wgt (Rack J N)) (w : Wgt A), IsLaw w →
      (∀ x y, |T x y|≤1) →2*num (Full p n)<N →
      pr (draws Bool w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      (let v := forumLaw m N
       let f := s.oexpect w T
       avg v (fun x => (f x-avg v f)^2)) ≤ u*bp (-(1/4:ℝ)*n) := by
  let t := tied g Bool
  let k := num (Bool×J)
  let b := 2*netFact t
  let c := num G* (2*bp k)+1
  filter_upwards [pay_div_nat (a:=1) (2*bp r) (u/2) (by positivity) (b:=1/4) (by norm_num),
    pay_div_nat (a:=1/2) (b*c) (u/2) (by positivity) (b:=1/4) (by norm_num),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hh hk N m A _ s T w hw hT hN h
  change (2*k+1) ≤ (↑(M*n) : ℝ) at hk
  have he := oVar m hN T w hw hT k (fun i => port_limit _ i) (by linarith only [hk])
    (bp (r-n)) h
  apply he.trans
  subst N
  have hv : (n:ℝ) ≤ (M*n:ℕ) := by exact_mod_cast (show n ≤ M*n from by nlinarith)
  let P := bp (-(1/2:ℝ)*n)
  have ht : twinkle t k (M*n) ≤ c*P := by
    have hq : bp (k-(M*n:ℕ)) ≤ bp k*P := by
      unfold P; rw [← bp_add]; apply bp_le; linarith only [hv,Nat.cast_nonneg (α:=ℝ) n]
    have hr : bp (-(↑(M*n):ℝ)/2)≤P := bp_le (by linarith only [hv])
    calc _ ≤ num G*(2*(bp k * P))+P := add_le_add
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by norm_num))
                  (Nat.cast_nonneg _)) hr
         _ = _ := by unfold c; ring
  have h1 : 2*bp (r-n) ≤ u/2*bp (-(1/4:ℝ)*n) := by
    simpa only [mul_assoc,← bp_add,neg_mul,one_mul,←sub_eq_add_neg] using hn
  have h2 : 2*netFact t* twinkle t k (M*n)≤ u/2*bp (-(1/4:ℝ)*n) :=
    (mul_le_mul_of_nonneg_left ht (by apply mul_nonneg (by norm_num) netFact_pos.le)).trans
      (le_trans (le_of_eq (Eq.symm (mul_assoc b c P))) hh)
  exact (add_le_add h1 h2).trans_eq (by ring)

theorem approx_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (r η : ℝ) (hη : 0<η) (hM : 1 ≤ M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (w : Wgt A), IsLaw w →
      2*num (Full p n)<N →
      pr (draws Bool w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      approxData (forumLaw m N) (s.makeData w) η (bp (-(1/4:ℝ)*n)) := by
  filter_upwards [variance_calendar p M g r (η^2) (by positivity) hM]
    with n hn N m A _ s w hw hN he F hF
  subst N
  let T (x : A) (y : Rack J (M*n)) := F (x,y)
  rw [mixW_avg]; simp_rw [view_data]
  refine (outlier (forum_law m hN).nz _ η hη
    (hn m _ s T w hw (fun x y => hF _) hN he)).trans_eq ?_
  field_simp

theorem thin_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (b η c : ℝ) (hc : 0 < c) (hη : 0<η) (hM : 1≤M) :
    ∃ l : ℕ, ∀ r : ℝ, ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (w : Wgt A), IsLaw w →
      2*num (Full p n)<N →
      pr (draws (Fin l) w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      thinData (forumLaw m N) (s.makeData w) (bp (-c*n)) η (bp (-b*n)) := by
  obtain ⟨l,hl⟩ := exists_nat_gt (b/c)
  let d := η^l/2
  have hd : 0<d := by positivity
  let t := tied g (Fin l)
  let k := num (Fin l × J)
  refine ⟨l,fun r => ?_⟩
  filter_upwards [pay_div_nat (a:=1) (bp r) d hd (b:=0) (by norm_num),
    pay_div_nat (a:=c*l) (netFact t) d hd (b:=b)
      (by rwa [div_lt_iff₀ hc,mul_comm] at hl),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hh hk N m A _ s w hw hN hr P hP
  subst N; let N := M*n
  change 2*k+1 ≤ (N:ℝ) at hk
  let T (x : A) (y : Rack J N) := P (x,y)
  let v := forumLaw (G:=G) m N
  let f := fun o => oFreq w T o s
  rw [show pr (mixW v (s.makeData w)) P=avg v (fun x => pr (s.makeData w x) P) from mixW_avg ..] at hP
  simp_rw [freq_data] at *
  have hi : bp (r-n) ≤ d := by
    simpa only [neg_zero,zero_mul,bp_zero,mul_one,← bp_add,neg_mul,one_mul, ← sub_eq_add_neg]
      using hn
  have hj : η^l=d+d := by unfold d; ring
  have he := oTail m hN T w hw (k:=k) (fun i => port_limit _ i) (by linarith only [hk])
    (bp (r-n)) hr hη.le
  have hv := forum_law (G:=G) m hN
  apply le_of_mul_le_mul_left _ hd
  calc d*pr v (fun x => η ≤ f x)
    _ ≤ _ := mul_le_mul_of_nonneg_right (show d≤η^l-bp (r-n) from by
             rw [hj]; linarith only [hi]) (pr_nonneg hv.nz)
    _ ≤ _ := he
    _ ≤ netFact t * bp (-c*n)^l := mul_le_mul_of_nonneg_left
           (pow_le_pow_left₀ (avg_nonneg hv.nz fun x => pr_nonneg hw.nz) hP l) netFact_pos.le
    _ ≤ _ := by rw [← bp_mul_nat,show -c*n*l= -(c*l)*n by ring]; exact hh
end Program
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EndpointTemplateConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint Template Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]

namespace Template

variable (v : Template p I)

omit [Fintype I] [DecidableEq I] in
theorem own_inj (i : Comp p.g) :
    Injective (fun i : Port (ownPort (p:=p) v.t) i => i.val.1) := by
  rintro ⟨⟨a,c⟩,ha⟩ ⟨⟨b,d⟩,hb⟩ he
  change a=b at he; subst b
  have h : c=d := Subtype.ext (ha.trans hb.symm)
  subst d; rfl

omit [Fintype G] in
theorem free_price (n : ℕ) (w : I→ Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (hz : ∀ i,mapW (w i) (freePart p)=unif)
    (g : Route (KeySlots p v.t) G)
    (he : ∀ i : G,Injective (fun j : Port g i => j.val.1)) :
    pr (draws K (prodW w)) (fun x => ¬ (v.callP n g).free x)≤ bp (num K * num I-n) := by
  refine le_trans ?_ (buds p n _ hz)
  exact pr_mono (draws_law (prodW_law hw)).nz fun i h hh => h
    ⟨queries_bloom v i g hh he, queries_bloom v i g hh he⟩

omit [Fintype I] [DecidableEq I] in
theorem single_show (z : Inputs p n I) (x : Orient p n N) :
    (v.singleP n).showKey z x=scatter v.t N (fun i => callOne v i (z i) x) := by
  apply Prod.ext <;> rfl

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedTemplateConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Template Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]

theorem paired_price (M : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      let d := bp (-(1/4:ℝ)*n)
      let τ := bp (-(1/8:ℝ)*n)
      let e := bp (-(C*M+1)*n)
      bp ((1/32:ℝ)*n)*(d+d/τ)+bp (C*(M*n:ℕ))*e≤ bp (-(1/16:ℝ)*n) := by
  filter_upwards [pay_div_nat (a:=1-1/2+1/2) 1 (1/3) (by norm_num) (b:=1/16) (by norm_num),
    pay_div_nat (a:=1/4-1/32) 1 (1/3) (by norm_num) (b:=1/16) (by norm_num),
    pay_div_nat (a:=1/8-1/32) 1 (1/3) (by norm_num) (b:=1/16) (by norm_num)]
    with n ha hb hc
  intro d τ e
  unfold d τ e
  rw [← bp_sub,mul_add,← bp_add,← bp_add,← bp_add,Nat.cast_mul]
  have h : C * ((M:ℝ)*n) + -(C*M+1)*n= - (1-1/2+1/2)*n := by ring
  rw [h]
  have hg : (1/32:ℝ)*n+(-(1/4:ℝ)*n- -(1/8:ℝ)*n) = -(1/8-1/32:ℝ)*n := by ring
  have hf : (1/32:ℝ)*n+ -(1/4:ℝ)*n = -(1/4-1/32:ℝ)*n := by ring
  rw [hf,hg]
  linarith only [ha,hb,hc]

namespace Template

variable (v : Template p I) (z : Template p J)

set_option maxHeartbeats 800000 in
theorem twinned (v : Template p I) (z : Template p J) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (w : Wgt (UnitType p n N)), IsLaw w →
      let μ := raw m N; let ρ := pairW μ μ
      let H := bp ((1/32:ℝ)*n)
      (∀ x,mapW w Prod.fst x ≤ H*μ x) → (∀ x,mapW w Prod.snd x ≤ H*μ x) →
      (∀ x,w x ≤ bp (C*N) *ρ x) → 2*num (Full p n)<N →
      ∀ (u : I→ Wgt (Knobs p.g n)) (s : J→ Wgt (Knobs p.g n)),
        (∀ i, IsLaw (u i)) → (∀ i,mapW (u i) (freePart p)=unif) →
        (∀ i, IsLaw (s i)) → (∀ i,mapW (s i) (freePart p)=unif) →
        ∀ T : Wgt (v.Datum n N × z.Datum n N), (∀ x,|T x|≤1) →
        let f := fun x : UnitType p n N =>
          avg (pairW ((v.singleP n).makeData (prodW u) x.1)
            ((z.singleP n).makeData (prodW s) x.2)) T
        pr w (fun x => ε≤ |f x-avg ρ f|) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let g := ownPort (p:=p) v.t; let b := ownPort (p:=p) z.t
  let η := ε/5; have hη : 0<η := by positivity
  let a := C*M+1
  obtain ⟨l,hl⟩ := Program.thin_calendar p M b a η (1/8) (by norm_num) hη hM
  filter_upwards [Program.approx_calendar p M g (num Bool*num I) η hη hM,
    Program.approx_calendar p M b (num Bool*num J) η hη hM,
    hl (num (Fin l)*num J),paired_price M C]
    with n hn ha hq hp N m w hw μ ρ H hA hB hw' hN u s hu hu' hs hs' T hT f
  let f' := (v.singleP n).makeData (prodW u) (N:=N)
  let g' := (z.singleP n).makeData (prodW s) (N:=N)
  let d := bp (-(1/4:ℝ)*n); let τ := bp (-(1/8:ℝ)*n); let e := bp (-a*n)
  have hx : approxData μ f' η d := hn m _ _ _ (prodW_law hu) hN
    (free_price v n u hu hu' g (own_inj v))
  have hy : approxData μ g' η d := ha m _ _ _ (prodW_law hs) hN
    (free_price z n s hs hs' b (own_inj z))
  have hz : thinData μ g' τ η e := hq m _ _ _ (prodW_law hs) hN
    (free_price z n s hs hs' b (own_inj z))
  have hm : IsLaw μ := forum_law m hN
  have he := paired_spread T f' g' hm hm hw
    (fun x => Program.data_law _ _ _ (prodW_law hu))
    (fun x => Program.data_law _ _ _ (prodW_law hs))
    hT η d e τ hη (bp_pos _) (bp_pos _).le hx hy hz
    _ _ (bp_pos _).le (bp_pos _).le hA hB hw'
  rw [show 5*η=ε by unfold η; ring] at he
  exact he.trans hp

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TemplateTypicality
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template Typicality -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J G : Type} [Fintype I] [DecidableEq I]

theorem fork_law {a : I → Type} [∀ i,Fintype (a i)]
    (p : I→Prop) [DecidablePred p] (w : ∀ i,Wgt (a i)) :
    let E := Equiv.piEquivPiSubtypeProd p a
    mapW (prodW w) E=pairW (prodW (fun i:{i // p i} => w i.val))
      (prodW (fun i:{i // ¬p i} => w i.val)) := by
  intro E
  funext x
  obtain ⟨y,rfl⟩ := E.surjective x
  rw [mapW_equiv_val,Equiv.symm_apply_apply]
  exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (y i))).symm

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 800000 in
theorem connect_avg (u : I→Wgt (Knobs p.g n))
    (T : Inputs p n I → Keys (p:=p) v.t N → ℝ)
    (x : UnitType p n N) :
    let a := fun i : v.PosA => u i.val
    let b := fun i : v.PosB => u i.val
    v.sampleAll u T x = avg
      (pairW ((v.atA.singleP n).makeData (prodW a) x.1)
        ((v.atB.singleP n).makeData (prodW b) x.2)) (v.connectT T) := by
  classical
  intro a b
  let s (i : Inputs p n v.PosA) : v.atA.Datum n N :=
    (i,(v.atA.singleP n).showKey i x.1)
  let t (i : Inputs p n v.PosB) : v.atB.Datum n N :=
    (i,(v.atB.singleP n).showKey i x.2)
  have hi (i : Inputs p n I) :
      T i ((v.draw i).keys v.t x) =
      v.connectT T (s ((v.forkI n i).1), t ((v.forkI n i).2)) := by
    let y := (v.draw i).keys v.t x
    let Y := v.forkK N y
    have hA :
        (scatter v.atA.t N).symm ((v.atA.singleP n).showKey ((v.forkI n i).1) x.1)=Y.1 := by
      rw [single_show,Equiv.symm_apply_apply]; funext j

      change keyOne p (v.t j.val) _ _ x.1=keyOne p _ _ _ (onSide x (v.aim j.val))
      rw [j.property]; rfl
    have hB :
        (scatter v.atB.t N).symm ((v.atB.singleP n).showKey ((v.forkI n i).2) x.2)=Y.2 := by
      rw [single_show,Equiv.symm_apply_apply]; funext j
      change keyOne p (v.t j.val) _ _ x.2=keyOne p _ _ _ (onSide x (v.aim j.val))
      rw [Bool.eq_false_iff.mpr j.property]; rfl
    unfold connectT s t
    rw [hA,hB]
    simp [Y,Equiv.symm_apply_apply,y]
  let Q (j : Inputs p n v.PosA × Inputs p n v.PosB) := v.connectT T (s j.1, t j.2)
  calc _ = avg (mapW (prodW u) (v.forkI n)) Q := by
             rw [mapW_avg,sampleAll]; simp_rw [hi]; rfl
       _ = avg (pairW (prodW a) (prodW b)) Q := congrArg (fun w => avg w Q)
          (fork_law (fun i => v.aim i) u)
       _ = _ := by
         rw [pairW_avg,pairW_avg,Program.makeData,Program.makeData,mapW_avg]
         simp_rw [mapW_avg]; rfl

theorem typical_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (w : Wgt (UnitType p n N)), IsLaw w →
      let μ := raw m N; let ρ := pairW μ μ
      let H := bp ((1/32:ℝ)*n)
      (∀ x,mapW w Prod.fst x ≤ H*μ x) → (∀ x,mapW w Prod.snd x ≤ H*μ x) →
      (∀ x,w x ≤ bp (C*N) *ρ x) → 2*num (Full p n)<N →
      ∀ (u : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (u i)) →
        (∀ i,mapW (u i) (freePart p)=unif) →
        ∀ T : Inputs p n I → Keys (p:=p) v.t N → ℝ, (∀ x y,|T x y|≤1) →
        let f := v.sampleAll u T
        pr w (fun x => ε≤ |f x-avg ρ f|) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  filter_upwards [twinned v.atA v.atB M hM C ε hε]
    with n hn N m w hw μ ρ H hA hB hw' hN u hu hz T hT f
  let a := u ∘ (Subtype.val : v.PosA→I)
  let b := u ∘ (Subtype.val : v.PosB→I)
  have h := hn m w hw hA hB hw' hN a b
    (fun i => hu _) (fun i => hz _) (fun i => hu _) (fun i => hz _)
    (connectT v T) (fun x => hT _ _)
  have he : f = fun x : UnitType p n N => avg
      (pairW ((v.atA.singleP n).makeData (prodW a) x.1)
        ((v.atB.singleP n).makeData (prodW b) x.2)) (v.connectT T) :=
    funext fun x => connect_avg v u T x
  rw [he]; exact h

end Template
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourCornerViews
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Corner Views -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Matrix Function
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype A] [Fintype B] [Fintype C] in
theorem criss_pair (p : A × A) (a b : Bool) (E : A≃ B × C) :
    E (criss E p (a,b))=((E (onSide p a)).1,(E (onSide p b)).2) := by
  cases a <;> cases b <;> simp [criss,onSide]

variable {E : A≃ B × C}

theorem quart_shift (E : A ≃ B×C) (U : Wgt A) (p : Wgt A) :
    avg (pairW p p) (quart E U) =
      avg (pairW (mapW p E) (mapW p E)) (spread (U∘E.symm)) := by
  classical
  rw [←map_pair_law,mapW_avg]
  refine avg_congr fun x hx => ?_
  unfold quart spread
  rw [Fintype.prod_prod_type,Fintype.prod_bool,Fintype.prod_bool,Fintype.prod_bool]
  rfl

set_option maxHeartbeats 800000 in
theorem spread_gain (u : Wgt B) (v : Wgt C) (f : Wgt (B×C)) (hu : IsLaw u) (hv : IsLaw v)
    (p : Wgt B) (q : Wgt C) (hp : ∀ i,|p i|≤1) (hq : ∀ i,|q i|≤1):
    |avg (pairW u v) (fun i=> f i*(p i.1*q i.2))|^4 ≤
      avg (pairW (pairW u v) (pairW u v)) (spread f) := by
  classical
  let U := fun i => avg v (fun j => f (i,j)*q j)
  let T : Wgt (B×C) := fun i=> f i*(p i.1*q i.2)
  have h :
      avg (pairW u v) T =dip u p U := by
    unfold T U dip; rw [pairW_avg]; simp_rw [mul_left_comm _ (p _),avg_mul']
  have h0 (x y : ℝ) (hx:|x|≤1) (hy:|y|≤1) : |x*y|≤1 := by rw [abs_mul]; exact
    (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (by ring)
  have hh {A : Type} [Fintype A] {w : Wgt A} (hw : IsLaw w) (p q : Wgt A)
      (hp : ∀ i,|p i|≤1) :
      dip w p q ^2 ≤ ode w q := by
    have he : ode w p≤1 := (ode_upper hw.sub _ 1 hp).trans_eq (by ring)
    apply le_trans _ ((mul_le_mul_of_nonneg_right he (ode_nonneg hw.nz q)).trans_eq (one_mul _))
    simpa only [dip,ode,pow_two] using avg_CS hw.nz p q
  let V := pairW v v
  have hV := pairW_law hv hv
  let Y (j : C×C) (i:B) := f (i,j.1)*f (i,j.2)
  let W (j) := avg u (Y j)
  let Q (j : C×C) := q j.1*q j.2
  have he : ode u U=dip V Q W := by
    have hi i : U i*U i=avg V (fun j => Q j*Y j i) := by
      unfold U
      rw [avg_prod]; apply avg_congr; intro j _
      unfold Q Y; ring
    unfold ode dip; simp_rw [hi]; rw [avg_avg]; simp_rw [avg_mul']; rfl
  let D (j : C×C) (i : B× B) := Y j i.1*Y j i.2
  have hw : ode V W= avg (pairW (pairW u v) (pairW u v)) (spread f) := by
    have hi j : W j*W j=avg (pairW u u) (fun i => D j i) := avg_prod u _ _
    unfold ode dip; simp_rw [hi]; unfold V; simp_rw [pairW_avg]
    conv_rhs => rw [avg_avg]
    apply avg_congr; intro i _
    conv_rhs =>

      skip
    unfold D Y spread

    conv_lhs => rw [avg_avg]
    refine avg_congr fun i _ => ?_
    rw [avg_avg]
  change |avg (pairW u v) T|^4≤ _
  rw [h,←hw,show |dip u p U|^4=(dip u p U^2)^2 by rw [show |dip u p U|^4=(|dip u p U|^2)^2 by ring,
    sq_abs]]
  apply (pow_le_pow_left₀ (sq_nonneg _) (hh hu p U hp) 2).trans
  rw [he]
  exact hh hV Q W (fun i=>h0 _ _ (hq _) (hq _))

theorem quart_CS (E : A≃ B×C) (U : Wgt A) (u : Wgt A) (p : Wgt B) (q : Wgt C)
    (he : mapW u E=pairW p q) (hp : IsLaw p) (hq : IsLaw q)
    (f : Wgt B) (g : Wgt C) (hf : ∀ i,|f i|≤1) (hg : ∀ i,|g i|≤1) :
    |avg u (fun i=>U i*(f (E i).1*g (E i).2))|^4 ≤ avg (pairW u u) (quart E U) := by
  have hh := spread_gain p q (U∘E.symm) hp hq f g hf hg
  rw [quart_shift]
  rw [← he,mapW_avg] at hh
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hh
  exact hh
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SinglePositionExpansion
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Single Position Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Matrix
open scoped BigOperators
variable {I A B C : Type} [Fintype I] [DecidableEq I]
variable {p : Shape} {n N : ℕ}
variable {X : I → Type}

theorem chair_split (p : ∀ i,Wgt (X i)) (x : ∀ i,X i) (a : I) :
    prodW p x = p a (x a) *
      prodW (fun i : Aside a=>p i.val) ((chair X a x).2) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne _ _

variable [∀ i,Fintype (X i)]
set_option maxHeartbeats 600000 in
theorem chair_weight (p : ∀ i,Wgt (X i)) (a : I) :
    mapW (prodW p) (chair X a)= pairW (p a)
      (prodW (fun i : Aside a=>p i.val)) := by
  funext i
  obtain ⟨i,rfl⟩ := (chair X a).surjective i
  rw [mapW_equiv_val,Equiv.symm_apply_apply]; exact chair_split p i a

omit [Fintype I] [∀ i,Fintype (X i)] in
theorem chair_arm (p : (∀ i,X i)×(∀ i,X i)) (i j : I) (x : Corn) :
    criss (chair X i) p x j=(onSide p (arm i j x)) j := by
  rcases x with ⟨a,b⟩
  have he := criss_pair p a b (chair X i)
  by_cases h : j=i
  · subst j
    rw [arm,ite_eq_left rfl]; exact congrArg Prod.fst he
  rw [arm,ite_eq_right h]
  exact congr_fun (congrArg Prod.snd he) (⟨j,h⟩:Aside i)

namespace Template
variable (v : Template p I)

omit [Fintype I] in
theorem key_quoin (v : Template p I) (x : I) (o : UnitType p n N)
    (p' : Inputs p n I× Inputs p n I) (c : Corn) :
    criss (v.chairK x N) (Prod.map (v.resultKey o) (v.resultKey o) p') c=
      v.resultKey o (criss (v.chairI x n) p' c) := by
  classical
  funext i; unfold resultKey
  change criss (chair (fun i=>AtomKey (p:=p) (v.t i) N) x) _ _ i=keyOne p _ _ (lit _ _ (criss (chair (fun _=>Knobs p.g n) x) _ _ i)) _
  rw [chair_arm _ x,chair_arm _ x]
  cases arm x i c <;> rfl

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourCornerTrials
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Corner Trials -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

theorem quart_bound {A B C : Type} (U : Wgt A) (hU : ∀ i, |U i|≤1) (e : A≃B×C) (i) :
    |quart e U i|≤ 1 := by
  unfold quart; rw [Finset.abs_prod]
  exact (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _=>hU _)).trans_eq (by simp)

namespace Template
variable (v : Template p I)

omit [Fintype I] in
theorem quart_prot (v : Template p I) (j : I) (T : Wgt (Inputs p n I))
    (U : Wgt (Keys (p:=p) v.t N)) (o : UnitType p n N)
    (c : Inputs p n I × Inputs p n I) :
    quart (v.chairI j n) (v.protean T U o) c=
      quart (v.chairI j n) T c *quart (v.chairK j N) U
        (Prod.map (v.resultKey o) (v.resultKey o) c) := by
  unfold quart protean
  rw [Finset.prod_mul_distrib]
  simp_rw [key_quoin]

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CutIntegralBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut Integral Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Matrix Function Filter
open scoped BigOperators Topology
variable {p : Shape} {n N M : ℕ} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]

theorem chairpan_law (p : I→Wgt A) :
    mapW (prodW (chairpan p)) (reparse I A)=pairW (prodW p) (prodW p) := by
  classical
  funext i
  obtain ⟨i,rfl⟩ := (reparse I A).surjective i
  rw [mapW_equiv_val,Equiv.symm_apply_apply]; unfold pairW prodW
  rw [Fintype.prod_prod_type,Fintype.prod_bool]; rfl
namespace Template
variable (v : Template p I)

theorem clue_crane (v : Template p I) (j : I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys
    (p:=p) v.t N)) (w : I→ Wgt (Knobs p.g n)) :
    crane v j T U w=v.panels.sampleAll (chairpan w) (clue v j T U) := by
  classical
  funext i
  unfold crane; dsimp only
  rw [←chairpan_law w,mapW_avg]; unfold sampleAll
  refine avg_congr fun k hk => ?_
  rw [quart_prot]; rfl

theorem shaft (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N))
    (T : Wgt (Inputs p n I)) (w f : I→ Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (hf : ∀ i j,|f i j|≤1) (o : UnitType p n N) :
    |scene v T U w f o|^4 ≤ crane v j T U w o := by
  classical
  let D (i : Aside j) := f i.val
  have h0 i : |prodW D i|≤1 := by
    unfold prodW; rw [abs_prod]; exact (Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>hf _ _)).trans_eq
                                       (by simp)
  have he (i : Inputs p n I) :
      prodW f i=f j (i j)*prodW D ((chairI v j n i).2) := chair_split f i j
  unfold scene; simp_rw [he]
  exact quart_CS (chairI v j n) _ _ _ _ (chair_weight w j) (hw j)
    (prodW_law fun i:Aside j=> hw i.val) (f j) (prodW D) (hf j) h0

set_option maxHeartbeats 1200000 in
theorem shade_calendar_oai (v : Template p I) (j : I) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n
      ∀ (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (T : Wgt (Inputs p n I))
        (w : I→Wgt (Knobs p.g n)), (∀ x, |U x|≤1) → chairCut v j U δ →
        carried U (ownPart (p:=p) v.t q) →
        (∀ x, |T x|≤1) → (∀ i,IsLaw (w i)) →
        (∀ i,mapW (w i) (freePart p)=unif) →
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      let μ:=raw m N; let H:=bp ((1/32:ℝ)*n)
      ∀ (ρ : Wgt (UnitType p n N)), IsLaw ρ →
      (∀ x,mapW ρ Prod.fst x≤ H*μ x) → (∀ x,mapW ρ Prod.snd x≤ H*μ x) →
      (∀ x,ρ x ≤ bp (C*N)*pairW μ μ x) →
      pr ρ (blackout v T U w ε) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let E := ε^4/2; have hE : 0<E := by positivity
  let k := num v.PackSlot
  let W := netFact v.seam; have hW : 0<W := netFact_pos
  let d:=E/2/W
  have hd : 0<d := by positivity
  let f (N : ℕ) := 2*W * (num (Ports p)*(2*bp (k-N)))+W*(d+bp (-(N:ℝ)/2))
  let z (n : ℕ) := bp (num Bool*num I-n)
  have hh₁ : Tendsto (fun n:ℕ=>f (M*n)+z n) atTop (𝓝 (W*d)) := by
    have hh (c : ℝ) (C : ℝ) (hC : 0<C) {v : ℕ→ℝ} (hv : Tendsto v atTop atTop) :
        Tendsto (fun i => bp (c-C*v i)) atTop (𝓝 0) := by
      simp_rw [sub_eq_add_neg,bp_add, ← neg_mul]
      simpa using ((bp_tendsto_zero hC).comp hv).const_mul (bp c)
    let N (i : ℕ) := (↑(M*i):ℝ)
    have he := cast_tops M hM
    have hz := hh (num Bool*num I) 1 zero_lt_one (v:=fun n:ℕ=>(n:ℝ)) tendsto_natCast_atTop_atTop
    have h1 := hh k 1 zero_lt_one he
    have h2 : Tendsto (fun i => bp (-N i/2)) atTop (𝓝 0) := by
      have hq := hh 0 (1/2) (by norm_num) he
      refine (tendsto_congr' ?_).mp hq
      exact .of_forall (fun n => by unfold N; simp only [zero_sub]; congr 1; ring)
    have h3 := (((h1.const_mul 2).const_mul (num (Ports p))).const_mul (2*W)).add
      ((h2.const_add d).const_mul W)
    simpa only [mul_zero,zero_add,add_zero,f,z,N,one_mul] using h3.add hz
  have hh₂ : W*d<E := by unfold d; field_simp; linarith only [hE]
  refine ⟨d,hd,?_⟩
  filter_upwards [typical_calendar v.panels M hM C E hE,
    hh₁.eventually (gt_mem_nhds hh₂),(cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hq he N q U T w hU hx hP hT hw hz m hN μ H ρ hρ h1 h2 h3
  have hk : 2*k-N ≤ -1 := by
    change 2*k+1 ≤ (N:ℝ) at he
    linarith only [he]
  have hm := crane_mean v j q U T w hw hz m hN d hd.le hU hT hx hP k
    (port_limit v.seam) hk
  have hi (x y) : |clue v j T U x y|≤1 := by
    unfold clue; rw [abs_mul]
    exact (mul_le_mul (quart_bound T hT _ _) (quart_bound U hU _ _)
      (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  let g := crane v j T U w
  have h4 := hn m ρ hρ h1 h2 h3 hN (chairpan w) (fun i=>hw i.2)
    (fun i=>hz i.2) _ hi
  change pr ρ _ ≤ _ at h4
  have hh (x) : (panels v).sampleAll (chairpan w) (clue v j T U) x=g x :=
    Eq.symm (congr_fun (clue_crane ..) x)

  have hh' : (panels v).sampleAll (chairpan w) (clue v j T U)=g := funext hh
  change pr ρ (fun x => E≤ |(panels v).sampleAll (chairpan w) (clue v j T U) x-
    avg (pairW μ μ) ((panels v).sampleAll (chairpan w) (clue v j T U))|)≤_ at h4
  rw [hh'] at h4
  apply (pr_mono hρ.nz ?_).trans h4
  rintro i ⟨b,hb,hv⟩
  have ht := shaft v j U T w b hw hb i
  have hG : avg (pairW μ μ) g ≤ E := (le_abs_self _).trans (hm.trans hq.le)
  have hy : ε^4 ≤ g i := (pow_le_pow_left₀ hε.le hv.le 4).trans ht
  exact le_trans (show E ≤ g i-avg (pairW μ μ) g from by unfold E at *; linarith only [hG,hy])
    (le_abs_self _)
end Template
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.Template.shade_calendar_oai := @OAI.HadwigerCounterexample.Template.shade_calendar_oai
