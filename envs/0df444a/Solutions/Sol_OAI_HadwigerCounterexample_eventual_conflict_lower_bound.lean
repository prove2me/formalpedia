-- Prove2me | solution 1 for OAI.HadwigerCounterexample.eventual_conflict_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:08:11.966199+00:00
-- url     : https://prove2.me/submissions/25c385b7-60c3-48b8-8dd5-028adc58967b

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
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
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
import Mathlib.Tactic.SplitIfs
import Definitions.Def_OAIQ430Hc000
import Theorems.Thm_OAI_HadwigerCounterexample_PreparationParameters_outlook_to_dose
import Theorems.Thm_OAI_HadwigerCounterexample_PreparationParameters_phaseAbsent
import Theorems.Thm_OAI_HadwigerCounterexample_PreparationParameters_phaseSplit
import Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_refuteVeil

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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

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
theorem bit_sq (x : F) : x*x = x := by rcases bit_cases x with e|e <;> rw [e] <;> simp

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AffineFrames
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine Frames -/

noncomputable section
namespace HadwigerCounterexample

open Matrix
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

theorem T_diag (m : Mixer p n) (x : Profile p n) : Tsym m x x = role p n x := by
  have h (a b : F) : a*b+b*a=0 := by rw [mul_comm b a,char_two]
  simp only [Tsym_val,T0_val,char_two,h,Finset.sum_const_zero,add_zero,bit_sq]

theorem ufun_self {m : Mixer p n} {o : Orient p n N} (h : frameLaw m o) (x : Profile p n) :
    ufun o (Uembed o x) = 0 := by
  simp only [ufun,Uembed,LinearMap.coe_mk,AddHom.coe_mk]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mpair_liftM,liftM_def,← Matrix.mul_assoc,(h i).2.2.2.2,Matrix.zero_mul,
    Matrix.zero_mul,mpair_comm,map_zero]

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

theorem mrk_add_le (A B : Mat I J) : (A+B).rank ≤ A.rank + B.rank := by
  rw [rank_cast,rank_cast,rank_cast,mulVecLin_add]; exact rk_add_le _ _

omit [Fintype I] in
theorem colSp_dim (P : Mat I J) : dim (colSp P) = P.rank := rfl

omit [Fintype I] in
theorem colSp_mem {P : Mat I J} (j : J) : P.col j ∈ colSp P := by
  rw [colSp,range_mulVecLin]
  exact Submodule.subset_span ⟨j,rfl⟩

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

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

theorem tot_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ tot w := Finset.sum_nonneg fun x _ => hw x

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

theorem unif_law [Nonempty α] : IsLaw (unif : Wgt α) := by
  refine normW_law (fun _ => zero_le_one) ?_
  simp [tot, Fintype.card_pos]

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

theorem unifOn_sub (p : A → Prop) : SubLaw (unifOn p) :=
  normW_subLaw fun x => ind_nonneg (p x)

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

theorem avg_bij (e : A ≃ A) (w f : Wgt A) :
    avg (fun x => w (e x)) (fun x => f (e x)) = avg w f := by
  unfold avg
  exact Equiv.sum_comp e (fun x => w x * f x)

variable [Fintype B]

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

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}

namespace ExpSmall

theorem mul (hf : ExpSmall l n f) (hg : ExpO l n g) :
    ExpSmall l n (fun i => f i*g i) := by
  obtain ⟨c,hc,h⟩ := hf
  refine ⟨c/2,by linarith,?_⟩
  filter_upwards [h,hg (c/2) (by linarith)] with i hi hj
  rw [abs_mul, show -(c/2)*n i = -c*n i + c/2*n i by ring, bp_add]
  exact mul_le_mul hi hj (abs_nonneg _) (bp_pos _).le

theorem add (hn : Tendsto n l atTop) (hf : ExpSmall l n f) (hg : ExpSmall l n g) :
    ExpSmall l n (fun i => f i+g i) := by
  obtain ⟨c,hc,h⟩ := hf; obtain ⟨d,hd,h'⟩ := hg
  let a := min c d
  have ha : 0 < a := lt_min hc hd
  refine ⟨a/2,by linarith, ?_⟩
  filter_upwards [h,h',hn.eventually (eventually_ge_atTop 0),
    ((bp_tendsto (show 0 < a/2 by linarith)).comp hn).eventually
      (eventually_ge_atTop 2)] with i hi hj hx hb
  change 2 ≤ bp (a/2*n i) at hb
  have h₁ : -c*n i ≤ -a*n i := by gcongr; exact min_le_left _ _
  have h₂ : -d*n i ≤ -a*n i := by gcongr; exact min_le_right _ _
  refine le_trans (abs_add_le _ _) ?_
  rw [show -(a/2)*n i = a/2*n i + -a*n i by ring,bp_add]
  calc |f i| + |g i| ≤ bp (-a*n i)+bp (-a*n i) :=
         add_le_add (hi.trans (bp_le h₁)) (hj.trans (bp_le h₂))
       _ = 2*bp (-a*n i) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hb (bp_pos _).le

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteAffineLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

end General

theorem dim_mat (I J : Type) [Fintype I] [Fintype J] :
    dim (Mat I J) = Fintype.card I * Fintype.card J := by
  simp only [dim,Mat,finrank_matrix,finrank_self,mul_one]

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TensorIntersections
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
theorem colSp_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    colSp (liftM P Q A) ≤ colSp P := by
  rw [liftM_def,Matrix.mul_assoc,colSp, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

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

theorem box_dim (S : Space (Vec I)) (T : Space (Vec J)) :
    dim (box S T) = dim S*dim T := by
  have h := rk_inj.mp (liftM_inj (pack_inj S) (pack_inj T))
  change dim (box S T)=dim (Mat _ _) at h
  rw [dim_mat, Fintype.card_fin,Fintype.card_fin] at h
  exact h

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

theorem effective_mem {s : Plan p n} {i} {x : Profile p n} : x∈effective s i ↔
    x∈Xspace p n ∧ ∀ e, x e∈box (sPin s (e,true) i) (sPin s (e,false) i) :=
  and_congr Iff.rfl (by simp)

theorem sPin_dim (s : Plan p n) (z : Place p) (i) : dim (sPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _

theorem sPin_sum (s : Plan p n) (b i : Bool) :
    ∑ e : Comp p.g, dim (sPin s (e,b) i) ≤ planRank s := by
  unfold planRank
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum (fun e _ => (sPin_dim _ _ _).trans ?_)
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((fun b => dim (s (e,b))) j))
    (Finset.mem_univ b)

theorem dim_le_plan (s : Plan p n) (e : Place p) :
    dim (s e) ≤ planRank s := Finset.single_le_sum (fun j _ => Nat.zero_le (dim (s j)))
      (Finset.mem_univ _)

private theorem pi_dim_le {V J : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (s : J→ Submodule F V) :
    dim (Submodule.pi Set.univ s) ≤ ∑ i, dim (s i) := by
  let T := Submodule.pi Set.univ s
  have h (i : J) (x : T) : x.val i∈ s i := x.property i (Set.mem_univ i)
  let f : T →ₗ[F] (∀ i,s i) := {
    toFun := fun x i => ⟨_,h i x⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro x y; rfl }
  have hf : Function.Injective f := fun x y e => Subtype.ext (funext (fun i =>
    show x.val i=y.val i from congrArg (fun t:s i => t.val) (congr_fun e i)))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq
    (Module.finrank_pi_fintype _)

theorem effective_dim (s : Plan p n) (i : Bool) :
    dim (effective s i) ≤ (planRank s)^2 := by
  unfold effective
  let p' (e : Comp p.g) := (sPin s (e,true) i)
  let q (e : Comp p.g) := (sPin s (e,false) i)
  refine ((Submodule.finrank_mono (show _ ⊓ _ ≤ Submodule.pi Set.univ (fun e => box (p' e)
    (q e)) from inf_le_right)).trans (pi_dim_le _)).trans ?_
  simp_rw [box_dim]
  calc ∑ i, dim (p' i) * dim (q i) ≤ ∑ i, dim (p' i)* planRank s := Finset.sum_le_sum (fun j _ =>
         Nat.mul_le_mul_left _ ((sPin_dim s _ i).trans (dim_le_plan s _)))
       _ ≤ _ := by rw [← Finset.sum_mul,pow_two]; exact Nat.mul_le_mul_right _ (sPin_sum s true i)

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelDecomposition
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

theorem covered_iff (S : Cov p N) (x) : covered p S x ↔
    ∀ e,vanish (S (e,true)) (S (e,false)) (x e) := by
  constructor
  · intro h e
    apply (vanish_chop _).mpr
    exact congr_fun h e
  intro h
  exact funext fun e => (vanish_chop _).mp (h e)

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

private theorem cov_pi_bound {V J : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (s : J→ Submodule F V) :
    dim (Submodule.pi Set.univ s) ≤ ∑ i, dim (s i) := by
  let T := Submodule.pi Set.univ s
  have h (i : J) (x : T) : x.val i∈ s i := x.property i (Set.mem_univ i)
  let f : T →ₗ[F] (∀ i,s i) := {
    toFun := fun x i => ⟨_,h i x⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro x y; rfl }
  have hf : Function.Injective f := fun x y e => Subtype.ext (funext (fun i =>
    show x.val i=y.val i from congrArg (fun t:s i => t.val) (congr_fun e i)))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq
    (Module.finrank_pi_fintype _)

theorem cover_dim (p : Shape) {N} (S : Cov p N) :
    dim (coverX p S)≤ N*cdim p S := by
  let A (i : Comp p.g) : Space (Mat (Fin N) (Fin N)) :=
    box (S (i,true)) ⊤ ⊔ box ⊤ (S (i,false))
  have he : coverX p S≤ Submodule.pi Set.univ A := by
    intro x hx i _
    exact (cover_mem ..).mp hx i
  refine ((Submodule.finrank_mono he).trans (cov_pi_bound ..)).trans ?_
  unfold cdim
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  have ht : dim (⊤ : Space (Vec (Fin N)))=N := (finrank_top ..).trans
    ((dim_vec _).trans (Fintype.card_fin _))
  refine Finset.sum_le_sum fun i _ => ?_
  apply (Submodule.finrank_add_le_finrank_add_finrank ..).trans
  change dim (box (S (i,true)) _)+dim (box _ (S (i,false)))≤_
  rw [box_dim,box_dim,ht,Fintype.sum_bool,Nat.mul_add,Nat.mul_comm N _]
  rw [Nat.mul_comm N _]

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

theorem wsign_add (x y : F) : wsign (x+y) = wsign x * wsign y := by
  rcases bit_cases x with h|h <;> rcases bit_cases y with g|g <;>
    simp [h,g,char_two]

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

variable {A B V W : Type} [Fintype A] [Fintype B]

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentPhaseBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
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

theorem phase_actual (p : Shape) {n N} (x : Orient p n N) :
    uPhase p (hcube p x)=ufun x := by
  apply LinearMap.ext
  intro v
  simp only [uPhase,LinearMap.sum_apply]; rfl

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

theorem onW_ne {w : Wgt A} {P : A→Prop} {x : A} (h : onW w P x≠0) : P x ∧ w x≠0 := by
  have hh : subW w P x≠0 := fun hx => h (by unfold onW normW; rw [hx,zero_div])
  exact ⟨Classical.byContradiction (fun hx => hh (subW_carried _ _ _ hx)),
    left_ne_zero_of_mul hh⟩

theorem on_law {w : Wgt A} (hw : ∀ x,0 ≤ w x) {P : A→Prop} (hp : 0<pr w P) :
    IsLaw (onW w P) := normW_law (subW_nonneg hw _) hp
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

theorem pitch_turn (Δ : UnitType p n N → Ambient p N) (w S R) :
    pitch p Δ w S R=pitch p Δ w R S := by
  unfold pitch
  rw [pairW_avg,pairW_avg,avg_avg]
  refine avg_congr (fun x hx => avg_congr (fun y hy => ?_))
  exact congrArg wsign (add_comm _ _)

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TableInjectionTransfer
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

theorem named_at [Fintype B] {P : A×A → Prop} {C : ℝ}
    (S : B → A → Prop) (h : (Fintype.card B:ℝ) ≤ C)
    (he : ∀ y,∃ i,∀ x,P (x,y) ↔ S i x) :
    named P C := by
  classical
  let e := Fintype.equivFin B
  refine ⟨Fintype.card B,h,fun i => S (e.symm i),fun y => ?_⟩
  obtain ⟨i,hi⟩ := he y
  exact ⟨e i,by simpa using hi⟩

theorem named_true {A : Type} {C : ℝ} (h : 1 ≤ C) :
    named (fun _ : A×A => True) C :=
  ⟨1,(by simpa using h),fun _ _ => True,fun _ => ⟨0,fun _ => Iff.rfl⟩⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SmallCoverBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small Cover Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A B V : Type} [Fintype A] [Fintype B]

theorem shadow_valid (p : Shape) {n N} (T : Cov p N)
    (Δ : UnitType p n N→Ambient p N) {w}
    (h : ∀ x,w x≠0 → covered p T (Δ x)) (x y : UnitType p n N) (S) (hx : w x≠0) :
    shadow p T Δ w x y S=tone p y S (Δ x) := by
  classical
  unfold shadow cutDown
  rw [dite_eq_left ⟨hx,h x hx⟩]; rfl

theorem tone_vec (p : Shape) {n N} (x : UnitType p n N) (S : Party) (Δ : Ambient p N) :
    tone p x S Δ=dotProduct S (fun i => tone p x (unary i) Δ) := by
  classical
  have hg (i) : tone p x (unary i) Δ=uPhase p (onSide (listens p x) i) Δ := by
    unfold tone joinPhase unary
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same,one_smul]
    · intro j _ hj; simp [hj]
    simp
  unfold dotProduct
  simp_rw [hg]
  unfold tone joinPhase
  simp

theorem day_named (p : Shape) {n N} (T : Cov p N)
    (Δ : UnitType p n N→Ambient p N)
    (w : Wgt (UnitType p n N)) (d : ℕ) (hT : cdim p T≤d)
    (P : Daypair p T × Daypair p T → Prop) :
    named (fun v => P (daypair p T Δ w v.1,daypair p T Δ w v.2)) (bp (3*d*(N:ℝ))) := by
  classical
  let A := (coverX p T)
  let : Finite (Module.Dual F (coverX p T)) := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype (Module.Dual F (coverX p T)) := Fintype.ofFinite _
  have he : dim (Daypair p T) ≤ 3*d*N := by
    unfold Daypair dim
    rw [Module.finrank_prod, Module.finrank_pi_fintype,Fintype.sum_bool,
      Subspace.dual_finrank_eq]
    change dim A+(dim A+dim A)≤_
    have h : dim A≤N*d := (cover_dim p T).trans (Nat.mul_le_mul_left N hT)
    nlinarith
  refine named_at (fun y x => P (daypair p T Δ w x,y)) ?_ (fun y => ⟨daypair p T Δ w y,fun x => Iff.rfl⟩)
  rw [card_space]
  exact bp_le (by exact_mod_cast he)

variable [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem dual_matrix_rank (f : A→ V) (g : B→Module.Dual F V) :
    (Matrix.of (fun x : A => fun y : B => g y (f x))).rank ≤ dim V := by
  classical
  let M := Matrix.of (fun x : A => fun y : B => g y (f x))
  let L : V →ₗ[F] Vec B := LinearMap.pi g
  have hi : colSp Mᵀ ≤ LinearMap.range L := by
    rw [colSp, range_mulVecLin]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun x => ⟨f x,rfl⟩)
  have he : dim (colSp Mᵀ) ≤ dim V := (Submodule.finrank_mono hi).trans
    (LinearMap.finrank_range_le L)
  rw [colSp_dim,Matrix.rank_transpose] at he
  exact he

theorem circus_rank (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N)) :
    (circus p T Δ w).rank≤ N*cdim p T := (dual_matrix_rank (cutDown p T Δ w)
      (fun y => juris p T y allSide)).trans (cover_dim p T)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LowRankKernelAlternative
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Low Rank Kernel Alternative -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Filter
open scoped BigOperators Topology
variable {A J B : Type} [Fintype A] [Fintype J] [Fintype B]

omit [Fintype A] in
private theorem row_extract (a : A → Vec B) (S : Finset A) :
    ∃ T⊆ S,rbase a T=rbase a S ∧ T.card=dim (rbase a T) := by
  classical
  induction S using Finset.induction with
  | empty =>
    have hh : Set.image a ((∅:Finset A):Set _) = ∅ := by ext; simp
    have he : rbase a ∅=⊥ := by unfold rbase; rw [hh,Submodule.span_empty]
    refine ⟨∅,by simp, rfl,?_⟩; rw [he]; exact (finrank_bot ..).symm
  | insert x S hx ih =>
    obtain ⟨T,hT,hR,hD⟩ := ih
    have he (S : Finset A) :
        rbase a (insert x S)= rbase a S⊔Submodule.span F ({a x} : Set _) := by
      unfold rbase
      rw [← span_union]
      congr 1
      ext; simp [eq_comm]
    rw [he]
    by_cases h : a x∈rbase a T
    · refine ⟨T,hT.trans (Finset.subset_insert ..),?_,hD⟩
      rw [←hR,sup_eq_left.mpr (by rwa [Submodule.span_singleton_le_iff_mem])]
    refine ⟨insert x T,Finset.insert_subset_insert x hT,by rw [he,hR],?_⟩
    rw [he]
    have hh (h' : a x∉rbase a T) :=
      Submodule.finrank_sup_span_singleton h'
    rw [Finset.card_insert_of_notMem (fun e => hx (hT e)),hD]
    exact (hh h).symm

private theorem tilt_sub (m u : ℝ) (h : bp (-m)+bp (-u) ≤1) : SubLaw (tilt m u) := by
  classical
  refine ⟨fun x => ?_,?_⟩
  · unfold tilt; split <;> exact (bp_pos _).le
  unfold tot
  rw [show (Finset.univ : Finset F)={0,1} from (by ext x; simp [bit_cases])]
  simpa only [Finset.sum_insert (show (0:F)∉({1}:Finset _) by simp), tilt,ite_true, if_true,
    Finset.sum_singleton, ite_eq_right (show (1:F) ≠ 0 from one_ne_zero)] using h

theorem draws_sub {K : Type} [Fintype K] [DecidableEq K] (w : Wgt A) (h : SubLaw w) :
    SubLaw (draws K w) := by
  refine ⟨prodW_nonneg (fun _ => h.nz),?_⟩
  rw [draws,prodW_tot]
  refine (Finset.prod_le_prod (g:=fun _ => 1) (fun _ _ => tot_nonneg h.nz) (fun _ _ => h.total)).trans_eq
    (by simp)

private theorem tilted_fiber [DecidableEq J] (w : Wgt A) (f : A → Vec J)
    (v m u η : ℝ) (hh : 0<v)
    (hw : IsLaw w)
    (hm : 0 < m) (hu : 0<u) (hp : bp (-m)+bp (-u)≤1)
    (he : Fintype.card J*(u+m*η)≤v/2)
    (h : ∀ i,pr w (fun x => f x i=0)≤η) :
    ∃ z : Vec J,bp (-v)/4 ≤ pr w (fun x => f x=z) := by
  classical
  let d (i : F) := u+m*ind (i=0)
  let c (v : Vec J) := ∑ i,d (v i)
  have hd i : 0 ≤ d i := add_nonneg hu.le (mul_nonneg hm.le (ind_nonneg _))
  have hc :
      avg w (fun x => c (f x)) ≤ v/2 := by
    unfold c; rw [avg_sum]
    refine (Finset.sum_le_sum (g:=fun _ => u+m*η) fun i _ => ?_).trans ?_
    · simp only [d,avg_add,avg_mul',hw.avg_const]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (h _) hm.le) _
    simpa [mul_add] using he
  let H (x : Vec J) := ¬ v≤ c x
  let W := mapW w f
  have h1 : (1/2:ℝ) ≤ pr W H := by
    rw [mapW_pr,show (fun x => H (f x))=(fun x => ¬ v ≤ c (f x)) from rfl,
      pr_not,hw.total]
    have heq := (le_avg_markov hw.nz (f:=fun x => c (f x))
      (fun x => Finset.sum_nonneg (fun i _ => hd _)) v).trans hc
    apply le_of_mul_le_mul_right _ hh; linarith only [heq]
  let t : Wgt (Vec J) := draws J (tilt m u)
  have hk (x : Vec J) : H x → bp (-v) ≤ t x := by
    intro h'
    apply le_trans (bp_le (show -v ≤ -c x from neg_le_neg (le_of_not_ge h')))
    unfold c t draws prodW
    rw [← Finset.sum_neg_distrib,bp_sum]
    refine Finset.prod_le_prod (fun i _ => (bp_pos _).le) fun i _ => ?_
    by_cases he : x i=0
    · simp only [tilt,d,he,ite_true, if_true,ind_true,mul_one]
      exact bp_le (by linarith)
    simp only [d,tilt,ite_eq_right he,ind_zero he,mul_zero,add_zero,le_refl]
  by_contra! hz
  have hi x : W x*ind (H x)≤t x * (1/4) := by
    by_cases h : H x
    · rw [ind_one h,mul_one]
      apply le_trans (hz x).le
      simpa only [div_eq_mul_inv,one_mul] using div_le_div_of_nonneg_right (hk x h)
        (show 0 ≤ (4:ℝ) by norm_num)
    · rw [ind_zero h,mul_zero]
      exact mul_nonneg ((draws_sub _ (tilt_sub m u hp)).nz _) (by norm_num)
  have ht : SubLaw t := draws_sub _ (tilt_sub m u hp)
  have h2 := h1.trans ((Finset.sum_le_sum (s:=Finset.univ) fun i _ => hi i).trans
    (ht.avg_le (show (0:ℝ) ≤ 1/4 by norm_num) (fun _ => le_rfl)))
  norm_num at h2

set_option maxHeartbeats 800000 in
theorem fiber_growth (d : ℝ) (c : ℝ) (hc : 0 < c) (hd : 0≤d) :
    ∃ θ : ℝ,0<θ ∧ ∀ᶠ N : ℕ in atTop,∀ (A : Type) [Fintype A]
    (P : Mat A A) (w : Wgt A), IsLaw w → (P.rank : ℝ) ≤ d*N →
      (∀ x,P x x=0) →
      pr (pairW w w) (fun x => P x.1 x.2=0)≤ θ →
      ∃ S : A→Prop, bp (-c*N) ≤ pr w S ∧ ∀ x,S x → ∀ y,S y → P x y=0 := by
  classical
  let u := c /(16*(d+1))
  have hu : 0 < u := div_pos hc (by linarith)
  obtain ⟨m,hm,hp⟩ : ∃ m : ℝ,0 < m ∧ bp (-m)+bp (-u) ≤1 := by
    have hh : 0 < 1-bp (-u) := sub_pos.mpr ((bp_lt (neg_lt_zero.mpr hu)).trans_eq bp_zero)
    have he := (bp_nat_vanish (by norm_num : 0<(1:ℝ))).eventually (gt_mem_nhds hh)
    obtain ⟨n,hn,hN⟩ := (he.and (eventually_gt_atTop 0)).exists
    refine ⟨n,Nat.cast_pos.mpr hN,?_⟩
    have he' : bp (-(n:ℝ))<1-bp (-u) := by simpa using hn
    linarith
  let θ := u/(4*m)
  have ht : 0<θ := div_pos hu (by linarith)
  refine ⟨θ,ht,?_⟩
  filter_upwards [eventually_gt_atTop 0,tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (8/c))] with N hN h A _ P w hw hP hz hp'
  let f (x : A) := pr w (fun y => P x y=0)
  let Q : Finset A := Finset.univ.filter (fun x => ¬ 2*θ ≤ f x)
  have hq : (1/2:ℝ) ≤ pr w (fun x => x∈Q) := by
    have hg : avg w f ≤ θ := by rw [pr,pairW_avg] at hp'; exact hp'
    have hi := (le_avg_markov hw.nz (f:=f) (fun x => pr_nonneg hw.nz) (2*θ)).trans hg
    simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and,pr_not,hw.total]
    apply le_of_mul_le_mul_right _ ht; linarith only [hi]
  let v := onW w (fun x => x∈Q)
  obtain ⟨T,hT,hR,hM⟩ := row_extract (P.row) Q
  have hM' : ↑T.card ≤ d*N := by
    rw [hM]
    have hg : rbase P.row T ≤ colSp Pᵀ := by
      apply Submodule.span_le.mpr
      rintro y ⟨x,hx,rfl⟩; exact colSp_mem (P:=Pᵀ) x
    have hi := Submodule.finrank_mono hg
    change dim _ ≤ Pᵀ.rank at hi; rw [Matrix.rank_transpose] at hi
    exact le_trans (Nat.cast_le.mpr hi) hP
  let g (x : A) : Vec T := fun j => P j.val x
  let E (x : A) := x∈Q
  have hpc : 0<pr w E := by linarith
  have he (i : ↑T) : pr v (fun x => g x i=0)≤4*θ := by
    have h : f i.val ≤ 2*θ := le_of_not_ge (Finset.mem_filter.mp (hT i.property)).2
    unfold v
    rw [pr_on]; refine (div_le_iff₀ hpc).mpr ?_
    apply le_trans _ (le_trans h ?_)
    · exact pr_mono hw.nz fun x => And.right
    nlinarith only [mul_le_mul_of_nonneg_left hq ht.le]
  let x := c*N/2
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hx : 0<x := div_pos (mul_pos hc hn) (by norm_num)
  have ht' : (↑(Fintype.card ↑T):ℝ)*(u+m*(4*θ))≤x/2 := by
    rw [Fintype.card_coe]
    have hθ : u+m*(4*θ) = 2*u := by unfold θ; field_simp <;> ring
    rw [hθ]; refine (mul_le_mul_of_nonneg_right hM' (by linarith)).trans ?_
    have hu' : u*(16*(d+1))=c := by unfold u; field_simp
    unfold x
    rw [←hu']
    nlinarith
  obtain ⟨z,hZ⟩ := tilted_fiber v g x m u (4*θ) hx (on_law hw.nz hpc) hm hu hp ht' he
  refine ⟨fun x => E x∧g x=z,?_,fun x hx y hy => ?_⟩
  · rw [pr_of_on hw.nz E]
    calc bp (-c*N) ≤ (1/2)*(bp (-x)/4) := by
           have hq : bp (-c*N) ≤ bp (-3+ -x) := bp_le (by
             change (8/c) ≤ (N:ℝ) at h
             have he := (div_le_iff₀ hc).mp h
             unfold x; linarith only [he])
           rw [bp_add,bp_neg,show (3:ℝ)=↑(3:ℕ) from by norm_num,bp_nat] at hq
           linarith only [hq]
         _ ≤ _ := mul_le_mul hq hZ (div_nonneg (bp_pos _).le (by norm_num)) hpc.le
  · have hv (x y : A) (h : g x=g y) :
        ∀ i∈Q,P i x=P i y := by
      let f := LinearMap.proj (R:=HadwigerCounterexample.F) (φ:=fun _ : A => HadwigerCounterexample.F) x
      let f' := LinearMap.proj (R:=HadwigerCounterexample.F) (φ:=fun _ : A => HadwigerCounterexample.F) y
      have hh : rbase P.row T ≤ LinearMap.ker (f-f') := by
        refine Submodule.span_le.mpr ?_
        rintro v ⟨i,hi,rfl⟩
        exact sub_eq_zero.mpr (congr_fun h (⟨i,hi⟩ : T))
      intro i hi
      rw [hR] at hh
      exact sub_eq_zero.mp (hh (Submodule.subset_span ⟨i,hi,rfl⟩))
    rw [← hv x y (hx.2.trans hy.2.symm) x hx.1,hz]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolynomialRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {A B : Type} [Fintype A] [Fintype B]

theorem rank_mask (P Q : Mat A B) :
    (mpMask P Q).rank ≤ P.rank*Q.rank := by
  classical
  obtain ⟨X,Y,hX,hY,hP⟩ := rank_product P
  obtain ⟨U,V,hU,hV,hQ⟩ := rank_product Q
  let R := Fin P.rank × Fin Q.rank
  let f : Mat A R := Matrix.of (fun x r => X x r.1*U x r.2)
  let g : Mat R B := Matrix.of (fun r y => Y r.1 y * V r.2 y)
  have he : mpMask P Q=f*g := by
    ext i j
    have h (a : Fin P.rank) (b : Fin Q.rank) :
        f i (a,b)*g (a,b) j=(X i a*Y a j)*(U i b*V b j) := by
      unfold f g; simp only [Matrix.of_apply] <;> ring
    change P i j*Q i j = ∑ x : Fin P.rank × Fin Q.rank, f i x*g x j
    have ht :
        (∑ a,X i a * Y a j)*(∑ b,U i b*V b j)=P i j*Q i j :=
      congrArg₂ (·*·) (congr_fun (congr_fun hP i) j) (congr_fun (congr_fun hQ i) j)
    exact ht.symm.trans (by
      rw [Finset.sum_mul,Fintype.sum_prod_type]
      simp_rw [Finset.mul_sum,h])
  rw [he]
  exact (Matrix.rank_mul_le_left ..).trans (f.rank_le_card_width.trans_eq (by simp [R]))

private theorem choose_draws (w : Wgt A) (T : ℕ) (hw : IsLaw w)
    (i j : Fin T) (h : i≠j) :
    mapW (draws (Fin T) w) (fun x => (x i,x j))=pairW w w := by
  classical
  let g : Bool → Fin T := fun b => if b then i else j
  have hg : Injective g := by intro x y; cases x <;> cases y <;> simp [g,h,h.symm]
  funext x
  let P (b : Bool) := fun y : A => y=onSide x b
  have ht := prodW_pr_inj hg (w:=fun _ => w) (fun _ => hw) P
  have hm (z : Fin T → A) : (z i,z j)=x ↔ ∀ b,P b (z (g b)) := by
    simp [Bool.forall_bool, P, Prod.ext_iff,onSide,g,and_comm]
  unfold mapW
  simp_rw [hm]
  refine ht.trans ?_
  rw [Fintype.prod_bool]; unfold P onSide
  simp only [Bool.false_eq_true,ite_true, if_true,ite_false, if_false,pr_point']

  rfl

/-- Here T counts k^2+1 draws, union bound uses crude T^2.
Even repeats give the event. -/
theorem simultaneous_czeros (P : Mat A A) (k : ℕ)
    (w : Wgt A) (hw : IsLaw w) (hK : 1+P.rank ≤ k)
    (h : ∀ x,P x x=0) :
    1 ≤ ((k:ℝ)^2+1)^2 * pr (pairW w w) (fun x => P x.1 x.2=0 ∧ P x.2 x.1=0) := by
  classical
  let O : Vec A := fun _ => 1
  let Q := vecMulVec O O+P
  let V := mpMask Q Qᵀ
  have hr : Q.rank≤ k := (mrk_add_le ..).trans
    ((Nat.add_le_add_right (Matrix.rank_vecMulVec_le O O) _).trans hK)
  have he : V.rank ≤ k^2 := (rank_mask Q Qᵀ).trans (by rw [Matrix.rank_transpose]; nlinarith)
  let T := k^2+1
  let p := fun x : A×A => P x.1 x.2=0 ∧ P x.2 x.1=0
  let f := fun i : Fin T × Fin T => fun z : Fin T → A => i.1≠i.2 ∧ p (z i.1,z i.2)
  have hx (z : Fin T→A) : ∃ i,f i z := by
    by_contra! hz
    have heq : V.submatrix z z = 1 := by
      ext i j
      change (1+P (z i) (z j))*(1+P (z j) (z i)) = (1:Mat (Fin T) (Fin T)) i j
      by_cases h' : i=j
      · subst j; rw [Matrix.one_apply_eq,h]; simp
      rw [Matrix.one_apply_ne h']
      rcases bit_cases (P (z i) (z j)) with hP|hP
      · have hv := (bit_cases (P (z j) (z i))).resolve_left
          (fun hc => hz (i,j) ⟨h',hP,hc⟩)
        rw [hv,char_two,mul_zero]
      rw [hP,char_two,zero_mul]
    have hk := (V.rank_submatrix_le z z).trans he
    rw [heq,Matrix.rank_one,Fintype.card_fin] at hk; omega
  let μ := draws (Fin T) w
  have hm : IsLaw μ := draws_law hw
  have hB (i : Fin T×Fin T) :
      pr μ (f i) ≤ pr (pairW w w) p := by
    by_cases he : i.1=i.2
    · simp only [f,he,ne_eq,not_true_eq_false,false_and,pr_false]
      exact pr_nonneg (pairW_law hw hw).nz
    · rw [← choose_draws w T hw _ _ he, mapW_pr]
      simp only [μ,f,he,ne_eq,not_false_eq_true,true_and,le_refl]
  have hh : 1 = pr μ (fun z => ∃ i,f i z) := by
    simp_rw [show ∀ z,(∃ i,f i z)=True from (fun z => eq_true (hx z)),pr_true,hm.total]
  refine hh.trans_le (((pr_exists_le hm.nz f).trans
    (Finset.sum_le_sum fun i _ => hB i)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_fin,T]
  push_cast; unfold p; ring
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourPhaseBits
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Phase Bits -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
theorem quad_card : Fintype.card Quad=16 := by simp [Quad]
private theorem quad_rate (x : Quad) : unif x=(1:ℝ)/16 := by
  rw [unif_apply,quad_card]; norm_num

theorem quad_inv_zero (x : Quad) : avg unif (fun y => quadPhase y x)=ind (x=0) := by
  classical
  let B := (dotL x.1).coprod (dotL x.2)
  have h (y) : quadPhase y x=wsign (B y) := by
    change wsign (dotProduct y.1 x.1+dotProduct y.2 x.2)=wsign (dotProduct x.1 y.1+dotProduct x.2 y.2)
    rw [dotProduct_comm x.1,dotProduct_comm x.2]
  have he : B=0 ↔ x=0 := by
    constructor
    · intro he
      have hl : dotL x.1=0 := LinearMap.ext fun z => by
        have hf : dotL x.1 z+dotL x.2 0=0 := LinearMap.congr_fun he (z,0)
        rwa [map_zero,add_zero] at hf
      have hr : dotL x.2=0 := LinearMap.ext fun z => by
        have hf : dotL x.1 0+dotL x.2 z=0 := LinearMap.congr_fun he (0,z)
        rwa [map_zero,zero_add] at hf
      refine Prod.ext (dot_ext_zero (fun y => ?_)) (dot_ext_zero (fun y => ?_))
      · rw [dotProduct_comm]; exact LinearMap.congr_fun hl y
      rw [dotProduct_comm]; exact LinearMap.congr_fun hr y
    · intro he
      refine LinearMap.ext fun y => ?_
      unfold B; rw [he]
      change dotProduct (0:Party) y.1 +dotProduct (0:Party) y.2=0
      rw [zero_dotProduct,zero_dotProduct]; simp
  simp_rw [h,wsign_lin,he]

theorem quad_inv (x y : Quad) : ind (x=y)=avg unif (fun S => quadPhase S x*quadPhase S y) := by
  classical
  have he (S) : quadPhase S (x+y) = quadPhase S x*quadPhase S y := by
    unfold quadPhase quadDot
    rw [← wsign_add]
    simp only [Prod.fst_add,Prod.snd_add,dotProduct_add,add_comm,add_left_comm]
  simp_rw [← he,quad_inv_zero]
  apply congrArg ind
  exact propext (by rw [← ZModModule.sub_eq_add,sub_eq_zero])
private theorem joint_phase (p : Shape) {n N} (Δ : UnitType p n N→ Ambient p N) (x) (S) :
    quadPhase S (quench p Δ x) = chant p Δ S.1 S.2 x := by
  unfold quadPhase chant
  unfold quadDot quench
  dsimp only
  rw [←tone_vec, ←tone_vec,add_comm]

theorem quad_invert (p : Shape) {n N} (Δ : UnitType p n N→Ambient p N) (w) (s : Quad) :
    pr (pairW w w) (fun x => quench p Δ x=s)=
    avg unif (fun v : Quad => pitch p Δ w v.1 v.2 * quadPhase v s) := by
  unfold pr
  simp_rw [quad_inv, joint_phase]
  rw [avg_avg]
  simp_rw [avg_mul]
  rfl

theorem mix_pattern (p : Shape) {n N} (Δ : UnitType p n N→Ambient p N) (w)
    (hw : IsLaw w) (h : tonalMix p Δ w) (s : Quad) :
    0.05 < pr (pairW w w) (fun x => quench p Δ x=s) := by
  classical
  rw [quad_invert]
  let f := fun S : Quad => ind (S=0) - 0.005
  have hf S : f S≤pitch p Δ w S.1 S.2*quadPhase S s := by
    by_cases hS : S=0
    · have h0 : pitch p Δ w 0 0=1 := by
        unfold pitch
        have hz (x : UnitType p n N) y : tone p x 0 (Δ y)=0 := by rw [tone_vec,zero_dotProduct]
        simp_rw [hz,add_zero, wsign_zero]; exact (pairW_law hw hw).avg_const _
      rw [hS]
      change f 0≤pitch p Δ w 0 0*quadPhase 0 s
      rw [h0]
      norm_num [f,quadPhase,quadDot]
    · have hh := h _ _ (show S.1≠0 ∨ S.2≠0 from by
        by_contra! he; exact hS (Prod.ext he.1 he.2))
      have he : |pitch p Δ w S.1 S.2*quadPhase S s| < 0.005 := by rwa [abs_mul,quadPhase,wsign_abs,mul_one]
      simpa only [f,ind_zero hS,zero_sub] using (abs_lt.mp he).1.le
  apply lt_of_lt_of_le _ (avg_mono unif_law.nz hf)
  unfold f; rw [avg_sub, unif_law.avg_const]
  change 0.05 < pr unif (fun S : Quad => S=0)-0.005
  rw [pr_point',quad_rate]; norm_num

private theorem party_single (x : Party) (h : x∉evenP) : ∃ i,x=unary i := by
  classical
  rcases bit_cases (x true) with a|a <;> rcases bit_cases (x false) with b|b
  · have he : x=0 := funext fun i => by cases i; exact b; exact a
    simp [he,evenP] at h
  · refine ⟨false,funext fun i => ?_⟩; cases i <;> simp [a,b,unary]
  · refine ⟨true,funext fun i => ?_⟩; cases i <;> simp [a,b,unary]
  have he : x=allSide := funext fun i => by cases i; exact b; exact a
  simp [he,evenP] at h

private theorem even_dot (_ : Quad) (v : Quad) (h : v∈evenQ) (j : F) :
    quadPhase v (repeatQ j)=1 := by
  classical
  have he (b : Party) (h : b∈evenP) : dotProduct b (fun _ => j)=0 := by
    have h : b=0 ∨ b=allSide := by simpa [evenP] using h
    rcases h with h|h
    · rw [h,zero_dotProduct]
    simp only [h,dotProduct,Fintype.sum_bool,allSide,one_mul,char_two]
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp h
  unfold quadPhase quadDot repeatQ
  dsimp only
  rw [he _ ha,he _ hb]; simp

private theorem even_sum (x : Quad) (i : F) :
    ∑ v∈evenQ,quadPhase v x*quadPhase v (repeatQ i)=4*ind (repeated x) := by
  classical
  let f (x : Party) (v : Party) := wsign (dotProduct v x)
  have hh (x) :
      ∑ v∈evenP,f x v=2*ind (dotProduct allSide x=0) := by
    have hn : allSide≠0 := by
      intro e
      have hh := congr_fun e true
      change (1:F)=0 at hh; simp at hh
    simp only [evenP,Finset.sum_insert (show (0:Party)∉ ({allSide}:Finset _) from
      fun h => hn (mem_singleton.mp h).symm),Finset.sum_singleton,f, zero_dotProduct, wsign_zero]
    by_cases ht : dotProduct allSide x=0
    · norm_num [ind,ht]
    norm_num [ind,ht,wsign]
  have ht (v : Quad) (h : v∈evenQ) : quadPhase v x * quadPhase v (repeatQ i)
      = f x.1 v.1 * f x.2 v.2 := by
    rw [even_dot x _ h,mul_one,quadPhase,quadDot,wsign_add]
  rw [Finset.sum_congr (g:=fun v => f x.1 v.1 * f x.2 v.2) rfl ht,evenQ, Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,hh,hh,repeated,ind_and]; ring

set_option maxHeartbeats 800000 in
theorem tiny_pattern (p : Shape) {n N} (Δ : UnitType p n N→Ambient p N) (w)
    (i : F) {h : ℝ} (h0 : 0≤h)
    (hw : ∀ i : Bool,∀ R, |pitch p Δ w (unary i) R|≤h) :
    (1/4:ℝ)*pr (pairW w w) (fun x => repeated (quench p Δ x))-h ≤
      pr (pairW w w) (fun x => quench p Δ x=repeatQ i) := by
  classical
  let f (v : Quad) := pitch p Δ w v.1 v.2*quadPhase v (repeatQ i)
  let μ := pairW w w
  let g (S : Quad) := ind (S∈evenQ)*f S
  have he (x : Quad) : g x - h ≤ f x := by
    by_cases hx : x∈evenQ
    · unfold g; rw [ind_one hx,one_mul]
      exact sub_le_self _ h0
    have hi : |pitch p Δ w x.1 x.2|≤h := by
      by_cases he : x.1∈evenP
      · obtain ⟨i,hit⟩ := party_single x.2 (fun hh => hx (Finset.mem_product.mpr ⟨he,hh⟩))
        rw [hit,pitch_turn]
        exact hw i _
      obtain ⟨i,hi⟩ := party_single _ he
      rw [hi]; exact hw i _
    have hs : |f x|≤h := by unfold f quadPhase; rwa [abs_mul,wsign_abs,mul_one]
    unfold g; rw [ind_zero hx,zero_mul,zero_sub]
    exact (abs_le.mp hs).1
  have hg : avg unif g=(1/4:ℝ)*pr μ (fun x => repeated (quench p Δ x)) := by
    have ht : ∑ x : Quad,g x= ∑ x∈evenQ,f x := by
      symm
      simp only [g,ind,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
      simp
    have hB (x : Quad) :
        f x=avg μ (fun y => quadPhase x (quench p Δ y)*quadPhase x (repeatQ i)) := by
      rw [avg_mul]; simp_rw [joint_phase]; rfl
    have hf : ∑ x∈evenQ,f x=4*pr μ (fun x => repeated (quench p Δ x)) := by
      simp_rw [hB,← avg_sum,even_sum,avg_mul']; rfl
    simp only [avg,quad_rate,← Finset.mul_sum, ht,hf]
    unfold pr avg
    ring
  rw [quad_invert,show _*pr _ _=_ from hg.symm]
  calc avg unif g - h = avg unif (fun x => g x-h) := by rw [avg_sub,unif_law.avg_const]
       _ ≤ _ := avg_mono unif_law.nz he

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolynomialCompatibility
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Finset Filter
variable {p : Shape} {n N d : ℕ}

set_option maxHeartbeats 600000 in
theorem tiny_poll (p : Shape) {n N : ℕ} (Δ : UnitType p n N→Ambient p N)
    (w : Wgt (UnitType p n N)) (hw : IsLaw w)
    (h : tonalTiny p Δ w d)
    (hd : ∀ x, w x≠0 → tone p x allSide (Δ x) = 0) (i : F) :
    (1/4 : ℝ)/poll d N-bp (-0.24*N)≤
      pr (pairW w w) (fun x => quench p Δ x=repeatQ i) := by
  classical
  obtain ⟨T,hT,hZ,hE⟩ := h
  let M := circus p T Δ w
  have hM : M.rank≤ d*N := (circus_rank ..).trans ((Nat.mul_le_mul_left N hT).trans_eq
    (Nat.mul_comm _ _))
  have hB (x y) (hx : w x≠0) :
      tone p y allSide (Δ x)=M x y := (shadow_valid p T Δ hZ x y allSide hx).symm
  have hD x : M x x=0 := by
    by_cases hx : w x=0
    · change juris p T x _ (cutDown p T Δ w x) = _
      simp [cutDown,hx]
    exact (hB _ _ hx).symm.trans (hd x hx)
  let u := pairW w w
  have hX :
      pr u (fun x => M x.1 x.2=0 ∧ M x.2 x.1=0)=
        pr u (fun x => repeated (quench p Δ x)) := by
    refine avg_congr (fun x hx => ?_)
    congr 1
    have h1 := hB x.1 x.2 (left_ne_zero_of_mul hx)
    have h2 := hB x.2 x.1 (right_ne_zero_of_mul hx)
    unfold repeated quench
    simp only [←tone_vec,h1,h2]
  have hi : 1 ≤ poll d N*pr u (fun x => repeated (quench p Δ x)) := by
    have hh := simultaneous_czeros M (1+d*N) w hw (by omega) hD
    rw [show pairW w w=u from rfl,hX] at hh
    refine le_trans hh (le_of_eq ?_)
    push_cast; unfold poll
    ring
  have hh : 0 < poll d N := by unfold poll; positivity
  apply le_trans _ (tiny_pattern p Δ w i (bp_pos _).le hE)
  apply sub_le_sub_right
  exact (div_le_iff₀ hh).mpr (by linarith only [hi])

theorem eventually_tiny_poll (d : ℕ) :
    ∃ b> (0:ℝ),∀ᶠ N : ℕ in atTop,
      b/N^ (4:ℕ) ≤ (1/4:ℝ)/poll d N-bp (-0.24*N) := by
  classical
  let B : ℝ := (1+(1+(d:ℝ))^2)^2
  have hb : 0 < B := by unfold B; positivity
  let c := B⁻¹/8
  have hc : 0 < c := by unfold c; positivity
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop 1,bp_poly_dom_nat (by norm_num : 0<(0.24:ℝ)) c⁻¹ 4] with
    N hN hE
  have h : 1≤ (N:ℝ) := by exact_mod_cast hN
  have hh : poll d N ≤ B*N^(4:ℕ) := by
    unfold poll B
    have hf : 1+d*(N:ℝ) ≤ (1+d)*N := by linarith only [h]
    calc (1+(1+d*(N:ℝ))^2)^2
      _ ≤ ((N:ℝ)^2+((1+d)*N)^2)^2 := by
        have hi : 1 ≤ (N:ℝ)^2 := by nlinarith
        gcongr
      _ = _ := by ring
  have hB : 2*(c / N^(4:ℕ)) ≤ (1/4:ℝ)/poll d N := by
    have hf : 0 < poll d N := by unfold poll; positivity
    calc 2*(c/N^(4:ℕ)) = (1/4:ℝ)/(B*N^(4:ℕ)) := by unfold c; field_simp <;> norm_num
         _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hf hh
  have hx := bp_pos (0.24*N)
  have hζ : bp (-0.24*N) ≤ c/N^(4:ℕ) := by rw [neg_mul,bp_neg]; field_simp; field_simp at hE; rw [mul_comm _ (0.24:ℝ)] at hE; linarith
  linarith only [hB,hζ]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WeightedPartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.idxDec
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

theorem issued_sub (w : Wgt A) (hw : ∀ x, 0≤w x) (S R : Finset A) (h : R⊆S) :
    partMass w R=partMass w S*partMass (partW w S) R := by
  have he : (fun x => x∈ R)=(fun x => x∈S∧x∈R) := by ext; tauto
  unfold partMass
  exact ((congrArg (pr w) he).trans (pr_of_on hw _ _))

theorem issued_law (w : Wgt A) (hw : ∀ x, 0≤w x)
    {S R : Finset A} (hp : 0 < partMass w S) (h : R⊆S)
    (he : 0 < partMass (partW w S) R) :
    0 < partMass w R ∧ partW w R=partW (partW w S) R := by
  refine ⟨by rw [issued_sub w hw S R h]; exact mul_pos hp he,?_⟩
  have ht := on_both w (fun x => x∈S) (fun x => x∈R) hw hp he
  unfold partW; rw [ht]
  exact congrArg (onW w) (by ext; tauto)

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

/-- Refine on every old tile, with rules allowed to be different on every
tile. Total loss bound relative to the old tiled union. -/
theorem improve (T : Tiles A) (w : Wgt A) (hw : ∀ x,0 ≤ w x)
    (P : A→Prop) (R : Finset A→Finset A→Prop) (hT : apart T) {c : ℝ}
    (h : ∀ i∈T,∃ V : Tiles A, apart V ∧
      (∀ S∈V,S ⊆ i ∧ R i S) ∧
      pr (partW w i) (fun x => x∈i∧P x∧¬inTiles V x) ≤ c) :
    ∃ V : Tiles A,apart V∧ (∀ S∈V,∃ i∈T,S⊆i ∧ R i S) ∧
      pr w (fun x => inTiles T x ∧ P x ∧ ¬inTiles V x)≤ allMass w T*c := by
  classical
  have h1 : ∀ i : Finset A, ∃ V : Tiles A,i∈T → apart V ∧
      (∀ S∈V,S ⊆ i ∧ R i S) ∧
      pr (partW w i) (fun x => x∈i∧P x∧¬inTiles V x) ≤ c := by
    intro i
    by_cases hi : i∈T
    · obtain ⟨V,h⟩ := h i hi
      exact ⟨V,fun _ => h⟩
    exact ⟨∅,fun h => (hi h).elim⟩
  choose V hV using h1
  let G := T.biUnion V
  refine ⟨G,?_,?_,?_⟩
  · intro x S hS W hw hx hx'
    obtain ⟨i,hi,hS⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,hj,hW⟩ := Finset.mem_biUnion.mp hw
    obtain rfl := hT x i hi j hj (((hV i hi).2.1 S hS).1 hx) (((hV j hj).2.1 W hW).1 hx')
    exact (hV i hi).1 x S hS W hW hx hx'
  · rintro S hS
    obtain ⟨i,hi,hS⟩ := Finset.mem_biUnion.mp hS
    exact ⟨i,hi,(hV i hi).2.1 _ hS⟩
  · rw [mass_apart hT,tiles_inter _ T _ hT, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have he (x) (hx : inTiles (V i) x) : inTiles G x := by
      obtain ⟨S,hS,h⟩ := hx
      exact ⟨S,Finset.mem_biUnion.mpr ⟨i,hi,hS⟩,h⟩
    let Z (x : A) := x∈i∧P x∧¬inTiles (V i) x
    calc pr w _
      _ ≤ pr w (fun x => x∈i∧ Z x) :=
        pr_mono hw (fun x h => ⟨h.1,h.1,h.2.1,fun hx => h.2.2 (he _ hx)⟩)
      _ = _ := pr_of_on hw (fun x => x∈i) Z
      _ ≤ _ := mul_le_mul_of_nonneg_left (hV i hi).2.2 (pr_nonneg hw)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PartitionSelection
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
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

theorem ripe_restrict (hw : ∀ x,0≤w x) {S Y} {a : Pin p n N} {D ζ : ℝ} {K : ℕ}
    (h : Ripe p w μ S a D ζ K) (hz : 0≤ζ) (he : Y⊆S)
    (hp : bp (-ζ*N) ≤ partMass (partW w S) Y) :
    Ripe p w μ Y a (D+ζ) (2*ζ) K := by
  classical
  let v := partW w S
  have hv : IsLaw v := on_law hw h.pos
  have ht := lt_of_lt_of_le (bp_pos _) hp
  have hh := on_mon hv.nz (bp_pos _) hp
  obtain ⟨h1,h2⟩ := issued_law w hw h.pos he ht
  have hk (x) : partW w Y x ≤ bp (ζ*N) * v x := by
    rw [h2]
    have hg := hh x
    rw [neg_mul,bp_neg, inv_inv] at hg
    exact hg
  have hy : IsLaw (partW w Y) := on_law hw h1
  refine ⟨h1,fun x hx => h.fixpin x (he hx),h.bound,fun b => ?_,fun x => ?_⟩
  · let r := planNew a.sp b.sp
    by_cases hr : r=0
    · change pr _ _ ≤ fee N _ r
      rw [hr]
      simp only [fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero]
      exact (pr_le_tot hy.nz).trans hy.total.le
    apply ((pr_cap hk _).trans
      (mul_le_mul_of_nonneg_left (h.clear b) (bp_pos _).le)).trans
    change bp (ζ*N)*fee N ζ r ≤ fee N (2*ζ) r
    rw [fee,fee,←bp_add]
    apply bp_le
    have hh : 1≤(r:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have he := mul_le_mul_of_nonneg_right hh (mul_nonneg hz
      (show 0≤(N:ℝ) from Nat.cast_nonneg _))
    linarith only [he]
  exact ((hk x).trans (mul_le_mul_of_nonneg_left (h.density x) (bp_pos _).le)).trans_eq
    (by rw [add_mul,bp_add]; ring)

theorem trim (P : UnitType p n N→Prop) (hw : ∀ x,0≤w x) {D ζ : ℝ} (hz : 0≤ζ) {K}
    {T : Canopy p n N} (hT : apart T) (g : CTile p n N → Pin p n N)
    (h : ∀ i∈T,Ripe p w μ i (g i) D ζ K) :
    ∃ V : Canopy p n N,apart V ∧
    (∀ S∈V,∃ i∈T,S⊆i ∧ Ripe p w μ S (g i) (D+ζ) (2*ζ) K ∧ ∀ x∈S,P x) ∧
    pr w (fun x => inTiles T x ∧ P x ∧ ¬inTiles V x) ≤ allMass w T*bp (-ζ*N) := by
  classical
  refine improve T w hw P (fun i S => Ripe p w μ S (g i) (D+ζ) (2*ζ) K ∧ ∀ x∈S,P x)
    hT (fun i hi => ?_)
  let S := i.filter P
  have hs : S⊆i := Finset.filter_subset _ _
  let v := partW w i
  by_cases he : bp (-ζ*N) ≤ partMass v S
  · refine ⟨{S},?_,?_,?_⟩
    · intro x S h T h'; rw [mem_singleton.mp h,mem_singleton.mp h']; simp only [implies_true]
    · intro j hj; rw [mem_singleton.mp hj]
      exact ⟨hs,ripe_restrict hw (h i hi) hz hs he,fun x h => (mem_filter.mp h).2⟩
    have hh : (fun x => x∈i∧ P x∧ ¬inTiles ({S}:Tiles _) x)=(fun _ => False) := by
      ext x; simp [S,inTiles]; tauto
    rw [hh,pr_false]; exact (bp_pos _).le
  refine ⟨∅,by intro x S h; simp at h, by simp,?_⟩
  have hh (x : UnitType p n N) : x∈S ↔ x∈i∧ P x := by simp [S]
  have hn := le_of_not_ge he
  unfold partMass at hn
  simp_rw [hh] at hn
  simpa [inTiles,v] using hn

variable {I : Type} [Fintype I]

set_option maxHeartbeats 700000 in
theorem reparts (w μ : Wgt (UnitType p n N))
    (hw : IsLaw w) (S : CTile p n N) (D ζ u : ℝ) (hn : 0<N)
    (hz : 0 < ζ) (hz' : ζ < 1)
    (hMu : ∀ a : Pin p n N, pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N)*μ x)
    (f : UnitType p n N → I) (K1 K2 : ℕ)
    (P : CTile p n N → Pin p n N → Prop)
    (h : ∀ i : I, ∃ b : Pin p n N,
       (∀ x∈ S,f x=i → b.agree x) ∧ planRank b.sp ≤ K1 ∧
       ∀ (c : Pin p n N) (G : CTile p n N), G.Nonempty → (∀ x∈G,x∈S ∧ f x=i) → b.sp ≤ c.sp → P G c)
    (hK : (D+u) + ζ ≤ (ζ-ζ/4)*K2) :
    ∃ V : Canopy p n N, apart V ∧ (∀ G∈V,
      G⊆S ∧ ∃ b,Ripe p w μ G b (D+u+K2+1) ζ (K1+K2) ∧ P G b) ∧
      pr w (fun x => x∈S∧ ¬inTiles V x)≤
        (num I*bp (-u*N)) + bp (-ζ*N) := by
  classical
  let X := UnitType p n N
  let F (i : I) := S.filter (fun x => f x=i)
  have hF (i : I) (x : X) : x∈F i ↔ x∈ S ∧ f x=i := mem_filter
  choose b hb hL hP using h
  let R (G : Finset X) (b : Pin p n N) := Ripe p w μ G b (D+u+K2+1) ζ (K1+K2) ∧ P G b
  let C := bp (-ζ*N); let t := bp (-u*N)
  have ht (i : I) :
      ∃ V : Tiles X, apart V ∧ (∀ G∈V,G⊆F i∧∃ b,R G b) ∧
        pr w (fun x => x∈F i ∧ ¬inTiles V x)≤t+partMass w (F i)*C := by
    let S' := F i
    let v := partW w S'
    by_cases hi : t≤partMass w (F i)
    · have ht := lt_of_lt_of_le (bp_pos _ : 0<t) hi
      have hv : IsLaw v := on_law hw.nz ht
      have hx (x) : v x≤bp ((D+u)*N)*μ x := by
        apply ((on_mon hw.nz (bp_pos _) hi x).trans
          (mul_le_mul_of_nonneg_left (hc x) (inv_pos_of_pos (bp_pos _)).le)).trans_eq
        rw [add_mul,bp_add,neg_mul,bp_neg,inv_inv]; ring
      obtain ⟨G,hG,hA,hB⟩ :=
        peel_family hz hz' hn hMu hx hv.nz S' (b i)
          (fun x h => hb i x ((hF ..).mp h).1 ((hF ..).mp h).2) hK
      refine ⟨G,hA,fun S h => ?_,?_⟩
      · obtain ⟨hh,b',hp⟩ := hG S h
        obtain ⟨hz,hzm,_⟩ := exists_of_pr_pos hv.nz hp.pos
        obtain ⟨h1,h2⟩ := issued_law w hw.nz ht hh hp.pos
        refine ⟨hh,b',⟨h1,hp.fixpin,(hp.bound.trans (Nat.add_le_add_right (hL _) _)),?_,?_⟩,
          hP i _ _ ⟨hz,hzm⟩ (fun x hx => (hF ..).mp (hh hx)) hp.extendsSp⟩
        · rw [h2]; exact hp.clear
        rw [h2]; exact hp.density
      · rw [pr_of_on hw.nz (fun x => x∈ F i)]
        have hh : pr v (fun x => ¬inTiles G x) = pr v (fun x => x∈F i ∧ ¬inTiles G x) := by
          apply avg_congr
          intro x h; simp only [show x∈F i from (onW_ne h).1,true_and]
        refine le_trans (mul_le_mul_of_nonneg_left (hh.trans_le hB) ht.le) ?_
        exact le_add_of_nonneg_left (bp_pos _).le
    · refine ⟨∅,(fun x S h => ?_),by simp,?_⟩
      · simp at h
      apply le_trans (pr_mono hw.nz (q:=fun x => x∈F i) fun _ => And.left)
        ((le_of_not_ge hi).trans ?_)
      exact le_add_of_nonneg_right (mul_nonneg (pr_nonneg hw.nz) (bp_pos _).le)
  choose V hV h1 h2 using ht
  let G := Finset.univ.biUnion V
  refine ⟨G,?_,?_,?_⟩
  · intro x S hS T hT h hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hT
    obtain rfl : i=j := ((hF ..).mp ((h1 i S hi).1 h)).2.symm.trans
      ((hF ..).mp ((h1 j T hj).1 hx)).2
    exact hV i x S hi T hj h hx
  · intro S h
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨h,h'⟩ := h1 i S hi
    exact ⟨h.trans (Finset.filter_subset _ _),h'⟩
  · let Q (i : I) := fun x : X => x∈ F i ∧ ¬inTiles (V i) x
    have hf x (h : x∈ S∧¬inTiles G x) : ∃ i,Q i x := by
      refine ⟨f x,(hF ..).mpr ⟨h.1,rfl⟩,?_⟩
      rintro ⟨T,hT,h'⟩
      exact h.2 ⟨T,Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ (f x),hT⟩,h'⟩
    refine ((pr_mono hw.nz hf).trans ((pr_exists_le hw.nz Q).trans
      (Finset.sum_le_sum fun i _ => h2 i))).trans ?_
    rw [Finset.sum_add_distrib]
    have ht : (∑ i, partMass w (F i)) ≤ 1 := by
      simp_rw [partMass, hF,sum_pr_tag]
      exact (pr_le_tot hw.nz).trans hw.total.le
    calc (∑ _ : I,t)+∑ i,partMass w (F i)*C ≤ num I*t+1*C := by
           rw [← Finset.sum_mul]
           simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]
           exact add_le_add_right (mul_le_mul_of_nonneg_right ht (bp_pos _).le) _
         _ = _ := by rw [one_mul]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RefinedPinImages
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Refined Pin Images -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem front_rank (s : Plan p n) : planRank (front s) ≤2*planRank s := by
  classical
  unfold planRank
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hh (j) :
      dim ((sPin s i j).map (IP p n j).mulVecLin)≤dim (s i) :=
    (Submodule.finrank_map_le ..).trans (sPin_dim ..)
  exact ((Submodule.finrank_add_le_finrank_add_finrank ..).trans (add_le_add (hh _) (hh _))).trans_eq
    (two_mul _).symm

theorem combined_rank (s t : Plan p n) : planRank (s⊔t)≤planRank s+planRank t := by
  unfold planRank; rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => finrank_add_le_finrank_add_finrank ..

private theorem storyOk (T : Cov p N) (m : BMark p n N)
    (a : Pin p n N) (S : CTile p n N) (K : ℕ) (hk : planRank a.sp≤K)
    (h : ∀ x∈S, a.agree x ∧ covered p T (delta m x) ∧
       ∀ i,m x i∈effective a.sp i) :
    ∀ i : Story T a.sp,∃ b : Pin p n N,
       (∀ x∈ S,story T a.sp m x=i → b.agree x) ∧ planRank b.sp ≤ 3*K ∧
       ∀ c (G : CTile p n N), G.Nonempty →
         (∀ x∈G,x∈S ∧ story T a.sp m x=i) → b.sp ≤ c.sp → specialLeaf T m a G c := by
  classical
  intro i
  let A := a.sp ⊔ front a.sp
  have hK : planRank A≤3*K := by
    apply (combined_rank ..).trans
    have hh := front_rank a.sp
    omega
  have h1 : ∃ x : UnitType p n N, ∀ y∈ S,story T a.sp m y=i → (Pin.make A x).agree y := by
    by_cases hg : ∃ x∈S,story T a.sp m x=i
    · obtain ⟨x,hx,he⟩ := hg
      refine ⟨x,fun y hy ht => ?_⟩
      let b := Pin.make (front a.sp) x
      have hf : b.agree y := by
        rw [Pin.agree_pack]; intro z
        have hh : readPin y (front a.sp)=readPin x (front a.sp) :=
          congrArg (fun x : Story T a.sp => x.2.1) (ht.trans he.symm)
        exact congr_fun hh z
      exact (Pin.combine (b:=b) (h x hx).1 (show b.agree x from fun _ _ _ => rfl)).mpr
        ⟨(h y hy).1,hf⟩
    exact ⟨0,fun x hx he => (hg ⟨x,hx,he⟩).elim⟩
  obtain ⟨x,hx⟩ := h1
  refine ⟨Pin.make A x,hx,hK,fun c G hm hC hA => ⟨le_trans le_sup_left hA,
    le_trans le_sup_right hA, fun x hx y hy => ?_⟩⟩
  have he := (hC x hx).2.trans (hC y hy).2.symm
  have hD := congrArg Prod.fst he
  have hr z (hz : z∈G) : (story T a.sp m z).1.1.val=delta m z := by
    unfold story daypair; change (cutDown p T (delta m) (fun _ => 1) z).val=_
    unfold cutDown; rw [dite_eq_left ⟨(by norm_num),(h z (hC z hz).1).2.1⟩]
  have ht z (hz : z∈G) (i) : ((story T a.sp m z).2.2 i).val=m z i := by
    unfold story entrySeq; dsimp only
    rw [dite_eq_left ((h z (hC z hz).1).2.2 i)]
  refine ⟨funext (fun i => ?_),?_,fun i => ?_⟩
  · rw [←ht x hx i,←ht y hy i,he]
  · rw [←hr x hx, ←hr y hy,he]
  exact congr_fun (congrArg Prod.snd hD) i

theorem story_size (T : Cov p N) (s : Plan p n) (K d : ℕ)
    (hK : planRank s≤K) (hd : cdim p T≤d) :
    num (Story T s) ≤ bp ((3*d+2*K : ℝ)*N + 2*K^2) := by
  classical
  have h1 : dim (coverX p T)≤ N*d := (cover_dim p T).trans (Nat.mul_le_mul_left N hd)
  have h2 : dim (Daypair p T) ≤ 3*d*N := by
    unfold dim Daypair
    rw [finrank_prod,finrank_pi_fintype, Fintype.sum_bool,Subspace.dual_finrank_eq]
    change dim _+(dim _+dim _) ≤ _
    nlinarith
  have h3 : dim (Signal p N (front s)) ≤ (2*K)*N := tuple_dim.trans_le (by
    rw [mul_comm]; apply Nat.mul_le_mul_right
    exact (front_rank s).trans (Nat.mul_le_mul_left _ hK))
  have h4 : dim (EffSeq s)≤ 2*K^2 := by
    unfold EffSeq dim
    rw [finrank_pi_fintype,Fintype.sum_bool,two_mul]
    have hh i : dim (effective s i) ≤ K^2 := (effective_dim ..).trans (by gcongr)
    exact add_le_add (hh _) (hh _)
  unfold num
  rw [card_space]
  apply bp_le
  have hh : dim (Story T s)≤ (3*d+2*K)*N+2*K^2 := by
    unfold Story dim; rw [finrank_prod, finrank_prod (M:=Signal p N (front s))]
    change dim (Daypair p T)+(dim (Signal p N (front s))+dim (EffSeq s)) ≤ _
    rw [Nat.add_mul,add_assoc]
    exact add_le_add h2 (add_le_add h3 h4)
  exact_mod_cast hh

theorem plan_inc_eff (s t : Plan p n) (h : s ≤ t) (i : Bool) :
    effective s i≤effective t i := by
  intro x hx
  obtain ⟨h1,h2⟩ := effective_mem.mp hx
  have he z : sPin s z i ≤ sPin t z i := Submodule.map_mono (h z)
  exact effective_mem.mpr ⟨h1,fun z => box_le (he _) (he _) (h2 _)⟩

set_option maxHeartbeats 900000 in
theorem weave (P : UnitType p n N→Prop)
    {w μ : Wgt (UnitType p n N)}
    (m : BMark p n N) (T : Cov p N)
    (hw : ∀ x,0≤w x) {D ζ u : ℝ} (hz : 0 < ζ) (hz' : ζ<1) {K K' d : ℕ}
    (hn : 0<N)
    (hμ : ∀ a : Pin p n N,pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hd : cdim p T≤d)
    {F : Canopy p n N} (hT : apart F) (g : CTile p n N → Pin p n N)
    (h : ∀ i∈F,Ripe p w μ i (g i) D ζ K)
    (hg : ∀ i∈ F,∀ x∈i,P x→covered p T (delta m x) ∧ ∀ j,m x j∈effective (g i).sp j)
    (hk : D+u+ζ≤(ζ-ζ/4)*K')
    (hu : (3*d+2*K:ℝ)*N+2*K^2 ≤ (u-1)*N) :
    ∃ V : Canopy p n N,apart V ∧
    (∀ S∈V,∃ i∈F,S⊆i ∧ (∀ x∈ S,P x) ∧
      ∃ b : Pin p n N,Ripe p w μ S b (D+u+K'+1) ζ (3*K+K') ∧ specialLeaf T m (g i) S b) ∧
    pr w (fun x => inTiles F x ∧ P x ∧ ¬inTiles V x) ≤
      allMass w F*(bp (-(N:ℝ))+bp (-ζ*N)) := by
  classical
  refine improve F w hw P
    (fun i S => (∀ x∈ S,P x) ∧ ∃ b : Pin p n N,Ripe p w μ S b (D+u+K'+1) ζ (3*K+K') ∧
      specialLeaf T m (g i) S b)
    hT (fun i hi => ?_)
  let A := CTile p n N
  let S := i.filter P
  let Q := specialLeaf T m (g i)
  have hs (x : UnitType p n N) : x∈S↔ x∈i∧ P x := Finset.mem_filter
  have hq := h i hi
  let w' := partW w i
  have hw' : IsLaw w' := on_law hw hq.pos
  have hg : ∀ x∈ S,(g i).agree x∧ covered p T (delta m x)∧∀ j,m x j∈effective (g i).sp j :=
    fun x h => ⟨hq.fixpin _ ((hs ..).mp h).1,hg i hi x ((hs ..).mp h).1 ((hs ..).mp h).2⟩
  obtain ⟨V,hV,hX,hZ⟩ := reparts w' μ hw' S D ζ u hn hz hz' hμ hq.density
    (story T (g i).sp m) (3*K) K' Q
    (storyOk T m (g i) S K hq.bound hg) hk
  refine ⟨V,hV,fun x hx => ?_,?_⟩
  · obtain ⟨hS,b,hB,hL⟩ := hX x hx
    have hx' : x⊆i := hS.trans (Finset.filter_subset ..)
    obtain ⟨he,hLaw⟩ := issued_law w hw hq.pos hx' hB.pos
    refine ⟨hx', (fun z hz => ((hs ..).mp (hS hz)).2),b,⟨he,hB.fixpin,hB.bound,?_,?_⟩,hL⟩
    · rw [hLaw]; exact hB.clear
    rw [hLaw]; exact hB.density
  simp_rw [hs,and_assoc] at hZ
  refine hZ.trans (add_le_add_left ?_ _)
  refine (mul_le_mul_of_nonneg_right (story_size T _ K d hq.bound hd) (bp_pos _).le).trans ?_
  rw [←bp_add]; apply bp_le
  linarith only [hu]

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

theorem slight_gap :
    slight (U : Filter A) x ∨ ∃ δ:ℝ,0<δ∧∀ᶠ n in U, δ < x n := by
  by_cases h : slight (U : Filter A) x
  · exact Or.inl h
  right
  unfold slight at h

  push Not at h
  obtain ⟨δ,hd,h⟩:=h
  exact ⟨δ,hd,h⟩

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
theorem inv_cap (h : warm l z x) : ExpO l z (fun i=> (x i)⁻¹) := by
  intro c hc
  filter_upwards [h c hc] with i hi
  rw [abs_of_nonneg (inv_nonneg.mpr ((bp_pos _).le.trans hi))]
  exact le_trans (inv_anti₀ (bp_pos _) hi) (le_of_eq (by rw [neg_mul,bp_neg,inv_inv]))

theorem survive (hz : Tendsto z l atTop) (h : warm l z x) (hg : ExpSmall l z y) :
    warm l z (fun i=> x i - y i) := by
  have he := (hg.mul h.inv_cap).lim hz
  refine ((const hz (by norm_num : 0<(1/2:ℝ))).mul h).mono ?_
  filter_upwards [h.positive,he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with i hi hg
  change y i*(x i)⁻¹<1/2 at hg
  rw [←div_eq_mul_inv] at hg
  linarith only [(div_lt_iff₀ hi).mp hg]
end warm

namespace ExpSmall
theorem bp_n {c : ℝ} (hc : 0 < c) : ExpSmall l z (fun n=>bp (-c*z n)) :=
  ⟨_,hc,.of_forall (fun _ => (abs_of_pos (bp_pos _)).le)⟩

theorem poly (hz : Tendsto z l atTop) (hx : ExpSmall l z x) (k : ℕ) :
    ExpSmall l z (fun n=>x n*(z n)^k) := by
  refine hx.mul (fun ε he => ?_)
  have hp : ∀ᶠ n in l, 1*(z n)^(k:ℝ)< bp (ε*z n) :=
    hz.eventually (bp_poly_dom he _ _)
  filter_upwards [hp,hz.eventually (eventually_ge_atTop 0)] with n hn h
  rw [abs_of_nonneg (pow_nonneg h _),←Real.rpow_natCast]
  simpa only [one_mul] using hn.le

end ExpSmall

theorem taking {X : A→ Type*} [∀ n,Nonempty (X n)]
    {P : ∀ n,X n→Prop} (h : ∀ᶠ n in l,∃ w:X n,P n w) :
    ∃ w:∀ n,X n,∀ᶠ n in l,P n (w n) := by
  classical
  let f n:= if h:∃ w,P n w then h.choose else Classical.choice (inferInstance:Nonempty (X n))
  refine ⟨f,h.mono (fun n hn=>?_)⟩
  unfold f; rw [dite_eq_left hn]; exact hn.choose_spec

theorem diagonal_gains (l : Filter ℕ) (h : l ≤ atTop) (P : ℕ → ℕ→Prop)
    (hp : ∀ k,∀ᶠ n in l,P n k) :
    ∃ k:ℕ→ℕ,Tendsto k l atTop∧∀ᶠ n in l,P n (k n) := by
  classical
  let a (n : ℕ) : Finset ℕ := (Finset.range (n+1)).filter (P n)
  let k (n : ℕ) := if h:(a n).Nonempty then (a n).max' h else 0
  have he (n r : ℕ) (hr : r≤n) (hc : P n r) : P n (k n) ∧ r≤k n := by
    have hx : r∈a n := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    unfold k; rw [dite_eq_left ⟨r,hx⟩]
    exact ⟨(mem_filter.mp (Finset.max'_mem _ _)).2,Finset.le_max' _ _ hx⟩
  have heq r : ∀ᶠ n in l,P n (k n) ∧ r≤ k n :=
    (hp r).and ((eventually_ge_atTop r).filter_mono h) |>.mono (fun n ⟨hh,hx⟩=>he n r hx hh)
  exact ⟨k,tendsto_atTop.mpr (fun b=> (heq b).mono fun _=> And.right),(heq 0).mono fun _=> And.left⟩

theorem slight_inv_stage {f : ℕ→ℕ} {l : Filter ℕ} (hf : Tendsto f l atTop) :
    slight l (fun i=> ((f i:ℝ)+1)⁻¹) := by
  have h : Tendsto (fun i => (f i:ℝ)+1) l atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hf)
  intro ε he
  exact (h.inv_tendsto_atTop.eventually (gt_mem_nhds he)).mono fun n hn=>hn.le

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseClassCompatibility
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Class Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace PredictionClass
theorem meet (c : PredictionClass) (α : Party) (x : F) : ∃ v,c.compatible α x v := by
  cases c
  · exact ⟨_,rfl⟩
  · rename_i i; exact ⟨(0,fun _=>firstBit α i),zero_add _⟩
  · exact ⟨0, by simp [compatible]⟩
  exact ⟨0,trivial⟩
end PredictionClass

open PredictionClass

theorem lone (p : Shape) {n N} (x : UnitType p n N) (i : Bool) (v : Ambient p N) :
    tone p x (unary i) v= ufun (onSide x i) v := by
  classical
  unfold tone joinPhase unary; rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,one_smul]
    rw [show onSide (listens p x) i=hcube p (onSide x i) from by cases i<;>rfl, phase_actual]
  · intro j _ h; simp [h]
  simp

theorem exactInner (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (h : exactInk p m z x) :
    ∀ i, ∀ v∈Xspace p n,innerP p x i v = grad m (z x i) v := by
  intro i v hv
  have he := h i v hv
  change innerP p x i v+(Tsym m (z x i) v +1*role p n v)=0 at he
  rw [one_mul,add_comm (Tsym m (z x i) v),← grad_val] at he
  exact add_right_cancel (he.trans (char_two _).symm)

theorem diag_dusk (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (hx : ∀ i,z x i∈Xspace p n)
    (h : exactInk p m z x) (hi : ∀ i,frameLaw m (onSide x i)) :
    tone p x allSide (delta z x)=0 := by
  have he (i) : innerP p x i (z x i)=0 := by
    rw [exactInner m z x h _ _ (hx i),grad_val,T_diag,char_two]
  have he1 : ufun x.1 (mrAmbient z x false)=0 := he false
  have he2 : ufun x.2 (mrAmbient z x true)=0 := he true
  rw [tone_vec]
  unfold dotProduct; simp_rw [Fintype.sum_bool,allSide,one_mul,lone,delta,map_add]
  have h1 : ufun x.1 (mrAmbient z x true)=0 := ufun_self (hi true) _
  have h2 : ufun x.2 (mrAmbient z x false)=0 := ufun_self (hi false) _
  simp [onSide,h1,h2,he1,he2]

theorem tiny_morn (p : Shape) {n N : ℕ} (Δ : UnitType p n N→Ambient p N)
    (w : Wgt (UnitType p n N)) (hw : IsLaw w) (d : ℕ) (h : tonalTiny p Δ w d)
    (hN : bp (-0.24*N) < 0.1) (α r i) :
    0.4 ≤ pr (pairW w w) (matchUp Δ α r (dawn i)) := by
  classical
  obtain ⟨_,_,_,hx⟩:= h
  have hi : |pitch p Δ w (unary i) (unary i)| ≤0.1 := (hx i _).trans hN.le
  let P := matchUp Δ α r (dawn i)
  let v := firstBit α i
  let x (x : UnitType p n N×UnitType p n N) :=
    tone p x.1 (unary i) (Δ x.2)+tone p x.2 (unary i) (Δ x.1)
  let C:=pairW w w
  have he (j) : P j ↔ x j = v := by
    unfold P matchUp compatible quench x v; simp only [add_comm]
  have hU : pr C P=(1/2)*(avg C (fun _=>1)+wsign v * avg C (fun i=> wsign (x i))) := by
    unfold pr
    rw [←avg_mul',←avg_add,←avg_mul']
    apply avg_congr
    intro i _
    rcases bit_cases v with h|h<;> rcases bit_cases (x i) with hx|hx <;> norm_num [he,h,hx,ind]
  have hz := abs_le.mp hi
  change |avg C (fun i=> wsign (x i))| ≤_ at hi
  change _≤pr C P
  rw [hU,(pairW_law hw hw).avg_const]
  rcases bit_cases v with h|h <;> rw [h] <;> simp only [wsign_zero, wsign_one,one_mul,neg_mul] <;>
    linarith only [(abs_le.mp hi).1,(abs_le.mp hi).2]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoverAlternatives
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cover Alternatives -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Filter
open scoped BigOperators Topology
open PredictionClass
variable {p : Shape} {n N M : ℕ}
theorem longStory (T : Cov p N) (d : ℕ) (hd : cdim p T≤d)
    (c : PredictionClass) (α : Party) (r : F) (Δ : UnitType p n N → Ambient p N)
    (w : Wgt (UnitType p n N)) (hh : ∀ x,w x≠ 0 → covered p T (Δ x)) :
    ∃ P : UnitType p n N×UnitType p n N→Prop,named P (bp (3*d*(N:ℝ))) ∧
      named (P ∘ Prod.swap) (bp (3*d*(N:ℝ))) ∧
      ∀ x,pairW w w x≠0→ (P x↔ matchUp Δ α r c x) := by
  classical
  let Q (x : Daypair p T×Daypair p T) : Prop :=
    c.compatible α r (fun i=>x.2.2 i x.1.1, fun i => x.1.2 i x.2.1)
  let f := daypair p T Δ w
  refine ⟨fun x=>Q (f x.1,f x.2),day_named p T Δ w d hd Q,day_named p T Δ w d hd (Q∘Prod.swap),
    fun x hx=>?_⟩
  have hs (x y : UnitType p n N) (hz : w x≠0) (i) :
      (f y).2 i (f x).1=tone p y (unary i) (Δ x) :=
    shadow_valid p T Δ hh x y (unary i) hz
  unfold Q matchUp quench
  dsimp only
  simp_rw [hs _ _ (left_ne_zero_of_mul hx), hs _ _ (right_ne_zero_of_mul hx)]

theorem matSeason (T : Cov p N) (d : ℕ) (hd : cdim p T≤d)
    (α : Party) (r : F) (Δ : UnitType p n N → Ambient p N)
    (w : Wgt (UnitType p n N)) (hh : ∀ x,w x≠ 0 → covered p T (Δ x)) :
    ∃ F : Mat (UnitType p n N) (UnitType p n N), F.rank ≤ 2*d*N ∧
      (∀ x, F x x=0) ∧ ∀ x,pairW w w x≠0→ (F x.1 x.2=0 ↔ matchUp Δ α r twinned x) := by
  let F := circus p T Δ w
  have he : F.rank ≤ N*d := (circus_rank ..).trans (Nat.mul_le_mul_left _ hd)
  refine ⟨F+Fᵀ, (mrk_add_le F Fᵀ).trans ?_,fun x=>char_two _,fun x hx=>?_⟩
  · rw [Matrix.rank_transpose]; nlinarith
  · unfold matchUp compatible quench
    dsimp only; rw [←tone_vec,←tone_vec]
    have h x y (hx : w x ≠ 0) : F x y = tone p y allSide (Δ x) :=
      shadow_valid p T Δ hh x y allSide hx
    change (F x.1 x.2+F x.2 x.1=0) ↔ _
    rw [h _ _ (left_ne_zero_of_mul hx),h _ _ (right_ne_zero_of_mul hx)]

set_option maxHeartbeats 1000000 in
theorem coFiber (l : Filter ℕ) (hz : l≤atTop) {M : ℕ} (hM : 1≤ M) (d : ℕ)
    (p : Shape) (w : ∀ n,Wgt (UnitType p n (M*n)))
    (α : Party) (r : F) (Δ : ∀ n, UnitType p n (M*n) → Ambient p (M*n))
    (h : ∀ᶠ n in l, IsLaw (w n) ∧
       ∃ T : Cov p (M*n),cdim p T≤d∧∀ x,w n x≠0 → covered p T (Δ n x))
    (he : slight l (fun n=>pr (pairW (w n) (w n)) (matchUp (Δ n) α r twinned))) :
    ∃ S : ∀ n, UnitType p n (M*n)→Prop,warm l (fun n=>((M*n:ℕ):ℝ)) (fun n=>pr (w n) (S n)) ∧
      ∀ᶠ n in l, ∀ x,S n x.1 → S n x.2 → matchUp (Δ n) α r twinned x := by
  classical
  let X n:= UnitType p n (M*n)
  let q n:= matchUp (Δ n) α r twinned
  let c (k : ℕ) := ((k:ℝ)+1)⁻¹
  let P n (S : X n→Prop) (k : ℕ) :=
     bp (-(c k)*((M*n:ℕ):ℝ)) ≤ pr (w n) S ∧ ∀ x,S x.1 → S x.2 → q n x
  have hf (k : ℕ) : ∀ᶠ n in l,∃ S : X n→Prop,P n S k := by
    obtain ⟨θ,hθ,hg⟩:= fiber_growth (2*d) (c k) (by unfold c; positivity) (by positivity)
    filter_upwards [h,he θ hθ, (trend_sizes l hz hM).1.eventually hg] with n hn hh hF
    obtain ⟨hv,T,hT,h⟩:=hn
    obtain ⟨F,hf,hz,hc⟩:= matSeason T d hT α r (Δ n) (w n) h
    have ht : pr (pairW (w n) (w n)) (fun x => F x.1 x.2=0) ≤ θ :=
      (avg_congr (fun x hx => show ind _=ind _ from congrArg ind (propext (hc x hx)))).trans_le hh
    have hr : (F.rank:ℝ)≤ 2*d*(M*n:ℕ) := by exact_mod_cast hf
    obtain ⟨S,hS,ht⟩:= hF (X n) F (w n) hv hr hz ht
    let Y (x:X n) := S x∧ w n x≠0
    have he : pr (w n) Y=pr (w n) S := avg_congr (fun x hx=>by simp [Y, hx])
    refine ⟨Y, hS.trans_eq he.symm, fun x hx hy =>
      (hc x (mul_ne_zero hx.2 hy.2)).mp (ht x.1 hx.1 x.2 hy.1)⟩
  obtain ⟨k,hk,hf⟩:= diagonal_gains l hz (fun n k => ∃ S : X n→Prop,P n S k) hf
  obtain ⟨S,h⟩:= taking hf
  refine ⟨S,fun ε he=>?_, h.mono fun i hi=>hi.2⟩
  filter_upwards [h,slight_inv_stage hk ε he] with n hn hh
  exact (bp_le (mul_le_mul_of_nonneg_right (neg_le_neg hh) (Nat.cast_nonneg _))).trans hn.1
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PartitionDeletionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partition Deletion Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Filter Finset

variable {A B : Type} [Fintype A] {w : Wgt A}

/-- power lost on further restriction: measure removed at most error and
including normalization does not hurt the lower bound. -/
theorem joint_trim (hw : IsLaw w) (Q : A→Prop) (hq : 0<pr w Q)
    (P : A×A→Prop) :
    pr (pairW w w) P - 2*pr w (fun x=>¬Q x) ≤ pr (pairW (onW w Q) (onW w Q)) P := by
  classical
  let v:=pairW w w; let u:= onW w Q; let Z (x : A×A) := Q x.1 ∧ Q x.2
  have hv := pairW_law hw hw
  have h1 : pr v (fun x=>¬Z x) ≤ 2*pr w (fun x=>¬Q x) := by
    let M (x : A×A) := ¬Q x.1; let T (x : A×A) := ¬Q x.2
    have hM : pr v M = pr w (fun x=>¬Q x) := by
      have hh := pairW_pr w w (fun x=>¬Q x) (fun _=>True)
      simpa only [and_true,pr_true,hw.total,mul_one] using hh
    have hT : pr v T = pr w (fun x=>¬Q x) := by
      have hh := pairW_pr w w (fun _=>True) (fun x=>¬Q x)
      simpa only [true_and,pr_true,hw.total,one_mul] using hh
    have hm x : ¬Z x → M x ∨ T x := by unfold M Z T; tauto
    exact ((pr_mono hv.nz hm).trans (pr_or_le hv.nz)).trans_eq
      (by rw [hM,hT,two_mul])
  have h2 :
      pr v (fun x=> P x∧Z x) ≤ pr (pairW u u) P := by
    have hh (i) (hi : Q i) : w i ≤ u i := by
      unfold u; rw [onW_val,ind_one hi,mul_one]
      exact (le_div_iff₀ hq).mpr ((mul_le_mul_of_nonneg_left
        ((pr_le_tot hw.nz).trans hw.total.le) (hw.nz _)).trans_eq (mul_one _))
    unfold pr avg
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp only
    by_cases hi : P i∧Z i
    · rw [ind_one hi,ind_one hi.1,mul_one,mul_one]
      exact mul_le_mul (hh _ hi.2.1) (hh _ hi.2.2) (hw.nz _) ((on_law hw.nz hq).nz _)
    rw [ind_zero hi,mul_zero]
    have huv : IsLaw u:=on_law hw.nz hq
    exact mul_nonneg ((pairW_law huv huv).nz _) (ind_nonneg _)
  exact (sub_le_sub_left h1 _).trans ((pr_shield hv.nz P Z).trans h2)

/-- Compose several restrictions starting from union T.
P marks on prior union. T restrict -> P -> V union subset of P in T;
user-given skip bound in absolute w. -/
theorem equity_trim (hw : ∀ x,0≤w x) (T V : A→Prop) (P : A→Prop)
    (hf : ∀ x,V x → T x∧P x)
    (hT : 0<pr w T) (hP : 0<pr (onW w T) P)
    {δ : ℝ} (hδ : pr w (fun x=>T x ∧ P x ∧ ¬V x) ≤ δ) :
    let W := onW (onW w T) P; let z := pr w T*pr (onW w T) P
    z-δ ≤ pr w V ∧
      (0<pr w V →
         ∀ Q : A×A→Prop,
          pr (pairW W W) Q-2*(δ/z) ≤ pr (pairW (onW w V) (onW w V)) Q) := by
  classical
  let B (x : A) := T x∧P x
  let W := onW w B
  have hz : pr w T*pr (onW w T) P=pr w B :=
    (pr_of_on hw T P).symm
  have hB := hz ▸ mul_pos hT hP
  have hh : pr w B ≤ pr w V+δ := by
    let R x := T x∧P x∧¬V x
    have he x : B x → V x ∨ R x := by unfold B R; tauto
    exact ((pr_mono hw he).trans (pr_or_le hw)).trans (add_le_add_right hδ _)
  dsimp only
  rw [on_both w T P hw hT hP,hz]
  refine ⟨by linarith only [hh],fun hv Q=>?_⟩
  have ht : (fun x=> B x∧V x) = V := by ext x; exact ⟨And.right, fun h=>⟨hf x h,h⟩⟩
  have hu : pr W V=pr w V / pr w B := by unfold W; rw [pr_on,ht]
  have hW : 0<pr W V := hu ▸ div_pos hv hB
  have h1 : onW W V=onW w V := by unfold W; rw [on_both w B V hw hB hW,ht]
  have h2 : pr W (fun x=>¬ V x)≤ δ/pr w B := by
    unfold W; rw [pr_on]
    refine div_le_div_of_nonneg_right ?_ hB.le
    unfold B; simpa only [and_assoc] using hδ
  rw [← h1]
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤2 by norm_num)) _).trans
    (joint_trim (on_law hw hB) V hW Q)

set_option maxHeartbeats 800000 in
theorem vigor_trim {l : Filter ℕ} (z : ℕ→ℝ) (hz : Tendsto z l atTop)
    {A : ℕ→Type} [∀ i,Fintype (A i)]
    (w : ∀ i,Wgt (A i)) (hw : ∀ᶠ i in l,∀ x,0 ≤ w i x)
    (T V P : ∀ i,A i→Prop) {δ : ℕ→ℝ} (hδ : ExpSmall l z δ)
    (hT : warm l z (fun i=>pr (w i) (T i)))
    (hP : warm l z (fun i=>pr (onW (w i) (T i)) (P i)))
    (hf : ∀ᶠ i in l,(∀ x,V i x → T i x ∧ P i x) ∧
       pr (w i) (fun x=>T i x∧ P i x∧¬V i x)≤δ i) :
    warm l z (fun i=>pr (w i) (V i)) ∧ ∃ d : ℕ→ℝ, ExpSmall l z d ∧
      ∀ᶠ i in l, let W:=onW (onW (w i) (T i)) (P i); let X := onW (w i) (V i);
        ∀ Q : A i×A i→Prop, pr (pairW W W) Q - d i ≤ pr (pairW X X) Q := by
  classical
  let c i:=pr (w i) (T i)*pr (onW (w i) (T i)) (P i)
  have hc : warm l z c := hT.mul hP
  let d i:= 2*(δ i / c i)
  have hd : ExpSmall l z d := by
    have hh := (hδ.mul hc.inv_cap).mul (expO_const hz 2)
    unfold d
    rw [show (fun i=>2*(δ i/c i))=(fun i=>δ i*(c i)⁻¹*2) from funext (fun i=>by rw [div_eq_mul_inv,mul_comm])]
    exact hh
  have he :
      ∀ᶠ i in l,c i-δ i≤ pr (w i) (V i) ∧ (0< pr (w i) (V i) →
        ∀ Q:A i × A i→Prop, let W:=onW (onW (w i) (T i)) (P i); let X:=onW (w i) (V i)
        pr (pairW W W) Q-d i≤pr (pairW X X) Q) := by
    filter_upwards [hw,hT.positive,hP.positive,hf] with i hi ht hv hf
    exact equity_trim hi _ _ _ hf.1 ht hv hf.2
  have hV := (hc.survive hz hδ).mono (he.mono (fun i hi=> hi.1))
  exact ⟨hV,d,hd,(he.and hV.positive).mono fun i ⟨hi,hv⟩=>hi.2 hv⟩
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafMixtures
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem poller_eq (s : LeafMixture p n N) (h : apart s.T) {x i} (hi : i∈s.T) (hx : x∈i) :
    s.poller x=s.pin i := by
  classical
  have hc : inTiles s.T x := ⟨_,hi,hx⟩
  unfold poller; rw [dite_eq_left hc,h _ _ hc.choose_spec.1 _ hi hc.choose_spec.2 hx]

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
variable {D E ζ η : ℝ} {K L : ℕ}

theorem root_bound (hh : strength s w μ D ζ K) (x : X p n N) : planRank (s.rooting x) ≤ K := by
  classical
  by_cases hs : inTiles s.T x
  · rw [rooting,poller,dite_eq_left hs]
    exact (hh.leaf _ hs.choose_spec.1).bound
  unfold rooting poller; rw [dite_eq_right hs]
  exact le_of_eq_of_le (Finset.sum_eq_zero (fun i _=>finrank_bot ..)) K.zero_le

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

theorem ancestral {s t : LeafMixture p n N} {P Q}
    (he : elder s t P Q) {x} (h : inTiles t.T x) : inTiles s.T x∧P x := by
  obtain ⟨j,hj,hx⟩ := h
  obtain ⟨i,hi,hs,hp,_⟩ := he j hj
  exact ⟨⟨_,hi,hs hx⟩,hp x hx⟩
theorem elder_trim {s : LeafMixture p n N} (h : strength s w μ D ζ K) (hz : 0≤ζ)
    (hw : IsLaw w) (P : X p n N→Prop) :
    ∃ t : LeafMixture p n N, t.strength w μ (D+ζ) (2*ζ) K ∧
      elder s t P (fun i j=>t.pin i=s.pin j) ∧
      pr w (fun x=>inTiles s.T x∧P x∧¬inTiles t.T x)≤ bp (-ζ*N) := by
  classical
  obtain ⟨T,ht,hg,hf⟩:= trim P hw.nz hz h.part s.pin h.leaf
  let f (i : CTile p n N) := if hi:i∈T then (hg i hi).choose else ∅
  let t : LeafMixture p n N := ⟨T,fun i=>s.pin (f i)⟩
  have he (i : CTile p n N) (hi : i∈T) :
      f i∈s.T ∧ i⊆ f i ∧ Ripe p w μ i (s.pin (f i)) (D+ζ) (2*ζ) K ∧ ∀ x∈i,P x := by
    unfold f; rw [dite_eq_left hi]; exact (hg i hi).choose_spec
  exact ⟨t,⟨ht,fun i hi=>(he i hi).2.2.1⟩,fun i hi=>by
    obtain ⟨h,h1,h2,h3⟩:= he i hi; exact ⟨_,h,h1,h3,rfl⟩,
    hf.trans (by
      have hi : allMass w s.T ≤1 := (pr_le_tot hw.nz).trans hw.total.le
      exact (mul_le_mul_of_nonneg_right hi (bp_pos _).le).trans_eq (one_mul _))⟩

set_option maxHeartbeats 800000 in
theorem elder_weave {s : LeafMixture p n N} (h : strength s w μ D ζ K) (hz : 0<ζ)
    (hw : IsLaw w) (P : X p n N→Prop)
    {u : ℝ} {K' d : ℕ}
    (m : BMark p n N) (T : Cov p N)
    (hz' : ζ<1) (hn : 0<N)
    (hμ : ∀ a : Pin p n N,pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hd : cdim p T≤ d)
    (hg : ∀ i∈s.T,∀ x∈i,P x → covered p T (delta m x) ∧ ∀ j,m x j∈effective (s.pin i).sp j)
    (hk : D+u+ζ≤(ζ-ζ/4)*K')
    (hu : (3*d+2*K:ℝ)*N+2*K^2 ≤ (u-1)*N) :
    ∃ t : LeafMixture p n N, t.strength w μ (D+u+K'+1) ζ (3*K+K') ∧
      elder s t P (fun i j => specialLeaf T m (s.pin j) i (t.pin i)) ∧
      pr w (fun x=>inTiles s.T x∧P x∧¬inTiles t.T x)≤ bp (-(N:ℝ))+bp (-ζ*N) := by
  classical
  obtain ⟨V,hV,hX,hF⟩:= weave P m T hw.nz hz hz' hn hμ hd h.part _ h.leaf hg hk hu
  let R (i j : CTile p n N) b := j∈s.T ∧ i⊆j ∧ (∀ x∈i,P x) ∧
    Ripe p w μ i b (D+u+K'+1) ζ (3*K+K') ∧ specialLeaf T m (s.pin j) i b
  choose f h1 using (show ∀ i: CTile p n N,∃ b,i∈V → ∃ j,R i j b from
    fun i=>by
      by_cases hi : i∈ V
      · obtain ⟨j,hj,hp,hc,b,h⟩:= hX i hi
        exact ⟨b,fun _ => ⟨_,hj,hp,hc,h⟩⟩
      exact ⟨dustPin ..,fun hh=> (hi hh).elim⟩)
  refine ⟨⟨V,f⟩,⟨hV,fun i hi=>?_⟩,fun i hi=>?_,hF.trans (by
    have hh : allMass w s.T ≤1 := (pr_le_tot hw.nz).trans hw.total.le
    exact (mul_le_mul_of_nonneg_right hh (add_nonneg (bp_pos _).le (bp_pos _).le)).trans_eq
      (one_mul _))⟩
  · obtain ⟨_,_,_,_,hh,_⟩:= h1 i hi; exact hh
  obtain ⟨_,h',hx,hy,_,hh⟩:= h1 i hi; exact ⟨_,h',hx,hy,hh⟩

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreparationConditions
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparation Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters

variable {p : Shape} {M n N : ℕ}

theorem gilding (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ)
    (h : IsLaw ((s n).sap (w n))) :
    glow s w b n-gleam s w b n≤gilded s w b n := by
  let G:= matchProg b n
  let Q := secureAt p (s n).rooting
  have ht (x) : G x → (G x∧ Q x) ∨ (G x ∧¬Q x) := by tauto
  have hv := pairW_law h h
  have hx : glow s w b n ≤ gilded s w b n+gleam s w b n :=
    (pr_mono hv.nz ht).trans (pr_or_le hv.nz)
  linarith only [hx]

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreparedOutcomes
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prepared Outcomes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M}

theorem durable.gripped (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) :
    ∀ᶠ n in l,let N:=M*n; let v:=(s n).sap (w n); let x:=(s n).rooting;
    IsLaw v ∧ ∀ P:UnitType p n N×UnitType p n N→Prop, named P (bp (3*q.d*(N:ℝ))) →
      named (P ∘ Prod.swap) (bp (3*q.d*(N:ℝ))) →
    pr (pairW v v) (fun y=>P y∧¬secureAt p x y) ≤
      0.0005* pr (pairW v v) P +edgeError N := by
  let N (n:ℕ):=M*n
  let z (i:ℕ):=((N i):ℝ)
  have hz := (trend_sizes l hl hq.hM).2
  let a := (0.005:ℝ)
  have ha : 0<a:=by norm_num [a]
  filter_upwards [h.mass.inv_cap a ha, expO_const hz q.L a ha, h.shape,hq.wrap.filter_mono hl,
    hw,h.mass.positive] with n hn ht hh hB hW hS
  obtain ⟨h,hF⟩:=hh
  let v:=(s n).sap (w n)
  let C := ((s n).amount (w n))⁻¹
  have hc : 0≤C := (inv_pos_of_pos hS).le
  have hm : IsLaw v:= LeafMixture.sapLaw hS hW.law
  have hg : bySide p v (m n) (shine (N n)) := by
    refine LeafMixture.upperSide hW.border (LeafMixture.upper_sap hW.law hS) hc ?_
    rw [abs_of_nonneg hq.early.hL] at ht
    change |C|≤bp (a*z n) at hn
    rw [abs_of_nonneg hc] at hn
    refine (mul_le_mul hn ht hq.early.hL (bp_pos _).le).trans_eq ?_
    rw [←bp_add]; unfold a shine z; congr 1
    ring
  refine ⟨hm,fun P hp hP=> hB.2.2.2.2 P hp hP v (s n).rooting (m n)
    (LeafMixture.root_bound h) hm hg (fun x hx => ?_)⟩
  exact LeafMixture.in_parent hF (LeafMixture.present hx).1

theorem durable.unconditional (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) :
    ∀ᶠ n in l,let v:=(s n).sap (w n);
      pr (pairW v v) (fun x=>¬secureAt p (s n).rooting x) <0.01 ∧
      0.99 < pr (pairW v v) (secureAt p (s n).rooting) := by
  have he :
      ∀ᶠ n in l,edgeError (M*n)<0.0005 :=
    (((bp_tendsto_zero (by norm_num : 0 < (0.005:ℝ))).comp
      (trend_sizes l hl hq.hM).2).eventually (gt_mem_nhds (by norm_num)))
  filter_upwards [h.gripped hl hq hw,he] with n hn ht
  obtain ⟨hm,hg⟩:=hn
  let v:=(s n).sap (w n)
  let P := secureAt p (s n).rooting
  have hp : 1≤bp (3*q.d*((M*n:ℕ):ℝ)) := by
    rw [←bp_zero]; exact bp_le (by positivity)
  have hx := hg (fun _=>True) (named_true hp) (named_true hp)
  have hv : IsLaw (pairW v v):=pairW_law hm hm
  change pr (pairW v v) (fun x=>True∧¬P x) ≤ 0.0005*pr (pairW v v) (fun _=>True)+ _ at hx
  simp only [true_and,pr_true,hv.total,mul_one] at hx
  have hh : pr (pairW v v) (fun x=>¬P x)<0.01 := by linarith only [hx,ht]
  refine ⟨hh,?_⟩; rw [pr_not,hv.total] at hh
  linarith only [hh]

variable {b : Sketch p M}

theorem durable.kindles (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hf : ∀ᶠ n in l,0.04 ≤ glow s w b n) :
    glowOutcome l p M w s b := by
  refine ⟨0.02, by norm_num,?_⟩
  filter_upwards [h.gripped hl hq hw,h.unconditional hl hq hw,hf] with n hn ht hv
  obtain ⟨hm,_⟩:=hn
  have hi : gleam s w b n <0.01 :=
    lt_of_le_of_lt (pr_mono (pairW_law hm hm).nz (fun i hi=>hi.2)) ht.1
  have hg := gilding s w b n hm
  linarith only [hi,hg,hv]

theorem durable.domeLight (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) (hd : q.domed l s b) :
    ∀ᶠ n in l,gleam s w b n≤0.0005*glow s w b n+edgeError (M*n) := by
  classical
  filter_upwards [h.gripped hl hq hw,hd] with n hn hd
  obtain ⟨T,hT,hC⟩:= hd
  let v:=(s n).sap (w n)
  let P := matchProg b n
  obtain ⟨Q,h1,h2,h3⟩:= longStory T q.d hT b.c b.α b.r (delta (b.m n)) v
    (fun x hx=>LeafMixture.in_parent hC (LeafMixture.present hx).1)
  have hi : pr (pairW v v) Q=glow s w b n := avg_congr
    (fun x hx=> congrArg ind (propext (h3 x hx)))
  have hf : gleam s w b n=pr (pairW v v) (fun y=> Q y∧¬secureAt p (s n).rooting y) :=
    avg_congr (fun x hx=> congrArg ind (propext (and_congr_left fun _=>(h3 x hx).symm)))
  rw [hf,←hi]; exact hn.2 _ h1 h2

theorem durable.domeGlow (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) (hd : q.domed l s b)
    {δ : ℝ} (hδ : 0<δ) (hg : ∀ᶠ n in l,δ ≤ glow s w b n) :
    glowOutcome l p M w s b := by
  have he : ∀ᶠ n in l,edgeError (M*n)<δ/4 := (((bp_tendsto_zero
    (by norm_num : 0<(0.005:ℝ))).comp
    (trend_sizes l hl hq.hM).2).eventually (gt_mem_nhds (by positivity)))
  refine ⟨δ/2,half_pos hδ,?_⟩
  filter_upwards [h.gripped hl hq hw,h.domeLight hl hq hw hd,he,hg] with n hn ht he hg
  have hh := gilding s w b n hn.1
  linarith only [hh,he,hg,hδ,ht]

theorem durable.domeSpark (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hd : b.c=dusk)
    (hb : ∀ᶠ n in l,q.hardened p (M*n) (s n) (b.m n))
    {δ : ℝ} (hδ : 0<δ) (hg : ∀ᶠ n in l,δ/((M*n:ℕ):ℝ)^4 ≤ glow s w b n) :
    q.glimmer l p M w s b := by
  have hB := show q.domed l s b from hb.mono (fun i h => by
    obtain ⟨T,hT,hC,_⟩:=h; exact ⟨T,hT,hC⟩)
  let z n:=((M*n:ℕ):ℝ)
  have hz : Tendsto z l atTop := (trend_sizes l hl hq.hM).2
  have hi : ExpSmall l z (fun n=>edgeError (M*n)*(z n)^4) :=
    (ExpSmall.bp_n (by norm_num)).poly hz 4
  refine ⟨hd,δ,hδ,?_⟩
  filter_upwards [h.domeLight hl hq hw hB,hb,hg,hz.eventually (eventually_gt_atTop 0),
    (hi.lim hz).eventually (gt_mem_nhds (show 0<0.0005*δ from mul_pos (by norm_num) hδ))]
    with n h hb hg he hi
  refine ⟨hb,hg,h.trans ?_⟩
  have hz : edgeError (M*n) ≤ 0.0005*glow s w b n := calc
      _ ≤ 0.0005*δ/(z n)^4 := (le_div_iff₀ (by positivity)).mpr hi.le
      _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hg (by norm_num)
  linarith only [hz]

end PreparationParameters
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

set_option maxHeartbeats 1400000 in
theorem dropHarvest (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) :
    ∃ t : rhythms p M, durable q l p M m w t ∧
      q.bright l p M m t b ∧
      (∀ᶠ n in l,(t n).within (fun x=>inTiles (s n).T x∧P n x)) ∧
      ∃ d,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) d ∧
        ∀ᶠ n in l,charm s w P b n-d n ≤ glow t w b n := by
  classical
  let N (n:ℕ) := M*n; let z n:=((N n):ℝ)
  let Y : Campaign p M := fun n=> inTiles (s n).T
  let E :=fun i=> bp (-q.ζ*z i)
  let R n (t : LeafMixture p n (M*n)) := t.strength (w n) (usual p (m n) (M*n)) (q.leafOld+q.ζ) (2*q.ζ) q.e ∧
    LeafMixture.elder (s n) t (P n) (fun i j=> t.pin i=(s n).pin j) ∧
    pr (w n) (fun x=> Y n x ∧ P n x∧¬inTiles t.T x)≤ E n
  obtain ⟨t,ht⟩ : ∃ t: rhythms p M,∀ᶠ n in l,R n (t n) := by
    refine taking ?_
    filter_upwards [hw,hx] with n hn h
    exact LeafMixture.elder_trim h.strength hq.early.pos.le hn.law _
  have hz := (trend_sizes l hl hq.hM).2
  let Q : Campaign p M := fun n=> inTiles (t n).T
  have ht' (i) : R i (t i) → (∀ x, Q i x → Y i x∧P i x) ∧
      pr (w i) (fun x=>Y i x∧P i x∧¬Q i x)≤E i := fun h=>⟨fun x hx=>LeafMixture.ancestral h.2.1 hx,h.2.2⟩
  obtain ⟨hW,d,hd,hZ⟩:= vigor_trim z hz w (hw.mono fun i h=>h.law.nz)
    Y Q P (ExpSmall.bp_n hq.early.pos) (retainInitial hl hq hx).mass hb.mass
    (ht.mono (fun i h=> ht' i h))
  have h1 : durable q l p M m w t := by
    refine ⟨hW,?_⟩
    filter_upwards [ht,hx] with n hn h
    refine ⟨hn.1.slide ?_ le_rfl (by unfold pins; omega)
      (fun x=> mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)),fun i hi x hx=>?_⟩
    · unfold leafNew
      linarith [hq.early.small,(Nat.cast_nonneg q.u : 0≤(q.u:ℝ)),(Nat.cast_nonneg q.s : 0≤(q.s:ℝ))]
    obtain ⟨j,hj,hs,_⟩:=hn.2.1 i hi
    exact (h.onTile j hj x (hs hx)).2.2.2
  refine ⟨t,h1,⟨hb.forecast,?_⟩,ht.mono fun i h j hj x hx=> (ht' i h).1 x ⟨j,hj,hx⟩,
    d,hd,hZ.mono (fun i h => h _)⟩
  filter_upwards [ht,hx,hb.mark] with n hn he hm
  intro i hi x hx
  obtain ⟨j,hj,hs,hc,hh⟩:=hn.2.1 i hi
  have hz : (t n).rooting x=(s n).rooting x := by
    unfold LeafMixture.rooting
    rw [LeafMixture.poller_eq (t n) hn.1.part hi hx,LeafMixture.poller_eq (s n) he.strength.part hj (hs hx),
      hh]
  have hH := hm j hj x (hs hx) (hc x hx)
  unfold engrave seems at hH ⊢; rwa [hz]

theorem hideOn (h : nebulous q l s w P b) (hb : q.citable l p M m w s b P)
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n)) :
    ∀ᶠ n in l,∃ T : Cov p (M*n),cdim p T≤q.d∧∀ i ∈ (s n).T,
       ∀ x∈i,P n x→covered p T (delta (b.m n) x) := by
  classical
  filter_upwards [hb.mass.positive,hx,h] with n hn h ht
  obtain ⟨T,hT,hc⟩:=ht
  refine ⟨T,hT,fun i hi x hx hp=> hc _ ?_⟩
  have hh := (h.onTile i hi x hx).1
  unfold potion
  have hm : 0< (s n).amount (w n) := lt_of_lt_of_le (by norm_num) h.weight
  have hv : (s n).sap (w n) x≠0 := by
    unfold LeafMixture.sap allW
    rw [onW_val,ind_one (show inTiles (s n).T x from ⟨i,hi,hx⟩),mul_one]
    exact div_ne_zero hh hm.ne'
  rw [onW_val,ind_one hp,mul_one]; exact div_ne_zero hv hn.ne'

set_option maxHeartbeats 1800000 in
theorem pressHarvest (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hc : q.nebulous l s w P b) :
    ∃ t : rhythms p M, durable q l p M m w t ∧
      q.bright l p M m t b ∧
      (∀ᶠ n in l,q.hardened p (M*n) (t n) (b.m n)) ∧
      ∃ d,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) d ∧
        ∀ᶠ n in l,charm s w P b n-d n ≤ glow t w b n := by
  classical
  let N (n:ℕ) := M*n; let z (n:ℕ):=((N n):ℝ)
  let Y : Campaign p M := fun n=> inTiles (s n).T
  let E := fun i => bp (-(z i)) + bp (-q.ζ*z i)
  let R n (t : LeafMixture p n (M*n)) := t.strength (w n) (usual p (m n) (M*n))
    (q.leafOld+q.u+q.s+1) q.ζ q.pins ∧ pr (w n) (fun x=> Y n x ∧ P n x∧¬inTiles t.T x)≤ E n ∧
    ∃ T:Cov p (M*n), cdim p T ≤q.d ∧
        (∀ i∈(s n).T,∀ x∈i,P n x → covered p T (delta (b.m n) x)) ∧
        LeafMixture.elder (s n) t (P n)
         (fun i j=> specialLeaf T (b.m n) ((s n).pin j) i (t.pin i))
  obtain ⟨t,ht⟩ : ∃ t: rhythms p M,∀ᶠ n in l,R n (t n) := by
    refine taking ?_
    filter_upwards [hw,hx,hideOn hc hb hx,hq.wrap.filter_mono hl,
      ((trend_sizes l hl hq.hM).1.eventually (eventually_gt_atTop 0)),hb.mark]
      with n hn h ht hZ hN hh
    obtain ⟨T,hT,hL⟩:=ht
    have he := hq.early
    have hf (i) (hi:i∈(s n).T) (x) (hx:x∈i) (hp:P n x) j :
       b.m n x j∈effective ((s n).pin i).sp j := by
      have hz : (s n).rooting x=((s n).pin i).sp :=
        congrArg Pin.sp (LeafMixture.poller_eq (s n) h.strength.part hi hx)
      rw [←hz]; exact (((hh i hi x hx hp).1.1 j).2)
    obtain ⟨t,h1,h2,h3⟩ := LeafMixture.elder_weave h.strength he.pos hn.law (P n) (b.m n) T
      he.small hN (hZ.2.2.1 _) hT (fun i hi x hx hp=> ⟨hL i hi x hx hp,hf i hi x hx hp⟩)
      he.bigS hZ.2.1
    exact ⟨t,h1,h3,T,hT,hL,h2⟩
  have hz : Tendsto z l atTop := (trend_sizes l hl hq.hM).2
  let Q : Campaign p M := fun n=> inTiles (t n).T
  have ht' (i) : R i (t i) → (∀ x, Q i x → Y i x∧P i x) ∧
      pr (w i) (fun x=>Y i x∧P i x∧¬Q i x)≤E i := by
    rintro ⟨h,h',T,hi,hz,hg⟩; exact ⟨fun x hx=> LeafMixture.ancestral hg hx,h'⟩
  have hE : ExpSmall l z E := by
    unfold E
    convert ((ExpSmall.bp_n zero_lt_one).add hz (ExpSmall.bp_n hq.early.pos)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  obtain ⟨hW,d,hd,hZ⟩:= vigor_trim z hz w (hw.mono fun i h=>h.law.nz)
    Y Q P hE (retainInitial hl hq hx).mass hb.mass
    (ht.mono (fun i h=> ht' i h))
  have h1 : durable q l p M m w t := by
    refine ⟨hW,?_⟩
    filter_upwards [ht,hx] with n hn h
    obtain ⟨hi,_,T,hT,hC,hL⟩:=hn
    refine ⟨hi.slide ?_ ?_ le_rfl
      (fun x=> mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)),fun i hi x hx=>?_⟩
    · unfold leafNew; linarith
    · linarith only [hq.early.pos]
    obtain ⟨j,hj,hs,_⟩:=hL i hi
    exact (h.onTile j hj x (hs hx)).2.2.2
  have he (i : ℕ) (h : q.entered p (M*i) (m i) (w i) (s i)) (j) (hj:j∈(s i).T)
      (x) (hx:x∈j) : (s i).rooting x=((s i).pin j).sp :=
    congrArg Pin.sp (LeafMixture.poller_eq (s i) h.strength.part hj hx)
  refine ⟨t,h1,⟨hb.forecast,?_⟩,?_,d,hd,hZ.mono (fun i h=>h _)⟩
  · filter_upwards [ht,hx,hb.mark] with n hn he' hm
    intro i hi x hx
    obtain ⟨hT,_,T,_,_,hL⟩:=hn
    obtain ⟨j,hj,hs,hc,hV⟩:=hL i hi
    have hz : (s n).rooting x≤(t n).rooting x := by
      rw [he n he' j hj x (hs hx),LeafMixture.rooting,LeafMixture.poller_eq (t n) hT.part hi hx]
      exact hV.1
    obtain ⟨⟨hE,hA⟩,he,hy⟩:=hm j hj x (hs hx) (hc x hx)
    exact ⟨⟨fun i=>⟨(hE i).1,plan_inc_eff _ _ hz _ ((hE i).2)⟩,hA⟩,he,hy⟩
  · filter_upwards [ht,hx,hb.mark] with n hn he' hm
    obtain ⟨hT,_,T,hC,hD,hL⟩:=hn
    refine ⟨T,hC,fun i hi x hx=>?_,fun i hi=>?_⟩
    · obtain ⟨j,hj,hS,hE,_⟩:= hL i hi; exact hD j hj x (hS hx) (hE x hx)
    obtain ⟨j,hj,hS,hE,hH⟩:= hL i hi
    refine ⟨(s n).pin j,hH,fun x hx k=> ?_⟩
    rw [←he n he' j hj x (hS hx)]
    exact (((hm j hj x (hS hx) (hE x hx)).1.1 k).2)

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

theorem byTorch (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hc : ∀ᶠ n in l,0.05 ≤ charm s w P b n) :
    satisfied q l p M m w := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= dropHarvest hl hq hw hx hb
  refine ⟨t,hT,Or.inr ⟨b,h1,Or.inl (hT.kindles hl hq hw ?_)⟩⟩
  filter_upwards [hF,hc,(he.lim (trend_sizes l hl hq.hM).2).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 0.01))]
    with n hn ht hv
  linarith only [hn,ht,hv]

theorem byCandle (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) (hn : q.nebulous l s w P b)
    {δ : ℝ} (hδ : 0<δ) (hc : ∀ᶠ n in l, δ ≤ charm s w P b n) :
    satisfied q l p M m w := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= dropHarvest hl hq hw hx hb
  have hk : q.domed l t b := by
    filter_upwards [hideOn hn hb hx,h2] with n hn hz
    obtain ⟨T,hT,hE⟩:=hn
    refine ⟨T,hT,fun i hi x hx=>?_⟩
    obtain ⟨⟨j,hj,hx'⟩,hv⟩:= hz i hi x hx
    exact hE j hj x hx' hv
  refine ⟨t,hT,Or.inr ⟨b,h1,Or.inl (hT.domeGlow hl hq hw hk (half_pos hδ) ?_)⟩⟩
  filter_upwards [hF,hc,(he.lim (trend_sizes l hl hq.hM).2).eventually
    (gt_mem_nhds (half_pos hδ))]
    with n hn ht hv
  linarith only [hn,ht,hv]

theorem byGlitter (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) (hn : q.nebulous l s w P b)
    (hd : b.c=dusk)
    {δ : ℝ} (hδ : 0<δ)
    (hc : ∀ᶠ n in l, δ/((M*n:ℕ):ℝ)^4 ≤ charm s w P b n) :
    satisfied q l p M m w := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= pressHarvest hl hq hw hx hb hn
  let z (n:ℕ):=((M*n:ℕ):ℝ)
  have hz := (trend_sizes l hl hq.hM).2
  have hi : ∀ᶠ n in l,e n * (z n)^4 <δ/2 :=
    ((he.poly hz 4).lim hz).eventually (gt_mem_nhds (half_pos hδ))
  refine ⟨t,hT,Or.inr ⟨b,h1,Or.inr (hT.domeSpark hl hq hw hd h2 (half_pos hδ) ?_)⟩⟩
  filter_upwards [hF,hc,hz.eventually (eventually_gt_atTop 0),hi] with n hn ht hv h'
  have hz : 0< z n := hv
  have he := (lt_div_iff₀ (show 0 < (z n)^4 from by positivity)).mpr h'
  change (δ/2)/(z n)^4 ≤ _
  change δ/(z n)^4 ≤ _ at ht
  rw [show (δ/2)/(z n)^4= (δ/(z n)^4)/2 from by ring] at he ⊢
  linarith only [hn,ht,he]

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

set_option maxHeartbeats 1000000 in
theorem outByMix (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hm : ∀ᶠ n in l, tonalMix p (delta (b.m n)) (potion s w P n)) :
    satisfied q l p M m w := by
  classical
  refine byTorch hl hq hw hx hb ?_
  filter_upwards [hm,hb.on_law hl hq hw hx] with n hn ht
  obtain ⟨v,hv⟩:= meet b.c b.α b.r
  apply (mix_pattern p _ _ ht hn v).le.trans
  refine pr_mono (pairW_law ht ht).nz (fun x h=>?_); unfold matchProg matchUp; rw [h]; exact hv

variable {U : Ultrafilter ℕ}
set_option maxHeartbeats 1400000 in
theorem outByCover (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable (U:Filter ℕ) p M m w s b P)
    (hm : ∀ᶠ n in U, tonalTiny p (delta (b.m n)) (potion s w P n) q.d) :
    satisfied q (U:Filter ℕ) p M m w := by
  classical
  let l:Filter ℕ:=U
  let v:= potion s w P
  have hc : q.nebulous (U:Filter ℕ) s w P b:= hm.mono (fun i h=> by
    obtain ⟨T,h1,h2,h3⟩:= h; exact ⟨T,h1,h2⟩)
  have hv := hb.on_law hl hq hw hx
  cases he : b.c with
  | noon =>
    refine byTorch hl hq hw hx hb ?_
    filter_upwards [hv] with n hn
    change _≤pr (pairW (v n) (v n)) _
    unfold matchProg matchUp; rw [he]
    simp [compatible, (pairW_law hn hn).total, v] <;> norm_num
  | dawn i =>
    let z (n : ℕ):=((M*n:ℕ):ℝ); have hz := (trend_sizes (U:Filter ℕ) hl hq.hM).2
    have ht : ∀ᶠ n in U,bp (-0.24*z n)<0.1 :=
      (((bp_tendsto_zero (by norm_num)).comp hz).eventually (gt_mem_nhds (by norm_num)))
    refine byTorch hl hq hw hx hb ?_
    filter_upwards [hv,ht,hm] with n hn ht hk
    unfold charm matchProg; rw [he]
    exact le_trans (by norm_num) (tiny_morn p _ _ hn q.d hk ht _ _ _)
  | twinned =>
    rcases slight_gap (U:=U) (x:=charm s w P b) with hj|⟨δ,hδ,hj⟩
    · obtain ⟨S,hS,hH⟩:= coFiber (U:Filter ℕ) hl hq.hM q.d p v b.α b.r (fun n=>delta (b.m n))
        (hv.and hc) (by unfold charm matchProg at hj; rwa [he] at hj)
      let X : Campaign p M := fun i x=> P i x∧S i x
      obtain ⟨h1,h2⟩:= citable_interpose hw hx hb hS
      refine byTorch hl hq hw hx (P:=X) (b:=b) h1 ?_
      filter_upwards [h1.on_law hl hq hw hx,h2,hH] with n hn ht hq
      let u := potion s w X n
      have hp : IsLaw (pairW u u) := pairW_law hn hn
      have hz (x) (hx : u x≠0) : S n x := by
        rw [show u=onW (v n) (S n) from ht] at hx
        exact (onW_ne hx).1
      have hi : charm s w X b n = pr (pairW u u) (fun _=> True) := by
        apply avg_congr
        intro x hx
        have hm : matchProg b n x := by
          unfold matchProg; rw [he]
          exact hq x (hz _ (left_ne_zero_of_mul hx)) (hz _ (right_ne_zero_of_mul hx))
        change ind (matchProg b n x)=ind True
        rw [ind_one hm,ind_true]
      rw [hi,pr_true,hp.total]; norm_num
    · exact byCandle hl hq hw hx hb hc hδ (hj.mono fun _ h=>h.le)
  | dusk =>
    obtain ⟨δ,hδ,hH⟩:= eventually_tiny_poll q.d
    refine byGlitter hl hq hw hx hb hc he hδ ?_
    filter_upwards [hx,hv,hm,hb.mark,(trend_sizes (U:Filter ℕ) hl hq.hM).1.eventually hH]
      with n hn ht hv h hH
    apply hH.trans
    unfold charm matchProg matchUp; rw [he]
    refine tiny_poll p _ _ ht hv ?_ b.r
    intro x hx
    obtain ⟨hp,hx⟩:= onW_ne hx
    obtain ⟨⟨i,hi,hx⟩,_⟩:= LeafMixture.present hx
    obtain ⟨⟨hE,h1⟩,h2,h3⟩:= h i hi x hx hp
    exact diag_dusk (m n) (b.m n) x (fun i=> (effective_mem.mp (hE i).2).1) (h3 he)
      (hn.onTile i hi x hx).2.2.2

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionDichotomy
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Dichotomy -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {U : Ultrafilter ℕ} {P : Campaign p M}

theorem eclipse (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n)) :
    q.silenceOutcome (U:Filter ℕ) p M m w s ∨ q.outlook (U:Filter ℕ) p M m w s := by
  classical
  let P (n : ℕ) ε := q.predicts p (M*n) (m n) (s n) (w n) ε
  let c (i:ℕ) := ((i:ℝ)+1)⁻¹
  by_cases he : ∀ k : ℕ,∀ᶠ n in U,P n (c k)
  · obtain ⟨k,h1,h2⟩:= diagonal_gains (U:Filter ℕ) hl (fun i j=>P i (c j)) he
    exact Or.inr ⟨fun i=>c (k i),slight_inv_stage h1,h2⟩
  push Not at he
  obtain ⟨k,hk⟩:=he
  exact Or.inl ⟨c k, by unfold c; positivity,
    hk.and (((retainInitial hl hq hx).unconditional hl hq hw).mono fun i hi=>hi.2)⟩

set_option maxHeartbeats 1000000 in
theorem prepare (U : Ultrafilter ℕ) (hl : (U:Filter ℕ) ≤ atTop) (hq : q.planted p M)
    {s : rhythms p M} (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n)) :
    satisfied q (U:Filter ℕ) p M m w := by
  classical
  rcases eclipse hl hq hw hx with hn|hn
  · exact ⟨s,retainInitial hl hq hx,Or.inl hn⟩
  obtain ⟨b,P,i,hQ,hz⟩:= outlook_to_dose hl hq hw hx hn
  cases i
  · obtain ⟨R,hR,hT⟩:= phaseSplit hl hq hw hx hQ
     (hz.mono fun n hn i hi x h hh ht=> Bool.false_ne_true ((hn x hh).mpr ht))
    rcases Ultrafilter.eventually_or.mp hT with hF|hF
    · exact outByMix hl hq hw hx hR hF
    exact outByCover hl hq hw hx hR hF
  exact phaseAbsent hl hq hw hx hQ (hz.mono fun n hn i hi x h hh=>(hn x hh).mp rfl)
end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counterexamples to Hadwiger's conjecture

The binary frame construction yields arbitrarily large graphs with independence
number at most two and small touching matchings. The matching–minor inequality
then separates their complete-minor order from their ordinary chromatic number.

This formalizes the construction theorem and the ordinary chromatic consequence
in OpenAI, *A counterexample to Hadwiger's conjecture* (September 23, 2026).
-/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset
open scoped BigOperators Topology

variable {p:Shape} {n N M s0 :ℕ} {b: PreparationParameters}
open PreparationParameters

set_option maxHeartbeats 1600000 in
theorem eventual_conflict_lower_bound_oai (h:AnalyticParameters p M b s0) :
    ∀ᶠ n : ℕ in atTop,∀ m:Mixer p n,unaryGood m b.pins s0→binaryGood m→conflictLowerBound p m (M*n) b := by
  classical
  let P:= fun n:ℕ=> ∃ (m:Mixer p n),unaryGood m b.pins s0∧binaryGood m∧
    ∃ w:Wgt (UnitType p n (M*n)), b.nascent p (M*n) w m ∧ carried w (rawHoles m).unit ∧
      conflicted p m (M*n) w
  suffices hf : ¬∃ᶠ n:ℕ in atTop,P n by
    have hx := not_frequently.mp hf
    refine hx.mono (fun n hn m hm hv w hw hx=>?_); by_contra! hT
    exact hn ⟨m,hm,hv,w,hw,hx,hT⟩
  intro hc
  have hn := frequently_iff_neBot.mp hc
  obtain ⟨U,hU⟩:= Filter.exists_ultrafilter_le (atTop⊓principal {n|P n})

  let l:Filter ℕ:= U
  have hl : l≤atTop := hU.trans inf_le_left
  have hr : ∀ᶠ n in l,P n :=
    (show ∀ᶠ n in principal {i|P i},P n from Filter.eventually_principal.mpr fun x hx=>hx).filter_mono
      (hU.trans inf_le_right)
  let (n:ℕ) : Nonempty (Mixer p n) := ⟨⟨0,0,0⟩⟩
  obtain ⟨m,hm⟩ := taking hr
  obtain ⟨w,hw⟩ := taking (hm.mono fun i h=> h.2.2)
  have hF : ∀ᶠ n in l, ∃ s : LeafMixture p n (M*n),b.entered p (M*n) (m n) (w n) s := by
    filter_upwards [hw,h.enter.hF.filter_mono hl] with n hn ht
    exact ht _ _ hn.1 hn.2.1
  obtain ⟨s,hS⟩:= taking hF
  obtain ⟨v,hv,hV⟩:= prepare U hl h.enter.first (hw.mono fun i hi=>hi.1) hS
  refine StatusAnalysis.refuteVeil ⟨h,hl,hv,(hm.and hw).mono fun n ⟨h1,h2⟩=>
    ⟨h2.1,h1.1,h1.2.1,h2.2.2⟩⟩ (show NeBot (U:Filter ℕ) from inferInstance) hV

open HadwigerMatching

end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.eventual_conflict_lower_bound_oai := @OAI.HadwigerCounterexample.eventual_conflict_lower_bound_oai
