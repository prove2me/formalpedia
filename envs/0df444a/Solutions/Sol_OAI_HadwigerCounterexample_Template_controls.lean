-- Prove2me | solution 1 for OAI.HadwigerCounterexample.Template.controls
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:08:10.557051+00:00
-- url     : https://prove2.me/submissions/a6cf1a24-105f-4389-82c2-e2f60022a381

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
import Theorems.Thm_OAI_HadwigerCounterexample_law_peekR

section
-- module Solutions.OAIQ430_HC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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

section Linear

variable {I J K L R S : Type} [Fintype I] [Fintype J]

theorem mpair_outer (M : Mat I J) (x : Vec I) (y : Vec J) :
    mpair M (vecMulVec x y) = evmat M x y := by
  dsimp [mpair,evmat,mulVec,dotProduct,vecMulVec]
  simp only [Finset.mul_sum,mul_left_comm]

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

theorem SubLaw.weight_le_one (hw : SubLaw w) (x) : w x ≤ 1 :=
  (weight_le_tot hw.nz x).trans hw.total

theorem IsLaw.weight_le_one (hw : IsLaw w) (x) : w x ≤ 1 := hw.sub.weight_le_one x

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

theorem semi_avg (w : Wgt A) (k : A → Wgt B) (f : A × B → ℝ) :
    avg (semi w k) f = avg w (fun x => avg (k x) (fun y => f (x,y))) := by
  simp only [avg,semi,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

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
theorem log_bp (x : ℝ) : log (bp x) = x * log 2 := Real.log_rpow (by norm_num) _

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixQuotients
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

theorem evmat_ext {M N : Mat I J} (h : ∀ x y, evmat M x y=evmat N x y) : M=N := by
  classical
  ext i j
  simpa [evmat] using h (Pi.single i 1) (Pi.single j 1)

theorem dot_ext_zero {x : Vec I} (h : ∀ y, dotProduct y x=0) : x=0 := by
  classical funext i
            simpa using h (Pi.single i 1)

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRankCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

private theorem bp_half_le {x a : ℝ} (h : x^2 ≤ bp a) : |x| ≤ bp (a/2) := by
  have hh : bp (a/2)^2 = bp a := by rw [pow_two,←bp_add]; congr 1; ring
  exact le_of_pow_le_pow_left₀ (show (2:ℕ) ≠ 0 by decide) (bp_pos _).le (by rwa [sq_abs,hh])

/-- Correlation with arbitrary bounded unary tests. -/
theorem walsh_bound (b : V →ₗ[F] W →ₗ[F] F) (f : Wgt V) (g : Wgt W)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) :
    |avg unif (fun w => g w * avg unif (fun x => f x*wsign (b x w)))| ≤ bp (-(rk b:ℝ)/2) := by
  classical
  have : Finite (W →ₗ[F] F) := Finite.of_injective _ DFunLike.coe_injective
  let := Fintype.ofFinite (W →ₗ[F] F)
  apply bp_half_le
  let F w := avg unif (fun x => f x*wsign (b x w))
  have h1 :
      avg unif (fun w => g w^2) ≤ 1 := unif_law.avg_le (fun x => by
    have h := abs_le.mp (hg x); nlinarith [h.1,h.2])
  have h2 :
      avg unif (fun w => (F w)^2) ≤ bp (-(rk b:ℝ)) := by
    unfold F; rw [avg_wsq]
    have hx : avg (pairW unif unif) (fun (x : V × V) => ind (b x.1 = b x.2))
        = bp (-(rk b:ℝ)) := by
      rw [pairW_avg]
      have hh x :
          avg unif (fun z => ind (b x = b z)) = bp (-(rk b:ℝ)) := by
        have h' : b x ∈ LinearMap.range b := ⟨x,rfl⟩
        have heq := pr_unif_lin b (b x)
        rw [ind_one h',one_mul] at heq
        change pr unif _ = _
        simp_rw [eq_comm (a:=b x)]
        exact heq
      simp_rw [hh]
      exact unif_law.avg_const _
    rw [← hx]
    refine avg_mono (pairW_law unif_law unif_law).nz fun ⟨x,y⟩ => ?_
    have hh : f x*f y ≤ 1 := by
      have hh := mul_le_mul (hf x) (hf y) (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ))
      rw [← abs_mul,one_mul] at hh
      exact (le_abs_self _).trans hh
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (ind_nonneg (b x=b y))
  apply le_trans (avg_CS unif_law.nz _ F)
  exact (mul_le_mul h1 h2 (avg_nonneg unif_law.nz fun _ => sq_nonneg _) (by norm_num)).trans_eq
    (one_mul _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImageCharacterBounds
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

variable {I J : Type} [Fintype I] [Fintype J]
theorem mpair_nondeg (M : Mat I J) (h : mpair M=0) : M=0 := by
  classical
  apply evmat_ext; intro x y
  rw [←mpair_outer,h]; simp [evmat]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentColumnBatches
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Column Batches -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Finset Function
variable {I G J A B : Type} [Fintype I] [Fintype G] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N : ℕ}

variable {g : Route I G}

theorem law_mergeR (m : Mixer p n) (N : ℕ) :
    mapW (pairW (raw m N) (raw m N)) (mergeR p)=forumLaw m N := by
  classical
  funext x
  rw [mapW_equiv_val,forumLaw,prodW,Fintype.prod_prod_type,Fintype.prod_bool]
  rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BoundedQueryTemplates
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Query Templates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem peek_keys (t : Tagging p I) (v : Volley p n I) (x : UnitType p n N) :
    peekR p (globPort p t v.obj) (nomAsk t v) (nomAsk t v) (mergeR p x) =
      scatter t N (v.keys t x) := by
  apply Prod.ext
  · ext i j; rfl
  · ext i j; rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossPatternCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Pattern Correlation -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Finset Function
variable {p : Shape} {n N : ℕ}
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] [DecidableEq J] in
theorem layer_form (M : Mat I J) (X : PlusRack I N) (Y : PlusRack J N) :
    layerPhase M N X Y=mpair M (Xᵀ*Y) := by
  change (X*M*Yᵀ).trace=(M*(Xᵀ*Y)ᵀ).trace
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,
    ← Matrix.mul_assoc M,Matrix.trace_mul_comm _ X,Matrix.mul_assoc]

omit [DecidableEq I] [DecidableEq J] in
theorem layer_rank (M : Mat I J) (N : ℕ) :
    rk (layerPhase M N)=N*M.rank := by
  classical
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product M
  let t := M.rank
  let P := layerPhase B N
  let X := rmult (Fin N) A
  have h1 : P ∘ₗ X=layerPhase M N := by
    refine LinearMap.ext fun W => ?_
    change mpair ((W*A)*B)=mpair (W*M)
    rw [Matrix.mul_assoc,hM]
  have hp : Injective P := by
    rw [←LinearMap.ker_eq_bot]
    refine le_bot_iff.mp (fun V hV => ?_)
    change mpair (V*B)=0 at hV
    have hg := mpair_nondeg _ hV
    have hh : Injective Bᵀ.mulVec := transpose_surj_iff.mp (by rwa [transpose_transpose])
    obtain ⟨D,hD⟩ := mat_left_inv hh
    have hf : B*Dᵀ=1 := by
      rw [←transpose_transpose B,← transpose_mul,hD,transpose_one]
    have he : V=0 := calc
      V = V*1 := (Matrix.mul_one _).symm
      _ = _ := by rw [←hf,←Matrix.mul_assoc,hg,Matrix.zero_mul]
    rw [he]; exact Submodule.zero_mem _
  have hx : Surjective X := by
    obtain ⟨D,hD⟩ := mat_left_inv hA
    intro v
    exact ⟨v*D,by change v*D*A=v; rw [Matrix.mul_assoc,hD,Matrix.mul_one]⟩
  have hf : rk (P ∘ₗ X)=rk P := by
    unfold rk; rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hx,Submodule.map_top]
  rw [←h1,hf]
  exact (rk_inj.mp hp).trans ((dim_mat _ _).trans (by simp))

omit [DecidableEq J] [DecidableEq K] in
theorem shifted_sub (M : Mat I I) (f : J→I) (g : K→I) (x : PlusRack J N) (y : PlusRack K N) :
    layerPhase M N (upliftR f x) (upliftR g y)=layerPhase (M.submatrix f g) N x y := by
  rw [layer_form,layer_form]
  let X := embedMat f
  let Y := embedMat g
  have he : (upliftR f x)ᵀ* upliftR g y=liftM X Y (xᵀ*y) := by
    simp only [upliftR,transpose_mul,transpose_transpose,liftM_def,X,Y,Matrix.mul_assoc]
  rw [he,mpair_liftM]
  rw [show liftM Xᵀ Yᵀ M=M.submatrix f g from (by
    unfold X Y; rw [liftM_def,transpose_transpose,embedMat_mul,mul_embedMat]; rfl)]

private theorem uniform_shift {A : Type} [AddGroup A] [Fintype A] (f : Wgt A) (x : A) :
    avg unif f=avg unif (fun y => f (y+x)) := by
  let e : A≃ A :=
    { toFun := (·+x)
      invFun := (·-x)
      left_inv a := add_sub_cancel_right ..
      right_inv a := sub_add_cancel .. }
  have h := avg_bij e unif f
  rw [show (fun y => unif (e y))=unif from (by ext; simp [unif_apply])] at h
  exact h.symm

set_option maxHeartbeats 600000 in
theorem layerLeak (M : Mat I I) (f g r : Wgt (Rack I N)) (U : J→I) (V : K→I)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x,|g x|≤1)
    (h1 : ∀ x y, f (x+(0,upliftR V y))=f x)
    (h2 : ∀ x y,g (x+(upliftR U y,0))=g x)
    (h3 : ∀ x y z,r (x+(upliftR U y,upliftR V z))=r x) :
    |avg unif (fun x => phasedBy M x*f x*g x*r x)| ≤
      bp (- (N:ℝ)*(M.submatrix U V).rank / 2) * avg unif (fun x => |r x|) := by
  classical
  let A x := phasedBy M x*f x*g x*r x
  let D : Wgt (PlusRack J N × PlusRack K N) := pairW unif unif
  have hD : IsLaw D := pairW_law unif_law unif_law
  have he :
      avg unif A=avg unif (fun x => avg D (fun q => A (x+pairedShift U V q.1 q.2))) := by
    rw [avg_avg]; refine (hD.avg_const (avg unif A)).symm.trans
      (avg_congr fun q _ => uniform_shift A _)
  let E := bp (- (N:ℝ)*(M.submatrix U V).rank /2)
  let c (x : Rack I N) := layerPhase M N x.1 x.2
  have hQ (x) : |avg D (fun q => A (x+pairedShift U V q.1 q.2))|≤E*|r x| := by
    let S (y : PlusRack J N) := f (x+(upliftR U y,0))*wsign (layerPhase M N (upliftR U y) x.2)
    let T (y : PlusRack K N) := g (x+(0,upliftR V y))*wsign (layerPhase M N x.1 (upliftR V y))
    let L (q : PlusRack J N × PlusRack K N) :=
      S q.1*(T q.2*wsign (layerPhase (M.submatrix U V) N q.1 q.2))
    have hx q : A (x+pairedShift U V q.1 q.2)=L q*(r x*wsign (c x)) := by
      rcases q with ⟨y,z⟩
      let Y := upliftR U y
      let Z := upliftR V z
      have hfg : f (x+(Y,Z))=f (x+(Y,0)) := by
        rw [show x+(Y,Z)=x+(Y,0)+(0,Z) from by
          rw [add_assoc]; apply congrArg
          apply Prod.ext <;> simp,h1]
      have hgg : g (x+(Y,Z))=g (x+(0,Z)) := by
        rw [show x+(Y,Z)=x+(0,Z)+(Y,0) from by
          rw [add_assoc]; apply congrArg
          apply Prod.ext <;> simp,h2]
      unfold A L phasedBy; dsimp only
      change wsign (layerPhase M N (x.1+Y) (x.2+Z))*f (x+(Y,Z))*g (x+(Y,Z))*r (x+(Y,Z))=_
      rw [hfg,hgg,h3]
      unfold S T c
      simp only [map_add,LinearMap.add_apply,wsign_add]
      rw [show layerPhase M N Y Z=_ from shifted_sub M U V y z]
      dsimp only [Y,Z] <;> ring
    have hs x : |S x|≤ 1 := by simpa only [S,abs_mul,wsign_abs,mul_one] using hf _
    have ht x : |T x|≤ 1 := by simpa only [T,abs_mul,wsign_abs,mul_one] using hg _
    have hl : |avg D L|≤ E := by
      unfold D L
      rw [pairW_avg,avg_avg]
      simp_rw [mul_left_comm (S _),avg_mul']
      refine (walsh_bound _ S T hs ht).trans_eq ?_
      unfold E; rw [layer_rank,Nat.cast_mul,neg_mul]
    simp_rw [hx]
    rw [avg_mul,abs_mul,abs_mul,wsign_abs,mul_one]
    exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
  change |avg unif A| ≤_
  rw [he]
  exact ((abs_avg_le unif_law.nz).trans (avg_mono unif_law.nz hQ)).trans_eq (avg_mul' ..)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramCharacterExpansion
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Character Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : ℕ}

theorem vector_expand (x y : Vec I) :
    ind (x=y)=avg unif (fun z => vectorPhase z x*vectorPhase z y) := by
  classical
  have hh (z : Vec I) : vectorPhase z x * vectorPhase z y = wsign (dotL (x+y) z) := by
    unfold vectorPhase
    rw [← wsign_add]
    change _ = wsign (dotProduct _ _)
    rw [dotProduct_comm (x+y),dotProduct_add]
  have hi : dotL (x+y)=0 ↔ x=y := by
    have he : dotL (x+y)=0 ↔ x+y=0 := by
      constructor
      · intro h
        refine dot_ext_zero fun z => ?_
        rw [dotProduct_comm]; exact LinearMap.congr_fun h z
      intro h; rw [h]; exact LinearMap.ext fun z => zero_dotProduct z
    rw [he,←ZModModule.sub_eq_add,sub_eq_zero]
  simp_rw [hh,wsign_lin]
  rw [hi]

variable {E : Rail I}

omit [Fintype I] in
theorem inLedger (E : Rail I) (v : Vec E) : railsM E (ledgerM E v)=v := by
  classical
  funext i; rcases i with ⟨⟨i,j⟩,h⟩
  simp [ledgerM,railsM,h]

omit [Fintype I] in
theorem within_recorded (E : Rail I) (v : Vec E) :
    withinRail (ledgerM E v) E := fun _ _ h => dite_eq_right h

theorem rail_charge (x : Rack I N) (E : Rail I) (v : Vec E) :
    vectorPhase v (railsM E (x.1ᵀ*x.2))=phasedBy (ledgerM E v) x := by
  classical
  unfold vectorPhase phasedBy
  rw [layer_form]
  let A := x.1ᵀ*x.2
  let r (i : I × I) := ledgerM E v i.1 i.2 * A i.1 i.2
  change wsign _ = wsign (∑ i:I,∑ j:I,r (i,j))
  rw [←Fintype.sum_prod_type]
  congr 1
  change ∑ i:E,_ = ∑ i:I × I,r i
  calc (∑ i:E,_) = ∑ i:E, r i.val := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      unfold r
                      rw [show ledgerM E v i.val.1 i.val.2 =v i from congr_fun (inLedger E v) i]
                      rfl
       _ = ∑ i ∈ E,r i := Finset.sum_coe_sort ..
       _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
         rcases i with ⟨i,j⟩
         unfold r
         simp only [ledgerM,Matrix.of_apply,dite_eq_right hi,zero_mul])

theorem rail_expand (x : Rack I N) (E : Rail I) (Z : Vec E) :
    ind (traced x E Z) =
      avg unif (fun v : Vec E => phasedBy (ledgerM E v) x*vectorPhase v Z) := by
  unfold traced
  rw [vector_expand]
  simp_rw [rail_charge]

omit [Fintype J] [DecidableEq I] in
theorem match_crowd (x : Rack I N) (g : Route I J) (A : GeoM g) :
    traced x (crowded g) (directions g A) ↔ gramPart A x := by
  classical
  rw [part_scores]
  constructor
  · intro h i a b
    obtain ⟨a,ha⟩ := a
    obtain ⟨b,hb⟩ := b
    subst i
    let y : crowded g := ⟨(a,b), mem_filter.mpr ⟨mem_univ _, hb.symm⟩⟩
    exact congr_fun h y
  · intro h
    funext i
    exact h _ ⟨_,rfl⟩ ⟨i.val.2,(mem_filter.mp i.property).2.symm⟩

omit [DecidableEq I] in
theorem rail_count (g : Route I J) :
    ((crowded g).card:ℝ)=netSize g := by
  classical
  let E := crowded g
  let e : (Σ j,Port g j × Port g j) ≃ ↑E :=
    { toFun := fun i => ⟨(i.2.1.val,i.2.2.val),mem_filter.mpr ⟨mem_univ _,i.2.1.property.trans
      i.2.2.property.symm⟩⟩
      invFun := fun i => ⟨g i.val.1,⟨_,rfl⟩,⟨i.val.2,(mem_filter.mp i.property).2.symm⟩⟩
      left_inv := by rintro ⟨j,⟨a,ha⟩,⟨b,hb⟩⟩; subst j; rfl
      right_inv i := by rcases i with ⟨⟨i,j⟩,ha⟩; rfl }
  have ht := Fintype.card_congr e
  rw [Fintype.card_coe,Fintype.card_sigma] at ht
  have hx : (crowded g).card=∑ i : J, (Fintype.card (Port g i)*Fintype.card (Port g i)) := by
    rw [ht.symm]; exact Finset.sum_congr rfl fun i _ => Fintype.card_prod ..
  rw [hx,netSize]
  simp only [Nat.cast_sum,Nat.cast_mul,num]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RankSubrectangles
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rank Subrectangles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
theorem basis_subcolumns (A : Mat I J) :
    ∃ f : Fin A.rank→J, Injective (A.submatrix _root_.id f).mulVec := by
  classical
  let M (S : Finset J) := Submodule.span F (A.col '' (S : Set J))
  have hg (S : Finset J) : ∃ T⊆S,M T=M S ∧ T.card=dim (M T) := by
    induction S using Finset.induction with
    | empty =>
      have he : M ∅ = ⊥ := by
        unfold M
        rw [show (A.col '' ((∅ : Finset J) : Set _))=∅ by ext; simp, Submodule.span_empty]
      refine ⟨∅,by simp,rfl,?_⟩; rw [he]; exact (finrank_bot ..).symm
    | insert x S hx ih =>
      obtain ⟨T,hT,hM,hD⟩ := ih
      have he (S : Finset J) :
          M (insert x S)=M S⊔Submodule.span F ({A.col x}:Set _) := by
        unfold M
        rw [← span_union]
        congr 1
        ext; simp [eq_comm]
      rw [he,←hM]
      by_cases h : A.col x∈M T
      · exact ⟨T,hT.trans (Finset.subset_insert _ _),
          (sup_eq_left.mpr (by rwa [Submodule.span_singleton_le_iff_mem])).symm,hD⟩
      refine ⟨insert x T,Finset.insert_subset_insert x hT,he T,?_⟩
      rw [Finset.card_insert_of_notMem (fun v => hx (hT v)), he,hD]
      exact (Submodule.finrank_sup_span_singleton h).symm
  obtain ⟨S,hS,hA,ht⟩ := hg Finset.univ
  have hs : M S=colSp A := by
    rw [hA,colSp, Matrix.range_mulVecLin]; unfold M
    congr 1
    ext x; simp
  have he : S.card=A.rank := by rw [ht,hs,colSp_dim]
  let e := Fintype.equivFinOfCardEq (Fintype.card_coe S |>.trans he)
  let f (x : Fin A.rank) := (e.symm x).val
  have hB : colSp (A.submatrix _root_.id f)=M S := by
    rw [colSp,Matrix.range_mulVecLin]; unfold M
    congr 1
    ext x; constructor
    · rintro ⟨k,rfl⟩; exact ⟨f k,(e.symm k).property,rfl⟩
    · rintro ⟨k,h,rfl⟩
      refine ⟨e ⟨k,h⟩,?_⟩
      have heq : f (e ⟨k,h⟩) = k := by unfold f; rw [Equiv.symm_apply_apply]
      ext; simp [Matrix.col_apply,heq]
  rw [hs] at hB
  refine ⟨f,mrk_inj.mpr ?_⟩
  rw [← colSp_dim,hB,Fintype.card_fin,colSp_dim]

theorem minor_arc (A : Mat I J) :
    ∃ (f : Fin A.rank→ I) (g : Fin A.rank→ J), Injective (A.submatrix f g).mulVec := by
  classical
  let t := A.rank
  obtain ⟨g,hg⟩ := basis_subcolumns A
  let B := A.submatrix _root_.id g
  have he : Bᵀ.rank=t := (Matrix.rank_transpose _).trans ((mrk_inj.mp hg).trans
    (Fintype.card_fin _))
  obtain ⟨f,hf⟩ : ∃ f : Fin t→I,Injective ((Bᵀ.submatrix _root_.id f)).mulVec := by
    have hi := basis_subcolumns Bᵀ
    rwa [he] at hi
  have hh := mrk_inj.mp hf
  refine ⟨f,g,mrk_inj.mpr ?_⟩
  rw [← Matrix.rank_transpose]
  exact hh

private theorem lastCol {t : ℕ} {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Mat I J)
    (f : Fin t→I) (g : Fin t→J) (x : I) (y : J)
    (h : (A.submatrix (Sum.elim f (fun _ : Unit => x))
      (Sum.elim g (fun _ : Unit => y))).rank ≤ t)
    (hb : Injective (A.submatrix f g).mulVec) :
    ∃ z : Vec (Fin t),(A.submatrix f g)*ᵥ z=(fun i => A (f i) y) ∧
      A x y=∑ i,A x (g i)*z i := by
  classical
  let C := A.submatrix (Sum.elim f (fun _ : Unit => x)) (Sum.elim g (fun _ : Unit => y))
  let M := C.submatrix _root_.id (.inl ·)
  have hm : Injective M.mulVec := by
    intro X Y h
    apply hb
    funext i
    exact congr_fun h (.inl i)
  have hM : colSp M ≤ colSp C := by
    rw [colSp,colSp, Matrix.range_mulVecLin,Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro s ⟨i,rfl⟩; exact ⟨.inl i,rfl⟩
  have he : colSp M=colSp C := Submodule.eq_of_le_of_finrank_le hM (by
    have he : dim (colSp M)=t := (mrk_inj.mp hm).trans (Fintype.card_fin _)
    change dim (colSp C) ≤ dim (colSp M)
    rw [he]; exact h)
  obtain ⟨v,hv⟩ := show C.col (.inr ()) ∈ colSp M from he.symm ▸ colSp_mem _
  exact ⟨v,funext (fun i => congr_fun hv (.inl i)),(congr_fun hv (.inr ())).symm⟩

theorem border_same {t : ℕ} (A B : Mat I J) (f : Fin t→I) (g : Fin t→J)
    (x : I) (y : J)
    (h : Injective (A.submatrix f g).mulVec)
    (hx : ∀ i j,A (f i) j=B (f i) j)
    (hy : ∀ i j,A i (g j)=B i (g j))
    (hA : (A.submatrix (Sum.elim f (fun _ : Unit => x))
      (Sum.elim g (fun _ : Unit => y))).rank ≤ t)
    (hB : (B.submatrix (Sum.elim f (fun _ : Unit => x))
      (Sum.elim g (fun _ : Unit => y))).rank ≤ t) :
    A x y=B x y := by
  classical
  have hh : A.submatrix f g=B.submatrix f g := Matrix.ext fun i j => hx i _
  obtain ⟨s,hs,hL⟩ := lastCol A f g x y hA h
  obtain ⟨s',hs',hR⟩ := lastCol B f g x y hB (hh ▸ h)
  obtain rfl : s=s' := h ((show A.submatrix f g *ᵥ s=(fun i => A (f i) y) from hs).trans
    ((funext (fun i => hx i y)).trans (hh ▸ hs'.symm)))
  rw [hL,hR]; simp_rw [hy]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossPatternCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Pattern Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators

variable {I J T L : Type} [Fintype I] [Fintype J] [Fintype T] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq T] [DecidableEq L]

omit [DecidableEq I] [DecidableEq J] in
private theorem peak_bdd (M : Avenue I J) (t : ℕ) (h : arcPeak M t) :
    t≤ Fintype.card (I×J) := by
  obtain ⟨f,g,hg,h⟩ := h
  have hx := ((mrk_inj.mp h).trans (Fintype.card_fin _)).symm
  exact hx.trans_le ((M.rank_submatrix_le f g).trans M.rank_le_card_width)

omit [DecidableEq I] [DecidableEq J] in
theorem real_peak (M : Avenue I J) : arcPeak M (peak M) := by
  classical
  have he : arcPeak M 0 := ⟨Fin.elim0,Fin.elim0,
    fun i => Fin.elim0 i, fun _ _ _ => Subsingleton.elim _ _⟩
  exact Nat.sSup_mem (show Set.Nonempty {t | arcPeak M t} from ⟨0,he⟩)
    ⟨Fintype.card (I×J),fun _ => peak_bdd M _⟩

omit [DecidableEq I] [DecidableEq J] in
theorem peak_le (M : Avenue I J) : peak M ≤ Fintype.card (I×J) :=
  peak_bdd M _ (real_peak M)

omit [DecidableEq I] [DecidableEq J] in
theorem sized_peak (M : Avenue I J) {f : T→I × J} {g : L → I × J}
    (h : disperses f g) : (M.submatrix f g).rank ≤ peak M := by
  classical
  obtain ⟨a,b,hb⟩ := minor_arc (M.submatrix f g)
  let W := {t | arcPeak M t}
  refine le_csSup ⟨Fintype.card (I×J),fun t => peak_bdd M t⟩
    (show (M.submatrix f g).rank∈W from ?_)
  exact ⟨f ∘ a,g ∘ b,fun i j => h _ _,hb⟩

private theorem took_same (A B : Avenue I J) {t : ℕ} (f g : Fin t→ I×J)
    (hA : peak A=t) (hB : peak B=t) (ha : interDraw A) (hb : interDraw B)
    (hd : disperses f g) (hf : Injective (A.submatrix f g).mulVec)
    (hL : ∀ i,took A (f i).1=took B (f i).1)
    (hR : ∀ i,took A (g i).1=took B (g i).1) : A=B := by
  classical
  let touched (x : I) := (∃ i,x=(f i).1)∨∃ i,x=(g i).1
  have he {i : I} (h : touched i) (j : J) (k : I × J) :
      A (i,j) k=B (i,j) k ∧ A k (i,j)=B k (i,j) := by
    have hE : took A i=took B i := by
      rcases h with ⟨i,rfl⟩|⟨i,rfl⟩; exact hL i; exact hR i
    exact ⟨congr_fun (congr_fun (congrArg Prod.fst hE) j) k,
      congr_fun (congr_fun (congrArg Prod.snd hE) j) k⟩
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : i=k
  · subst k; rw [ha,hb]
  by_cases hi : touched i
  · exact (he hi j _).1
  by_cases hj : touched k
  · exact (he hj l _).2
  let u := Sum.elim f (fun _ : Unit => (i,j))
  let v := Sum.elim g (fun _ : Unit => (k,l))
  have ht : disperses u v := by
    rintro (x|x) (y|y) h'
    · exact hd _ _ h'
    · exact hj (Or.inl ⟨_,h'.symm⟩)
    · exact hi (Or.inr ⟨_,h'⟩)
    · exact h h'
  have h1 x y : A (f x) y=B (f x) y :=
    (he (i:=(f x).1) (Or.inl ⟨x,rfl⟩) (f x).2 y).1
  have h2 x y : A x (g y)=B x (g y) :=
    (he (i:=(g y).1) (Or.inr ⟨y,rfl⟩) (g y).2 x).2
  exact border_same A B f g (i,j) (k,l) hf h1 h2 ((sized_peak A ht).trans_eq hA)
    ((sized_peak B ht).trans_eq hB)

private theorem bagCount :
    num (Bag I J) ≤ bp ((1+2*num J)*num I*num J) := by
  classical
  have hA : num (I×J) ≤ bp (num (I×J)) := by
    let K := I×J
    have h : Fintype.card K <2^(Fintype.card K) := Nat.lt_two_pow_self
    unfold num
    rw [bp_nat]
    exact_mod_cast h.le
  have he {I J : Type} [Fintype I] [Fintype J] : num (I×J)=num I*num J := by
    simp only [num,Fintype.card_prod,Nat.cast_mul]
  unfold Bag
  rw [he, he (I:=Incident ..)]
  simp only [Incident,cast_mat]
  calc num (I×J)* _ ≤ bp (num (I×J))* _ :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg (bp_pos _).le (bp_pos _).le)
       _ = _ := by rw [←bp_add,←bp_add,he]; congr 1; ring

set_option maxHeartbeats 800000 in
theorem price_peak (t : ℕ) :
    nbr (fun M : Avenue I J => interDraw M ∧ peak M=t)≤bp (peakExpense I J t) := by
  classical
  let S := {M : Avenue I J // interDraw M ∧ peak M=t}
  have ht (M : S) : arcPeak M.val t := by
    have hf {A : Avenue I J} {t : ℕ} (h : peak A=t) : arcPeak A t := h ▸ real_peak A
    exact hf M.property.2
  choose f g hD hG using ht
  let P := (Fin t → Bag I J) × (Fin t → Bag I J)
  let e : S→P := fun M => (fun i => (f M i,took M.val (f M i).1),
    fun i => (g M i,took M.val (g M i).1))
  have hf : Injective e := by
    intro A B h
    have h1 (i) : (f A i,took A.val (f A i).1)=(f B i,took B.val (f B i).1) :=
      congr_fun (congrArg Prod.fst h) i
    have h2 (i) : (g A i,took A.val (g A i).1)=(g B i,took B.val (g B i).1) :=
      congr_fun (congrArg Prod.snd h) i
    refine Subtype.ext (took_same A.val B.val (f A) (g A) A.property.2 B.property.2
      A.property.1 B.property.1 (hD A) (hG A) (fun i => ?_) (fun i => ?_))
    · have he : took A.val (f A i).1=took B.val (f B i).1 := congrArg Prod.snd (h1 i)
      rwa [← show f A i=f B i from congrArg Prod.fst (h1 i)] at he
    have he : took A.val (g A i).1=took B.val (g B i).1 := congrArg Prod.snd (h2 i)
    rwa [← show g A i=g B i from congrArg Prod.fst (h2 i)] at he
  rw [nbr_eq_card]
  have hZ : (Fintype.card S:ℝ) ≤ Fintype.card P := by exact_mod_cast Fintype.card_le_of_injective e hf
  apply hZ.trans
  apply le_trans ((show (↑(Fintype.card P):ℝ)=num (Bag I J)^t*num (Bag I J)^t by
    simp [P,num]).le)
  let V := ((1+2*num J)*num I*num J)
  have h1 := @bagCount I J _ _ _ _
  have he := pow_le_pow_left₀ (Nat.cast_nonneg _ : 0 ≤ num (Bag I J)) h1 t
  have hz := bp_mul_nat V t
  rw [← hz] at he
  refine (mul_le_mul he he (pow_nonneg (Nat.cast_nonneg _) _) (bp_pos _).le).trans_eq ?_
  rw [←bp_add]; unfold V peakExpense; congr 1; ring

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

omit [Fintype I] [Fintype J] [DecidableEq A] in
theorem heard_fresh {T : A→I × J} {i : I} (B : PlusRack A N) (h : i∉heard T) (j : J) (k) :
    upliftR T B k (i,j)=0 := by
  classical
  unfold upliftR
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  have he : (i,j)≠T x := fun e => h (mem_image.mpr
    ⟨x,mem_univ _, (congrArg Prod.fst e).symm⟩)
  simp [embedMat,he]

omit [Fintype I] [Fintype J] [DecidableEq A] in
private theorem led_off_r (x : Rack (I×J) N) {T : A→I×J} {i : I} (B : PlusRack A N)
    (h : i∉heard T) :
    led i (x+(0,upliftR T B)) = led i x := by
  apply Prod.ext
  · ext; simp [led,sectionR]
  ext
  simp only [led,sectionR,Prod.snd_add,Matrix.add_apply,Matrix.submatrix_apply,
    heard_fresh B h,add_zero]

omit [Fintype I] [Fintype J] [DecidableEq A] in
private theorem led_off_l (x : Rack (I×J) N) {T : A→I×J} {i : I} (B : PlusRack A N)
    (h : i∉heard T) :
    led i (x+(upliftR T B,0)) = led i x := by
  apply Prod.ext
  · ext
    simp only [led,sectionR,Prod.fst_add,Matrix.add_apply,Matrix.submatrix_apply,
      heard_fresh B h,add_zero]
  ext; simp [led,sectionR]

set_option maxHeartbeats 800000 in
theorem light_bound (M : Avenue I J) (P : I→Rack J N→Prop) (u : ℝ) (hu : 0 ≤ u)
    (hp : ∀ i,bp (-u) ≤ pr unif (P i)) :
    |avg unif (fun x => phasedBy M x*phot P x)| ≤
      bp ((-(N:ℝ)/2+2*u)*(peak M:ℝ)) * ∏ i,pr unif (P i) := by
  classical
  obtain ⟨T,U,hTU,hA⟩ := real_peak M
  let t := peak M
  let L := heard T
  let R := heard U
  let D := L∪R
  let S := Finset.univ \ D
  have hd : Disjoint L R := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hy
    exact hTU i j he.symm
  let f (Z : Finset I) (x : Rack (I×J) N) := ∏ i∈Z,ind (P i (led i x))
  have hs (V : Finset I) x : |f V x|=f V x := abs_of_nonneg (Finset.prod_nonneg (fun i _ =>
    ind_nonneg _))
  have heq (V : Finset I) x : |f V x|≤1 := (hs V x).trans_le
    ((Finset.prod_le_prod (fun _ _ => ind_nonneg _) (fun _ _ => ind_le_one _)).trans_eq (by simp))
  have h1 :
      (∏ i,pr unif (P i))=(∏ i∈D,pr unif (P i))*(∏ i∈S,pr unif (P i)) := by
    rw [←Finset.prod_union (show Disjoint D S from disjoint_sdiff),
      Finset.union_sdiff_of_subset (Finset.subset_univ D)]
  have hf x : phot P x=f L x*f R x*f S x := by
    unfold phot f
    rw [←Finset.prod_union hd,←Finset.prod_union (show Disjoint D S from disjoint_sdiff),
      Finset.union_sdiff_of_subset (Finset.subset_univ D)]
  have hl :
      |avg unif (fun x => phasedBy M x*phot P x)| ≤ bp (-(N:ℝ)*t/2) * avg unif (fun x => |f S x|) := by
    have he x : phasedBy M x*phot P x=phasedBy M x*f L x*f R x*f S x := by rw [hf]; ring
    simp_rw [he]
    rw [←show (M.submatrix T U).rank=t from
      (mrk_inj.mp hA).trans (Fintype.card_fin _)]

    refine layerLeak M (f L) (f R) (f S) T U (heq _) (heq _) (fun x y => ?_)
      (fun x y => ?_) (fun x y z => ?_)
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [led_off_r x y (fun h => Finset.disjoint_left.mp hd hi h)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [led_off_l x y (fun h => Finset.disjoint_left.mp hd h hi)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hr := (Finset.mem_sdiff.mp hi).2
      rw [show x+(upliftR T y,upliftR U z)=x+(0,upliftR U z)+(upliftR T y,0) from
        by rw [add_assoc]; apply congrArg; apply Prod.ext <;> simp,
        led_off_l _ y (fun h => hr (mem_union_left _ h)),
        led_off_r _ z (fun h => hr (mem_union_right _ h))]
  apply hl.trans
  simp_rw [hs]
  rw [show avg unif (fun x => f S x)= _ from led_piece S P,h1,← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => pr_nonneg unif_law.nz)
  have hc : D.card ≤ 2*t := by
    apply le_trans (Finset.card_union_le ..)
    have hi (T : Fin t→ I × J) : (heard T).card≤t :=
      Finset.card_image_le.trans_eq (by simp)
    rw [two_mul]; exact add_le_add (hi T) (hi U)
  have hQ : bp (-u*(2*(t:ℝ))) ≤ ∏ i∈D,pr unif (P i) := by
    refine le_trans ?_ (Finset.prod_le_prod (fun i _ => (bp_pos _).le) fun i _ => hp i)
    rw [Finset.prod_const,←bp_mul_nat]
    apply bp_le
    apply mul_le_mul_of_nonpos_left
    · exact_mod_cast hc
    exact neg_nonpos.mpr hu
  calc bp _
    _ = bp ((-(N:ℝ)/2+2*u)*(peak M:ℝ)) * bp (-u*(2*t)) := by rw [←bp_add]; congr 1; unfold t; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ (bp_pos _).le
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RepeatedQueryBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated Query Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

private theorem num_cross_peak (E : Rail (I×J))
    (he : ∀ i∈E,i.1.1≠i.2.1) (t : ℕ) :
    nbr (fun v : Vec E=> peak (ledgerM E v)=t) ≤ bp (peakExpense I J t) := by
  classical
  let Γ := fun M : Avenue I J => interDraw M ∧ peak M=t
  have hh (v) : interDraw (ledgerM E v) := fun i j k => within_recorded E v _ _
    (fun h => he _ h rfl)
  rw [nbr_eq_card]
  apply le_trans _ (price_peak (I:=I) (J:=J) t)
  rw [nbr_eq_card]
  let f (v : {v : Vec E//peak (ledgerM E v)=t}) : { M//Γ M} :=
    ⟨ledgerM E v.val, hh _,v.property⟩
  have h : Injective f := by
    intro v w he
    apply Subtype.ext
    have h : ledgerM E v.val=ledgerM E w.val := congrArg Subtype.val he
    rw [←inLedger E v.val,h,inLedger]
  exact_mod_cast Fintype.card_le_of_injective f h

private theorem peak_sum (E : Rail (I×J))
    (he : ∀ i∈E,i.1.1≠ i.2.1) (u : ℝ)
    (h : peakExpense I J 1+u≤0) :
    ∑ v : Vec E,bp (u*peak (ledgerM E v))≤num (I×J)+1 := by
  classical
  let T := Fintype.card (I×J)
  let f (v : Vec E) : Fin (T+1) :=
     ⟨peak (ledgerM E v), Nat.lt_succ_of_le (peak_le _)⟩
  have hg : ∑ v : Vec E,bp (u*peak (ledgerM E v))=
      ∑ i : Fin (T+1),bp (u*i.val) * nbr (fun v : Vec E => peak (ledgerM E v)=i.val) := by
    unfold nbr tot; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single (f v)]
    · simp only [f,ind_true,mul_one]
    · intro i _ hi; rw [ind_zero (show peak _≠i.val from
        fun h => hi (Fin.ext h.symm)),mul_zero]
    simp
  have hi (i : Fin (T+1)) :
      bp (u*i.val)*nbr (fun v : Vec E=>peak (ledgerM E v)=i.val) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left (num_cross_peak E he i.val) (bp_pos _).le).trans ?_
    rw [←bp_add,←bp_zero]
    apply bp_le
    unfold peakExpense at *
    have h1 := mul_nonpos_of_nonpos_of_nonneg h (Nat.cast_nonneg i.val : 0≤(i.val:ℝ))
    norm_num at h1
    linarith only [h1]
  rw [hg]
  exact (Finset.sum_le_sum fun i _ => hi i).trans_eq (by simp [num,T])

set_option maxHeartbeats 800000 in
theorem cross_flood (E : Rail (I×J)) (Z : Vec E)
    (he : ∀ i∈E,i.1.1≠ i.2.1) (u : ℝ) (hu : 0≤u)
    (P : I → Rack J N → Prop) (hp : ∀ i,bp (-u)≤pr unif (P i))
    (hδ : peakExpense I J 1+(-(N:ℝ)/2+2*u) ≤0) :
    pr unif (fun x => traced x E Z ∧ ∀ i,P i (led i x))≤
      bp (-(E.card:ℝ)) * (num (I×J)+1) *∏ i,pr unif (P i) := by
  classical
  let H := ∏ i,pr unif (P i)
  have hg : 0≤H := Finset.prod_nonneg fun _ _ => pr_nonneg unif_law.nz
  let C : ℝ := -(N:ℝ)/2+2*u
  let F (v : Vec E) :=
    vectorPhase v Z*avg unif (fun x => phasedBy (ledgerM E v) x*phot P x)
  have hh v : F v ≤ bp (C*peak (ledgerM E v))*H := by
    refine (le_abs_self _).trans ?_
    unfold F; rw [abs_mul,vectorPhase,wsign_abs,one_mul]
    exact light_bound _ P u hu hp
  have heq : pr unif (fun x => traced x E Z ∧ ∀ i,P i (led i x))=
      avg unif F := by
    unfold pr F
    simp_rw [ind_and,ind_all,rail_expand,← avg_mul,← avg_mul']
    rw [avg_avg]
    refine avg_congr fun v _ => avg_congr fun x _ => ?_
    unfold phot; ring
  rw [heq]
  refine (avg_mono unif_law.nz hh).trans ?_
  let lamh := bp (-(E.card:ℝ))
  have he' (x : Vec E) :
      unif x=lamh := by rw [unif_apply,card_space,dim_vec,Fintype.card_coe, ← bp_neg]
  simp only [avg,he',← Finset.mul_sum]
  rw [← Finset.sum_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (peak_sum E he _ hδ) hg)
    (bp_pos _).le

omit [Fintype G] in
theorem inside_count (g : Route (I×J) G) :
    (cInside g).card≤ Fintype.card I*Fintype.card J*Fintype.card J := by
  classical
  let f : I×J×J → (I×J)×(I×J) := fun x => ((x.1,x.2.1),(x.1,x.2.2))
  have h : cInside g ⊆ Finset.univ.image f := by
    rintro ⟨⟨x,i⟩,y,j⟩ hv
    obtain rfl : x=y := (mem_filter.mp hv).2
    exact mem_image.mpr ⟨(x,i,j),mem_univ _,rfl⟩
  exact (card_le_card h).trans (card_image_le.trans_eq (by simp [mul_assoc]))

set_option maxHeartbeats 800000 in
theorem many_frames (g : Route (I×J) G) (Z : GeoM g) (hN : ∀ i,2*num (Port g i)-N≤ -1)
    (u : ℝ) (hu : 0≤u) (P : I→Rack J N→Prop) (hp : ∀ i,bp (-u) ≤ pr unif (P i))
    (hd : peakExpense I J 1+ (-(N:ℝ)/2+2*u) ≤0) :
    pr (rackStation Z N) (fun x => ∀ i,P i (led i x))≤
      (4:ℝ)^Fintype.card G * bp (num I * num J * num J) * (num (I×J)+1) *
        ∏ i:I,pr unif (P i) := by
  classical
  let E := crowded g
  let Y := cInside g
  let R := E\Y
  have hn := (net_norm Z N hN).1
  let Z' := directions g Z
  let w (x : R) := Z' ⟨x.val,sdiff_subset x.property⟩
  have hl (x : Rack (I×J) N) (h : gramPart Z x) :
      traced x R w := by
    have he := (match_crowd x g Z).mpr h
    funext i
    exact congr_fun he (⟨i.val,sdiff_subset i.property⟩ : ↑E)
  have he i (h : i∈R) : i.1.1≠ i.2.1 := by
    intro hx
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp h
    exact h2 (Finset.mem_filter.mpr ⟨h1,hx⟩)
  let Q := fun x => ∀ i, P i (led i x)
  let H := ∏ i,pr unif (P i)
  have h0 := netFact_pos (f:=g)
  unfold rackStation
  rw [← on_unif, pr_on]
  have hh : pr unif (fun x => bothPart (N:=N) Z x ∧ Q x) ≤
      pr unif (fun x => traced x R w ∧ Q x) :=
    pr_mono unif_law.nz (fun x h => ⟨hl x ((both_test ..).mp h.1).1,h.2⟩)
  have hf := cross_flood R w he u hu P hp hd
  refine le_trans (div_le_div₀ ((pr_nonneg unif_law.nz).trans hf)
    (hh.trans hf) (inv_pos_of_pos h0) hn) ?_
  let K : ℝ := num (I×J)+1
  have hk : 0 ≤ K := by unfold K num; positivity
  change bp (- (R.card:ℝ)) * K * H / (netFact g)⁻¹ ≤ (4:ℝ)^_ * _ * K * H
  have hY : Y ⊆ E := Finset.filter_subset ..
  have hy : (R.card:ℝ)+(Y.card:ℝ) = netSize g := by
    rw [← rail_count]; exact_mod_cast Finset.card_sdiff_add_card_eq_card hY
  have hY' : (Y.card:ℝ) ≤ num I * num J * num J := by exact_mod_cast inside_count g
  unfold netFact
  have hg : 0 ≤ H := Finset.prod_nonneg fun i _ => pr_nonneg unif_law.nz
  calc _ = (4:ℝ)^Fintype.card G * bp (netSize g- (R.card:ℝ))*K*H := by
            rw [div_eq_mul_inv,inv_inv,bp_sub,bp_neg]; ring
       _ ≤ _ := by gcongr; linarith
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RepeatedBatchLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

/-- pay slack for any fixed multiple of exponentially smaller term. -/
theorem pay_nat {a b : ℝ} (c : ℝ) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,c * bp (-a*n) ≤ bp (-b*n) := by
  have h := (bp_tendsto (sub_pos.mpr hab)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually (eventually_ge_atTop c)] with n hn
  change c ≤ bp ((a-b)*n) at hn
  refine (mul_le_mul_of_nonneg_right hn (bp_pos _).le).trans_eq ?_
  rw [← bp_add, show (a-b)*n + -a*n= -b*n by ring]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Entropy -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Real

variable {α : Type*} [Fintype α]

theorem negEnt_le_zero {w : Wgt α} (hw : SubLaw w) : negEnt w ≤ 0 := by
  refine Finset.sum_nonpos fun x _ => mul_nonpos_of_nonneg_of_nonpos (hw.nz x) ?_
  exact Real.log_nonpos (hw.nz x) (hw.weight_le_one x)

private theorem log_bound {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    x * (1 - Real.log m) - m⁻¹ ≤ x * Real.log x := by
  rcases lt_or_eq_of_le hx with h | h
  · have hp := Real.self_sub_one_le_mul_log (show 0 ≤ m*x from mul_nonneg hm.le hx)
    rw [Real.log_mul hm.ne' h.ne'] at hp
    apply (mul_le_mul_iff_right₀ hm).mp

    have hi := mul_inv_cancel₀ hm.ne'
    nlinarith only [hp, hi]
  · rw [← h]
    have := inv_pos.mpr hm
    linarith

theorem log_card_le_negEnt [Nonempty α] {w : Wgt α} (hw : IsLaw w) :
    -Real.log (Fintype.card α) ≤ negEnt w := by
  let m := (Fintype.card α : ℝ)
  have hm : 0 < m := by simp [m, Fintype.card_pos]
  have h1 :
      ∑ x, (w x * (1 - Real.log m) - m⁻¹) ≤ negEnt w :=
    Finset.sum_le_sum fun x _ => log_bound hm (hw.nz x)
  have hs : ∑ x, w x = 1 := hw.total
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, Finset.sum_const] at h1
  simp only [Finset.card_univ, nsmul_eq_mul] at h1
  change 1 - Real.log m - m * m⁻¹ ≤ _ at h1
  rw [mul_inv_cancel₀ hm.ne'] at h1
  change -Real.log m ≤ _
  linarith

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RelativeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative Entropy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

theorem tension_as_diff (p q : Wgt A) :
    tension p q= negEnt p-avg p (fun x => log (q x)) := avg_sub p _ _

theorem tension_mix {μ : Wgt A} {f : A→Wgt B} (q : Wgt B) :
    avg μ (fun x => tension (f x) q) =
      avg μ (fun x => tension (f x) (mixW μ f))+tension (mixW μ f) q := by
  let u := mixW μ f
  have h (x : A) : tension (f x) q=tension (f x) u+
      avg (f x) (fun i => log (u i)-log (q i)) := by
    simp only [tension_as_diff,avg_sub]
    ring
  simp_rw [h,avg_add,← mixW_avg]; rfl

theorem tension_le_cap {p q : Wgt A} (hp : ∀ i,0 ≤ p i) (hq : ∀ i,0 ≤ q i)
    (C : ℝ) (hc : 0<C) (h : ∀ i,p i≤ C*q i) :
    tension p q≤tot p*log C := by
  rw [←avg_const]
  unfold tension avg
  refine sum_le_sum fun i _ => ?_
  rcases eq_or_lt_of_le (hp i) with h'|h'
  · rw [←h']; simp
  have hqi : q i ≠ 0 :=
    (pos_of_mul_pos_right (h'.trans_le (h i)) hc.le).ne'
  have hg : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
  refine mul_le_mul_of_nonneg_left ?_ h'.le
  change log (p i) - log (q i) ≤ log C
  rw [← Real.log_div h'.ne' hg.ne']
  exact Real.log_le_log (by positivity) ((div_le_iff₀ hg).mpr (h i))

private theorem tension_cell (a b : ℝ) (ha : 0≤a) (hb : 0 ≤ b) (h : a≠0→b≠0) :
    (√a-√b)^2 ≤ a*(log a - log b)+ b - a := by
  rcases eq_or_lt_of_le ha with h'|h'
  · rw [← h']; simp only [sqrt_zero,zero_sub,neg_sq,zero_mul,zero_add,sub_zero]; rw [sq_sqrt hb]
  have hb' := lt_of_le_of_ne hb (Ne.symm (h h'.ne'))
  have hc : 0<√a := by positivity
  have ht := Real.log_le_sub_one_of_pos (x:=√b/√a) (by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hb,Real.log_sqrt ha] at ht
  have hh := mul_le_mul_of_nonneg_right ht ha
  have he : √b/√a*a = √b*√a := by
    field_simp; rw [sq_sqrt ha]
  rw [sub_mul,sub_mul,he] at hh
  nlinarith only [hh,sq_sqrt ha,sq_sqrt hb]

set_option maxHeartbeats 600000 in
theorem var_tension (p q : Wgt A) (hp : IsLaw p) (hq : IsLaw q) (h : lsupp p q) :
    varOne p q ^ 2 ≤ tension p q * 4 := by
  let a (i : A) := |√(p i)-√(q i)|
  let b (i : A) := √(p i)+√(q i)
  have ha : ∑ i, a i ^ 2 ≤ tension p q := by
    have ht (x : A) :
        a x ^2 ≤ p x * (log (p x)-log (q x))+q x-p x := by
      unfold a; rw [sq_abs]; exact tension_cell _ _ (hp.nz _) (hq.nz _) (h _)
    refine (sum_le_sum (fun i (_: i∈univ) => ht i)).trans_eq ?_
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    change _ +tot q-tot p=tension p q
    rw [hp.total,hq.total,add_sub_cancel_right]
    rfl
  have hb : ∑ i,b i^2 ≤ 4 := by
    have ht (x : A) :
        b x ^ 2 ≤ 2*p x+2*q x := by
      unfold b; nlinarith only [sq_sqrt (hp.nz x),sq_sqrt (hq.nz x),
        sq_nonneg (√(p x)-√(q x))]
    refine (sum_le_sum (fun i (_: i∈univ) => ht i)).trans_eq ?_
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    change 2*tot p + 2*tot q = 4
    rw [hp.total,hq.total]
    norm_num
  have h0 : 0≤tension p q := le_trans (sum_nonneg (fun i _ => sq_nonneg _)) ha
  have he : varOne p q = ∑ i, a i * b i := by
    unfold varOne
    refine sum_congr rfl (fun i _ => ?_)
    have hy :
        (√(p i)-√(q i))*b i=p i-q i := by
      unfold b; nlinarith only [sq_sqrt (hp.nz i),sq_sqrt (hq.nz i)]
    rw [← hy,abs_mul,abs_of_nonneg (show 0≤b i from by unfold b; positivity)]
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq ..).trans
    (mul_le_mul ha hb (sum_nonneg (fun i _ => sq_nonneg _)) h0)

theorem tension_nonneg {p q : Wgt A} (hp : IsLaw p) (hq : IsLaw q) (h : lsupp p q) :
    0 ≤ tension p q := by nlinarith only [var_tension p q hp hq h,sq_nonneg (varOne p q)]
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

theorem map_mass (p : Wgt A) (f : A→B) : tot (mapW p f)=tot p := by
  simpa only [avg_const,mul_one] using mapW_avg p f (fun _ => 1)
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

omit [Fintype C] in
theorem map_nested {p : Wgt A} (f : A→B) (g : B→C) :
    mapW (mapW p f) g = mapW p (g ∘ f) := funext fun _ => mapW_pr p f _

omit [Fintype C] in
theorem map_mix (w : Wgt A) (p : A→ Wgt B) (f : B→C) :
    mapW (mixW w p) f = mixW w (fun i => mapW (p i) f) := funext fun _ => mixW_avg ..

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

omit [Fintype B] in
theorem pour_nz {q : Wgt A} {u : Wgt B} (f : A→B)
    (hq : ∀ i,0 ≤ q i) (hu : ∀ i,0 ≤ u i) (i) : 0 ≤ pour q f u i :=
  mul_nonneg (hq i) (div_nonneg (hu _) (map_nz hq f _))

omit [Fintype B] in
theorem bucket_scale (q p : Wgt A) (hq : ∀ i,0≤q i) (h : lsupp p q) (f : A→B) :
    mapW (bucket q f p) f=mapW p f := map_pour q f _ (lsupp.map h hq f)

theorem bucket_law {q p : Wgt A} (hp : IsLaw p)
    (f : A→B) (hq : ∀ i,0≤q i) (h : lsupp p q) :
    IsLaw (bucket q f p) := by
  refine ⟨pour_nz f hq (map_nz hp.nz f),?_⟩
  rw [←map_mass _ f,bucket_scale q p hq h,map_mass,hp.total]

omit [Fintype B] in
theorem lsupp_bucket {p q : Wgt A} (f : A → B) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i,0 ≤ q i) (h : lsupp p q) : lsupp p (bucket q f p) :=
  fun x hx => mul_ne_zero (h x hx) (div_ne_zero (lsupp_hit hp f x hx) (lsupp_hit hq f x (h x hx)))

omit [Fintype C] in
theorem bucket_nested (q p : Wgt A) (f : A→B) (g : B→C) :
    mapW (bucket q (g ∘ f) p) f=bucket (mapW q f) g (mapW p f) := by
  unfold bucket pour
  rw [map_nested,map_nested]
  have h := map_resize q f (fun i=>mapW p (g∘f) (g i)/mapW q (g∘f) (g i))
  exact h

omit [Fintype B] in
theorem bucket_mix (q : Wgt A) (f : A → B) (w : Wgt C) (p : C→ Wgt A) :
    bucket q f (mixW w p)=mixW w (fun y => bucket q f (p y)) := by
  unfold bucket pour
  rw [map_mix]
  funext i; simp only [mixW,avg_mul',avg_div]

theorem tension_stage (p q : Wgt A) (hp : ∀ i,0 ≤ p i) (hq : ∀ i, 0≤ q i)
    (h : lsupp p q) (f : A→B) :
    tension p q=tension p (bucket q f p)+tension (mapW p f) (mapW q f) := by
  unfold tension
  rw [mapW_avg, ← avg_add]
  refine avg_congr (fun i hi => ?_)
  have hu := h i hi; have hw := lsupp_hit hp f i hi; have hv := lsupp_hit hq f i hu
  dsimp only [bucket,pour]
  rw [log_mul hu (div_ne_zero hw hv),log_div hw hv]
  ring
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MutualInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mutual Information -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
theorem mix_high {μ : Wgt A} {p : A→ Wgt B} (hμ : ∀ i,0 ≤ μ i) (hp : ∀ i j,0 ≤ p i j)
    (i j) : μ i * p i j ≤ mixW μ p j :=
  weight_le_tot (fun x => mul_nonneg (hμ x) (hp x j)) i

theorem mix_overhead [Nonempty B] {μ : Wgt A} {p : A→Wgt B}
    (hμ : IsLaw μ) (hp : ∀ i,IsLaw (p i)) :
    avg μ (fun x => tension (p x) (mixW μ p))≤log (Fintype.card B) := by
  simp_rw [tension_as_diff,avg_sub,← mixW_avg]
  change avg μ (fun x => negEnt (p x))-negEnt _ ≤ _
  linarith only [hμ.avg_le (fun i => negEnt_le_zero ((hp i).sub)),
    log_card_le_negEnt (mixW_law hμ hp)]

theorem mix_charge [Nonempty A] {μ : Wgt A} {p : A→Wgt B}
    (hμ : IsLaw μ) (hp : ∀ i,IsLaw (p i)) :
    avg μ (fun x => tension (p x) (mixW μ p))≤log (Fintype.card A) := by
  let q := mixW μ p
  have h (i : A) (hi : μ i ≠0) :
      tension (p i) q≤0-log (μ i) := by
    have hr := lt_of_le_of_ne (hμ.nz i) (Ne.symm hi)
    have hcap (j) : p i j ≤ (μ i)⁻¹*q j := by
      rw [mul_comm,←div_eq_mul_inv,le_div_iff₀ hr,mul_comm]
      exact mix_high hμ.nz (fun i => (hp i).nz) i j
    refine (tension_le_cap (hp i).nz (mixW_law hμ hp).nz _ (by positivity) hcap).trans_eq ?_
    rw [(hp i).total,one_mul,log_inv,zero_sub]
  calc _ ≤ avg μ (fun i => (0-log (μ i))) :=
           Finset.sum_le_sum fun i _ => (by
              by_cases hi : μ i=0
              · simp only [hi,zero_mul]; rfl
              exact mul_le_mul_of_nonneg_left (h i hi) (hμ.nz i))
       _ = -negEnt μ := by rw [avg_sub,avg_zero,zero_sub]; rfl
       _ ≤ _ := neg_le.mpr (log_card_le_negEnt hμ)

omit [Fintype C] in
theorem map_banded {p : Wgt B} (f : B→C) (h : ∀ i j,f i=f j → p i=p j)
    (i : B) : mapW p f (f i) = p i * nbr (fun j => f j=f i) := by
  unfold mapW pr avg nbr tot
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : f j=f i
  · rw [h j i hj]
  simp only [ind_zero hj,mul_zero]

theorem tension_banded {p q : Wgt B} (f : B→C) (h : lsupp p q)
    (hp : ∀ i j,f i=f j→p i=p j) (hq : ∀ i j,f i=f j→q i=q j) :
    tension p q=tension (mapW p f) (mapW q f) := by
  unfold tension; rw [mapW_avg]
  apply avg_congr
  intro i hi
  let P (j : B) := f j=f i
  have hk : nbr P≠0 := by
    have he := weight_le_tot (fun j => ind_nonneg (P j)) i
    rw [ind_one (show P i from rfl)] at he
    exact (lt_of_lt_of_le zero_lt_one he).ne'
  change _=Real.log (mapW p f (f i))-Real.log (mapW q f (f i))
  rw [map_banded f hp,map_banded f hq,log_mul hi hk, log_mul (h i hi) hk]
  ring

theorem banded_overhead [Nonempty C] {μ : Wgt A} {p : A→Wgt B}
    (hμ : IsLaw μ) (hp : ∀ i,IsLaw (p i)) (f : B→C)
    (h : ∀ i j k,f j=f k→ p i j=p i k) :
    avg μ (fun i => tension (p i) (mixW μ p)) ≤ log (Fintype.card C) := by
  let q := mixW μ p
  have he (i : A) (hi : μ i ≠0) :
      tension (p i) (mixW μ p) =
      tension (mapW (p i) f) (mixW μ (fun i => mapW (p i) f)) := by
    have hh : lsupp (p i) q := fun x hx =>
      (lt_of_lt_of_le (mul_pos (lt_of_le_of_ne (hμ.nz i) (Ne.symm hi))
        (lt_of_le_of_ne ((hp i).nz x) (Ne.symm hx)))
        (mix_high hμ.nz (fun i => (hp i).nz) i x)).ne'
    rw [←map_mix]
    exact tension_banded f hh (h i) (fun i j ht => by unfold mixW; simp_rw [h _ i j ht])
  exact (le_of_eq (avg_congr he)).trans
    (mix_overhead hμ (fun i => mapW_law (hp i) f))

private theorem add_charge (x y : ℝ) (hx : 0 ≤ x) (hy : 0≤y) :
    (x+y)*log (x+y) ≤ x*log x+y*log y+(x+y)*log 2 := by

  have hh := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy)
    (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num)
  simp only [smul_eq_mul] at hh
  by_cases he : x+y=0
  · obtain rfl : x=0 := by linarith
    obtain rfl : y=0 := by linarith
    simp
  rw [←mul_add,log_mul (by norm_num) he, log_inv] at hh
  linarith

theorem tension_add_le (p q w u : Wgt A) (h : ∀ i,p i=q i+w i)
    (hq : ∀ i, 0 ≤ q i) (hw : ∀ i,0 ≤ w i) :
    tension p u≤ tension q u+tension w u+tot p * log 2 := by
  unfold tension tot avg
  rw [Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply sum_le_sum; intro i _
  change p i*_ ≤ _
  simp only [h]
  linarith only [add_charge _ _ (hq i) (hw i)]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EmpiricalInformation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Empirical Information -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C J : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype J]
variable [DecidableEq J] {l : ℕ}

theorem draw_pick {p : Wgt B} (hp : IsLaw p) (i : J) :
    mapW (draws J p) (fun x => x i)=p := by
  funext b
  let f := fun (_ : Unit) => i
  let R := fun (_ : Unit) (j : B) => j=b
  have ht := prodW_pr_inj (f.injective_of_subsingleton) (w:=fun _ => p)
    (fun _ => hp) R
  unfold mapW
  simpa [f,R,draws] using ht
omit [Fintype B] [DecidableEq J] in
theorem draw_elem {p : Wgt B} (x : J→B) (i : J)
    (h : draws J p x≠0) : p (x i)≠0 := fun hx => h (prod_eq_zero (mem_univ _) hx)

theorem tension_traj (J : Type) [Fintype J] [DecidableEq J]
    (p q : Wgt B) (hp : IsLaw p) (h : lsupp p q) :
    tension (draws J p) (draws J q)=num J*tension p q := by
  let Q (x : J→B) :=
      ∑ i:J,(log (p (x i))-log (q (x i)))
  have he : tension (draws J p) (draws J q)=avg (draws J p) Q := by
    refine avg_congr fun i hi => ?_
    have hp (j) := draw_elem i j hi
    change log (∏ j:J,p (i j))-log (∏ j:J,q (i j))=_
    rw [log_prod (fun j _ => hp j),log_prod (fun j _ => h _ (hp j)), ← Finset.sum_sub_distrib]
  let r (j : J) := fun x : J→B => log (p (x j))-log (q (x j))
  rw [he, show avg _ Q= ∑ i:J,avg (draws J p) (r i) from avg_sum ..]
  have hr (i : J) :
      avg (draws J p) (r i)= tension p q := by
    unfold r
    rw [← mapW_avg (draws J p) (fun x => x i) (fun x => log (p x)-log (q x)), draw_pick hp i]
    rfl
  simp only [hr,Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]

theorem draws_trace [DecidableEq B] (p : Wgt B) (x : Fin l → B) :
    draws (Fin l) p x=∏ i:B,p i^(traceTraj x i).val := by
  classical
  have ht (i : B) : p i^(traceTraj x i).val =
      ∏ j:Fin l, if x j=i then p i else 1 := by
    unfold traceTraj; rw [←Finset.prod_filter]; simp
  simp_rw [ht]; rw [Finset.prod_comm]
  unfold draws prodW
  apply prod_congr rfl
  intro i _
  simp

theorem traj_charge (μ : Wgt A) (p : A→ Wgt B) (w : Wgt B)
    (hμ : IsLaw μ) (hp : ∀ i, IsLaw (p i))
    (h : ∀ i,lsupp (p i) w) :
    let f := fun i => draws (Fin l) (p i)
    let q := draws (Fin l) w
    (l:ℝ)*avg μ (fun i => tension (p i) w) ≤
      num B *log ((l:ℝ)+1) + tension (mixW μ f) q := by
  classical
  intro f q
  have he : ↑l*avg μ (fun i => tension (p i) w) =
      avg μ (fun i => tension (f i) q) := by
    unfold f q
    simp_rw [tension_traj _ _ _ (hp _) (h _),avg_mul']
    simp only [num,Fintype.card_fin]
  rw [he,tension_mix]
  refine add_le_add_left ?_ _
  have h0 : ∀ i,IsLaw (f i) := fun i => draws_law (hp i)
  refine (banded_overhead hμ h0 traceTraj (fun i j k ht => ?_)).trans_eq ?_
  · unfold f; rw [draws_trace,draws_trace,ht]
  simp only [Track,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow,Nat.cast_add,
    Nat.cast_one,num]

/-- If components are coarse with no tiny positive atoms,
    their repeat law has a corresponding cap cost for any submeasure. -/
theorem traj_cap (p : Wgt B) (hp : IsLaw p) (u : ℝ)
    (h : ∀ i, p i≠0 → bp (-u)≤p i) :
    ∀ x, draws (Fin l) p x≠0 → bp (-u*l) ≤ draws (Fin l) p x := by
  intro x hx
  have hpos (i : Fin l) : 0 < p (x i) :=
    lt_of_le_of_ne (hp.nz _) (Ne.symm (draw_elem _ i hx))
  rw [bp_mul_nat]
  refine le_trans ?_ (Finset.prod_le_prod (fun i (_: i∈(univ:Finset (Fin l))) =>
    (bp_pos (-u)).le) fun i _ => h (x i) (hpos i).ne')
  simp
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RepeatedQueryEnergy
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated Query Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X J : Type} [Fintype A] [Fintype B] [Fintype X] [Fintype J]
variable [DecidableEq J]

omit [Fintype B] in
theorem path_repeat {μ : Wgt A} {w : Wgt X} (f : A→ X→B) :
    mixW μ (fun i => draws J (mapW w (f i))) =
      mixW (draws J w) (fun x => mapW μ (fun i => f i ∘ x)) := by
  classical
  funext i
  have h (j : A) :
      draws J (mapW w (f j)) i=pr (draws J w) (fun x => f j ∘ x=i) := by
    simp_rw [funext_iff]
    exact Eq.symm (prodW_pr _ (fun l y => f j y=i l))
  simp_rw [mixW,h]
  exact avg_avg ..

theorem path_sub (w : Wgt X) (p : X→Prop) (f : X → Wgt A)
    (hw : SubLaw w) (hf : ∀ i,IsLaw (f i)) :
    SubLaw (mixW (subW w p) f) ∧ tot (mixW (subW w p) f)=pr w p := by
  have hh : tot (mixW (subW w p) f)=pr w p := by
    rw [mixW_tot]; simp_rw [(hf _).total,avg_const,mul_one,subW_tot]
  exact ⟨⟨fun i => avg_nonneg (subLaw_sub hw p).nz (fun j => (hf j).nz i),
    hh ▸ (pr_le_tot hw.nz).trans hw.total⟩,hh⟩

omit [Fintype A] in
theorem path_patch (w : Wgt X) (p : X→Prop) (f : X → Wgt A) :
    ∀ i,mixW w f i=mixW (subW w p) f i+mixW (subW w (fun x=>¬ p x)) f i := by
  intro i
  unfold mixW subW avg
  rw [←Finset.sum_add_distrib]; simp_rw [ind_not]
  exact sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in
theorem path_energy (μ : Wgt A) (w : Wgt X) (q : Wgt B)
    (f : A → X→B) (hμ : IsLaw μ) (hw : IsLaw w) (hq : IsLaw q)
    (h : ∀ i j,q (f i j)≠0)
    (u : ℝ) (hu : 0≤u) (hp : ∀ i,q i ≠0 → bp (-u)≤q i)
    (l : ℕ) (P : (Fin l→X)→ Prop) (r : ℝ)
    (hr : pr (draws (Fin l) w) (fun x => ¬ P x) ≤ r)
    (C : ℝ) (hc : 0≤C)
    (hP : ∀ x,P x→ ∀ y,mapW μ (fun i => f i ∘ x) y ≤ bp C * draws (Fin l) q y) :
    (l:ℝ)* avg μ (fun i => tension (mapW w (f i)) q) ≤
      num B*log (↑l+1)+(C+r*u*l+1)*log 2 := by
  classical
  let F (i : A) := mapW w (f i)
  let W := draws (Fin l) w
  let Q := draws (Fin l) q
  let k (x : Fin l → X) := mapW μ (fun i => f i ∘ x)
  let g := mixW (subW W P) k
  let b := mixW (subW W (fun x => ¬ P x)) k
  let V := mixW μ (fun i => draws (Fin l) (F i))
  have h0 : ∀ i, lsupp (F i) q := by
    intro i j hj; obtain ⟨t,ht,rfl⟩ := lsupp_witness hj
    exact h _ _
  have hF : ∀ i,IsLaw (F i) := fun i => mapW_law hw (f i)
  have hV : IsLaw V := mixW_law hμ (fun i => draws_law (hF i))
  have hQ : IsLaw Q := draws_law hq
  have hW : IsLaw W := draws_law hw
  have hk : ∀ i,IsLaw (k i) := fun i => mapW_law hμ _
  have h1 := traj_charge (l:=l) μ F q hμ hF h0
  have h2 : ∀ i,V i=g i+b i := by unfold V F; rw [path_repeat]; exact path_patch W P k
  have hg := path_sub W P k hW.sub hk
  have hb := path_sub W (fun x => ¬ P x) k hW.sub hk
  have h2L : 0 ≤ log (2:ℝ) := (Real.log_pos (by norm_num)).le
  have h3 : tension g Q ≤ C*log 2 := by
    have hz i : g i ≤ bp C*Q i := by
      let c := bp C*Q i
      have hc : 0 ≤ c := mul_nonneg (bp_pos _).le (hQ.nz _)
      have he (j) : ind (P j)*k j i ≤ c := by
        by_cases h : P j
        · rw [ind_one h,one_mul]; exact hP j h i
        rw [ind_zero h,zero_mul]; exact hc
      refine le_trans ?_ (hW.avg_le he)
      simp only [g,mixW,subW,avg,mul_assoc]; rfl
    refine (tension_le_cap hg.1.nz hQ.nz _ (bp_pos _) hz).trans ?_
    rw [log_bp]
    exact (mul_le_mul_of_nonneg_right hg.1.total
      (mul_nonneg hc h2L)).trans_eq (one_mul _)
  have h4 : tension b Q ≤ r*(u*l*log 2) := by
    have hz (i : Fin l → B) : b i ≤ bp (u*l)*Q i := by
      by_cases he : Q i=0
      · have ht (j) : k j i=0 := by
          by_contra h
          obtain ⟨z,hz,rfl⟩ := lsupp_witness h
          have ht : Q (f z ∘ j) ≠ 0 := by
            change ∏ i:Fin l,q (f z (j i)) ≠0
            rw [Finset.prod_ne_zero_iff]; exact fun i _ => ‹∀ i j,q (f i j)≠0› _ _
          exact ht he
        unfold b mixW; simp_rw [ht]; rw [he,avg_zero,mul_zero]
      have hq := traj_cap q hq u hp i he
      refine (hb.1.weight_le_one i).trans ?_
      exact (le_of_eq (by rw [←bp_add,show u*l+ -u*l = 0 by ring,bp_zero])).trans
        (mul_le_mul_of_nonneg_left hq (bp_pos _).le)
    refine (tension_le_cap hb.1.nz hQ.nz _ (bp_pos _) hz).trans ?_
    rw [log_bp]
    exact mul_le_mul_of_nonneg_right (hb.2.le.trans hr)
      (by apply mul_nonneg (by positivity) h2L)
  apply h1.trans
  refine add_le_add_right ?_ _
  have h5 := tension_add_le V g b Q h2 hg.1.nz hb.1.nz
  rw [hV.total] at h5
  linarith only [h5,h4,h3]
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
theorem glob_inj (i : Ports p) :
    Injective (fun i : Port (globPort p v.t v.aim) i => i.val.1) := by
  rintro ⟨⟨a,c⟩,ha⟩ ⟨⟨b,d⟩,hb⟩ he
  change a=b at he; subst b
  have h : c=d := Subtype.ext (congrArg Prod.snd (ha.trans hb.symm))
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
theorem double_show (z : Inputs p n I) (x : UnitType p n N) :
    (v.doubleP n).showKey z (mergeR p x)=scatter v.t N ((v.draw z).keys v.t x) :=
  peek_keys v.t (v.draw z) x

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_HistogramEnergyScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Histogram Energy Scales -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators Topology
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

theorem log_thrift (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ l : ℕ in atTop,r * Real.log ((l:ℝ)+1)≤(l:ℝ) := by
  have h2 := Real.log_pos (x:=2) (by norm_num)
  let a := (1:ℝ)/(log 2*(r+1))
  have hr' : 0 < r+1 := by linarith
  have ha : 0<a := by positivity
  filter_upwards [bp_poly_dom_nat ha 2 1,eventually_ge_atTop 1] with l hl hl'
  have hi : 1 ≤ (l:ℝ) := by exact_mod_cast hl'
  simp only [pow_one] at hl
  have he := Real.log_le_log (x:=(l:ℝ)+1) (by positivity)
    (le_trans (show (l:ℝ)+1≤2*l by linarith) hl.le)
  rw [log_bp] at he
  have ht : (r+1)*(a*l*log 2)=l := by unfold a; field_simp
  have hx := mul_le_mul_of_nonneg_left he hr'.le
  rw [ht] at hx
  have hz : 0≤ log ((l:ℝ)+1) := Real.log_nonneg (by linarith)
  linarith

theorem div_grows (d : ℕ) (hd : 0<d) :
    Tendsto (fun n : ℕ => n / d) atTop atTop := tendsto_atTop.mpr fun b =>
  (eventually_ge_atTop (b*d)).mono fun _ h => (Nat.le_div_iff_mul_le hd).mpr h

set_option maxHeartbeats 800000 in
theorem toll_calendar (M : ℕ) (hM : 1≤M) (C : ℝ) (hC : 0≤C)
    (I J G : Type) [Fintype I] [Fintype J]
    [Fintype G] [DecidableEq G] (g : Route J G) :
    ∃ (s : ℕ) (E V : ℝ), 0 < s ∧ 0≤E ∧
    ∀ r u : ℝ, 0 ≤ r→0≤u →
      ∀ᶠ n : ℕ in atTop,TollBar M C I J G g n (n / s) r u E V := by
  classical
  let a := num I; let b := num J
  let d := 2*((1+2*b)*b)
  have ha : 0≤a := Nat.cast_nonneg _
  have hb : 0≤b := Nat.cast_nonneg _
  have hd : 0 ≤ d := by positivity
  obtain ⟨s,hs⟩ := exists_nat_gt (1+4*(a+b+d))
  have hs' : 0 < s := by exact_mod_cast (show (0:ℝ) < s from by linarith)
  have hi : (1:ℝ)≤M := by exact_mod_cast hM
  let E := C*(M*2*s)+b*b+1
  have hM' : (0:ℝ)≤M := by positivity
  have hE : 0 ≤ E := by positivity
  let V := 1+(E+2)*log 2
  refine ⟨s,E,V,hs',hE,fun r u hr hu => ?_⟩
  have ht := div_grows s hs'
  let B := (4:ℝ)^Fintype.card G
  filter_upwards [ht.eventually (eventually_ge_atTop 1),
    ht.eventually (bp_poly_dom_nat (a:=1) (by norm_num) (B*(b+1)) 1),ht.eventually
    (log_thrift r hr),ht.eventually ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (eventually_ge_atTop (max 2 (8*u)))),pay_nat (a:=1/2) u (b:=0) (by norm_num)]
    with n hl hG hr hpeak hU
  let l := n/s
  have hl' : 1≤(l:ℝ) := by exact_mod_cast hl
  have hsl : (s:ℝ)*l ≤ n := by
    rw [mul_comm]; exact_mod_cast Nat.div_mul_le_self n s
  have hnl : (n:ℝ) ≤ 2*s*l := by
    have h := Nat.lt_mul_div_succ n hs'
    change n < s*(l+1) at h
    have h1 : (n:ℝ) ≤ s*((l:ℝ)+1) := by exact_mod_cast h.le
    nlinarith only [h1,mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg (α:=ℝ) s)]
  have hx : (n:ℝ) ≤ ↑(M*n) := by
    exact_mod_cast (show n ≤ M*n from by nlinarith)
  change max 2 (8*u)≤ (l:ℝ) at hpeak
  have hh1 := mul_le_mul_of_nonneg_right hs.le (Nat.cast_nonneg l : 0≤(l:ℝ))
  have hq :
      num (Fin l)=(l:ℝ) ∧ num (Fin l × J)=(l:ℝ)*b := by simp [num,b]
  constructor
  · exact hl
  · intro i
    change 2*num (Port (tied g (Fin l)) i)-↑(M*n) ≤ -1
    have hg := port_limit (tied g (Fin l)) i
    rw [hq.2] at hg
    nlinarith only [hg,hx,hsl,hl',hh1,
      mul_nonneg ha (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ))]
  · have he : peakExpense (Fin l) J 1=d*l := by unfold peakExpense d b; rw [hq.1]; norm_num <;> ring
    change peakExpense (Fin l) J 1+ _ ≤ _
    rw [he]
    nlinarith only [hh1,hsl,hx, (max_le_iff.mp hpeak).2,
      mul_nonneg ha (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
      mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ)), Nat.cast_nonneg (α:=ℝ) l]
  · change bp _ * (B *bp (num (Fin l)*b*b) * (num (Fin l×J)+1)) ≤ bp (E*l)
    have hg : B*(num (Fin l×J)+1) ≤ bp l := by
      change B*(b+1)*(l:ℝ)^1 < bp (1*l) at hG
      simp only [hq.2]; rw [pow_one,one_mul] at hG
      refine le_trans ?_ hG.le
      exact (mul_le_mul_of_nonneg_left (show (l:ℝ)*b+1≤(b+1)*l by linarith only [hl'])
        (by positivity)).trans_eq (Eq.symm (mul_assoc _ _ _))
    have he : C*(↑(M*n):ℝ) ≤ C*(M*2*s)*l := by
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnl hM') hC).trans_eq (by ring)
    rw [show E*l=C*(M*2*s)*l+num (Fin l)*b*b+l by rw [hq.1]; unfold E; ring,bp_add,bp_add]
    let D := num (Fin l)*b*b
    calc bp _*_ = (bp (C*↑(M*n))*bp D)*(B*(num (Fin l×J)+1)) := by unfold D; ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (bp_le he) (bp_pos D).le) hg
           (by unfold B num; positivity) (mul_nonneg (bp_pos _).le (bp_pos D).le)

  · change r*log ((l:ℝ)+1)+_ ≤ (l:ℝ)*V
    have hz : bp (num (Fin l)*num I-n)*u≤1 := by
      have he : (l:ℝ)*a-n≤ -(1/2:ℝ)*n := by
        nlinarith only [hh1,hsl,mul_nonneg hb (Nat.cast_nonneg l : 0≤(l:ℝ)),
          mul_nonneg hd (Nat.cast_nonneg l : 0≤(l:ℝ)),Nat.cast_nonneg (α:=ℝ) l]
      rw [hq.1,mul_comm (bp _) u]
      exact (mul_le_mul_of_nonneg_left (bp_le he) hu).trans (by simpa using hU)
    have hh :
        (E*l+bp (num (Fin l)*num I-n)*u*l+1)*log 2 ≤ ((E+2)*l)*log 2 :=
      mul_le_mul_of_nonneg_right (by
        have hmul := mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg l : 0≤(l:ℝ))
        linarith only [hl',hmul]) (Real.log_pos (x:=2) (by norm_num)).le
    change r*log ((l:ℝ)+1)≤l at hr
    exact (add_le_add hr hh).trans_eq (by unfold V; ring)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnfilteredHistogramEnergy
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unfiltered Histogram Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter Matrix Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N M : ℕ}

theorem stamina_buy {δ : ℝ} (hδ : 0<δ) : ∃ u : ℝ,0≤u ∧ bp (-u) ≤ δ := by
  have ht := bp_tendsto_zero (a:=1) zero_lt_one
  obtain ⟨u,hu,hb⟩ := ((eventually_ge_atTop (0:ℝ)).and (ht.eventually
    (eventually_le_nhds hδ))).exists
  exact ⟨u,hu,by simpa using hb⟩
namespace Template
variable (v : Template p I)

variable {B : Type} [Fintype B]

set_option maxHeartbeats 1200000 in
theorem roadmap {l : ℕ} {r u E V : ℝ} (v : Template p I) (C : ℝ)
    (z : TollBar M C I (KeySlots p v.t) (Ports p)
    (globPort p v.t v.aim) n l r u E V)
    (hE : 0≤E) (hu : 0 ≤ u)
    (m : Mixer p n) (hN : 2*num (Full p n)<↑(M*n))
    (f : Keys (p:=p) v.t (M*n)→ B)
    (hB : num B ≤ r)
    (h : stamina (mapW unif f) (bp (-u)))
    (w : Wgt (UnitType p n (M*n))) (hw : IsLaw w)
    (hh : ∀ i,w i ≤ bp (C*↑(M*n))*pairW (raw m (M*n)) (raw m (M*n)) i)
    (x : I→Wgt (Knobs p.g n)) (hx : ∀ i,IsLaw (x i))
    (hz : ∀ i,mapW (x i) (freePart p)=unif) :
    avg w (fun i => tension (mapW (heatMap v i x) f) (mapW unif f)) ≤ V := by
  classical
  let N := M*n
  let W := UnitType p n N
  let D := Keys (p:=p) v.t N
  let q := mapW unif f
  let X := prodW x
  let g := globPort p v.t v.aim
  let s := v.doubleP n
  have hum : IsLaw (unif : Wgt D) := unif_law
  have hq : IsLaw q := mapW_law hum f
  let t := num (Fin l)*num I-n
  let F (i : W) := f∘v.resultKey i
  let Q (x) := draws (Fin l) q x
  have h0 (i : D) : unif i≠0 := by rw [unif_apply]; positivity
  have h1 (i : D) : q (f i) ≠0 := lsupp_hit hum.nz f i (h0 i)
  have h2 (i) (y : Fin l→B) (hF : s.free i) :
      mapW w (fun x => F x ∘ i) y≤ bp (E*l)*Q y := by
    by_cases hy : mapW w (fun x => F x∘i) y =0
    · rw [hy]; exact mul_nonneg (bp_pos _).le ((draws_law hq).nz _)
    let Λ := tied g (Fin l)
    let P (j : Fin l) (x : Rack (KeySlots p v.t) N) := f ((scatter v.t N).symm x)=y j
    have ht (j : Fin l) :
        pr unif (P j)=q (y j) := by
      rw [show pr unif (P j) = pr (mapW unif (scatter v.t N).symm) (fun i => f i=y j) from
        (mapW_pr unif (scatter v.t N).symm (fun i => f i=y j)).symm, unif_equiv]; rfl
    have hr (j : Fin l) :
        bp (-u) ≤ pr unif (P j) := by
      obtain ⟨o,ho,h'⟩ := lsupp_witness hy
      rw [ht, ← congr_fun h' j]
      exact h _ (h1 _)
    let A := pooled (s.left ∘ i)
    let Z := database m A A
    have hL := many_frames (N:=N) Λ Z z.frame u hu P hr z.peak
    let μ := raw m N
    have hk :
        mapW (pairW μ μ) (fun x => F x ∘ i) y =
        pr (rackStation Z N) (fun x => ∀ j,P j (led j x)) := by
      let e (a : Rack (Fin l × KeySlots p v.t) N) := ∀ j,P j (led j a)
      let K (o : Forum p n N (Ports p)) := peekR p Λ A A o
      have ht : mapW (pairW μ μ) (K ∘ mergeR p) = rackStation Z N := by
        rw [← mapW_nested,law_mergeR]; exact law_peekR m hN hF.1 hF.2
      have he (o : W) : e (K (mergeR p o)) ↔ F o ∘ i=y := by
        unfold e K Λ P A; simp_rw [peek_pooled,Function.comp_apply]
        rw [funext_iff]
        have ht (j : Fin l) :
            peekR p g (s.left (i j)) (s.left (i j)) (mergeR p o)=scatter v.t N
              (v.resultKey o (i j)) := double_show v _ _
        simp_rw [ht,Equiv.symm_apply_apply]
        rfl
      unfold mapW
      change _=pr (rackStation Z N) e
      rw [←ht,mapW_pr]; simp_rw [Function.comp_apply,he]
    simp_rw [ht] at hL
    refine (pr_cap hh _).trans ?_
    change bp _ * (mapW (pairW μ μ) _ _)≤_
    rw [hk]
    exact (mul_le_mul_of_nonneg_left hL (bp_pos _).le).trans
      (le_trans (le_of_eq (Eq.symm (mul_assoc _ _ _))) (mul_le_mul_of_nonneg_right z.cap
        ((draws_law hq).nz y)))
  have hv : 0<(l:ℝ) := by exact_mod_cast z.pos
  have he := path_energy w X q F hw (prodW_law hx) hq (fun i j => h1 _) u hu h
    l (fun i => s.free i) (bp t)
    (free_price v n x hx hz g (glob_inj v)) (E*l) (by positivity) (fun i h y => h2 i y h)
  unfold heatMap; simp_rw [mapW_nested]
  apply le_of_mul_le_mul_left _ hv
  apply he.trans
  refine le_trans ?_ z.charge
  exact add_le_add_left (mul_le_mul_of_nonneg_right hB (log_nonneg (by linarith))) _

theorem hist_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ V : ℝ,∀ r δ : ℝ, 0 ≤ r → 0<δ →
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n), 2*num (Full p n)<N →
    ∀ (w : Wgt (UnitType p n N)), IsLaw w →
    (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
    ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
    (∀ i,mapW (x i) (freePart p)=unif) →
    ∀ (B : Type) [Fintype B],num B ≤ r →
    ∀ (f : Keys (p:=p) v.t N → B), stamina (mapW unif f) δ →
    avg w (fun i => tension (mapW (heatMap v i x) f) (mapW unif f)) ≤ V := by
  obtain ⟨s,E,V,hs,hE,h⟩ := toll_calendar M hM C hC I _ _ (globPort p v.t v.aim)
  refine ⟨V,fun r δ hr hδ => ?_⟩
  obtain ⟨u,hu,hh⟩ := stamina_buy hδ
  filter_upwards [h r u hr hu]
    with n hn N m hN w hw hW x hx hz B _ hB f hF
  exact roadmap v C hn hE hu m hN f hB (fun i hi => hh.trans (hF i hi)) w hw hW x hx hz

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InformationSmallSetBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Information Small Set Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real
open scoped BigOperators
variable {A B C X : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X]

variable {μ : Wgt A} {p : A→Wgt B}

namespace Ultra

variable [Nonempty B] (h : Ultra μ p)

omit [Nonempty B] in
theorem maxCat (h : Ultra μ p) : IsLaw (mixW μ p) := mixW_law h.law h.labs
omit [Nonempty B] in
theorem cat_dom (h : Ultra μ p) (w : Wgt B) (hw : catalog μ p w) :
    (∀ i, 0 ≤ w i) ∧ (∀ i, w i ≤ mixW μ p i) := by
  obtain ⟨t,hp,hq,rfl⟩ := hw
  exact ⟨fun i => avg_nonneg hp (fun j => (h.labs j).nz _),fun i => avg_mono_left
    (fun j => (h.labs j).nz _) hq⟩

omit [Nonempty B] in
theorem cat_sub (h : Ultra μ p) (w : Wgt B) (hw : catalog μ p w) :
    SubLaw w := by
  obtain ⟨h1,h2⟩ := h.cat_dom w hw
  exact ⟨h1,(Finset.sum_le_sum fun i _ => h2 i).trans_eq h.maxCat.total⟩

end Ultra

private theorem binary_info (q w : Wgt Bool) (hq : IsLaw q) (hw : IsLaw w)
    (L : ℝ) (he : 0 < q true) (h : q true ≤ exp (-L)) :
    w true * L-log 2 ≤ tension w q := by
  have h1 := Real.log_le_log he h
  rw [Real.log_exp] at h1
  have h2 : log (q false)≤0 := log_nonpos (hq.nz _) (hq.weight_le_one _)
  rw [tension_as_diff]
  have hh : -log 2 ≤ negEnt w := by simpa using log_card_le_negEnt hw
  simp only [avg,Fintype.sum_bool]
  linarith only [hh,mul_nonpos_of_nonneg_of_nonpos (hw.nz false) h2,
    mul_le_mul_of_nonneg_left h1 (hw.nz true)]

theorem expand_event {w : Wgt B} (hw : IsLaw w) (P : B→Prop) (δ : ℝ)
    (he : 2*δ < 1) (hm : ∀ x,w x ≤ δ) (hP : pr w P ≤ 2*δ) :
    ∃ Q : B→Prop,(∀ x,P x → Q x) ∧ δ ≤ pr w Q ∧ pr w Q ≤2*δ := by
  classical
  let S := Finset.univ.filter P
  let M := Finset.univ.filter (fun T : Finset B => S ⊆ T ∧ pr w (·∈T) ≤2*δ)
  have hS (i : B) : i∈S ↔ P i := by simp [S]
  have hh : S∈M := mem_filter.mpr ⟨mem_univ _,(by simp_rw [hS]; exact ⟨le_rfl,hP⟩)⟩
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image M Finset.card ⟨S,hh⟩
  obtain ⟨hx,hz⟩ := (mem_filter.mp hT).2
  refine ⟨(·∈T),fun i hi => hx ((hS i).mpr hi),?_,hz⟩
  by_contra! h
  obtain ⟨i,hi⟩ : ∃ i,i∉T := by
    by_contra! hs
    simp only [hs,pr_true,hw.total] at hz
    linarith
  let T' := insert i T
  have hh' : pr w (·∈T') ≤ w i + pr w (·∈T) :=
    le_trans (le_of_eq (congrArg (pr w) (funext fun i => propext (Finset.mem_insert))))
      ((pr_or_le hw.nz).trans_eq (by simp))
  have ht : T' ∈ M := mem_filter.mpr
    ⟨mem_univ _,hx.trans (subset_insert ..),by linarith only [hh',h,hm i]⟩
  specialize hmax _ ht
  rw [show T'.card=T.card+1 from Finset.card_insert_of_notMem hi] at hmax
  omega

set_option maxHeartbeats 800000 in
theorem ui_threshold (V η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ δ≤1 ∧
    ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      tariffs μ p 2 δ V →
      ∀ S : B→Prop, pr unif S ≤δ → pr (mixW μ p) S ≤ η := by
  classical
  obtain ⟨L,hL,hL'⟩ : ∃ L : ℝ,0<L ∧ V+log 2≤ η*L := by
    obtain ⟨L,hL⟩ := exists_gt (max 0 ((V+log 2)/η))
    exact ⟨L,lt_of_le_of_lt (le_max_left ..) hL,
      by rw [mul_comm]; exact (div_le_iff₀ hη).mp ((le_max_right ..).trans hL.le)⟩
  let δ := min (exp (-L)/2) (1/4)
  have h0 := min_le_left (exp (-L)/2) (1/4)
  change δ≤ _ at h0
  have h1 := min_le_right (exp (-L)/2) (1/4)
  change δ ≤ _ at h1
  have hδ : 0<δ := by unfold δ; exact lt_min (by positivity) (by norm_num)
  refine ⟨δ,hδ,by linarith,fun A B _ _ _ μ p hw ht S hS => ?_⟩
  have he : IsLaw (unif : Wgt B) := unif_law
  by_cases hy : ∃ i,S i
  · obtain ⟨i,hi⟩ := hy
    have hh (j : B) : unif j ≤δ := by
      rw [show unif j=unif i from by simp [unif_apply],← pr_point' unif i]
      exact (pr_mono he.nz (fun j (h:j=i) => h.symm ▸ hi)).trans hS
    obtain ⟨Q,hq,hQ,hQ'⟩ := expand_event he S δ (by linarith) hh (by linarith)
    let f := fun x : B => decide (Q x)
    let q := mapW (unif : Wgt B) f
    have hqL := mapW_law he f
    have hf (w : Wgt B) : mapW w f true=pr w Q := by simp [mapW,f]
    have hq1 : δ≤q true := by unfold q; rw [hf]; exact hQ
    have hq2 : q true ≤2*δ := by unfold q; rw [hf]; exact hQ'
    have hE : budget μ p f ≤ V := ht Bool (by simp) f (by
      rintro (a|a) _
      case false =>
        have hh : q true+q false=1 := by
          have h := hqL.total; rw [tot,Fintype.sum_bool] at h; exact h
        change δ≤q false; linarith only [hh,hq2,h1]
      case true => exact hq1)
    have hi (j : A) :
        pr (p j) Q*L-log 2 ≤ tension (mapW (p j) f) q := by
      rw [← hf]; exact binary_info q _ hqL (mapW_law (hw.labs j) _) L (hδ.trans_le hq1)
        (by linarith only [hq2,h0])
    have hz := avg_mono hw.law.nz hi
    rw [avg_sub,avg_mul,hw.law.avg_const] at hz
    change avg μ (fun i => pr (p i) Q) * _-_ ≤ budget μ p f at hz
    have hv : pr (mixW μ p) Q=avg μ (fun i => pr (p i) Q) := mixW_avg ..
    apply (pr_mono hw.maxCat.nz hq).trans
    rw [hv]
    exact le_of_mul_le_mul_right (by linarith only [hz,hE,hL']) hL
  have ht (i) : ¬ S i := fun h => hy ⟨i,h⟩
  simp [pr,ht,hη.le]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RefinementEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Refinement Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Real
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem var_nonneg (p q : Wgt A) : 0≤ varOne p q := Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem var_tri (p q r : Wgt A) :
    varOne p q≤varOne p r+varOne r q := by
  unfold varOne; rw [← Finset.sum_add_distrib]; exact sum_le_sum fun i _ => abs_sub_le _ _ _

theorem var_pr (p q : Wgt A) (P : A→Prop) :
    pr p P-pr q P ≤ varOne p q := by
  unfold pr avg varOne
  rw [← Finset.sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  by_cases h : P i
  · simp only [ind_one h,mul_one]; exact le_abs_self _
  simp only [ind_zero h,mul_zero,sub_zero]; exact abs_nonneg _

theorem var_event (p q : Wgt A) (h : tot p=tot q) :
    let P := fun i => q i<p i
    varOne p q=2*(pr p P-pr q P) := by
  intro P
  have hi (i:A) : |p i-q i|=
      2*(p i*ind (P i)-q i*ind (P i))+q i-p i := by
    by_cases h : P i
    · rw [ind_one h,abs_of_pos (sub_pos.mpr h)]; ring
    rw [ind_zero h,abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring
  unfold varOne pr avg
  simp_rw [hi,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [show ∑ i,q i=∑ i,p i from h.symm]; ring

theorem var_mix {μ : Wgt A} (p q : A→Wgt B) (hμ : ∀ i,0≤μ i) :
    varOne (mixW μ p) (mixW μ q) ≤ avg μ (fun i => varOne (p i) (q i)) := by
  unfold varOne mixW
  rw [avg_sum]
  simp_rw [←avg_sub]; exact sum_le_sum fun i _ => abs_avg_le hμ

omit [Fintype D] in
theorem bucket_m (μ : Wgt A) (p : A → Wgt B) (f : B→C) (g : C→D) :
    mapW (bucket unif (g∘f) (mixW μ p)) f =
      mixW μ (fun x => bucket (mapW unif f) g (mapW (p x) f)) := by
  rw [bucket_mix,map_mix]
  simp only [bucket_nested]

variable {μ : Wgt A} {p : A→Wgt B}

theorem tariffs_monotone {r s : ℕ} {a b V : ℝ} (h : tariffs μ p r a V)
    (hrs : s ≤ r) (hb : a ≤ b) : tariffs μ p s b V :=
  fun C _ hC f hf => h C (hC.trans hrs) f (fun _ hi => hb.trans (hf _ hi))

theorem budget_nonneg [Nonempty B] (h : Ultra μ p) (f : B→ C) :
    0≤budget μ p f := by
  have h0 {p : Wgt B} : lsupp p unif := fun i _ => by rw [unif_apply]; positivity
  have hv : IsLaw (mapW unif f) := mapW_law unif_law f
  exact avg_nonneg h.law.nz (fun i => tension_nonneg (mapW_law (h.labs i) f) hv
    (lsupp.map h0 unif_law.nz f))

set_option maxHeartbeats 800000 in
theorem budget_progress [Nonempty B] (h : Ultra μ p) (w : Wgt B)
    (hw : catalog μ p w) (f : B→C) (g : C→D) :
    varOne (mapW w f) (mapW (bucket unif (g∘f) w) f) ^ 2 ≤
      (budget μ p f-budget μ p (g∘f))*4 := by
  classical
  let q := mapW unif f
  let Q (i : A) := mapW (p i) f
  let R (i : A) := bucket q g (Q i)
  have hu : IsLaw q := mapW_law unif_law f
  have hQ (i) : IsLaw (Q i) := mapW_law (h.labs i) f
  have he (i) : lsupp (Q i) q := lsupp.map
    (p:=p i) (q:=unif) (fun i _ => by rw [unif_apply]; positivity) unif_law.nz f
  have hp (i : A) :
      varOne (Q i) (R i) ^ 2 ≤ tension (Q i) (R i) *4 :=
    var_tension _ _ (hQ i) (bucket_law (hQ i) g hu.nz (he i))
      (lsupp_bucket g (hQ i).nz hu.nz (he i))
  have hn :
      budget μ p f=avg μ (fun i => tension (Q i) (R i))+budget μ p (g∘f) := by
    unfold budget
    have hi := fun i : A => tension_stage (Q i) q (hQ i).nz hu.nz (he i) g
    unfold Q q at hi
    simp_rw [map_nested] at hi
    rw [← avg_add]; exact avg_congr fun i _ => hi i
  let Z (i : A) := varOne (Q i) (R i)
  have hs : avg μ Z ^ 2 ≤ avg μ (fun i => Z i ^ 2) := by
    have hh := avg_CS h.law.nz Z (fun _ => 1)
    simp only [mul_one,one_pow,h.law.avg_const] at hh; exact hh
  obtain ⟨s,hs',ht,rfl⟩ := hw
  rw [bucket_m,map_mix]
  have h' := (var_mix Q R hs').trans (avg_mono_left (fun i => var_nonneg ..) ht)
  refine (pow_le_pow_left₀ (var_nonneg ..) h' 2).trans (hs.trans ?_)
  have hz := avg_mono h.law.nz hp; rw [avg_mul] at hz
  rw [hn]; exact hz.trans_eq (by ring)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RoundedRefinements
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounded Refinements -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

set_option maxHeartbeats 900000 in
theorem divide_fit (q : Wgt B) (hq : IsLaw q) (f : B→C) (P : B→Prop)
    (δ γ : ℝ) (hγ : 0<γ) (hz : 2*γ ≤ δ) (h : stamina (mapW q f) δ) :
    ∃ F : B→C×Bool, f=Prod.fst∘F ∧ stamina (mapW q F) γ ∧
    pr q (fun i => ¬(P i ↔ (F i).2))≤num (C×Bool)*γ := by
  classical
  let g (i : B) : C × Bool := (f i,decide (P i))
  let Q := mapW q g
  have hQ := mapW_law hq g
  have hf : f=Prod.fst∘g := rfl
  have hi (i) : mapW q f i=Q (i,true)+Q (i,false) := by
    have hs : mapW q f=mapW Q Prod.fst := hf ▸ Eq.symm (map_nested g Prod.fst)
    rw [hs]
    simp only [mapW,pr,avg,Fintype.sum_prod_type,Fintype.sum_bool]; simp [ind,Finset.sum_add_distrib]
  let s (j:C×Bool) : Bool := if Q (j.1,true) < γ then false else
    if Q (j.1,false) < γ then true else j.2
  let F (j : C × Bool) : C × Bool := (j.1,s j)
  refine ⟨F ∘ g,rfl,?_,?_⟩
  · rintro ⟨i,b⟩ h'
    have hb :
        mapW Q F (i,b)=Q (i,true)*ind (s (i,true)=b)+
          Q (i,false)*ind (s (i,false)=b) := by
      unfold mapW pr avg
      rw [Fintype.sum_prod_type, sum_eq_single i]
      · rw [Fintype.sum_bool]; simp [ind,F]
      · intro j _ hj; rw [Fintype.sum_bool]; simp [ind,F,hj]
      simp
    rw [←map_nested,hb] at h' ⊢
    by_cases hx : Q (i,true)<γ
    · cases b
      · simp only [s,hx,ite_true, if_true,ind_true,mul_one] at *
        rw [←hi] at *
        exact le_trans (by linarith only [hz,hγ]) (h i h')
      simp [s,hx,ind] at h'
    by_cases hy : Q (i,false)<γ
    · cases b
      · simp [s,hx,hy,ind] at h'
      simp only [s,hx,hy,ite_true, if_true,ite_false, if_false,ind_true,mul_one] at *
      rw [←hi] at *
      exact le_trans (by linarith only [hz,hγ]) (h i h')
    cases b
    · simpa [s,hx,hy,ind] using (le_of_not_gt hy)
    simpa [s,hx,hy,ind] using (le_of_not_gt hx)
  let R (i : C×Bool) := i.2≠s i
  have he j : (¬ (P j ↔ (F (g j)).2)) ↔ R (g j) := by
    change (¬ (P j ↔ s (g j)=true)) ↔ decide (P j)≠s (g j)
    cases s (g j) <;> simp
  have h1 (j : C×Bool) : R j→ Q j≤γ := by
    intro hj
    rcases j with ⟨i,b⟩
    by_cases hx : Q (i,true)<γ
    · cases b
      · simp [R,s,hx] at hj
      exact hx.le
    by_cases hy : Q (i,false)<γ
    · cases b
      · exact hy.le
      simp [R,s,hx,hy] at hj
    simp [R,s,hx,hy] at hj
  have hg (j) : Q j * ind (R j) ≤ γ := by
    by_cases hh : R j
    · simpa only [ind_one hh,mul_one] using h1 j hh
    rw [ind_zero hh,mul_zero]; exact hγ.le
  simp_rw [Function.comp_apply,he]
  rw [← mapW_pr]
  exact (Finset.sum_le_sum fun i _ => hg i).trans_eq (by simp only [Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,num])

theorem bucket_upper (w : Wgt B) (hw : SubLaw w) (q : Wgt B) (hq : IsLaw q)
    (f : B→ C) (δ : ℝ) (h0 : 0<δ) (hz : stamina (mapW q f) δ) :
    ∀ i,bucket q f w i ≤ δ⁻¹*q i := by
  intro i
  have he : mapW w f (f i) ≤1 := by
    exact (pr_le_tot hw.nz).trans hw.total
  unfold bucket pour
  by_cases hi : mapW q f (f i)=0
  · rw [hi,div_zero,mul_zero]; exact mul_nonneg (inv_pos_of_pos h0).le (hq.nz _)
  rw [mul_comm δ⁻¹]
  exact mul_le_mul_of_nonneg_left ((div_le_div₀ zero_le_one he h0 (hz _ hi)).trans_eq
    (one_div _)) (hq.nz _)

theorem pr_ref_delta (w : Wgt A) (hw : ∀ i,0 ≤ w i) (P Q : A→ Prop) :
    pr w P ≤ pr w Q + pr w (fun i => ¬(P i↔Q i)) :=
  (pr_mono hw (q:=fun i => Q i ∨ ¬(P i↔Q i)) fun i _ => by tauto).trans (pr_or_le hw)

variable {μ : Wgt A} {p : A →Wgt B}

set_option maxHeartbeats 1000000 in
theorem divide_progress [Nonempty B] (h : Ultra μ p)
    (ε δ α k : ℝ) (hε : 0<ε) (hk : 0<k) (hk' : 2*k≤1)
    (hδ : 0<δ) (hα : δ≤1)
    (hB : ∀ P : B→ Prop, pr unif P ≤α → pr (mixW μ p) P ≤ε)
    (f : B→ C) (hz : stamina (mapW unif f) δ)
    (hC : num (C×Bool)*k ≤ min α ε)
    (w : Wgt B) (hw : catalog μ p w) (hr : 8*ε<varOne w (bucket unif f w)) :
    ∃ F : B → C×Bool, stamina (mapW unif F) (k*δ) ∧
      budget μ p f + ε^2 ≤ budget μ p F := by
  classical
  let q : Wgt B := unif
  have hq : IsLaw q := unif_law
  let v := bucket q f w
  have ht := h.cat_sub w hw
  let P (i : B) := v i < w i
  have hv (i) : 0≤v i := pour_nz _ hq.nz (map_nz ht.nz f) i
  have hh : varOne w v=2*(pr w P-pr v P) := by
    have hx : lsupp w q := fun i _ => by unfold q; rw [unif_apply]; positivity
    exact var_event w v (by rw [←map_mass w f,←map_mass v f,bucket_scale q w hq.nz hx])
  obtain ⟨F,hF,hφ,hL⟩ := divide_fit q hq f P δ (k*δ) (by positivity)
    ((le_of_eq (by rw [← mul_assoc])).trans ((mul_le_mul_of_nonneg_right hk' hδ.le).trans_eq
      (one_mul _))) hz
  refine ⟨F,hφ,?_⟩
  let Q := fun i : B => ((F i).2=true)
  let S := fun i => ¬(P i ↔ Q i)
  have h1 : pr w S ≤ ε := by
    obtain ⟨hu,he⟩ := h.cat_dom w hw
    have hs : pr q S ≤α := by
      have hμ := (le_min_iff.mp hC).1
      have : 0≤num (C×Bool) := Nat.cast_nonneg _
      exact hL.trans (by nlinarith only [this,hk,hα,hμ,
        mul_le_mul_of_nonneg_left hα (mul_nonneg this hk.le)])
    exact (pr_mono_left he S).trans (hB S hs)
  have h2 : pr v S ≤ ε := by
    have hh := (pr_cap (bucket_upper w ht q hq f δ hδ hz) S).trans
      (mul_le_mul_of_nonneg_left hL (inv_pos_of_pos hδ).le)
    exact hh.trans ((le_of_eq (by field_simp)).trans (le_min_iff.mp hC).2)
  have h3 : 2*ε < pr w Q-pr v Q := by
    have he := pr_ref_delta w ht.nz P Q
    have hr' := pr_ref_delta v hv Q P
    have heq : (fun i=>¬(Q i↔P i))=S := funext fun i => propext (by unfold S; tauto)
    rw [heq] at hr'
    change 8*ε < varOne w v at hr
    rw [hh] at hr; change pr w P≤pr w Q+pr w S at he
    linarith only [hr,h1,h2,he,hr']
  have h4 := var_pr (mapW w F) (mapW v F) (fun i:C×Bool => i.2=true)
  rw [mapW_pr,mapW_pr] at h4
  have he := budget_progress h w hw F Prod.fst
  change varOne _ (mapW (bucket q (Prod.fst ∘ F) w) F) ^ 2 ≤ _ at he
  rw [← hF] at he
  nlinarith only [he,hε,(le_trans h3.le h4)]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionNets
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Nets -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem stamina_equiv (p : Wgt A) (e : A≃C) (a : ℝ)
    (h : stamina p a) :
    stamina (mapW p e) a := by
  intro i hi; rw [mapW_equiv_val] at *
  exact h _ hi

theorem tension_equiv (p q : Wgt A) (e : A≃C) :
    tension (mapW p e) (mapW q e)=tension p q := by
  unfold tension
  rw [mapW_avg]
  simp_rw [mapW_equiv_val,Equiv.symm_apply_apply]

theorem budget_equiv (μ : Wgt A) (p : A → Wgt B) (f : B→C) (e : C≃D) :
    budget μ p (e ∘ f)=budget μ p f := by
  unfold budget
  simp_rw [←map_nested f _,tension_equiv]

set_option maxHeartbeats 800000 in
theorem ample_thresh (V ε : ℝ) (hε : 0<ε) :
    ∃ (r : ℕ) (δ : ℝ),0<δ ∧ ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      tariffs μ p r δ V → ample μ p r ε := by
  classical
  let c := ε/8
  have hc : 0 < c := by positivity
  obtain ⟨α,hα,hα',hh⟩ := ui_threshold V c hc
  obtain ⟨D,hD⟩ := exists_nat_gt (max 0 (V/c^2))
  have hd := (max_lt_iff.mp hD).2
  rw [div_lt_iff₀ (by positivity)] at hd
  let r := 2^(D+1)
  have h0 : 0<(r:ℝ) := by unfold r; positivity
  let k := min (min α c/r) (1/2)
  have hk : 0<k := lt_min (div_pos (lt_min hα hc) h0) (by norm_num)
  have hk0 : k≤1/2 := min_le_right ..
  have hk' : k≤1 := le_trans hk0 (by norm_num)
  let δ := min α (k^D)
  have hδ : 0<δ := lt_min hα (pow_pos hk D)
  refine ⟨r,δ,hδ,fun A B _ _ _ μ p hw hV => ?_⟩
  let e : Wgt B := unif
  have he : IsLaw e := unif_law
  by_contra h
  have hr2 : 2 ≤ r := by
    unfold r; rw [pow_succ]
    have : 0<2^D := by positivity
    omega
  have ht := hh A B μ p hw (tariffs_monotone hV hr2 (min_le_left ..))
  have hstep (n : ℕ) (hn : n≤ D) :
      ∃ f : B → Fin (2^n), stamina (mapW e f) (k^n) ∧
        ↑n*c^2 ≤ budget μ p f := by
    induction n with
    | zero =>
      let f := fun _ : B => (0 : Fin (2^0))
      refine ⟨f,?_,by simpa using budget_nonneg hw f⟩
      intro i hi
      have hi : i = 0 := by
        have hh := i.isLt; norm_num at hh
        exact Fin.ext (by simp only [Fin.val_zero]; omega)
      subst i; change 1 ≤ pr e (fun x => f x=0)
      simp [f,he.total]
    | succ i ih =>
      obtain ⟨f,hf,hB⟩ := ih (by omega)
      let t := 2^i
      have he' : ∃ w,catalog μ p w ∧ 8*c<varOne w (bucket unif f w) := by
        by_contra! hh
        apply h; refine ⟨t,Nat.pow_le_pow_right (by decide) (by omega),f,?_⟩
        rwa [show 8*c=ε by unfold c; ring] at hh
      obtain ⟨w,hw',hwv⟩ := he'
      have hz : num (Fin t × Bool)*k ≤ min α c := by
        have h1 : Fintype.card (Fin t × Bool) ≤ r :=
          calc _ = 2^(i+1) := by simp [pow_succ,t]
               _ ≤ r := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 := min_le_left (min α c/r) (1/2)
        change k ≤ min α c/r at h2
        rw [le_div_iff₀ h0,mul_comm k] at h2
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hk.le).trans h2
      obtain ⟨F,hF',hF⟩ := divide_progress hw c (k^i) α k hc hk (by linarith)
        (pow_pos hk _) (pow_le_one₀ hk.le hk') ht f hf hz w hw' hwv
      let E : (Fin t×Bool)≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ,t])
      refine ⟨E ∘ F,?_,?_⟩
      · rw [←map_nested,pow_succ' k]; exact stamina_equiv _ E _ hF'
      rw [budget_equiv,Nat.cast_add,Nat.cast_one]; linarith only [hF,hB]
  obtain ⟨f,hf,hf'⟩ := hstep D le_rfl
  have he' : stamina (mapW unif f) δ := fun i hi => (min_le_right ..).trans (hf i hi)
  have hz := hV _ (f:=f) (by simp; unfold r; rw [pow_succ]; omega) he'
  exact (not_lt_of_ge (le_trans hf' hz)) hd
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteProjectionCenters
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Projection Centers -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem var_pour (q : Wgt B) (f : B → C) (hq : IsLaw q) (w v : Wgt C) :
    varOne (pour q f w) (pour q f v)≤varOne w v := by
  classical
  let Q := mapW q f
  have hQ := mapW_law hq f
  let g i := |w i-v i| / Q i
  have he : varOne (pour q f w) (pour q f v)=avg Q g := by
    unfold Q
    rw [mapW_avg]
    unfold varOne avg; refine sum_congr rfl fun i _ => ?_
    simp only [pour,←mul_sub,←sub_div,abs_mul,abs_div,
      abs_of_nonneg (hq.nz i),abs_of_nonneg (hQ.nz _)]
    rfl
  rw [he]
  unfold varOne avg; refine sum_le_sum fun i _ => ?_
  by_cases hi : Q i=0
  · rw [hi,zero_mul]; exact abs_nonneg _
  exact le_of_eq (by unfold g; field_simp)

theorem roster_mono (P Q : Wgt A → Prop) (h : ∀ i,P i→Q i) (r ε)
    (hw : roster Q r ε) : roster P r ε := by
  obtain ⟨t,ht,w,hw⟩ := hw; exact ⟨t,ht,w,fun i hi => hw i (h i hi)⟩

private theorem grid_form (k : ℕ) (hk : 0<k) :
    let G := fun i : Fin (k+1) => (i.val:ℝ)/(k:ℝ)
    ∀ a : ℝ,0≤a→a≤1→∃ i,|a-G i|≤(k:ℝ)⁻¹ := by
  intro G a ha h1
  let i := ⌊a*(k:ℝ)⌋₊
  have hk : 0<(k:ℝ) := by exact_mod_cast hk
  have hx : ↑i≤a*k := Nat.floor_le (by positivity)
  have hy : i≤k := by
    exact_mod_cast (show (i:ℝ)≤k from hx.trans (by nlinarith))
  have hi : a*(k:ℝ)< (i:ℝ) +1 := Nat.lt_floor_add_one _
  refine ⟨⟨i,Nat.lt_succ_of_le hy⟩,?_⟩
  change |a-(i:ℝ)/k|≤_
  rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hk).mpr hx))]
  refine sub_le_iff_le_add.mpr ?_
  rw [← one_div,←add_div]
  exact (le_div_iff₀ hk).mpr (by linarith only [hi])

variable {μ : Wgt A} {p : A→ Wgt B}

theorem roster_price (r : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ s : ℕ,∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      ample μ p r (ε/2) → roster (catalog μ p) s ε := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt (max 0 ((r:ℝ)/(ε/2)))
  have h0 := (max_lt_iff.mp hk).1
  have h1 : 0<ε/2 := by positivity
  have hk' := (div_lt_iff₀ h1).mp ((max_lt_iff.mp hk).2)
  have hv := grid_form k (by exact_mod_cast h0)
  refine ⟨(k+1)^r,fun A B _ _ _ μ p hw ⟨t,ht,f,h⟩ => ?_⟩
  let e := Fintype.equivFin (Fin t → Fin (k+1))
  let G (i : Fin (k+1)) := (i.val:ℝ)/(k:ℝ)
  let g (i : Fin (Fintype.card (Fin t →Fin (k+1)))) := G∘(e.symm i)
  refine ⟨Fintype.card (Fin t → Fin (k+1)),(by simp; exact Nat.pow_le_pow_right (by omega) ht),
    fun i => pour unif f (g i),fun w hw' => ?_⟩
  let Q := mapW w f
  have he := hw.cat_sub w hw'
  choose j hj using fun i : Fin t =>
    hv (Q i) (map_nz he.nz f i) ((pr_le_tot he.nz).trans he.total)
  have he : varOne Q (g (e j)) ≤ ε/2 := by
    refine le_trans (Finset.sum_le_sum (g:=fun i : Fin t => (k:ℝ)⁻¹) ?_) ?_
    · intro i _
      simp only [g,Function.comp_apply,Equiv.symm_apply_apply]
      exact hj i
    simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, Fintype.card_fin,
      ←div_eq_mul_inv]
    rw [mul_comm (k:ℝ)] at hk'
    exact (div_le_iff₀ h0).mpr ((by exact_mod_cast ht : (t:ℝ) ≤ r).trans hk'.le)
  exact ⟨e j,(var_tri _ _ _).trans ((add_le_add (h w hw') ((var_pour _ f unif_law Q
    (g (e j))).trans he)).trans_eq (by ring))⟩

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

theorem stain_rebuild (f : X→Y) (P : Y→Prop) (hw : IsLaw w) :
    subW w (P∘f) = mixW (subW (mapW w f) P) (stained w f) := by
  classical
  have hh := disintegrate hw.nz f
  funext i
  have hi (y) :
      mapW w f y * stained w f y i=
        mapW w f y * onW w (fun x => f x=y) i := by
    by_cases h : mapW w f y=0 <;> simp [stained,h]
  have he := congr_fun hh i
  unfold subW mixW Function.comp
  unfold mixW at he
  rw [he,avg,Finset.sum_mul]
  unfold avg at *
  apply sum_congr rfl
  intro j _
  rw [mul_right_comm _ (ind _), hi]
  by_cases hx : f i=j
  · rw [hx]
  simp only [onW_val,ind_zero hx,mul_zero,zero_div,zero_mul]

theorem stain_inputs (f : X→Y) (hw : IsLaw w) :
    w=mixW (mapW w f) (stained w f) := by
  have ht := stain_rebuild f (fun _ => True) hw
  unfold subW at ht
  simpa only [Function.comp_apply,ind_true,mul_one] using ht

variable {μ : Wgt A}

theorem semi_total (μ : Wgt A) (v : A → Wgt Y) :
    tot (semi μ v)=avg μ (fun i=>tot (v i)) := by
  simpa only [avg_const,mul_one] using semi_avg μ v (fun i=>1)

theorem colored_ultra (hμ : IsLaw μ) (hw : IsLaw w) (K : A→X→B) (v : A→X→Y) :
    Ultra (colored μ w v) (coloredP w v K) := by
  have ht (i) := mapW_law hw (v i)
  refine ⟨⟨fun x => mul_nonneg (hμ.nz _) ((ht _).nz _),?_⟩,
    fun i => mapW_law (stained_law _ hw _) (K i.1)⟩
  unfold colored; rw [semi_total]
  simp_rw [(ht _).total]
  exact hμ.avg_const _

theorem flag_catalog (K : A→ X→B) (v : A→ X→ Y) (P : A→ Y→ Prop)
    (hw : IsLaw w) (hμ : IsLaw μ) :
    catalog (colored μ w v) (coloredP w v K)
      (flaggedW μ w v K P) := by
  classical
  let W := colored μ w v
  have hh := (colored_ultra hμ hw K v).law
  refine ⟨subW W (fun i => P i.1 i.2),subW_nonneg hh.nz _,subW_le hh.nz _,?_⟩
  unfold flaggedW
  simp_rw [stain_rebuild (v _) (P _) hw,map_mix]
  funext x
  simp only [mixW,coloredP,colored,W,avg,subW,semi,Finset.mul_sum,Fintype.sum_prod_type]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem colored_budget [Nonempty Y] (K : A→ X→B) (v : A→ X→ Y) (f : B→C)
    (hw : IsLaw w) (hμ : IsLaw μ) :
    budget (colored μ w v) (coloredP w v K) f ≤
      budget μ (fun i => mapW w (K i)) f + Real.log (num Y) := by
  unfold budget colored coloredP
  rw [semi_avg,← hμ.avg_const (Real.log _),← avg_add]
  apply avg_mono hμ.nz
  intro i
  let u := mapW w (v i)
  have he : IsLaw u := mapW_law hw (v i)
  let q (j : Y) := mapW (mapW (stained w (v i) j) (K i)) f
  have hq (j) : IsLaw (q j) := mapW_law (mapW_law (stained_law _ hw _) _) _
  have ht : mapW (mapW w (K i)) f=mixW u q := by
    calc mapW _ _ = mapW (mapW (mixW u (stained w (v i))) (K i)) f :=
                        congrArg (fun z => mapW (mapW z (K i)) f) (stain_inputs (v i) hw)
         _ = _ := by rw [map_mix,map_mix]
  change avg u (fun j => tension (q j) _)≤ tension _ _+_
  rw [tension_mix,add_comm _ (log _),ht]
  exact add_le_add_left (mix_charge he hq) _
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

theorem hung_roster (Q : Wgt B → Prop) (P : B→Prop) (r : ℕ) (ε : ℝ) :
    roster Q r ε → roster (hung Q P) r ε := by
  classical
  rintro ⟨t,ht,w,hw⟩
  refine ⟨t,ht,fun i => subW (w i) P,?_⟩
  rintro p ⟨v,h,rfl⟩
  obtain ⟨i,hi⟩ := hw v h
  refine ⟨i,le_trans ?_ hi⟩
  unfold varOne subW
  refine sum_le_sum fun x _ => ?_
  by_cases h : P x <;> simp [ind,h]

variable [Nonempty B]

theorem hung_small (Q : Wgt B→Prop) (P : B→Prop) (δ η : ℝ)
    (hq : smallSet Q unif δ η) : smallSet (hung Q P) (unifOn P) δ η := by
  classical
  rintro p ⟨v,hv,rfl⟩ S hs
  rw [pr_sub]
  refine hq v hv (fun x => P x∧ S x) ?_
  rw [pr_of_on unif_law.nz,on_unif]
  refine le_trans ?_ hs
  have ht := (pr_le_tot (α:=B) (p:=P) unif_law.nz).trans unif_law.total.le
  exact (mul_le_mul_of_nonneg_right ht (pr_nonneg (unifOn_sub _).nz)).trans_eq (one_mul _)

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

theorem hung_tail (Q : Wgt B→Prop) (P : B→ Prop)
    (h : ∀ p,Q p → SubLaw p) (δ η : ℝ)
    (hδ : 0<δ) (hh : smallSet Q unif δ η) :
    rosterTail (hung Q P) (unifOn P) δ⁻¹ η := by
  intro p hp
  apply hung_small Q P δ η hh p hp
  obtain ⟨w,hw,rfl⟩ := hp
  let q := unifOn P
  let v := subW w P
  let f := density q v
  have hq := unifOn_sub P
  have hv := subLaw_sub (h w hw) P
  have hh :
      avg q f = tot v := Finset.sum_congr rfl fun i _ => density_hung P v
        (subW_carried w P) i
  have hz := le_avg_markov hq.nz (fun i => div_nonneg (hv.nz i) (hq.nz i)) δ⁻¹
  change δ⁻¹*pr q _≤avg q f at hz
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos hδ)
  rw [inv_mul_cancel₀ hδ.ne']
  exact (hz.trans_eq hh).trans hv.total

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_HistogramBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Histogram Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators
variable {A X B C Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]

variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

namespace Template
set_option maxHeartbeats 1200000 in
theorem controls_oai (v : Template p I) (M : ℕ) (hM : 1≤M)
    (Y : Type) [Fintype Y] [Nonempty Y]
    (C η ε : ℝ) (hC : 0≤C) (hη : 0<η) (hε : 0<ε) :
    ∃ (r : ℕ) (δ R : ℝ), 0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n; let A := UnitType p n N
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      ∀ (w : Wgt A), IsLaw w →
      (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) →
      ∀ (f : A→Inputs p n I→Y),
        let Q := fromFlags w (prodW x) f (v.resultKey)
        Haberdash Q r δ R η ε := by
  classical
  obtain ⟨V,hV⟩ := hist_calendar v M hM C hC
  let U := V + log (num Y)
  obtain ⟨δ,hδ,_,hh⟩ := ui_threshold U η hη
  obtain ⟨r,a,ha,he⟩ := ample_thresh U (ε/2) (by positivity)
  obtain ⟨s,hR⟩ := roster_price r ε hε
  let D := min a δ; let z := max r 2
  refine ⟨s,δ,δ⁻¹,hδ,inv_pos_of_pos hδ,?_⟩
  filter_upwards [hV z D (Nat.cast_nonneg _) (lt_min ha hδ)]
    with n hn N A m hN w hw h x hx hz f Q
  let X := prodW x
  let K := resultKey v (n:=n) (N:=N)
  let B := Keys (p:=p) v.t N
  let μ := colored w X f
  let q := coloredP X f K
  have hX : IsLaw X := prodW_law hx
  have hu := colored_ultra hw hX K f
  have hg : tariffs μ q z D U := by
    intro C _ hC F hF
    refine (colored_budget K f F hX hw).trans ?_
    exact add_le_add_left (hn m hN w hw h x hx hz _ (by exact_mod_cast hC) F hF) _
  have h1 := tariffs_monotone hg (le_max_left ..) (min_le_left ..)
  have h2 := tariffs_monotone hg (le_max_right ..) (min_le_right ..)
  have ha := he (A×Y) B μ q hu h1
  have h3 (y : Wgt B) (hy : Q y) : catalog μ q y := by
    obtain ⟨P,rfl⟩ := hy
    exact flag_catalog K f P hX hw
  have h4 (y : Wgt B) (hy : Q y) : SubLaw y := hu.cat_sub _ (h3 y hy)
  have hi : roster Q s ε :=
    roster_mono Q _ h3 s ε (hR (A×Y) B μ q hu ha)
  have hj : smallSet Q unif δ η := fun i ht S hS =>
      (pr_mono_left (hu.cat_dom i (h3 i ht)).2 S).trans (hh (A×Y) B μ q hu h2 S hS)
  exact ⟨h4,hi,hj,fun P => ⟨hung_roster Q P _ _ hi,hung_small Q P _ _ hj,hung_tail Q P h4
    _ _ hδ hj⟩⟩
end Template
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.Template.controls_oai := @OAI.HadwigerCounterexample.Template.controls_oai
